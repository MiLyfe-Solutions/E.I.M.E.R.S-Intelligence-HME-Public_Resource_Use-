import V185TrunkScan20Chunk068

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_419381 : List Nat := [1, 3, 3, 1, 1, 5, 1, 1, 4]
def baseStart_419381 : Nat := 118140960795 + 419381 * 2 ^ 59
def prefixEnd_419381 : Nat := 4983230072969 + 3 ^ 40 * 419381 * 2
def baseEnd_419381 : Nat := 191416915878514580985607

theorem tailTrace_419381 : CollatzResearch.WordTrace tailWord_419381 prefixEnd_419381 191416915878514580985607 := by
  unfold tailWord_419381
  simp only [CollatzResearch.WordTrace]
  refine ⟨15296081693661736417585997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10197387795774490945057331 15296081693661736417585997)
  ·
    refine ⟨5736030635123151156594749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15296081693661736417585997 5736030635123151156594749)
    ·
      refine ⟨2151011488171181683723031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5736030635123151156594749 2151011488171181683723031)
      ·
        refine ⟨3226517232256772525584547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2151011488171181683723031 3226517232256772525584547)
        ·
          refine ⟨4839775848385158788376821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3226517232256772525584547 4839775848385158788376821)
          ·
            refine ⟨453728985786108636410327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4839775848385158788376821 453728985786108636410327)
            ·
              refine ⟨680593478679162954615491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453728985786108636410327 680593478679162954615491)
              ·
                refine ⟨1020890218018744431923237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680593478679162954615491 1020890218018744431923237)
                ·
                  refine ⟨191416915878514580985607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1020890218018744431923237 191416915878514580985607)
                  ·
                    rfl

theorem cell20_419381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_419381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419381 prefixEnd_419381 := by exact prefixLift 419381
  have htrace : WordTrace (prefixWord ++ tailWord_419381) baseStart_419381 baseEnd_419381 := by
    simpa [prefixWord, tailWord_419381, baseEnd_419381] using wordTrace_append hprefix tailTrace_419381
  have hstable : (prefixWord ++ tailWord_419381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419381).length < 2 ^ (prefixWord ++ tailWord_419381).sum := by decide
  have hdescent : baseEnd_419381 < baseStart_419381 := by decide
  rcases family_descends (prefixWord ++ tailWord_419381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419388 : List Nat := [2, 2, 2, 2, 4, 1, 2, 5]
def baseStart_419388 : Nat := 118140960795 + 419388 * 2 ^ 59
def prefixEnd_419388 : Nat := 4983230072969 + 3 ^ 40 * 419388 * 2
def baseEnd_419388 : Nat := 63806703623084555917415

theorem tailTrace_419388 : CollatzResearch.WordTrace tailWord_419388 prefixEnd_419388 63806703623084555917415 := by
  unfold tailWord_419388
  simp only [CollatzResearch.WordTrace]
  refine ⟨7648168502318188306545409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10197558003090917742060545 7648168502318188306545409)
  ·
    refine ⟨5736126376738641229909057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7648168502318188306545409 5736126376738641229909057)
    ·
      refine ⟨4302094782553980922431793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5736126376738641229909057 4302094782553980922431793)
      ·
        refine ⟨3226571086915485691823845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4302094782553980922431793 3226571086915485691823845)
        ·
          refine ⟨604982078796653567216971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3226571086915485691823845 604982078796653567216971)
          ·
            refine ⟨907473118194980350825457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604982078796653567216971 907473118194980350825457)
            ·
              refine ⟨680604838646235263119093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 907473118194980350825457 680604838646235263119093)
              ·
                refine ⟨63806703623084555917415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 680604838646235263119093 63806703623084555917415)
                ·
                  rfl

theorem cell20_419388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_419388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419388 prefixEnd_419388 := by exact prefixLift 419388
  have htrace : WordTrace (prefixWord ++ tailWord_419388) baseStart_419388 baseEnd_419388 := by
    simpa [prefixWord, tailWord_419388, baseEnd_419388] using wordTrace_append hprefix tailTrace_419388
  have hstable : (prefixWord ++ tailWord_419388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419388).length < 2 ^ (prefixWord ++ tailWord_419388).sum := by decide
  have hdescent : baseEnd_419388 < baseStart_419388 := by decide
  rcases family_descends (prefixWord ++ tailWord_419388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419488 : List Nat := [2, 1, 1, 4, 3, 3, 1, 2, 3]
def baseStart_419488 : Nat := 118140960795 + 419488 * 2 ^ 59
def prefixEnd_419488 : Nat := 4983230072969 + 3 ^ 40 * 419488 * 2
def baseEnd_419488 : Nat := 191465753594097764418503

theorem tailTrace_419488 : CollatzResearch.WordTrace tailWord_419488 prefixEnd_419488 191465753594097764418503 := by
  unfold tailWord_419488
  simp only [CollatzResearch.WordTrace]
  refine ⟨7649992152137046845865559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10199989536182729127820745 7649992152137046845865559)
  ·
    refine ⟨11474988228205570268798339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7649992152137046845865559 11474988228205570268798339)
    ·
      refine ⟨17212482342308355403197509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11474988228205570268798339 17212482342308355403197509)
      ·
        refine ⟨3227340439182816638099533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17212482342308355403197509 3227340439182816638099533)
        ·
          refine ⟨1210252664693556239287325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3227340439182816638099533 1210252664693556239287325)
          ·
            refine ⟨453844749260083589732747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1210252664693556239287325 453844749260083589732747)
            ·
              refine ⟨680767123890125384599121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453844749260083589732747 680767123890125384599121)
              ·
                refine ⟨510575342917594038449341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 680767123890125384599121 510575342917594038449341)
                ·
                  refine ⟨191465753594097764418503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 510575342917594038449341 191465753594097764418503)
                  ·
                    rfl

theorem cell20_419488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 3].length) (baseStart_419488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419488 prefixEnd_419488 := by exact prefixLift 419488
  have htrace : WordTrace (prefixWord ++ tailWord_419488) baseStart_419488 baseEnd_419488 := by
    simpa [prefixWord, tailWord_419488, baseEnd_419488] using wordTrace_append hprefix tailTrace_419488
  have hstable : (prefixWord ++ tailWord_419488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419488).length < 2 ^ (prefixWord ++ tailWord_419488).sum := by decide
  have hdescent : baseEnd_419488 < baseStart_419488 := by decide
  rcases family_descends (prefixWord ++ tailWord_419488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419516 : List Nat := [2, 2, 2, 3, 1, 2, 2, 2, 4]
def baseStart_419516 : Nat := 118140960795 + 419516 * 2 ^ 59
def prefixEnd_419516 : Nat := 4983230072969 + 3 ^ 40 * 419516 * 2
def baseEnd_419516 : Nat := 191478533557054111485055

theorem tailTrace_419516 : CollatzResearch.WordTrace tailWord_419516 prefixEnd_419516 191478533557054111485055 := by
  unfold tailWord_419516
  simp only [CollatzResearch.WordTrace]
  refine ⟨7650502774086327236875201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10200670365448436315833601 7650502774086327236875201)
  ·
    refine ⟨5737877080564745427656401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7650502774086327236875201 5737877080564745427656401)
    ·
      refine ⟨4303407810423559070742301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5737877080564745427656401 4303407810423559070742301)
      ·
        refine ⟨1613777928908834651528363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4303407810423559070742301 1613777928908834651528363)
        ·
          refine ⟨2420666893363251977292545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1613777928908834651528363 2420666893363251977292545)
          ·
            refine ⟨1815500170022438982969409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2420666893363251977292545 1815500170022438982969409)
            ·
              refine ⟨1361625127516829237227057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1815500170022438982969409 1361625127516829237227057)
              ·
                refine ⟨1021218845637621927920293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1361625127516829237227057 1021218845637621927920293)
                ·
                  refine ⟨191478533557054111485055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1021218845637621927920293 191478533557054111485055)
                  ·
                    rfl

theorem cell20_419516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_419516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419516 prefixEnd_419516 := by exact prefixLift 419516
  have htrace : WordTrace (prefixWord ++ tailWord_419516) baseStart_419516 baseEnd_419516 := by
    simpa [prefixWord, tailWord_419516, baseEnd_419516] using wordTrace_append hprefix tailTrace_419516
  have hstable : (prefixWord ++ tailWord_419516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419516).length < 2 ^ (prefixWord ++ tailWord_419516).sum := by decide
  have hdescent : baseEnd_419516 < baseStart_419516 := by decide
  rcases family_descends (prefixWord ++ tailWord_419516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419540 : List Nat := [2, 4, 1, 3, 1, 3, 6]
def baseStart_419540 : Nat := 118140960795 + 419540 * 2 ^ 59
def prefixEnd_419540 : Nat := 4983230072969 + 3 ^ 40 * 419540 * 2
def baseEnd_419540 : Nat := 21276609756779632742773

theorem tailTrace_419540 : CollatzResearch.WordTrace tailWord_419540 prefixEnd_419540 21276609756779632742773 := by
  unfold tailWord_419540
  simp only [CollatzResearch.WordTrace]
  refine ⟨7650940450042853286312037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10201253933390471048416049 7650940450042853286312037)
  ·
    refine ⟨1434551334383034991183507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7650940450042853286312037 1434551334383034991183507)
    ·
      refine ⟨2151827001574552486775261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1434551334383034991183507 2151827001574552486775261)
      ·
        refine ⟨806935125590457182540723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2151827001574552486775261 806935125590457182540723)
        ·
          refine ⟨1210402688385685773811085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 806935125590457182540723 1210402688385685773811085)
          ·
            refine ⟨453901008144632165179157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1210402688385685773811085 453901008144632165179157)
            ·
              refine ⟨21276609756779632742773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 453901008144632165179157 21276609756779632742773)
              ·
                rfl

theorem cell20_419540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 6].length) (baseStart_419540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419540 prefixEnd_419540 := by exact prefixLift 419540
  have htrace : WordTrace (prefixWord ++ tailWord_419540) baseStart_419540 baseEnd_419540 := by
    simpa [prefixWord, tailWord_419540, baseEnd_419540] using wordTrace_append hprefix tailTrace_419540
  have hstable : (prefixWord ++ tailWord_419540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419540).length < 2 ^ (prefixWord ++ tailWord_419540).sum := by decide
  have hdescent : baseEnd_419540 < baseStart_419540 := by decide
  rcases family_descends (prefixWord ++ tailWord_419540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419575 : List Nat := [1, 1, 3, 1, 1, 1, 4, 4, 4]
def baseStart_419575 : Nat := 118140960795 + 419575 * 2 ^ 59
def prefixEnd_419575 : Nat := 4983230072969 + 3 ^ 40 * 419575 * 2
def baseEnd_419575 : Nat := 191505462764712128518147

theorem tailTrace_419575 : CollatzResearch.WordTrace tailWord_419575 prefixEnd_419575 191505462764712128518147 := by
  unfold tailWord_419575
  simp only [CollatzResearch.WordTrace]
  refine ⟨15303157454958907550148179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10202104969972605033432119 15303157454958907550148179)
  ·
    refine ⟨22954736182438361325222269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15303157454958907550148179 22954736182438361325222269)
    ·
      refine ⟨8608026068414385496958351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22954736182438361325222269 8608026068414385496958351)
      ·
        refine ⟨12912039102621578245437527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8608026068414385496958351 12912039102621578245437527)
        ·
          refine ⟨19368058653932367368156291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12912039102621578245437527 19368058653932367368156291)
          ·
            refine ⟨29052087980898551052234437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19368058653932367368156291 29052087980898551052234437)
            ·
              refine ⟨5447266496418478322293957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29052087980898551052234437 5447266496418478322293957)
              ·
                refine ⟨1021362468078464685430117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5447266496418478322293957 1021362468078464685430117)
                ·
                  refine ⟨191505462764712128518147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1021362468078464685430117 191505462764712128518147)
                  ·
                    rfl

theorem cell20_419575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_419575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419575 prefixEnd_419575 := by exact prefixLift 419575
  have htrace : WordTrace (prefixWord ++ tailWord_419575) baseStart_419575 baseEnd_419575 := by
    simpa [prefixWord, tailWord_419575, baseEnd_419575] using wordTrace_append hprefix tailTrace_419575
  have hstable : (prefixWord ++ tailWord_419575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419575).length < 2 ^ (prefixWord ++ tailWord_419575).sum := by decide
  have hdescent : baseEnd_419575 < baseStart_419575 := by decide
  rcases family_descends (prefixWord ++ tailWord_419575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419597 : List Nat := [1, 7, 2, 1, 2, 1, 2, 2, 2]
def baseStart_419597 : Nat := 118140960795 + 419597 * 2 ^ 59
def prefixEnd_419597 : Nat := 4983230072969 + 3 ^ 40 * 419597 * 2
def baseEnd_419597 : Nat := 191515504164177829784725

theorem tailTrace_419597 : CollatzResearch.WordTrace tailWord_419597 prefixEnd_419597 191515504164177829784725 := by
  unfold tailWord_419597
  simp only [CollatzResearch.WordTrace]
  refine ⟨15303959860879205307449045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10202639907252803538299363 15303959860879205307449045)
  ·
    refine ⟨358686559239356374393337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 15303959860879205307449045 358686559239356374393337)
    ·
      refine ⟨269014919429517280795003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358686559239356374393337 269014919429517280795003)
      ·
        refine ⟨403522379144275921192505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269014919429517280795003 403522379144275921192505)
        ·
          refine ⟨302641784358206940894379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403522379144275921192505 302641784358206940894379)
          ·
            refine ⟨453962676537310411341569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302641784358206940894379 453962676537310411341569)
            ·
              refine ⟨340472007402982808506177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453962676537310411341569 340472007402982808506177)
              ·
                refine ⟨255354005552237106379633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340472007402982808506177 255354005552237106379633)
                ·
                  refine ⟨191515504164177829784725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255354005552237106379633 191515504164177829784725)
                  ·
                    rfl

theorem cell20_419597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_419597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419597 prefixEnd_419597 := by exact prefixLift 419597
  have htrace : WordTrace (prefixWord ++ tailWord_419597) baseStart_419597 baseEnd_419597 := by
    simpa [prefixWord, tailWord_419597, baseEnd_419597] using wordTrace_append hprefix tailTrace_419597
  have hstable : (prefixWord ++ tailWord_419597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419597).length < 2 ^ (prefixWord ++ tailWord_419597).sum := by decide
  have hdescent : baseEnd_419597 < baseStart_419597 := by decide
  rcases family_descends (prefixWord ++ tailWord_419597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419602 : List Nat := [3, 2, 4, 1, 1, 1, 1, 4, 3]
def baseStart_419602 : Nat := 118140960795 + 419602 * 2 ^ 59
def prefixEnd_419602 : Nat := 4983230072969 + 3 ^ 40 * 419602 * 2
def baseEnd_419602 : Nat := 191517786300420034618037

theorem tailTrace_419602 : CollatzResearch.WordTrace tailWord_419602 prefixEnd_419602 191517786300420034618037 := by
  unfold tailWord_419602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3826035556465272790345265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10202761483907394107587373 3826035556465272790345265)
  ·
    refine ⟨2869526667348954592758949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3826035556465272790345265 2869526667348954592758949)
    ·
      refine ⟨538036250127928986142303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2869526667348954592758949 538036250127928986142303)
      ·
        refine ⟨807054375191893479213455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538036250127928986142303 807054375191893479213455)
        ·
          refine ⟨1210581562787840218820183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807054375191893479213455 1210581562787840218820183)
          ·
            refine ⟨1815872344181760328230275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1210581562787840218820183 1815872344181760328230275)
            ·
              refine ⟨2723808516272640492345413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1815872344181760328230275 2723808516272640492345413)
              ·
                refine ⟨510714096801120092314765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2723808516272640492345413 510714096801120092314765)
                ·
                  refine ⟨191517786300420034618037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 510714096801120092314765 191517786300420034618037)
                  ·
                    rfl

theorem cell20_419602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_419602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419602 prefixEnd_419602 := by exact prefixLift 419602
  have htrace : WordTrace (prefixWord ++ tailWord_419602) baseStart_419602 baseEnd_419602 := by
    simpa [prefixWord, tailWord_419602, baseEnd_419602] using wordTrace_append hprefix tailTrace_419602
  have hstable : (prefixWord ++ tailWord_419602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419602).length < 2 ^ (prefixWord ++ tailWord_419602).sum := by decide
  have hdescent : baseEnd_419602 < baseStart_419602 := by decide
  rcases family_descends (prefixWord ++ tailWord_419602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419658 : List Nat := [3, 1, 2, 1, 1, 1, 11]
def baseStart_419658 : Nat := 118140960795 + 419658 * 2 ^ 59
def prefixEnd_419658 : Nat := 4983230072969 + 3 ^ 40 * 419658 * 2
def baseEnd_419658 : Nat := 21282594025148080972349

theorem tailTrace_419658 : CollatzResearch.WordTrace tailWord_419658 prefixEnd_419658 21282594025148080972349 := by
  unfold tailWord_419658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3826546178414553181354907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10204123142438808483613085 3826546178414553181354907)
  ·
    refine ⟨5739819267621829772032361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3826546178414553181354907 5739819267621829772032361)
    ·
      refine ⟨4304864450716372329024271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5739819267621829772032361 4304864450716372329024271)
      ·
        refine ⟨6457296676074558493536407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4304864450716372329024271 6457296676074558493536407)
        ·
          refine ⟨9685945014111837740304611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6457296676074558493536407 9685945014111837740304611)
          ·
            refine ⟨14528917521167756610456917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9685945014111837740304611 14528917521167756610456917)
            ·
              refine ⟨21282594025148080972349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14528917521167756610456917 21282594025148080972349)
              ·
                rfl

theorem cell20_419658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 11].length) (baseStart_419658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419658 prefixEnd_419658 := by exact prefixLift 419658
  have htrace : WordTrace (prefixWord ++ tailWord_419658) baseStart_419658 baseEnd_419658 := by
    simpa [prefixWord, tailWord_419658, baseEnd_419658] using wordTrace_append hprefix tailTrace_419658
  have hstable : (prefixWord ++ tailWord_419658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419658).length < 2 ^ (prefixWord ++ tailWord_419658).sum := by decide
  have hdescent : baseEnd_419658 < baseStart_419658 := by decide
  rcases family_descends (prefixWord ++ tailWord_419658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419668 : List Nat := [2, 4, 1, 1, 3, 1, 1, 3, 4]
def baseStart_419668 : Nat := 118140960795 + 419668 * 2 ^ 59
def prefixEnd_419668 : Nat := 4983230072969 + 3 ^ 40 * 419668 * 2
def baseEnd_419668 : Nat := 191547910498817138417767

theorem tailTrace_419668 : CollatzResearch.WordTrace tailWord_419668 prefixEnd_419668 191547910498817138417767 := by
  unfold tailWord_419668
  simp only [CollatzResearch.WordTrace]
  refine ⟨7653274721810992216641829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10204366295747989622189105 7653274721810992216641829)
  ·
    refine ⟨1434989010339561040620343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7653274721810992216641829 1434989010339561040620343)
    ·
      refine ⟨2152483515509341560930515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1434989010339561040620343 2152483515509341560930515)
      ·
        refine ⟨3228725273264012341395773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2152483515509341560930515 3228725273264012341395773)
        ·
          refine ⟨1210771977474004628023415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3228725273264012341395773 1210771977474004628023415)
          ·
            refine ⟨1816157966211006942035123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1210771977474004628023415 1816157966211006942035123)
            ·
              refine ⟨2724236949316510413052685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1816157966211006942035123 2724236949316510413052685)
              ·
                refine ⟨1021588855993691404894757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2724236949316510413052685 1021588855993691404894757)
                ·
                  refine ⟨191547910498817138417767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1021588855993691404894757 191547910498817138417767)
                  ·
                    rfl

theorem cell20_419668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_419668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419668 prefixEnd_419668 := by exact prefixLift 419668
  have htrace : WordTrace (prefixWord ++ tailWord_419668) baseStart_419668 baseEnd_419668 := by
    simpa [prefixWord, tailWord_419668, baseEnd_419668] using wordTrace_append hprefix tailTrace_419668
  have hstable : (prefixWord ++ tailWord_419668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419668).length < 2 ^ (prefixWord ++ tailWord_419668).sum := by decide
  have hdescent : baseEnd_419668 < baseStart_419668 := by decide
  rcases family_descends (prefixWord ++ tailWord_419668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419692 : List Nat := [2, 2, 1, 1, 4, 4, 2, 4]
def baseStart_419692 : Nat := 118140960795 + 419692 * 2 ^ 59
def prefixEnd_419692 : Nat := 4983230072969 + 3 ^ 40 * 419692 * 2
def baseEnd_419692 : Nat := 63852954917593240539223

theorem tailTrace_419692 : CollatzResearch.WordTrace tailWord_419692 prefixEnd_419692 63852954917593240539223 := by
  unfold tailWord_419692
  simp only [CollatzResearch.WordTrace]
  refine ⟨7653712397767518266078665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10204949863690024354771553 7653712397767518266078665)
  ·
    refine ⟨5740284298325638699558999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7653712397767518266078665 5740284298325638699558999)
    ·
      refine ⟨8610426447488458049338499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5740284298325638699558999 8610426447488458049338499)
      ·
        refine ⟨12915639671232687074007749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8610426447488458049338499 12915639671232687074007749)
        ·
          refine ⟨2421682438356128826376453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12915639671232687074007749 2421682438356128826376453)
          ·
            refine ⟨454065457191774154945585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2421682438356128826376453 454065457191774154945585)
            ·
              refine ⟨340549092893830616209189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454065457191774154945585 340549092893830616209189)
              ·
                refine ⟨63852954917593240539223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 340549092893830616209189 63852954917593240539223)
                ·
                  rfl

theorem cell20_419692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_419692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419692 prefixEnd_419692 := by exact prefixLift 419692
  have htrace : WordTrace (prefixWord ++ tailWord_419692) baseStart_419692 baseEnd_419692 := by
    simpa [prefixWord, tailWord_419692, baseEnd_419692] using wordTrace_append hprefix tailTrace_419692
  have hstable : (prefixWord ++ tailWord_419692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419692).length < 2 ^ (prefixWord ++ tailWord_419692).sum := by decide
  have hdescent : baseEnd_419692 < baseStart_419692 := by decide
  rcases family_descends (prefixWord ++ tailWord_419692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419730 : List Nat := [3, 2, 3, 2, 1, 2, 2, 5]
def baseStart_419730 : Nat := 118140960795 + 419730 * 2 ^ 59
def prefixEnd_419730 : Nat := 4983230072969 + 3 ^ 40 * 419730 * 2
def baseEnd_419730 : Nat := 63858736329406826116949

theorem tailTrace_419730 : CollatzResearch.WordTrace tailWord_419730 prefixEnd_419730 63858736329406826116949 := by
  unfold tailWord_419730
  simp only [CollatzResearch.WordTrace]
  refine ⟨3827202692349342255510161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10205873846264912681360429 3827202692349342255510161)
  ·
    refine ⟨2870402019262006691632621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3827202692349342255510161 2870402019262006691632621)
    ·
      refine ⟨1076400757223252509362233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2870402019262006691632621 1076400757223252509362233)
      ·
        refine ⟨807300567917439382021675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1076400757223252509362233 807300567917439382021675)
        ·
          refine ⟨1210950851876159073032513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807300567917439382021675 1210950851876159073032513)
          ·
            refine ⟨908213138907119304774385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1210950851876159073032513 908213138907119304774385)
            ·
              refine ⟨681159854180339478580789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 908213138907119304774385 681159854180339478580789)
              ·
                refine ⟨63858736329406826116949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 681159854180339478580789 63858736329406826116949)
                ·
                  rfl

theorem cell20_419730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_419730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419730 prefixEnd_419730 := by exact prefixLift 419730
  have htrace : WordTrace (prefixWord ++ tailWord_419730) baseStart_419730 baseEnd_419730 := by
    simpa [prefixWord, tailWord_419730, baseEnd_419730] using wordTrace_append hprefix tailTrace_419730
  have hstable : (prefixWord ++ tailWord_419730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419730).length < 2 ^ (prefixWord ++ tailWord_419730).sum := by decide
  have hdescent : baseEnd_419730 < baseStart_419730 := by decide
  rcases family_descends (prefixWord ++ tailWord_419730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419737 : List Nat := [1, 2, 1, 2, 1, 3, 6, 1, 3]
def baseStart_419737 : Nat := 118140960795 + 419737 * 2 ^ 59
def prefixEnd_419737 : Nat := 4983230072969 + 3 ^ 40 * 419737 * 2
def baseEnd_419737 : Nat := 191579403978959565117485

theorem tailTrace_419737 : CollatzResearch.WordTrace tailWord_419737 prefixEnd_419737 191579403978959565117485 := by
  unfold tailWord_419737
  simp only [CollatzResearch.WordTrace]
  refine ⟨15309066080372009217545465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10206044053581339478363643 15309066080372009217545465)
  ·
    refine ⟨11481799560279006913159099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15309066080372009217545465 11481799560279006913159099)
    ·
      refine ⟨17222699340418510369738649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11481799560279006913159099 17222699340418510369738649)
      ·
        refine ⟨12917024505313882777303987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17222699340418510369738649 12917024505313882777303987)
        ·
          refine ⟨19375536757970824165955981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12917024505313882777303987 19375536757970824165955981)
          ·
            refine ⟨7265826284239059062233493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19375536757970824165955981 7265826284239059062233493)
            ·
              refine ⟨340585607073705893542195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7265826284239059062233493 340585607073705893542195)
              ·
                refine ⟨510878410610558840313293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340585607073705893542195 510878410610558840313293)
                ·
                  refine ⟨191579403978959565117485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 510878410610558840313293 191579403978959565117485)
                  ·
                    rfl

theorem cell20_419737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 3].length) (baseStart_419737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419737 prefixEnd_419737 := by exact prefixLift 419737
  have htrace : WordTrace (prefixWord ++ tailWord_419737) baseStart_419737 baseEnd_419737 := by
    simpa [prefixWord, tailWord_419737, baseEnd_419737] using wordTrace_append hprefix tailTrace_419737
  have hstable : (prefixWord ++ tailWord_419737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419737).length < 2 ^ (prefixWord ++ tailWord_419737).sum := by decide
  have hdescent : baseEnd_419737 < baseStart_419737 := by decide
  rcases family_descends (prefixWord ++ tailWord_419737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419751 : List Nat := [1, 1, 6, 1, 2, 1, 2, 6]
def baseStart_419751 : Nat := 118140960795 + 419751 * 2 ^ 59
def prefixEnd_419751 : Nat := 4983230072969 + 3 ^ 40 * 419751 * 2
def baseEnd_419751 : Nat := 63861931320145912883587

theorem tailTrace_419751 : CollatzResearch.WordTrace tailWord_419751 prefixEnd_419751 63861931320145912883587 := by
  unfold tailWord_419751
  simp only [CollatzResearch.WordTrace]
  refine ⟨15309576702321289608555107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10206384468214193072370071 15309576702321289608555107)
  ·
    refine ⟨22964365053481934412832661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15309576702321289608555107 22964365053481934412832661)
    ·
      refine ⟨1076454611881965675601531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22964365053481934412832661 1076454611881965675601531)
      ·
        refine ⟨1614681917822948513402297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1076454611881965675601531 1614681917822948513402297)
        ·
          refine ⟨1211011438367211385051723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1614681917822948513402297 1211011438367211385051723)
          ·
            refine ⟨1816517157550817077577585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211011438367211385051723 1816517157550817077577585)
            ·
              refine ⟨1362387868163112808183189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1816517157550817077577585 1362387868163112808183189)
              ·
                refine ⟨63861931320145912883587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1362387868163112808183189 63861931320145912883587)
                ·
                  rfl

theorem cell20_419751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 6].length) (baseStart_419751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419751 prefixEnd_419751 := by exact prefixLift 419751
  have htrace : WordTrace (prefixWord ++ tailWord_419751) baseStart_419751 baseEnd_419751 := by
    simpa [prefixWord, tailWord_419751, baseEnd_419751] using wordTrace_append hprefix tailTrace_419751
  have hstable : (prefixWord ++ tailWord_419751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419751).length < 2 ^ (prefixWord ++ tailWord_419751).sum := by decide
  have hdescent : baseEnd_419751 < baseStart_419751 := by decide
  rcases family_descends (prefixWord ++ tailWord_419751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419848 : List Nat := [2, 1, 3, 2, 1, 2, 2, 7]
def baseStart_419848 : Nat := 118140960795 + 419848 * 2 ^ 59
def prefixEnd_419848 : Nat := 4983230072969 + 3 ^ 40 * 419848 * 2
def baseEnd_419848 : Nat := 63876689134512170805677

theorem tailTrace_419848 : CollatzResearch.WordTrace tailWord_419848 prefixEnd_419848 63876689134512170805677 := by
  unfold tailWord_419848
  simp only [CollatzResearch.WordTrace]
  refine ⟨7656557291484937587418099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10208743055313250116557465 7656557291484937587418099)
  ·
    refine ⟨11484835937227406381127149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7656557291484937587418099 11484835937227406381127149)
    ·
      refine ⟨4306813476460277392922681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11484835937227406381127149 4306813476460277392922681)
      ·
        refine ⟨3230110107345208044692011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4306813476460277392922681 3230110107345208044692011)
        ·
          refine ⟨4845165161017812067038017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3230110107345208044692011 4845165161017812067038017)
          ·
            refine ⟨3633873870763359050278513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4845165161017812067038017 3633873870763359050278513)
            ·
              refine ⟨2725405403072519287708885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3633873870763359050278513 2725405403072519287708885)
              ·
                refine ⟨63876689134512170805677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2725405403072519287708885 63876689134512170805677)
                ·
                  rfl

theorem cell20_419848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_419848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419848 prefixEnd_419848 := by exact prefixLift 419848
  have htrace : WordTrace (prefixWord ++ tailWord_419848) baseStart_419848 baseEnd_419848 := by
    simpa [prefixWord, tailWord_419848, baseEnd_419848] using wordTrace_append hprefix tailTrace_419848
  have hstable : (prefixWord ++ tailWord_419848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419848).length < 2 ^ (prefixWord ++ tailWord_419848).sum := by decide
  have hdescent : baseEnd_419848 < baseStart_419848 := by decide
  rcases family_descends (prefixWord ++ tailWord_419848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419851 : List Nat := [1, 1, 1, 1, 6, 1, 5, 1, 3]
def baseStart_419851 : Nat := 118140960795 + 419851 * 2 ^ 59
def prefixEnd_419851 : Nat := 4983230072969 + 3 ^ 40 * 419851 * 2
def baseEnd_419851 : Nat := 191631436685281835317019

theorem tailTrace_419851 : CollatzResearch.WordTrace tailWord_419851 prefixEnd_419851 191631436685281835317019 := by
  unfold tailWord_419851
  simp only [CollatzResearch.WordTrace]
  refine ⟨15313224001959006687195407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10208816001306004458130271 15313224001959006687195407)
  ·
    refine ⟨22969836002938510030793111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15313224001959006687195407 22969836002938510030793111)
    ·
      refine ⟨34454754004407765046189667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22969836002938510030793111 34454754004407765046189667)
      ·
        refine ⟨51682131006611647569284501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34454754004407765046189667 51682131006611647569284501)
        ·
          refine ⟨2422599890934920979810211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51682131006611647569284501 2422599890934920979810211)
          ·
            refine ⟨3633899836402381469715317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2422599890934920979810211 3633899836402381469715317)
            ·
              refine ⟨340678109662723262785811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3633899836402381469715317 340678109662723262785811)
              ·
                refine ⟨511017164494084894178717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340678109662723262785811 511017164494084894178717)
                ·
                  refine ⟨191631436685281835317019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511017164494084894178717 191631436685281835317019)
                  ·
                    rfl

theorem cell20_419851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 3].length) (baseStart_419851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419851 prefixEnd_419851 := by exact prefixLift 419851
  have htrace : WordTrace (prefixWord ++ tailWord_419851) baseStart_419851 baseEnd_419851 := by
    simpa [prefixWord, tailWord_419851, baseEnd_419851] using wordTrace_append hprefix tailTrace_419851
  have hstable : (prefixWord ++ tailWord_419851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419851).length < 2 ^ (prefixWord ++ tailWord_419851).sum := by decide
  have hdescent : baseEnd_419851 < baseStart_419851 := by decide
  rcases family_descends (prefixWord ++ tailWord_419851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419861 : List Nat := [1, 3, 2, 1, 6, 1, 2, 4]
def baseStart_419861 : Nat := 118140960795 + 419861 * 2 ^ 59
def prefixEnd_419861 : Nat := 4983230072969 + 3 ^ 40 * 419861 * 2
def baseEnd_419861 : Nat := 63878666985922081661215

theorem tailTrace_419861 : CollatzResearch.WordTrace tailWord_419861 prefixEnd_419861 63878666985922081661215 := by
  unfold tailWord_419861
  simp only [CollatzResearch.WordTrace]
  refine ⟨15313588731922778395059437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10209059154615185596706291 15313588731922778395059437)
  ·
    refine ⟨5742595774471041898147289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15313588731922778395059437 5742595774471041898147289)
    ·
      refine ⟨4306946830853281423610467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5742595774471041898147289 4306946830853281423610467)
      ·
        refine ⟨6460420246279922135415701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4306946830853281423610467 6460420246279922135415701)
        ·
          refine ⟨302832199044371350097611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6460420246279922135415701 302832199044371350097611)
          ·
            refine ⟨454248298566557025146417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302832199044371350097611 454248298566557025146417)
            ·
              refine ⟨340686223924917768859813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454248298566557025146417 340686223924917768859813)
              ·
                refine ⟨63878666985922081661215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 340686223924917768859813 63878666985922081661215)
                ·
                  rfl

theorem cell20_419861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 4].length) (baseStart_419861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419861 prefixEnd_419861 := by exact prefixLift 419861
  have htrace : WordTrace (prefixWord ++ tailWord_419861) baseStart_419861 baseEnd_419861 := by
    simpa [prefixWord, tailWord_419861, baseEnd_419861] using wordTrace_append hprefix tailTrace_419861
  have hstable : (prefixWord ++ tailWord_419861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419861).length < 2 ^ (prefixWord ++ tailWord_419861).sum := by decide
  have hdescent : baseEnd_419861 < baseStart_419861 := by decide
  rcases family_descends (prefixWord ++ tailWord_419861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419892 : List Nat := [2, 5, 1, 2, 2, 2, 1, 1, 4]
def baseStart_419892 : Nat := 118140960795 + 419892 * 2 ^ 59
def prefixEnd_419892 : Nat := 4983230072969 + 3 ^ 40 * 419892 * 2
def baseEnd_419892 : Nat := 191650150202467914950185

theorem tailTrace_419892 : CollatzResearch.WordTrace tailWord_419892 prefixEnd_419892 191650150202467914950185 := by
  unfold tailWord_419892
  simp only [CollatzResearch.WordTrace]
  refine ⟨7657359697405235344718965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10209812929873647126291953 7657359697405235344718965)
  ·
    refine ⟨717877471631740813567403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7657359697405235344718965 717877471631740813567403)
    ·
      refine ⟨1076816207447611220351105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 717877471631740813567403 1076816207447611220351105)
      ·
        refine ⟨807612155585708415263329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1076816207447611220351105 807612155585708415263329)
        ·
          refine ⟨605709116689281311447497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 807612155585708415263329 605709116689281311447497)
          ·
            refine ⟨454281837516960983585623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 605709116689281311447497 454281837516960983585623)
            ·
              refine ⟨681422756275441475378435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454281837516960983585623 681422756275441475378435)
              ·
                refine ⟨1022134134413162213067653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 681422756275441475378435 1022134134413162213067653)
                ·
                  refine ⟨191650150202467914950185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1022134134413162213067653 191650150202467914950185)
                  ·
                    rfl

theorem cell20_419892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_419892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419892 prefixEnd_419892 := by exact prefixLift 419892
  have htrace : WordTrace (prefixWord ++ tailWord_419892) baseStart_419892 baseEnd_419892 := by
    simpa [prefixWord, tailWord_419892, baseEnd_419892] using wordTrace_append hprefix tailTrace_419892
  have hstable : (prefixWord ++ tailWord_419892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419892).length < 2 ^ (prefixWord ++ tailWord_419892).sum := by decide
  have hdescent : baseEnd_419892 < baseStart_419892 := by decide
  rcases family_descends (prefixWord ++ tailWord_419892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419902 : List Nat := [4, 2, 1, 3, 3, 1, 2, 1, 3]
def baseStart_419902 : Nat := 118140960795 + 419902 * 2 ^ 59
def prefixEnd_419902 : Nat := 4983230072969 + 3 ^ 40 * 419902 * 2
def baseEnd_419902 : Nat := 191654714474952324616811

theorem tailTrace_419902 : CollatzResearch.WordTrace tailWord_419902 prefixEnd_419902 191654714474952324616811 := by
  unfold tailWord_419902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1914385515596780299662745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10210056083182828264867973 1914385515596780299662745)
  ·
    refine ⟨1435789136697585224747059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1914385515596780299662745 1435789136697585224747059)
    ·
      refine ⟨2153683705046377837120589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1435789136697585224747059 2153683705046377837120589)
      ·
        refine ⟨807631389392391688920221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2153683705046377837120589 807631389392391688920221)
        ·
          refine ⟨302861771022146883345083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 807631389392391688920221 302861771022146883345083)
          ·
            refine ⟨454292656533220325017625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302861771022146883345083 454292656533220325017625)
            ·
              refine ⟨340719492399915243763219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454292656533220325017625 340719492399915243763219)
              ·
                refine ⟨511079238599872865644829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340719492399915243763219 511079238599872865644829)
                ·
                  refine ⟨191654714474952324616811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511079238599872865644829 191654714474952324616811)
                  ·
                    rfl

theorem cell20_419902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_419902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419902 prefixEnd_419902 := by exact prefixLift 419902
  have htrace : WordTrace (prefixWord ++ tailWord_419902) baseStart_419902 baseEnd_419902 := by
    simpa [prefixWord, tailWord_419902, baseEnd_419902] using wordTrace_append hprefix tailTrace_419902
  have hstable : (prefixWord ++ tailWord_419902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419902).length < 2 ^ (prefixWord ++ tailWord_419902).sum := by decide
  have hdescent : baseEnd_419902 < baseStart_419902 := by decide
  rcases family_descends (prefixWord ++ tailWord_419902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419948 : List Nat := [2, 2, 1, 1, 3, 3, 1, 4, 3]
def baseStart_419948 : Nat := 118140960795 + 419948 * 2 ^ 59
def prefixEnd_419948 : Nat := 4983230072969 + 3 ^ 40 * 419948 * 2
def baseEnd_419948 : Nat := 191675710128380609083289

theorem tailTrace_419948 : CollatzResearch.WordTrace tailWord_419948 prefixEnd_419948 191675710128380609083289 := by
  unfold tailWord_419948
  simp only [CollatzResearch.WordTrace]
  refine ⟨7658380941303796126738249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10211174588405061502317665 7658380941303796126738249)
  ·
    refine ⟨5743785705977847095053687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7658380941303796126738249 5743785705977847095053687)
    ·
      refine ⟨8615678558966770642580531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5743785705977847095053687 8615678558966770642580531)
      ·
        refine ⟨12923517838450155963870797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8615678558966770642580531 12923517838450155963870797)
        ·
          refine ⟨4846319189418808486451549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12923517838450155963870797 4846319189418808486451549)
          ·
            refine ⟨1817369696032053182419331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4846319189418808486451549 1817369696032053182419331)
            ·
              refine ⟨2726054544048079773628997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817369696032053182419331 2726054544048079773628997)
              ·
                refine ⟨511135227009014957555437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2726054544048079773628997 511135227009014957555437)
                ·
                  refine ⟨191675710128380609083289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511135227009014957555437 191675710128380609083289)
                  ·
                    rfl

theorem cell20_419948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_419948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419948 prefixEnd_419948 := by exact prefixLift 419948
  have htrace : WordTrace (prefixWord ++ tailWord_419948) baseStart_419948 baseEnd_419948 := by
    simpa [prefixWord, tailWord_419948, baseEnd_419948] using wordTrace_append hprefix tailTrace_419948
  have hstable : (prefixWord ++ tailWord_419948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419948).length < 2 ^ (prefixWord ++ tailWord_419948).sum := by decide
  have hdescent : baseEnd_419948 < baseStart_419948 := by decide
  rcases family_descends (prefixWord ++ tailWord_419948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419951 : List Nat := [1, 1, 2, 1, 3, 4, 4, 2, 2]
def baseStart_419951 : Nat := 118140960795 + 419951 * 2 ^ 59
def prefixEnd_419951 : Nat := 4983230072969 + 3 ^ 40 * 419951 * 2
def baseEnd_419951 : Nat := 191677079410125931983277

theorem tailTrace_419951 : CollatzResearch.WordTrace tailWord_419951 prefixEnd_419951 191677079410125931983277 := by
  unfold tailWord_419951
  simp only [CollatzResearch.WordTrace]
  refine ⟨15316871301596723765835707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10211247534397815843890471 15316871301596723765835707)
  ·
    refine ⟨22975306952395085648753561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15316871301596723765835707 22975306952395085648753561)
    ·
      refine ⟨17231480214296314236565171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22975306952395085648753561 17231480214296314236565171)
      ·
        refine ⟨25847220321444471354847757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17231480214296314236565171 25847220321444471354847757)
        ·
          refine ⟨9692707620541676758067909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25847220321444471354847757 9692707620541676758067909)
          ·
            refine ⟨1817382678851564392137733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9692707620541676758067909 1817382678851564392137733)
            ·
              refine ⟨340759252284668323525825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1817382678851564392137733 340759252284668323525825)
              ·
                refine ⟨255569439213501242644369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340759252284668323525825 255569439213501242644369)
                ·
                  refine ⟨191677079410125931983277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255569439213501242644369 191677079410125931983277)
                  ·
                    rfl

theorem cell20_419951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 2].length) (baseStart_419951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419951 prefixEnd_419951 := by exact prefixLift 419951
  have htrace : WordTrace (prefixWord ++ tailWord_419951) baseStart_419951 baseEnd_419951 := by
    simpa [prefixWord, tailWord_419951, baseEnd_419951] using wordTrace_append hprefix tailTrace_419951
  have hstable : (prefixWord ++ tailWord_419951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419951).length < 2 ^ (prefixWord ++ tailWord_419951).sum := by decide
  have hdescent : baseEnd_419951 < baseStart_419951 := by decide
  rcases family_descends (prefixWord ++ tailWord_419951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419958 : List Nat := [5, 1, 1, 2, 1, 4, 1, 5]
def baseStart_419958 : Nat := 118140960795 + 419958 * 2 ^ 59
def prefixEnd_419958 : Nat := 4983230072969 + 3 ^ 40 * 419958 * 2
def baseEnd_419958 : Nat := 63893424800288339583305

theorem tailTrace_419958 : CollatzResearch.WordTrace tailWord_419958 prefixEnd_419958 63893424800288339583305 := by
  unfold tailWord_419958
  simp only [CollatzResearch.WordTrace]
  refine ⟨957320413285710247583783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10211417741714242640893685 957320413285710247583783)
  ·
    refine ⟨1435980619928565371375675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 957320413285710247583783 1435980619928565371375675)
    ·
      refine ⟨2153970929892848057063513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1435980619928565371375675 2153970929892848057063513)
      ·
        refine ⟨1615478197419636042797635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2153970929892848057063513 1615478197419636042797635)
        ·
          refine ⟨2423217296129454064196453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1615478197419636042797635 2423217296129454064196453)
          ·
            refine ⟨454353243024272637036835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2423217296129454064196453 454353243024272637036835)
            ·
              refine ⟨681529864536408955555253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454353243024272637036835 681529864536408955555253)
              ·
                refine ⟨63893424800288339583305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 681529864536408955555253 63893424800288339583305)
                ·
                  rfl

theorem cell20_419958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_419958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419958 prefixEnd_419958 := by exact prefixLift 419958
  have htrace : WordTrace (prefixWord ++ tailWord_419958) baseStart_419958 baseEnd_419958 := by
    simpa [prefixWord, tailWord_419958, baseEnd_419958] using wordTrace_append hprefix tailTrace_419958
  have hstable : (prefixWord ++ tailWord_419958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419958).length < 2 ^ (prefixWord ++ tailWord_419958).sum := by decide
  have hdescent : baseEnd_419958 < baseStart_419958 := by decide
  rcases family_descends (prefixWord ++ tailWord_419958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419986 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_419986 : Nat := 118140960795 + 419986 * 2 ^ 59
def prefixEnd_419986 : Nat := 4983230072969 + 3 ^ 40 * 419986 * 2
def baseEnd_419986 : Nat := 191693054363821365816467

theorem tailTrace_419986 : CollatzResearch.WordTrace tailWord_419986 prefixEnd_419986 191693054363821365816467 := by
  unfold tailWord_419986
  simp only [CollatzResearch.WordTrace]
  refine ⟨3829536964117481185839953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10212098570979949828906541 3829536964117481185839953)
  ·
    refine ⟨2872152723088110889379965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3829536964117481185839953 2872152723088110889379965)
    ·
      refine ⟨1077057271158041583517487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2872152723088110889379965 1077057271158041583517487)
      ·
        refine ⟨1615585906737062375276231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1077057271158041583517487 1615585906737062375276231)
        ·
          refine ⟨2423378860105593562914347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1615585906737062375276231 2423378860105593562914347)
          ·
            refine ⟨3635068290158390344371521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2423378860105593562914347 3635068290158390344371521)
            ·
              refine ⟨2726301217618792758278641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3635068290158390344371521 2726301217618792758278641)
              ·
                refine ⟨2044725913214094568708981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2726301217618792758278641 2044725913214094568708981)
                ·
                  refine ⟨191693054363821365816467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2044725913214094568708981 191693054363821365816467)
                  ·
                    rfl

theorem cell20_419986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_419986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419986 prefixEnd_419986 := by exact prefixLift 419986
  have htrace : WordTrace (prefixWord ++ tailWord_419986) baseStart_419986 baseEnd_419986 := by
    simpa [prefixWord, tailWord_419986, baseEnd_419986] using wordTrace_append hprefix tailTrace_419986
  have hstable : (prefixWord ++ tailWord_419986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419986).length < 2 ^ (prefixWord ++ tailWord_419986).sum := by decide
  have hdescent : baseEnd_419986 < baseStart_419986 := by decide
  rcases family_descends (prefixWord ++ tailWord_419986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420000 : List Nat := [2, 1, 1, 4, 2, 3, 7]
def baseStart_420000 : Nat := 118140960795 + 420000 * 2 ^ 59
def prefixEnd_420000 : Nat := 4983230072969 + 3 ^ 40 * 420000 * 2
def baseEnd_420000 : Nat := 21299938260588837705527

theorem tailTrace_420000 : CollatzResearch.WordTrace tailWord_420000 prefixEnd_420000 21299938260588837705527 := by
  unfold tailWord_420000
  simp only [CollatzResearch.WordTrace]
  refine ⟨7659329239209602567184727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10212438985612803422912969 7659329239209602567184727)
  ·
    refine ⟨11488993858814403850777091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7659329239209602567184727 11488993858814403850777091)
    ·
      refine ⟨17233490788221605776165637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11488993858814403850777091 17233490788221605776165637)
      ·
        refine ⟨3231279522791551083031057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17233490788221605776165637 3231279522791551083031057)
        ·
          refine ⟨2423459642093663312273293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3231279522791551083031057 2423459642093663312273293)
          ·
            refine ⟨908797365785123742102485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2423459642093663312273293 908797365785123742102485)
            ·
              refine ⟨21299938260588837705527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 908797365785123742102485 21299938260588837705527)
              ·
                rfl

theorem cell20_420000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 7].length) (baseStart_420000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420000 prefixEnd_420000 := by exact prefixLift 420000
  have htrace : WordTrace (prefixWord ++ tailWord_420000) baseStart_420000 baseEnd_420000 := by
    simpa [prefixWord, tailWord_420000, baseEnd_420000] using wordTrace_append hprefix tailTrace_420000
  have hstable : (prefixWord ++ tailWord_420000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420000).length < 2 ^ (prefixWord ++ tailWord_420000).sum := by decide
  have hdescent : baseEnd_420000 < baseStart_420000 := by decide
  rcases family_descends (prefixWord ++ tailWord_420000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420065 : List Nat := [1, 2, 3, 1, 3, 1, 5, 2, 2]
def baseStart_420065 : Nat := 118140960795 + 420065 * 2 ^ 59
def prefixEnd_420065 : Nat := 4983230072969 + 3 ^ 40 * 420065 * 2
def baseEnd_420065 : Nat := 191729112116448202182811

theorem tailTrace_420065 : CollatzResearch.WordTrace tailWord_420065 prefixEnd_420065 191729112116448202182811 := by
  unfold tailWord_420065
  simp only [CollatzResearch.WordTrace]
  refine ⟨15321029223183721235485649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10214019482122480823657099 15321029223183721235485649)
  ·
    refine ⟨11490771917387790926614237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15321029223183721235485649 11490771917387790926614237)
    ·
      refine ⟨4309039469020421597480339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11490771917387790926614237 4309039469020421597480339)
      ·
        refine ⟨6463559203530632396220509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4309039469020421597480339 6463559203530632396220509)
        ·
          refine ⟨2423834701323987148582691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6463559203530632396220509 2423834701323987148582691)
          ·
            refine ⟨3635752051985980722874037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2423834701323987148582691 3635752051985980722874037)
            ·
              refine ⟨340851754873685692769441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3635752051985980722874037 340851754873685692769441)
              ·
                refine ⟨255638816155264269577081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340851754873685692769441 255638816155264269577081)
                ·
                  refine ⟨191729112116448202182811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255638816155264269577081 191729112116448202182811)
                  ·
                    rfl

theorem cell20_420065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 2].length) (baseStart_420065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420065 prefixEnd_420065 := by exact prefixLift 420065
  have htrace : WordTrace (prefixWord ++ tailWord_420065) baseStart_420065 baseEnd_420065 := by
    simpa [prefixWord, tailWord_420065, baseEnd_420065] using wordTrace_append hprefix tailTrace_420065
  have hstable : (prefixWord ++ tailWord_420065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420065).length < 2 ^ (prefixWord ++ tailWord_420065).sum := by decide
  have hdescent : baseEnd_420065 < baseStart_420065 := by decide
  rcases family_descends (prefixWord ++ tailWord_420065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420076 : List Nat := [2, 2, 1, 1, 2, 3, 4, 5]
def baseStart_420076 : Nat := 118140960795 + 420076 * 2 ^ 59
def prefixEnd_420076 : Nat := 4983230072969 + 3 ^ 40 * 420076 * 2
def baseEnd_420076 : Nat := 63911377605393684272033

theorem tailTrace_420076 : CollatzResearch.WordTrace tailWord_420076 prefixEnd_420076 63911377605393684272033 := by
  unfold tailWord_420076
  simp only [CollatzResearch.WordTrace]
  refine ⟨7660715213071935057068041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10214286950762580076090721 7660715213071935057068041)
  ·
    refine ⟨5745536409803951292801031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7660715213071935057068041 5745536409803951292801031)
    ·
      refine ⟨8618304614705926939201547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5745536409803951292801031 8618304614705926939201547)
      ·
        refine ⟨12927456922058890408802321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8618304614705926939201547 12927456922058890408802321)
        ·
          refine ⟨9695592691544167806601741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12927456922058890408802321 9695592691544167806601741)
          ·
            refine ⟨3635847259329062927475653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9695592691544167806601741 3635847259329062927475653)
            ·
              refine ⟨681721361124199298901685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3635847259329062927475653 681721361124199298901685)
              ·
                refine ⟨63911377605393684272033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 681721361124199298901685 63911377605393684272033)
                ·
                  rfl

theorem cell20_420076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_420076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420076 prefixEnd_420076 := by exact prefixLift 420076
  have htrace : WordTrace (prefixWord ++ tailWord_420076) baseStart_420076 baseEnd_420076 := by
    simpa [prefixWord, tailWord_420076, baseEnd_420076] using wordTrace_append hprefix tailTrace_420076
  have hstable : (prefixWord ++ tailWord_420076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420076).length < 2 ^ (prefixWord ++ tailWord_420076).sum := by decide
  have hdescent : baseEnd_420076 < baseStart_420076 := by decide
  rcases family_descends (prefixWord ++ tailWord_420076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420079 : List Nat := [1, 1, 2, 1, 6, 1, 4, 1, 3]
def baseStart_420079 : Nat := 118140960795 + 420079 * 2 ^ 59
def prefixEnd_420079 : Nat := 4983230072969 + 3 ^ 40 * 420079 * 2
def baseEnd_420079 : Nat := 191735502097926375716087

theorem tailTrace_420079 : CollatzResearch.WordTrace tailWord_420079 prefixEnd_420079 191735502097926375716087 := by
  unfold tailWord_420079
  simp only [CollatzResearch.WordTrace]
  refine ⟨15321539845133001626495291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10214359896755334417663527 15321539845133001626495291)
  ·
    refine ⟨22982309767699502439742937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15321539845133001626495291 22982309767699502439742937)
    ·
      refine ⟨17236732325774626829807203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22982309767699502439742937 17236732325774626829807203)
      ·
        refine ⟨25855098488661940244710805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17236732325774626829807203 25855098488661940244710805)
        ·
          refine ⟨1211957741656028448970819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25855098488661940244710805 1211957741656028448970819)
          ·
            refine ⟨1817936612484042673456229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211957741656028448970819 1817936612484042673456229)
            ·
              refine ⟨340863114840758001273043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1817936612484042673456229 340863114840758001273043)
              ·
                refine ⟨511294672261137001909565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340863114840758001273043 511294672261137001909565)
                ·
                  refine ⟨191735502097926375716087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511294672261137001909565 191735502097926375716087)
                  ·
                    rfl

theorem cell20_420079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 3].length) (baseStart_420079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420079 prefixEnd_420079 := by exact prefixLift 420079
  have htrace : WordTrace (prefixWord ++ tailWord_420079) baseStart_420079 baseEnd_420079 := by
    simpa [prefixWord, tailWord_420079, baseEnd_420079] using wordTrace_append hprefix tailTrace_420079
  have hstable : (prefixWord ++ tailWord_420079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420079).length < 2 ^ (prefixWord ++ tailWord_420079).sum := by decide
  have hdescent : baseEnd_420079 < baseStart_420079 := by decide
  rcases family_descends (prefixWord ++ tailWord_420079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420114 : List Nat := [3, 2, 4, 11]
def baseStart_420114 : Nat := 118140960795 + 420114 * 2 ^ 59
def prefixEnd_420114 : Nat := 4983230072969 + 3 ^ 40 * 420114 * 2
def baseEnd_420114 : Nat := 789100728607497158639

theorem tailTrace_420114 : CollatzResearch.WordTrace tailWord_420114 prefixEnd_420114 789100728607497158639 := by
  unfold tailWord_420114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3830704100001550651004849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10215210933337468402679597 3830704100001550651004849)
  ·
    refine ⟨2873028075001162988253637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3830704100001550651004849 2873028075001162988253637)
    ·
      refine ⟨538692764062718060297557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2873028075001162988253637 538692764062718060297557)
      ·
        refine ⟨789100728607497158639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 538692764062718060297557 789100728607497158639)
        ·
          rfl

theorem cell20_420114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 11].length) (baseStart_420114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420114 prefixEnd_420114 := by exact prefixLift 420114
  have htrace : WordTrace (prefixWord ++ tailWord_420114) baseStart_420114 baseEnd_420114 := by
    simpa [prefixWord, tailWord_420114, baseEnd_420114] using wordTrace_append hprefix tailTrace_420114
  have hstable : (prefixWord ++ tailWord_420114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420114).length < 2 ^ (prefixWord ++ tailWord_420114).sum := by decide
  have hdescent : baseEnd_420114 < baseStart_420114 := by decide
  rcases family_descends (prefixWord ++ tailWord_420114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420141 : List Nat := [1, 5, 3, 1, 2, 1, 1, 2, 4]
def baseStart_420141 : Nat := 118140960795 + 420141 * 2 ^ 59
def prefixEnd_420141 : Nat := 4983230072969 + 3 ^ 40 * 420141 * 2
def baseEnd_420141 : Nat := 191763800587329715649167

theorem tailTrace_420141 : CollatzResearch.WordTrace tailWord_420141 prefixEnd_420141 191763800587329715649167 := by
  unfold tailWord_420141
  simp only [CollatzResearch.WordTrace]
  refine ⟨15323801170908386215252277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10215867447272257476834851 15323801170908386215252277)
  ·
    refine ⟨1436606359772661207679901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15323801170908386215252277 1436606359772661207679901)
    ·
      refine ⟨538727384914747952879963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1436606359772661207679901 538727384914747952879963)
      ·
        refine ⟨808091077372121929319945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538727384914747952879963 808091077372121929319945)
        ·
          refine ⟨606068308029091446989959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 808091077372121929319945 606068308029091446989959)
          ·
            refine ⟨909102462043637170484939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606068308029091446989959 909102462043637170484939)
            ·
              refine ⟨1363653693065455755727409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909102462043637170484939 1363653693065455755727409)
              ·
                refine ⟨1022740269799091816795557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1363653693065455755727409 1022740269799091816795557)
                ·
                  refine ⟨191763800587329715649167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1022740269799091816795557 191763800587329715649167)
                  ·
                    rfl

theorem cell20_420141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_420141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420141 prefixEnd_420141 := by exact prefixLift 420141
  have htrace : WordTrace (prefixWord ++ tailWord_420141) baseStart_420141 baseEnd_420141 := by
    simpa [prefixWord, tailWord_420141, baseEnd_420141] using wordTrace_append hprefix tailTrace_420141
  have hstable : (prefixWord ++ tailWord_420141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420141).length < 2 ^ (prefixWord ++ tailWord_420141).sum := by decide
  have hdescent : baseEnd_420141 < baseStart_420141 := by decide
  rcases family_descends (prefixWord ++ tailWord_420141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420148 : List Nat := [2, 5, 1, 1, 1, 3, 3, 4]
def baseStart_420148 : Nat := 118140960795 + 420148 * 2 ^ 59
def prefixEnd_420148 : Nat := 4983230072969 + 3 ^ 40 * 420148 * 2
def baseEnd_420148 : Nat := 63922331859356267471935

theorem tailTrace_420148 : CollatzResearch.WordTrace tailWord_420148 prefixEnd_420148 63922331859356267471935 := by
  unfold tailWord_420148
  simp only [CollatzResearch.WordTrace]
  refine ⟨7662028240941513205378549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10216037654588684273838065 7662028240941513205378549)
  ·
    refine ⟨718315147588266863004239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7662028240941513205378549 718315147588266863004239)
    ·
      refine ⟨1077472721382400294506359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 718315147588266863004239 1077472721382400294506359)
      ·
        refine ⟨1616209082073600441759539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1077472721382400294506359 1616209082073600441759539)
        ·
          refine ⟨2424313623110400662639309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1616209082073600441759539 2424313623110400662639309)
          ·
            refine ⟨909117608666400248489741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2424313623110400662639309 909117608666400248489741)
            ·
              refine ⟨340919103249900093183653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 909117608666400248489741 340919103249900093183653)
              ·
                refine ⟨63922331859356267471935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 340919103249900093183653 63922331859356267471935)
                ·
                  rfl

theorem cell20_420148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_420148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420148 prefixEnd_420148 := by exact prefixLift 420148
  have htrace : WordTrace (prefixWord ++ tailWord_420148) baseStart_420148 baseEnd_420148 := by
    simpa [prefixWord, tailWord_420148, baseEnd_420148] using wordTrace_append hprefix tailTrace_420148
  have hstable : (prefixWord ++ tailWord_420148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420148).length < 2 ^ (prefixWord ++ tailWord_420148).sum := by decide
  have hdescent : baseEnd_420148 < baseStart_420148 := by decide
  rcases family_descends (prefixWord ++ tailWord_420148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420159 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 5]
def baseStart_420159 : Nat := 118140960795 + 420159 * 2 ^ 59
def prefixEnd_420159 : Nat := 4983230072969 + 3 ^ 40 * 420159 * 2
def baseEnd_420159 : Nat := 191772016277801653049093

theorem tailTrace_420159 : CollatzResearch.WordTrace tailWord_420159 prefixEnd_420159 191772016277801653049093 := by
  unfold tailWord_420159
  simp only [CollatzResearch.WordTrace]
  refine ⟨15324457684843175289407531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10216305123228783526271687 15324457684843175289407531)
  ·
    refine ⟨22986686527264762934111297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15324457684843175289407531 22986686527264762934111297)
    ·
      refine ⟨17240014895448572200583473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22986686527264762934111297 17240014895448572200583473)
      ·
        refine ⟨12930011171586429150437605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17240014895448572200583473 12930011171586429150437605)
        ·
          refine ⟨2424377094672455465707051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12930011171586429150437605 2424377094672455465707051)
          ·
            refine ⟨3636565642008683198560577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2424377094672455465707051 3636565642008683198560577)
            ·
              refine ⟨2727424231506512398920433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3636565642008683198560577 2727424231506512398920433)
              ·
                refine ⟨2045568173629884299190325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2727424231506512398920433 2045568173629884299190325)
                ·
                  refine ⟨191772016277801653049093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2045568173629884299190325 191772016277801653049093)
                  ·
                    rfl

theorem cell20_420159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_420159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420159 prefixEnd_420159 := by exact prefixLift 420159
  have htrace : WordTrace (prefixWord ++ tailWord_420159) baseStart_420159 baseEnd_420159 := by
    simpa [prefixWord, tailWord_420159, baseEnd_420159] using wordTrace_append hprefix tailTrace_420159
  have hstable : (prefixWord ++ tailWord_420159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420159).length < 2 ^ (prefixWord ++ tailWord_420159).sum := by decide
  have hdescent : baseEnd_420159 < baseStart_420159 := by decide
  rcases family_descends (prefixWord ++ tailWord_420159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420176 : List Nat := [2, 1, 1, 1, 1, 6, 3, 2, 3]
def baseStart_420176 : Nat := 118140960795 + 420176 * 2 ^ 59
def prefixEnd_420176 : Nat := 4983230072969 + 3 ^ 40 * 420176 * 2
def baseEnd_420176 : Nat := 191779775541025149482357

theorem tailTrace_420176 : CollatzResearch.WordTrace tailWord_420176 prefixEnd_420176 191779775541025149482357 := by
  unfold tailWord_420176
  simp only [CollatzResearch.WordTrace]
  refine ⟨7662538862890793596388191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10216718483854391461850921 7662538862890793596388191)
  ·
    refine ⟨11493808294336190394582287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7662538862890793596388191 11493808294336190394582287)
    ·
      refine ⟨17240712441504285591873431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11493808294336190394582287 17240712441504285591873431)
      ·
        refine ⟨25861068662256428387810147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17240712441504285591873431 25861068662256428387810147)
        ·
          refine ⟨38791602993384642581715221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25861068662256428387810147 38791602993384642581715221)
          ·
            refine ⟨1818356390314905121017901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38791602993384642581715221 1818356390314905121017901)
            ·
              refine ⟨681883646368089420381713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1818356390314905121017901 681883646368089420381713)
              ·
                refine ⟨511412734776067065286285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 681883646368089420381713 511412734776067065286285)
                ·
                  refine ⟨191779775541025149482357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511412734776067065286285 191779775541025149482357)
                  ·
                    rfl

theorem cell20_420176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_420176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420176 prefixEnd_420176 := by exact prefixLift 420176
  have htrace : WordTrace (prefixWord ++ tailWord_420176) baseStart_420176 baseEnd_420176 := by
    simpa [prefixWord, tailWord_420176, baseEnd_420176] using wordTrace_append hprefix tailTrace_420176
  have hstable : (prefixWord ++ tailWord_420176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420176).length < 2 ^ (prefixWord ++ tailWord_420176).sum := by decide
  have hdescent : baseEnd_420176 < baseStart_420176 := by decide
  rcases family_descends (prefixWord ++ tailWord_420176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420183 : List Nat := [1, 1, 3, 2, 3, 1, 4, 1, 4]
def baseStart_420183 : Nat := 118140960795 + 420183 * 2 ^ 59
def prefixEnd_420183 : Nat := 4983230072969 + 3 ^ 40 * 420183 * 2
def baseEnd_420183 : Nat := 191782970531764236248995

theorem tailTrace_420183 : CollatzResearch.WordTrace tailWord_420183 prefixEnd_420183 191782970531764236248995 := by
  unfold tailWord_420183
  simp only [CollatzResearch.WordTrace]
  refine ⟨15325333036756227388281203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10216888691170818258854135 15325333036756227388281203)
  ·
    refine ⟨22987999555134341082421805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15325333036756227388281203 22987999555134341082421805)
    ·
      refine ⟨8620499833175377905908177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22987999555134341082421805 8620499833175377905908177)
      ·
        refine ⟨6465374874881533429431133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8620499833175377905908177 6465374874881533429431133)
        ·
          refine ⟨2424515578080575036036675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6465374874881533429431133 2424515578080575036036675)
          ·
            refine ⟨3636773367120862554055013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2424515578080575036036675 3636773367120862554055013)
            ·
              refine ⟨681895006335161728885315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3636773367120862554055013 681895006335161728885315)
              ·
                refine ⟨1022842509502742593327973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 681895006335161728885315 1022842509502742593327973)
                ·
                  refine ⟨191782970531764236248995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1022842509502742593327973 191782970531764236248995)
                  ·
                    rfl

theorem cell20_420183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 4].length) (baseStart_420183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420183 prefixEnd_420183 := by exact prefixLift 420183
  have htrace : WordTrace (prefixWord ++ tailWord_420183) baseStart_420183 baseEnd_420183 := by
    simpa [prefixWord, tailWord_420183, baseEnd_420183] using wordTrace_append hprefix tailTrace_420183
  have hstable : (prefixWord ++ tailWord_420183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420183).length < 2 ^ (prefixWord ++ tailWord_420183).sum := by decide
  have hdescent : baseEnd_420183 < baseStart_420183 := by decide
  rcases family_descends (prefixWord ++ tailWord_420183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420211 : List Nat := [1, 1, 1, 2, 2, 1, 2, 10]
def baseStart_420211 : Nat := 118140960795 + 420211 * 2 ^ 59
def prefixEnd_420211 : Nat := 4983230072969 + 3 ^ 40 * 420211 * 2
def baseEnd_420211 : Nat := 63931916831573527771849

theorem tailTrace_420211 : CollatzResearch.WordTrace tailWord_420211 prefixEnd_420211 63931916831573527771849 := by
  unfold tailWord_420211
  simp only [CollatzResearch.WordTrace]
  refine ⟨15326354280654788170300487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10217569520436525446866991 15326354280654788170300487)
  ·
    refine ⟨22989531420982182255450731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15326354280654788170300487 22989531420982182255450731)
    ·
      refine ⟨34484297131473273383176097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22989531420982182255450731 34484297131473273383176097)
      ·
        refine ⟨25863222848604955037382073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34484297131473273383176097 25863222848604955037382073)
        ·
          refine ⟨19397417136453716278036555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25863222848604955037382073 19397417136453716278036555)
          ·
            refine ⟨29096125704680574417054833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19397417136453716278036555 29096125704680574417054833)
            ·
              refine ⟨21822094278510430812791125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29096125704680574417054833 21822094278510430812791125)
              ·
                refine ⟨63931916831573527771849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21822094278510430812791125 63931916831573527771849)
                ·
                  rfl

theorem cell20_420211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 10].length) (baseStart_420211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420211 prefixEnd_420211 := by exact prefixLift 420211
  have htrace : WordTrace (prefixWord ++ tailWord_420211) baseStart_420211 baseEnd_420211 := by
    simpa [prefixWord, tailWord_420211, baseEnd_420211] using wordTrace_append hprefix tailTrace_420211
  have hstable : (prefixWord ++ tailWord_420211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420211).length < 2 ^ (prefixWord ++ tailWord_420211).sum := by decide
  have hdescent : baseEnd_420211 < baseStart_420211 := by decide
  rcases family_descends (prefixWord ++ tailWord_420211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420234 : List Nat := [3, 1, 2, 5, 2, 1, 1, 1, 4]
def baseStart_420234 : Nat := 118140960795 + 420234 * 2 ^ 59
def prefixEnd_420234 : Nat := 4983230072969 + 3 ^ 40 * 420234 * 2
def baseEnd_420234 : Nat := 191806248321434725548787

theorem tailTrace_420234 : CollatzResearch.WordTrace tailWord_420234 prefixEnd_420234 191806248321434725548787 := by
  unfold tailWord_420234
  simp only [CollatzResearch.WordTrace]
  refine ⟨3831798289892865774596939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10218128773047642065591837 3831798289892865774596939)
  ·
    refine ⟨5747697434839298661895409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3831798289892865774596939 5747697434839298661895409)
    ·
      refine ⟨4310773076129473996421557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5747697434839298661895409 4310773076129473996421557)
      ·
        refine ⟨404134975887138187164521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4310773076129473996421557 404134975887138187164521)
        ·
          refine ⟨303101231915353640373391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404134975887138187164521 303101231915353640373391)
          ·
            refine ⟨454651847873030460560087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303101231915353640373391 454651847873030460560087)
            ·
              refine ⟨681977771809545690840131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454651847873030460560087 681977771809545690840131)
              ·
                refine ⟨1022966657714318536260197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 681977771809545690840131 1022966657714318536260197)
                ·
                  refine ⟨191806248321434725548787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1022966657714318536260197 191806248321434725548787)
                  ·
                    rfl

theorem cell20_420234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_420234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420234 prefixEnd_420234 := by exact prefixLift 420234
  have htrace : WordTrace (prefixWord ++ tailWord_420234) baseStart_420234 baseEnd_420234 := by
    simpa [prefixWord, tailWord_420234, baseEnd_420234] using wordTrace_append hprefix tailTrace_420234
  have hstable : (prefixWord ++ tailWord_420234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420234).length < 2 ^ (prefixWord ++ tailWord_420234).sum := by decide
  have hdescent : baseEnd_420234 < baseStart_420234 := by decide
  rcases family_descends (prefixWord ++ tailWord_420234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420235 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 5]
def baseStart_420235 : Nat := 118140960795 + 420235 * 2 ^ 59
def prefixEnd_420235 : Nat := 4983230072969 + 3 ^ 40 * 420235 * 2
def baseEnd_420235 : Nat := 191806704748683166515449

theorem tailTrace_420235 : CollatzResearch.WordTrace tailWord_420235 prefixEnd_420235 191806704748683166515449 := by
  unfold tailWord_420235
  simp only [CollatzResearch.WordTrace]
  refine ⟨15327229632567840269174159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10218153088378560179449439 15327229632567840269174159)
  ·
    refine ⟨22990844448851760403761239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15327229632567840269174159 22990844448851760403761239)
    ·
      refine ⟨34486266673277640605641859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22990844448851760403761239 34486266673277640605641859)
      ·
        refine ⟨51729400009916460908462789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34486266673277640605641859 51729400009916460908462789)
        ·
          refine ⟨9699262501859336420336773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51729400009916460908462789 9699262501859336420336773)
          ·
            refine ⟨1818611719098625578813145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9699262501859336420336773 1818611719098625578813145)
            ·
              refine ⟨1363958789323969184109859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1818611719098625578813145 1363958789323969184109859)
              ·
                refine ⟨2045938183985953776164789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363958789323969184109859 2045938183985953776164789)
                ·
                  refine ⟨191806704748683166515449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2045938183985953776164789 191806704748683166515449)
                  ·
                    rfl

theorem cell20_420235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_420235 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420235 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420235 prefixEnd_420235 := by exact prefixLift 420235
  have htrace : WordTrace (prefixWord ++ tailWord_420235) baseStart_420235 baseEnd_420235 := by
    simpa [prefixWord, tailWord_420235, baseEnd_420235] using wordTrace_append hprefix tailTrace_420235
  have hstable : (prefixWord ++ tailWord_420235).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420235).length < 2 ^ (prefixWord ++ tailWord_420235).sum := by decide
  have hdescent : baseEnd_420235 < baseStart_420235 := by decide
  rcases family_descends (prefixWord ++ tailWord_420235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420238 : List Nat := [4, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_420238 : Nat := 118140960795 + 420238 * 2 ^ 59
def prefixEnd_420238 : Nat := 4983230072969 + 3 ^ 40 * 420238 * 2
def baseEnd_420238 : Nat := 191808074030428489415437

theorem tailTrace_420238 : CollatzResearch.WordTrace tailWord_420238 prefixEnd_420238 191808074030428489415437 := by
  unfold tailWord_420238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1915917381444621472691671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10218226034371314521022245 1915917381444621472691671)
  ·
    refine ⟨2873876072166932209037507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1915917381444621472691671 2873876072166932209037507)
    ·
      refine ⟨4310814108250398313556261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2873876072166932209037507 4310814108250398313556261)
      ·
        refine ⟨808277645296949683791799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4310814108250398313556261 808277645296949683791799)
        ·
          refine ⟨1212416467945424525687699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808277645296949683791799 1212416467945424525687699)
          ·
            refine ⟨1818624701918136788531549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212416467945424525687699 1818624701918136788531549)
            ·
              refine ⟨681984263219301295699331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1818624701918136788531549 681984263219301295699331)
              ·
                refine ⟨1022976394828951943548997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 681984263219301295699331 1022976394828951943548997)
                ·
                  refine ⟨191808074030428489415437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1022976394828951943548997 191808074030428489415437)
                  ·
                    rfl

theorem cell20_420238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_420238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420238 prefixEnd_420238 := by exact prefixLift 420238
  have htrace : WordTrace (prefixWord ++ tailWord_420238) baseStart_420238 baseEnd_420238 := by
    simpa [prefixWord, tailWord_420238, baseEnd_420238] using wordTrace_append hprefix tailTrace_420238
  have hstable : (prefixWord ++ tailWord_420238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420238).length < 2 ^ (prefixWord ++ tailWord_420238).sum := by decide
  have hdescent : baseEnd_420238 < baseStart_420238 := by decide
  rcases family_descends (prefixWord ++ tailWord_420238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420248 : List Nat := [2, 1, 2, 5, 1, 3, 2, 1, 3]
def baseStart_420248 : Nat := 118140960795 + 420248 * 2 ^ 59
def prefixEnd_420248 : Nat := 4983230072969 + 3 ^ 40 * 420248 * 2
def baseEnd_420248 : Nat := 191812638302912899082063

theorem tailTrace_420248 : CollatzResearch.WordTrace tailWord_420248 prefixEnd_420248 191812638302912899082063 := by
  unfold tailWord_420248
  simp only [CollatzResearch.WordTrace]
  refine ⟨7663851890760371744698699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10218469187680495659598265 7663851890760371744698699)
  ·
    refine ⟨11495777836140557617048049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7663851890760371744698699 11495777836140557617048049)
    ·
      refine ⟨8621833377105418212786037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11495777836140557617048049 8621833377105418212786037)
      ·
        refine ⟨808296879103632957448691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8621833377105418212786037 808296879103632957448691)
        ·
          refine ⟨1212445318655449436173037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808296879103632957448691 1212445318655449436173037)
          ·
            refine ⟨454666994495793538564889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1212445318655449436173037 454666994495793538564889)
            ·
              refine ⟨341000245871845153923667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454666994495793538564889 341000245871845153923667)
              ·
                refine ⟨511500368807767730885501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341000245871845153923667 511500368807767730885501)
                ·
                  refine ⟨191812638302912899082063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511500368807767730885501 191812638302912899082063)
                  ·
                    rfl

theorem cell20_420248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 3].length) (baseStart_420248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420248 prefixEnd_420248 := by exact prefixLift 420248
  have htrace : WordTrace (prefixWord ++ tailWord_420248) baseStart_420248 baseEnd_420248 := by
    simpa [prefixWord, tailWord_420248, baseEnd_420248] using wordTrace_append hprefix tailTrace_420248
  have hstable : (prefixWord ++ tailWord_420248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420248).length < 2 ^ (prefixWord ++ tailWord_420248).sum := by decide
  have hdescent : baseEnd_420248 < baseStart_420248 := by decide
  rcases family_descends (prefixWord ++ tailWord_420248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420289 : List Nat := [1, 2, 7, 1, 1, 1, 1, 4, 2]
def baseStart_420289 : Nat := 118140960795 + 420289 * 2 ^ 59
def prefixEnd_420289 : Nat := 4983230072969 + 3 ^ 40 * 420289 * 2
def baseEnd_420289 : Nat := 191831351820098978715229

theorem tailTrace_420289 : CollatzResearch.WordTrace tailWord_420289 prefixEnd_420289 191831351820098978715229 := by
  unfold tailWord_420289
  simp only [CollatzResearch.WordTrace]
  refine ⟨15329199174372207491639921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10219466116248138327759947 15329199174372207491639921)
  ·
    refine ⟨11496899380779155618729941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15329199174372207491639921 11496899380779155618729941)
    ·
      refine ⟨269458579237011459813983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 11496899380779155618729941 269458579237011459813983)
      ·
        refine ⟨404187868855517189720975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269458579237011459813983 404187868855517189720975)
        ·
          refine ⟨606281803283275784581463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404187868855517189720975 606281803283275784581463)
          ·
            refine ⟨909422704924913676872195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606281803283275784581463 909422704924913676872195)
            ·
              refine ⟨1364134057387370515308293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909422704924913676872195 1364134057387370515308293)
              ·
                refine ⟨255775135760131971620305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1364134057387370515308293 255775135760131971620305)
                ·
                  refine ⟨191831351820098978715229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255775135760131971620305 191831351820098978715229)
                  ·
                    rfl

theorem cell20_420289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 2].length) (baseStart_420289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420289 prefixEnd_420289 := by exact prefixLift 420289
  have htrace : WordTrace (prefixWord ++ tailWord_420289) baseStart_420289 baseEnd_420289 := by
    simpa [prefixWord, tailWord_420289, baseEnd_420289] using wordTrace_append hprefix tailTrace_420289
  have hstable : (prefixWord ++ tailWord_420289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420289).length < 2 ^ (prefixWord ++ tailWord_420289).sum := by decide
  have hdescent : baseEnd_420289 < baseStart_420289 := by decide
  rcases family_descends (prefixWord ++ tailWord_420289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420300 : List Nat := [2, 2, 1, 4, 4, 1, 1, 5]
def baseStart_420300 : Nat := 118140960795 + 420300 * 2 ^ 59
def prefixEnd_420300 : Nat := 4983230072969 + 3 ^ 40 * 420300 * 2
def baseEnd_420300 : Nat := 63945457506610609782839

theorem tailTrace_420300 : CollatzResearch.WordTrace tailWord_420300 prefixEnd_420300 63945457506610609782839 := by
  unfold tailWord_420300
  simp only [CollatzResearch.WordTrace]
  refine ⟨7664800188666178185145177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10219733584888237580193569 7664800188666178185145177)
  ·
    refine ⟨5748600141499633638858883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7664800188666178185145177 5748600141499633638858883)
    ·
      refine ⟨8622900212249450458288325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5748600141499633638858883 8622900212249450458288325)
      ·
        refine ⟨1616793789796771960929061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8622900212249450458288325 1616793789796771960929061)
        ·
          refine ⟨303148835586894742674199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1616793789796771960929061 303148835586894742674199)
          ·
            refine ⟨454723253380342114011299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303148835586894742674199 454723253380342114011299)
            ·
              refine ⟨682084880070513171016949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454723253380342114011299 682084880070513171016949)
              ·
                refine ⟨63945457506610609782839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 682084880070513171016949 63945457506610609782839)
                ·
                  rfl

theorem cell20_420300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 5].length) (baseStart_420300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420300 prefixEnd_420300 := by exact prefixLift 420300
  have htrace : WordTrace (prefixWord ++ tailWord_420300) baseStart_420300 baseEnd_420300 := by
    simpa [prefixWord, tailWord_420300, baseEnd_420300] using wordTrace_append hprefix tailTrace_420300
  have hstable : (prefixWord ++ tailWord_420300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420300).length < 2 ^ (prefixWord ++ tailWord_420300).sum := by decide
  have hdescent : baseEnd_420300 < baseStart_420300 := by decide
  rcases family_descends (prefixWord ++ tailWord_420300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420341 : List Nat := [1, 3, 5, 1, 3, 1, 1, 2, 3]
def baseStart_420341 : Nat := 118140960795 + 420341 * 2 ^ 59
def prefixEnd_420341 : Nat := 4983230072969 + 3 ^ 40 * 420341 * 2
def baseEnd_420341 : Nat := 191855086037017908981683

theorem tailTrace_420341 : CollatzResearch.WordTrace tailWord_420341 prefixEnd_420341 191855086037017908981683 := by
  unfold tailWord_420341
  simp only [CollatzResearch.WordTrace]
  refine ⟨15331095770183820372532877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10220730513455880248355251 15331095770183820372532877)
  ·
    refine ⟨5749160913818932639699829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15331095770183820372532877 5749160913818932639699829)
    ·
      refine ⟨538983835670524934971859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5749160913818932639699829 538983835670524934971859)
      ·
        refine ⟨808475753505787402457789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538983835670524934971859 808475753505787402457789)
        ·
          refine ⟨303178407564670275921671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 808475753505787402457789 303178407564670275921671)
          ·
            refine ⟨454767611347005413882507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303178407564670275921671 454767611347005413882507)
            ·
              refine ⟨682151417020508120823761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454767611347005413882507 682151417020508120823761)
              ·
                refine ⟨511613562765381090617821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682151417020508120823761 511613562765381090617821)
                ·
                  refine ⟨191855086037017908981683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511613562765381090617821 191855086037017908981683)
                  ·
                    rfl

theorem cell20_420341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_420341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420341 prefixEnd_420341 := by exact prefixLift 420341
  have htrace : WordTrace (prefixWord ++ tailWord_420341) baseStart_420341 baseEnd_420341 := by
    simpa [prefixWord, tailWord_420341, baseEnd_420341] using wordTrace_append hprefix tailTrace_420341
  have hstable : (prefixWord ++ tailWord_420341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420341).length < 2 ^ (prefixWord ++ tailWord_420341).sum := by decide
  have hdescent : baseEnd_420341 < baseStart_420341 := by decide
  rcases family_descends (prefixWord ++ tailWord_420341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420342 : List Nat := [5, 1, 1, 1, 2, 1, 9]
def baseStart_420342 : Nat := 118140960795 + 420342 * 2 ^ 59
def prefixEnd_420342 : Nat := 4983230072969 + 3 ^ 40 * 420342 * 2
def baseEnd_420342 : Nat := 21317282496029594438705

theorem tailTrace_420342 : CollatzResearch.WordTrace tailWord_420342 prefixEnd_420342 21317282496029594438705 := by
  unfold tailWord_420342
  simp only [CollatzResearch.WordTrace]
  refine ⟨958195765198762346457455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10220754828786798362212853 958195765198762346457455)
  ·
    refine ⟨1437293647798143519686183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 958195765198762346457455 1437293647798143519686183)
    ·
      refine ⟨2155940471697215279529275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1437293647798143519686183 2155940471697215279529275)
      ·
        refine ⟨3233910707545822919293913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2155940471697215279529275 3233910707545822919293913)
        ·
          refine ⟨2425433030659367189470435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3233910707545822919293913 2425433030659367189470435)
          ·
            refine ⟨3638149545989050784205653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2425433030659367189470435 3638149545989050784205653)
            ·
              refine ⟨21317282496029594438705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3638149545989050784205653 21317282496029594438705)
              ·
                rfl

theorem cell20_420342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 9].length) (baseStart_420342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420342 prefixEnd_420342 := by exact prefixLift 420342
  have htrace : WordTrace (prefixWord ++ tailWord_420342) baseStart_420342 baseEnd_420342 := by
    simpa [prefixWord, tailWord_420342, baseEnd_420342] using wordTrace_append hprefix tailTrace_420342
  have hstable : (prefixWord ++ tailWord_420342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420342).length < 2 ^ (prefixWord ++ tailWord_420342).sum := by decide
  have hdescent : baseEnd_420342 < baseStart_420342 := by decide
  rcases family_descends (prefixWord ++ tailWord_420342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420349 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 5]
def baseStart_420349 : Nat := 118140960795 + 420349 * 2 ^ 59
def prefixEnd_420349 : Nat := 4983230072969 + 3 ^ 40 * 420349 * 2
def baseEnd_420349 : Nat := 191858737455005436714983

theorem tailTrace_420349 : CollatzResearch.WordTrace tailWord_420349 prefixEnd_420349 191858737455005436714983 := by
  unfold tailWord_420349
  simp only [CollatzResearch.WordTrace]
  refine ⟨15331387554154837738824101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10220925036103225159216067 15331387554154837738824101)
  ·
    refine ⟨2874635166404032076029519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15331387554154837738824101 2874635166404032076029519)
    ·
      refine ⟨4311952749606048114044279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2874635166404032076029519 4311952749606048114044279)
      ·
        refine ⟨6467929124409072171066419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4311952749606048114044279 6467929124409072171066419)
        ·
          refine ⟨9701893686613608256599629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6467929124409072171066419 9701893686613608256599629)
          ·
            refine ⟨3638210132480103096224861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9701893686613608256599629 3638210132480103096224861)
            ·
              refine ⟨1364328799680038661084323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3638210132480103096224861 1364328799680038661084323)
              ·
                refine ⟨2046493199520057991626485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1364328799680038661084323 2046493199520057991626485)
                ·
                  refine ⟨191858737455005436714983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2046493199520057991626485 191858737455005436714983)
                  ·
                    rfl

theorem cell20_420349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_420349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420349 prefixEnd_420349 := by exact prefixLift 420349
  have htrace : WordTrace (prefixWord ++ tailWord_420349) baseStart_420349 baseEnd_420349 := by
    simpa [prefixWord, tailWord_420349, baseEnd_420349] using wordTrace_append hprefix tailTrace_420349
  have hstable : (prefixWord ++ tailWord_420349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420349).length < 2 ^ (prefixWord ++ tailWord_420349).sum := by decide
  have hdescent : baseEnd_420349 < baseStart_420349 := by decide
  rcases family_descends (prefixWord ++ tailWord_420349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420358 : List Nat := [6, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_420358 : Nat := 118140960795 + 420358 * 2 ^ 59
def prefixEnd_420358 : Nat := 4983230072969 + 3 ^ 40 * 420358 * 2
def baseEnd_420358 : Nat := 191862845300241405414947

theorem tailTrace_420358 : CollatzResearch.WordTrace tailWord_420358 prefixEnd_420358 191862845300241405414947 := by
  unfold tailWord_420358
  simp only [CollatzResearch.WordTrace]
  refine ⟨479116119097569758621929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10221143874081488183934485 479116119097569758621929)
  ·
    refine ⟨359337089323177318966447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 479116119097569758621929 359337089323177318966447)
    ·
      refine ⟨539005633984765978449671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359337089323177318966447 539005633984765978449671)
      ·
        refine ⟨808508450977148967674507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539005633984765978449671 808508450977148967674507)
        ·
          refine ⟨1212762676465723451511761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808508450977148967674507 1212762676465723451511761)
          ·
            refine ⟨909572007349292588633821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1212762676465723451511761 909572007349292588633821)
            ·
              refine ⟨341089502755984720737683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 909572007349292588633821 341089502755984720737683)
              ·
                refine ⟨511634254133977081106525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341089502755984720737683 511634254133977081106525)
                ·
                  refine ⟨191862845300241405414947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511634254133977081106525 191862845300241405414947)
                  ·
                    rfl

theorem cell20_420358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_420358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420358 prefixEnd_420358 := by exact prefixLift 420358
  have htrace : WordTrace (prefixWord ++ tailWord_420358) baseStart_420358 baseEnd_420358 := by
    simpa [prefixWord, tailWord_420358, baseEnd_420358] using wordTrace_append hprefix tailTrace_420358
  have hstable : (prefixWord ++ tailWord_420358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420358).length < 2 ^ (prefixWord ++ tailWord_420358).sum := by decide
  have hdescent : baseEnd_420358 < baseStart_420358 := by decide
  rcases family_descends (prefixWord ++ tailWord_420358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420380 : List Nat := [2, 2, 3, 1, 2, 3, 1, 6]
def baseStart_420380 : Nat := 118140960795 + 420380 * 2 ^ 59
def prefixEnd_420380 : Nat := 4983230072969 + 3 ^ 40 * 420380 * 2
def baseEnd_420380 : Nat := 63957628899902368893841

theorem tailTrace_420380 : CollatzResearch.WordTrace tailWord_420380 prefixEnd_420380 63957628899902368893841 := by
  unfold tailWord_420380
  simp only [CollatzResearch.WordTrace]
  refine ⟨7666259108521265016601297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10221678811361686688801729 7666259108521265016601297)
  ·
    refine ⟨5749694331390948762450973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7666259108521265016601297 5749694331390948762450973)
    ·
      refine ⟨2156135374271605785919115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5749694331390948762450973 2156135374271605785919115)
      ·
        refine ⟨3234203061407408678878673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2156135374271605785919115 3234203061407408678878673)
        ·
          refine ⟨2425652296055556509159005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3234203061407408678878673 2425652296055556509159005)
          ·
            refine ⟨909619611020833690934627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2425652296055556509159005 909619611020833690934627)
            ·
              refine ⟨1364429416531250536401941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909619611020833690934627 1364429416531250536401941)
              ·
                refine ⟨63957628899902368893841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1364429416531250536401941 63957628899902368893841)
                ·
                  rfl

theorem cell20_420380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_420380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420380 prefixEnd_420380 := by exact prefixLift 420380
  have htrace : WordTrace (prefixWord ++ tailWord_420380) baseStart_420380 baseEnd_420380 := by
    simpa [prefixWord, tailWord_420380, baseEnd_420380] using wordTrace_append hprefix tailTrace_420380
  have hstable : (prefixWord ++ tailWord_420380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420380).length < 2 ^ (prefixWord ++ tailWord_420380).sum := by decide
  have hdescent : baseEnd_420380 < baseStart_420380 := by decide
  rcases family_descends (prefixWord ++ tailWord_420380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420387 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 5]
def baseStart_420387 : Nat := 118140960795 + 420387 * 2 ^ 59
def prefixEnd_420387 : Nat := 4983230072969 + 3 ^ 40 * 420387 * 2
def baseEnd_420387 : Nat := 191876081690446193448161

theorem tailTrace_420387 : CollatzResearch.WordTrace tailWord_420387 prefixEnd_420387 191876081690446193448161 := by
  unfold tailWord_420387
  simp only [CollatzResearch.WordTrace]
  refine ⟨15332773528017170228707415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10221849018678113485804943 15332773528017170228707415)
  ·
    refine ⟨22999160292025755343061123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15332773528017170228707415 22999160292025755343061123)
    ·
      refine ⟨34498740438038633014591685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22999160292025755343061123 34498740438038633014591685)
      ·
        refine ⟨6468513832132243690235941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34498740438038633014591685 6468513832132243690235941)
        ·
          refine ⟨1212846343524795691919239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6468513832132243690235941 1212846343524795691919239)
          ·
            refine ⟨1819269515287193537878859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212846343524795691919239 1819269515287193537878859)
            ·
              refine ⟨2728904272930790306818289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819269515287193537878859 2728904272930790306818289)
              ·
                refine ⟨2046678204698092730113717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2728904272930790306818289 2046678204698092730113717)
                ·
                  refine ⟨191876081690446193448161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2046678204698092730113717 191876081690446193448161)
                  ·
                    rfl

theorem cell20_420387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_420387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420387 prefixEnd_420387 := by exact prefixLift 420387
  have htrace : WordTrace (prefixWord ++ tailWord_420387) baseStart_420387 baseEnd_420387 := by
    simpa [prefixWord, tailWord_420387, baseEnd_420387] using wordTrace_append hprefix tailTrace_420387
  have hstable : (prefixWord ++ tailWord_420387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420387).length < 2 ^ (prefixWord ++ tailWord_420387).sum := by decide
  have hdescent : baseEnd_420387 < baseStart_420387 := by decide
  rcases family_descends (prefixWord ++ tailWord_420387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420401 : List Nat := [1, 2, 2, 3, 1, 1, 10]
def baseStart_420401 : Nat := 118140960795 + 420401 * 2 ^ 59
def prefixEnd_420401 : Nat := 4983230072969 + 3 ^ 40 * 420401 * 2
def baseEnd_420401 : Nat := 21320274630213818553493

theorem tailTrace_420401 : CollatzResearch.WordTrace tailWord_420401 prefixEnd_420401 21320274630213818553493 := by
  unfold tailWord_420401
  simp only [CollatzResearch.WordTrace]
  refine ⟨15333284149966450619717057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10222189433310967079811371 15333284149966450619717057)
  ·
    refine ⟨11499963112474837964787793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15333284149966450619717057 11499963112474837964787793)
    ·
      refine ⟨8624972334356128473590845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11499963112474837964787793 8624972334356128473590845)
      ·
        refine ⟨3234364625383548177596567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8624972334356128473590845 3234364625383548177596567)
        ·
          refine ⟨4851546938075322266394851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3234364625383548177596567 4851546938075322266394851)
          ·
            refine ⟨7277320407112983399592277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4851546938075322266394851 7277320407112983399592277)
            ·
              refine ⟨21320274630213818553493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7277320407112983399592277 21320274630213818553493)
              ·
                rfl

theorem cell20_420401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 10].length) (baseStart_420401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420401 prefixEnd_420401 := by exact prefixLift 420401
  have htrace : WordTrace (prefixWord ++ tailWord_420401) baseStart_420401 baseEnd_420401 := by
    simpa [prefixWord, tailWord_420401, baseEnd_420401] using wordTrace_append hprefix tailTrace_420401
  have hstable : (prefixWord ++ tailWord_420401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420401).length < 2 ^ (prefixWord ++ tailWord_420401).sum := by decide
  have hdescent : baseEnd_420401 < baseStart_420401 := by decide
  rcases family_descends (prefixWord ++ tailWord_420401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420414 : List Nat := [4, 2, 1, 4, 1, 1, 2, 5]
def baseStart_420414 : Nat := 118140960795 + 420414 * 2 ^ 59
def prefixEnd_420414 : Nat := 4983230072969 + 3 ^ 40 * 420414 * 2
def baseEnd_420414 : Nat := 63962801742051366516017

theorem tailTrace_420414 : CollatzResearch.WordTrace tailWord_420414 prefixEnd_420414 63962801742051366516017 := by
  unfold tailWord_420414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1916719787364919229992537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10222505532612902559960197 1916719787364919229992537)
  ·
    refine ⟨1437539840523689422494403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1916719787364919229992537 1437539840523689422494403)
    ·
      refine ⟨2156309760785534133741605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1437539840523689422494403 2156309760785534133741605)
      ·
        refine ⟨404308080147287650076551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2156309760785534133741605 404308080147287650076551)
        ·
          refine ⟨606462120220931475114827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404308080147287650076551 606462120220931475114827)
          ·
            refine ⟨909693180331397212672241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606462120220931475114827 909693180331397212672241)
            ·
              refine ⟨682269885248547909504181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909693180331397212672241 682269885248547909504181)
              ·
                refine ⟨63962801742051366516017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 682269885248547909504181 63962801742051366516017)
                ·
                  rfl

theorem cell20_420414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_420414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420414 prefixEnd_420414 := by exact prefixLift 420414
  have htrace : WordTrace (prefixWord ++ tailWord_420414) baseStart_420414 baseEnd_420414 := by
    simpa [prefixWord, tailWord_420414, baseEnd_420414] using wordTrace_append hprefix tailTrace_420414
  have hstable : (prefixWord ++ tailWord_420414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420414).length < 2 ^ (prefixWord ++ tailWord_420414).sum := by decide
  have hdescent : baseEnd_420414 < baseStart_420414 := by decide
  rcases family_descends (prefixWord ++ tailWord_420414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420421 : List Nat := [1, 3, 1, 1, 1, 7, 2, 1, 3]
def baseStart_420421 : Nat := 118140960795 + 420421 * 2 ^ 59
def prefixEnd_420421 : Nat := 4983230072969 + 3 ^ 40 * 420421 * 2
def baseEnd_420421 : Nat := 191891600216893186314689

theorem tailTrace_420421 : CollatzResearch.WordTrace tailWord_420421 prefixEnd_420421 191891600216893186314689 := by
  unfold tailWord_420421
  simp only [CollatzResearch.WordTrace]
  refine ⟨15334013609893994035445117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10222675739929329356963411 15334013609893994035445117)
  ·
    refine ⟨5750255103710247763291919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15334013609893994035445117 5750255103710247763291919)
    ·
      refine ⟨8625382655565371644937879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5750255103710247763291919 8625382655565371644937879)
      ·
        refine ⟨12938073983348057467406819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8625382655565371644937879 12938073983348057467406819)
        ·
          refine ⟨19407110975022086201110229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12938073983348057467406819 19407110975022086201110229)
          ·
            refine ⟨454854163477080145338521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 19407110975022086201110229 454854163477080145338521)
            ·
              refine ⟨341140622607810109003891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454854163477080145338521 341140622607810109003891)
              ·
                refine ⟨511710933911715163505837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341140622607810109003891 511710933911715163505837)
                ·
                  refine ⟨191891600216893186314689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511710933911715163505837 191891600216893186314689)
                  ·
                    rfl

theorem cell20_420421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_420421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420421 prefixEnd_420421 := by exact prefixLift 420421
  have htrace : WordTrace (prefixWord ++ tailWord_420421) baseStart_420421 baseEnd_420421 := by
    simpa [prefixWord, tailWord_420421, baseEnd_420421] using wordTrace_append hprefix tailTrace_420421
  have hstable : (prefixWord ++ tailWord_420421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420421).length < 2 ^ (prefixWord ++ tailWord_420421).sum := by decide
  have hdescent : baseEnd_420421 < baseStart_420421 := by decide
  rcases family_descends (prefixWord ++ tailWord_420421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420439 : List Nat := [1, 1, 3, 2, 2, 2, 1, 8]
def baseStart_420439 : Nat := 118140960795 + 420439 * 2 ^ 59
def prefixEnd_420439 : Nat := 4983230072969 + 3 ^ 40 * 420439 * 2
def baseEnd_420439 : Nat := 63966605302455041238205

theorem tailTrace_420439 : CollatzResearch.WordTrace tailWord_420439 prefixEnd_420439 63966605302455041238205 := by
  unfold tailWord_420439
  simp only [CollatzResearch.WordTrace]
  refine ⟨15334670123828783109600371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10223113415885855406400247 15334670123828783109600371)
  ·
    refine ⟨23002005185743174664400557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15334670123828783109600371 23002005185743174664400557)
    ·
      refine ⟨8625751944653690499150209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23002005185743174664400557 8625751944653690499150209)
      ·
        refine ⟨6469313958490267874362657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8625751944653690499150209 6469313958490267874362657)
        ·
          refine ⟨4851985468867700905771993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6469313958490267874362657 4851985468867700905771993)
          ·
            refine ⟨3638989101650775679328995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4851985468867700905771993 3638989101650775679328995)
            ·
              refine ⟨5458483652476163518993493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3638989101650775679328995 5458483652476163518993493)
              ·
                refine ⟨63966605302455041238205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5458483652476163518993493 63966605302455041238205)
                ·
                  rfl

theorem cell20_420439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 8].length) (baseStart_420439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420439 prefixEnd_420439 := by exact prefixLift 420439
  have htrace : WordTrace (prefixWord ++ tailWord_420439) baseStart_420439 baseEnd_420439 := by
    simpa [prefixWord, tailWord_420439, baseEnd_420439] using wordTrace_append hprefix tailTrace_420439
  have hstable : (prefixWord ++ tailWord_420439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420439).length < 2 ^ (prefixWord ++ tailWord_420439).sum := by decide
  have hdescent : baseEnd_420439 < baseStart_420439 := by decide
  rcases family_descends (prefixWord ++ tailWord_420439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420456 : List Nat := [2, 1, 4, 3, 2, 8]
def baseStart_420456 : Nat := 118140960795 + 420456 * 2 ^ 59
def prefixEnd_420456 : Nat := 4983230072969 + 3 ^ 40 * 420456 * 2
def baseEnd_420456 : Nat := 7107687969281060005477

theorem tailTrace_420456 : CollatzResearch.WordTrace tailWord_420456 prefixEnd_420456 7107687969281060005477 := by
  unfold tailWord_420456
  simp only [CollatzResearch.WordTrace]
  refine ⟨7667645082383597506484611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10223526776511463341979481 7667645082383597506484611)
  ·
    refine ⟨11501467623575396259726917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7667645082383597506484611 11501467623575396259726917)
    ·
      refine ⟨2156525179420386798698797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11501467623575396259726917 2156525179420386798698797)
      ·
        refine ⟨808696942282645049512049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2156525179420386798698797 808696942282645049512049)
        ·
          refine ⟨606522706711983787134037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 808696942282645049512049 606522706711983787134037)
          ·
            refine ⟨7107687969281060005477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 606522706711983787134037 7107687969281060005477)
            ·
              rfl

theorem cell20_420456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 8].length) (baseStart_420456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420456 prefixEnd_420456 := by exact prefixLift 420456
  have htrace : WordTrace (prefixWord ++ tailWord_420456) baseStart_420456 baseEnd_420456 := by
    simpa [prefixWord, tailWord_420456, baseEnd_420456] using wordTrace_append hprefix tailTrace_420456
  have hstable : (prefixWord ++ tailWord_420456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420456).length < 2 ^ (prefixWord ++ tailWord_420456).sum := by decide
  have hdescent : baseEnd_420456 < baseStart_420456 := by decide
  rcases family_descends (prefixWord ++ tailWord_420456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420462 : List Nat := [4, 1, 2, 2, 2, 3, 2, 2, 2]
def baseStart_420462 : Nat := 118140960795 + 420462 * 2 ^ 59
def prefixEnd_420462 : Nat := 4983230072969 + 3 ^ 40 * 420462 * 2
def baseEnd_420462 : Nat := 191910313734079265947855

theorem tailTrace_420462 : CollatzResearch.WordTrace tailWord_420462 prefixEnd_420462 191910313734079265947855 := by
  unfold tailWord_420462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1916938625343182254710955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10223672668496972025125093 1916938625343182254710955)
  ·
    refine ⟨2875407938014773382066433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1916938625343182254710955 2875407938014773382066433)
    ·
      refine ⟨2156555953511080036549825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2875407938014773382066433 2156555953511080036549825)
      ·
        refine ⟨1617416965133310027412369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2156555953511080036549825 1617416965133310027412369)
        ·
          refine ⟨1213062723849982520559277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1617416965133310027412369 1213062723849982520559277)
          ·
            refine ⟨454898521443743445209729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1213062723849982520559277 454898521443743445209729)
            ·
              refine ⟨341173891082807583907297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454898521443743445209729 341173891082807583907297)
              ·
                refine ⟨255880418312105687930473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 341173891082807583907297 255880418312105687930473)
                ·
                  refine ⟨191910313734079265947855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255880418312105687930473 191910313734079265947855)
                  ·
                    rfl

theorem cell20_420462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_420462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420462 prefixEnd_420462 := by exact prefixLift 420462
  have htrace : WordTrace (prefixWord ++ tailWord_420462) baseStart_420462 baseEnd_420462 := by
    simpa [prefixWord, tailWord_420462, baseEnd_420462] using wordTrace_append hprefix tailTrace_420462
  have hstable : (prefixWord ++ tailWord_420462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420462).length < 2 ^ (prefixWord ++ tailWord_420462).sum := by decide
  have hdescent : baseEnd_420462 < baseStart_420462 := by decide
  rcases family_descends (prefixWord ++ tailWord_420462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420463 : List Nat := [1, 1, 2, 1, 3, 2, 3, 4, 3]
def baseStart_420463 : Nat := 118140960795 + 420463 * 2 ^ 59
def prefixEnd_420463 : Nat := 4983230072969 + 3 ^ 40 * 420463 * 2
def baseEnd_420463 : Nat := 191910770161327706914517

theorem tailTrace_420463 : CollatzResearch.WordTrace tailWord_420463 prefixEnd_420463 191910770161327706914517 := by
  unfold tailWord_420463
  simp only [CollatzResearch.WordTrace]
  refine ⟨15335545475741835208474043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10223696983827890138982695 15335545475741835208474043)
  ·
    refine ⟨23003318213612752812711065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15335545475741835208474043 23003318213612752812711065)
    ·
      refine ⟨17252488660209564609533299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23003318213612752812711065 17252488660209564609533299)
      ·
        refine ⟨25878732990314346914299949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17252488660209564609533299 25878732990314346914299949)
        ·
          refine ⟨9704524871367880092862481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25878732990314346914299949 9704524871367880092862481)
          ·
            refine ⟨7278393653525910069646861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9704524871367880092862481 7278393653525910069646861)
            ·
              refine ⟨2729397620072216276117573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7278393653525910069646861 2729397620072216276117573)
              ·
                refine ⟨511762053763540551772045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2729397620072216276117573 511762053763540551772045)
                ·
                  refine ⟨191910770161327706914517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511762053763540551772045 191910770161327706914517)
                  ·
                    rfl

theorem cell20_420463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 3].length) (baseStart_420463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420463 prefixEnd_420463 := by exact prefixLift 420463
  have htrace : WordTrace (prefixWord ++ tailWord_420463) baseStart_420463 baseEnd_420463 := by
    simpa [prefixWord, tailWord_420463, baseEnd_420463] using wordTrace_append hprefix tailTrace_420463
  have hstable : (prefixWord ++ tailWord_420463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420463).length < 2 ^ (prefixWord ++ tailWord_420463).sum := by decide
  have hdescent : baseEnd_420463 < baseStart_420463 := by decide
  rcases family_descends (prefixWord ++ tailWord_420463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420504 : List Nat := [2, 1, 2, 4, 1, 1, 4, 3, 2]
def baseStart_420504 : Nat := 118140960795 + 420504 * 2 ^ 59
def prefixEnd_420504 : Nat := 4983230072969 + 3 ^ 40 * 420504 * 2
def baseEnd_420504 : Nat := 191929483678513786547683

theorem tailTrace_420504 : CollatzResearch.WordTrace tailWord_420504 prefixEnd_420504 191929483678513786547683 := by
  unfold tailWord_420504
  simp only [CollatzResearch.WordTrace]
  refine ⟨7668520434296649605358283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10224693912395532807144377 7668520434296649605358283)
  ·
    refine ⟨11502780651444974408037425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7668520434296649605358283 11502780651444974408037425)
    ·
      refine ⟨8627085488583730806028069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11502780651444974408037425 8627085488583730806028069)
      ·
        refine ⟨1617578529109449526130263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8627085488583730806028069 1617578529109449526130263)
        ·
          refine ⟨2426367793664174289195395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1617578529109449526130263 2426367793664174289195395)
          ·
            refine ⟨3639551690496261433793093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2426367793664174289195395 3639551690496261433793093)
            ·
              refine ⟨682415941968049018836205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3639551690496261433793093 682415941968049018836205)
              ·
                refine ⟨255905978238018382063577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 682415941968049018836205 255905978238018382063577)
                ·
                  refine ⟨191929483678513786547683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255905978238018382063577 191929483678513786547683)
                  ·
                    rfl

theorem cell20_420504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 2].length) (baseStart_420504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420504 prefixEnd_420504 := by exact prefixLift 420504
  have htrace : WordTrace (prefixWord ++ tailWord_420504) baseStart_420504 baseEnd_420504 := by
    simpa [prefixWord, tailWord_420504, baseEnd_420504] using wordTrace_append hprefix tailTrace_420504
  have hstable : (prefixWord ++ tailWord_420504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420504).length < 2 ^ (prefixWord ++ tailWord_420504).sum := by decide
  have hdescent : baseEnd_420504 < baseStart_420504 := by decide
  rcases family_descends (prefixWord ++ tailWord_420504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420525 : List Nat := [1, 5, 2, 1, 1, 2, 1, 3, 4]
def baseStart_420525 : Nat := 118140960795 + 420525 * 2 ^ 59
def prefixEnd_420525 : Nat := 4983230072969 + 3 ^ 40 * 420525 * 2
def baseEnd_420525 : Nat := 191939068650731046847597

theorem tailTrace_420525 : CollatzResearch.WordTrace tailWord_420525 prefixEnd_420525 191939068650731046847597 := by
  unfold tailWord_420525
  simp only [CollatzResearch.WordTrace]
  refine ⟨15337806801517219797231029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10225204534344813198154019 15337806801517219797231029)
  ·
    refine ⟨1437919387642239355990409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15337806801517219797231029 1437919387642239355990409)
    ·
      refine ⟨1078439540731679516992807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1437919387642239355990409 1078439540731679516992807)
      ·
        refine ⟨1617659311097519275489211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1078439540731679516992807 1617659311097519275489211)
        ·
          refine ⟨2426488966646278913233817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1617659311097519275489211 2426488966646278913233817)
          ·
            refine ⟨1819866724984709184925363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2426488966646278913233817 1819866724984709184925363)
            ·
              refine ⟨2729800087477063777388045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819866724984709184925363 2729800087477063777388045)
              ·
                refine ⟨1023675032803898916520517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2729800087477063777388045 1023675032803898916520517)
                ·
                  refine ⟨191939068650731046847597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1023675032803898916520517 191939068650731046847597)
                  ·
                    rfl

theorem cell20_420525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_420525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420525 prefixEnd_420525 := by exact prefixLift 420525
  have htrace : WordTrace (prefixWord ++ tailWord_420525) baseStart_420525 baseEnd_420525 := by
    simpa [prefixWord, tailWord_420525, baseEnd_420525] using wordTrace_append hprefix tailTrace_420525
  have hstable : (prefixWord ++ tailWord_420525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420525).length < 2 ^ (prefixWord ++ tailWord_420525).sum := by decide
  have hdescent : baseEnd_420525 < baseStart_420525 := by decide
  rcases family_descends (prefixWord ++ tailWord_420525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420535 : List Nat := [1, 1, 3, 1, 6, 1, 3, 1, 3]
def baseStart_420535 : Nat := 118140960795 + 420535 * 2 ^ 59
def prefixEnd_420535 : Nat := 4983230072969 + 3 ^ 40 * 420535 * 2
def baseEnd_420535 : Nat := 191943632923215456514223

theorem tailTrace_420535 : CollatzResearch.WordTrace tailWord_420535 prefixEnd_420535 191943632923215456514223 := by
  unfold tailWord_420535
  simp only [CollatzResearch.WordTrace]
  refine ⟨15338171531480991505095059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10225447687653994336730039 15338171531480991505095059)
  ·
    refine ⟨23007257297221487257642589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15338171531480991505095059 23007257297221487257642589)
    ·
      refine ⟨8627721486458057721615971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23007257297221487257642589 8627721486458057721615971)
      ·
        refine ⟨12941582229687086582423957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8627721486458057721615971 12941582229687086582423957)
        ·
          refine ⟨606636667016582183551123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12941582229687086582423957 606636667016582183551123)
          ·
            refine ⟨909955000524873275326685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606636667016582183551123 909955000524873275326685)
            ·
              refine ⟨341233125196827478247507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 909955000524873275326685 341233125196827478247507)
              ·
                refine ⟨511849687795241217371261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341233125196827478247507 511849687795241217371261)
                ·
                  refine ⟨191943632923215456514223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511849687795241217371261 191943632923215456514223)
                  ·
                    rfl

theorem cell20_420535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 3].length) (baseStart_420535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420535 prefixEnd_420535 := by exact prefixLift 420535
  have htrace : WordTrace (prefixWord ++ tailWord_420535) baseStart_420535 baseEnd_420535 := by
    simpa [prefixWord, tailWord_420535, baseEnd_420535] using wordTrace_append hprefix tailTrace_420535
  have hstable : (prefixWord ++ tailWord_420535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420535).length < 2 ^ (prefixWord ++ tailWord_420535).sum := by decide
  have hdescent : baseEnd_420535 < baseStart_420535 := by decide
  rcases family_descends (prefixWord ++ tailWord_420535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420545 : List Nat := [1, 2, 6, 2, 1, 2, 2, 4]
def baseStart_420545 : Nat := 118140960795 + 420545 * 2 ^ 59
def prefixEnd_420545 : Nat := 4983230072969 + 3 ^ 40 * 420545 * 2
def baseEnd_420545 : Nat := 63982732398566622060283

theorem tailTrace_420545 : CollatzResearch.WordTrace tailWord_420545 prefixEnd_420545 63982732398566622060283 := by
  unfold tailWord_420545
  simp only [CollatzResearch.WordTrace]
  refine ⟨15338536261444763212959089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10225690840963175475306059 15338536261444763212959089)
  ·
    refine ⟨11503902196083572409719317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15338536261444763212959089 11503902196083572409719317)
    ·
      refine ⟨539245415441417456705593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11503902196083572409719317 539245415441417456705593)
      ·
        refine ⟨404434061581063092529195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539245415441417456705593 404434061581063092529195)
        ·
          refine ⟨606651092371594638793793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404434061581063092529195 606651092371594638793793)
          ·
            refine ⟨454988319278695979095345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 606651092371594638793793 454988319278695979095345)
            ·
              refine ⟨341241239459021984321509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454988319278695979095345 341241239459021984321509)
              ·
                refine ⟨63982732398566622060283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 341241239459021984321509 63982732398566622060283)
                ·
                  rfl

theorem cell20_420545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 4].length) (baseStart_420545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420545 prefixEnd_420545 := by exact prefixLift 420545
  have htrace : WordTrace (prefixWord ++ tailWord_420545) baseStart_420545 baseEnd_420545 := by
    simpa [prefixWord, tailWord_420545, baseEnd_420545] using wordTrace_append hprefix tailTrace_420545
  have hstable : (prefixWord ++ tailWord_420545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420545).length < 2 ^ (prefixWord ++ tailWord_420545).sum := by decide
  have hdescent : baseEnd_420545 < baseStart_420545 := by decide
  rcases family_descends (prefixWord ++ tailWord_420545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420577 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 5]
def baseStart_420577 : Nat := 118140960795 + 420577 * 2 ^ 59
def prefixEnd_420577 : Nat := 4983230072969 + 3 ^ 40 * 420577 * 2
def baseEnd_420577 : Nat := 191962802867649977114051

theorem tailTrace_420577 : CollatzResearch.WordTrace tailWord_420577 prefixEnd_420577 191962802867649977114051 := by
  unfold tailWord_420577
  simp only [CollatzResearch.WordTrace]
  refine ⟨15339703397328832678123985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10226468931552555118749323 15339703397328832678123985)
  ·
    refine ⟨11504777547996624508592989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15339703397328832678123985 11504777547996624508592989)
    ·
      refine ⟨4314291580498734190722371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11504777547996624508592989 4314291580498734190722371)
      ·
        refine ⟨6471437370748101286083557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4314291580498734190722371 6471437370748101286083557)
        ·
          refine ⟨1213394507015268991140667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6471437370748101286083557 1213394507015268991140667)
          ·
            refine ⟨1820091760522903486711001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1213394507015268991140667 1820091760522903486711001)
            ·
              refine ⟨1365068820392177615033251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1820091760522903486711001 1365068820392177615033251)
              ·
                refine ⟨2047603230588266422549877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1365068820392177615033251 2047603230588266422549877)
                ·
                  refine ⟨191962802867649977114051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2047603230588266422549877 191962802867649977114051)
                  ·
                    rfl

theorem cell20_420577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_420577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420577 prefixEnd_420577 := by exact prefixLift 420577
  have htrace : WordTrace (prefixWord ++ tailWord_420577) baseStart_420577 baseEnd_420577 := by
    simpa [prefixWord, tailWord_420577, baseEnd_420577] using wordTrace_append hprefix tailTrace_420577
  have hstable : (prefixWord ++ tailWord_420577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420577).length < 2 ^ (prefixWord ++ tailWord_420577).sum := by decide
  have hdescent : baseEnd_420577 < baseStart_420577 := by decide
  rcases family_descends (prefixWord ++ tailWord_420577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420591 : List Nat := [1, 1, 2, 1, 5, 2, 1, 7]
def baseStart_420591 : Nat := 118140960795 + 420591 * 2 ^ 59
def prefixEnd_420591 : Nat := 4983230072969 + 3 ^ 40 * 420591 * 2
def baseEnd_420591 : Nat := 63989730949709383549109

theorem tailTrace_420591 : CollatzResearch.WordTrace tailWord_420591 prefixEnd_420591 63989730949709383549109 := by
  unfold tailWord_420591
  simp only [CollatzResearch.WordTrace]
  refine ⟨15340214019278113069133627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10226809346185408712755751 15340214019278113069133627)
  ·
    refine ⟨23010321028917169603700441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15340214019278113069133627 23010321028917169603700441)
    ·
      refine ⟨17257740771687877202775331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23010321028917169603700441 17257740771687877202775331)
      ·
        refine ⟨25886611157531815804162997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17257740771687877202775331 25886611157531815804162997)
        ·
          refine ⟨2426869796018607731640281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25886611157531815804162997 2426869796018607731640281)
          ·
            refine ⟨1820152347013955798730211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2426869796018607731640281 1820152347013955798730211)
            ·
              refine ⟨2730228520520933698095317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1820152347013955798730211 2730228520520933698095317)
              ·
                refine ⟨63989730949709383549109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2730228520520933698095317 63989730949709383549109)
                ·
                  rfl

theorem cell20_420591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 7].length) (baseStart_420591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420591 prefixEnd_420591 := by exact prefixLift 420591
  have htrace : WordTrace (prefixWord ++ tailWord_420591) baseStart_420591 baseEnd_420591 := by
    simpa [prefixWord, tailWord_420591, baseEnd_420591] using wordTrace_append hprefix tailTrace_420591
  have hstable : (prefixWord ++ tailWord_420591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420591).length < 2 ^ (prefixWord ++ tailWord_420591).sum := by decide
  have hdescent : baseEnd_420591 < baseStart_420591 := by decide
  rcases family_descends (prefixWord ++ tailWord_420591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420594 : List Nat := [3, 2, 1, 3, 1, 3, 1, 3, 3]
def baseStart_420594 : Nat := 118140960795 + 420594 * 2 ^ 59
def prefixEnd_420594 : Nat := 4983230072969 + 3 ^ 40 * 420594 * 2
def baseEnd_420594 : Nat := 191970562130873473547315

theorem tailTrace_420594 : CollatzResearch.WordTrace tailWord_420594 prefixEnd_420594 191970562130873473547315 := by
  unfold tailWord_420594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3835080859566811145373209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10226882292178163054328557 3835080859566811145373209)
  ·
    refine ⟨2876310644675108359029907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3835080859566811145373209 2876310644675108359029907)
    ·
      refine ⟨4314465967012662538544861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2876310644675108359029907 4314465967012662538544861)
      ·
        refine ⟨1617924737629748451954323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4314465967012662538544861 1617924737629748451954323)
        ·
          refine ⟨2426887106444622677931485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1617924737629748451954323 2426887106444622677931485)
          ·
            refine ⟨910082664916733504224307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2426887106444622677931485 910082664916733504224307)
            ·
              refine ⟨1365123997375100256336461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910082664916733504224307 1365123997375100256336461)
              ·
                refine ⟨511921499015662596126173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1365123997375100256336461 511921499015662596126173)
                ·
                  refine ⟨191970562130873473547315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511921499015662596126173 191970562130873473547315)
                  ·
                    rfl

theorem cell20_420594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_420594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420594 prefixEnd_420594 := by exact prefixLift 420594
  have htrace : WordTrace (prefixWord ++ tailWord_420594) baseStart_420594 baseEnd_420594 := by
    simpa [prefixWord, tailWord_420594, baseEnd_420594] using wordTrace_append hprefix tailTrace_420594
  have hstable : (prefixWord ++ tailWord_420594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420594).length < 2 ^ (prefixWord ++ tailWord_420594).sum := by decide
  have hdescent : baseEnd_420594 < baseStart_420594 := by decide
  rcases family_descends (prefixWord ++ tailWord_420594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420698 : List Nat := [3, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_420698 : Nat := 118140960795 + 420698 * 2 ^ 59
def prefixEnd_420698 : Nat := 4983230072969 + 3 ^ 40 * 420698 * 2
def baseEnd_420698 : Nat := 192018030564711334080223

theorem tailTrace_420698 : CollatzResearch.WordTrace tailWord_420698 prefixEnd_420698 192018030564711334080223 := by
  unfold tailWord_420698
  simp only [CollatzResearch.WordTrace]
  refine ⟨3836029157472617585819687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10229411086593646895519165 3836029157472617585819687)
  ·
    refine ⟨5754043736208926378729531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3836029157472617585819687 5754043736208926378729531)
    ·
      refine ⟨8631065604313389568094297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5754043736208926378729531 8631065604313389568094297)
      ·
        refine ⟨6473299203235042176070723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8631065604313389568094297 6473299203235042176070723)
        ·
          refine ⟨9709948804852563264106085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6473299203235042176070723 9709948804852563264106085)
          ·
            refine ⟨1820615400909855612019891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9709948804852563264106085 1820615400909855612019891)
            ·
              refine ⟨2730923101364783418029837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1820615400909855612019891 2730923101364783418029837)
              ·
                refine ⟨1024096163011793781761189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2730923101364783418029837 1024096163011793781761189)
                ·
                  refine ⟨192018030564711334080223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1024096163011793781761189 192018030564711334080223)
                  ·
                    rfl

theorem cell20_420698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_420698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420698 prefixEnd_420698 := by exact prefixLift 420698
  have htrace : WordTrace (prefixWord ++ tailWord_420698) baseStart_420698 baseEnd_420698 := by
    simpa [prefixWord, tailWord_420698, baseEnd_420698] using wordTrace_append hprefix tailTrace_420698
  have hstable : (prefixWord ++ tailWord_420698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420698).length < 2 ^ (prefixWord ++ tailWord_420698).sum := by decide
  have hdescent : baseEnd_420698 < baseStart_420698 := by decide
  rcases family_descends (prefixWord ++ tailWord_420698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420718 : List Nat := [4, 1, 2, 3, 2, 2, 2, 4]
def baseStart_420718 : Nat := 118140960795 + 420718 * 2 ^ 59
def prefixEnd_420718 : Nat := 4983230072969 + 3 ^ 40 * 420718 * 2
def baseEnd_420718 : Nat := 64009053036560051137825

theorem tailTrace_420718 : CollatzResearch.WordTrace tailWord_420718 prefixEnd_420718 64009053036560051137825 := by
  unfold tailWord_420718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1918105761227251719875851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10229897393212009172671205 1918105761227251719875851)
  ·
    refine ⟨2877158641840877579813777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1918105761227251719875851 2877158641840877579813777)
    ·
      refine ⟨2157868981380658184860333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2877158641840877579813777 2157868981380658184860333)
      ·
        refine ⟨809200868017746819322625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2157868981380658184860333 809200868017746819322625)
        ·
          refine ⟨606900651013310114491969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 809200868017746819322625 606900651013310114491969)
          ·
            refine ⟨455175488259982585868977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 606900651013310114491969 455175488259982585868977)
            ·
              refine ⟨341381616194986939401733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455175488259982585868977 341381616194986939401733)
              ·
                refine ⟨64009053036560051137825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 341381616194986939401733 64009053036560051137825)
                ·
                  rfl

theorem cell20_420718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_420718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420718 prefixEnd_420718 := by exact prefixLift 420718
  have htrace : WordTrace (prefixWord ++ tailWord_420718) baseStart_420718 baseEnd_420718 := by
    simpa [prefixWord, tailWord_420718, baseEnd_420718] using wordTrace_append hprefix tailTrace_420718
  have hstable : (prefixWord ++ tailWord_420718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420718).length < 2 ^ (prefixWord ++ tailWord_420718).sum := by decide
  have hdescent : baseEnd_420718 < baseStart_420718 := by decide
  rcases family_descends (prefixWord ++ tailWord_420718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420722 : List Nat := [3, 2, 1, 2, 1, 1, 6, 4]
def baseStart_420722 : Nat := 118140960795 + 420722 * 2 ^ 59
def prefixEnd_420722 : Nat := 4983230072969 + 3 ^ 40 * 420722 * 2
def baseEnd_420722 : Nat := 64009661606224639093375

theorem tailTrace_420722 : CollatzResearch.WordTrace tailWord_420722 prefixEnd_420722 64009661606224639093375 := by
  unfold tailWord_420722
  simp only [CollatzResearch.WordTrace]
  refine ⟨3836247995450880610538105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10229994654535681628101613 3836247995450880610538105)
  ·
    refine ⟨2877185996588160457903579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3836247995450880610538105 2877185996588160457903579)
    ·
      refine ⟨4315778994882240686855369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2877185996588160457903579 4315778994882240686855369)
      ·
        refine ⟨3236834246161680515141527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4315778994882240686855369 3236834246161680515141527)
        ·
          refine ⟨4855251369242520772712291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3236834246161680515141527 4855251369242520772712291)
          ·
            refine ⟨7282877053863781159068437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4855251369242520772712291 7282877053863781159068437)
            ·
              refine ⟨341384861899864741831333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7282877053863781159068437 341384861899864741831333)
              ·
                refine ⟨64009661606224639093375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 341384861899864741831333 64009661606224639093375)
                ·
                  rfl

theorem cell20_420722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_420722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420722 prefixEnd_420722 := by exact prefixLift 420722
  have htrace : WordTrace (prefixWord ++ tailWord_420722) baseStart_420722 baseEnd_420722 := by
    simpa [prefixWord, tailWord_420722, baseEnd_420722] using wordTrace_append hprefix tailTrace_420722
  have hstable : (prefixWord ++ tailWord_420722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420722).length < 2 ^ (prefixWord ++ tailWord_420722).sum := by decide
  have hdescent : baseEnd_420722 < baseStart_420722 := by decide
  rcases family_descends (prefixWord ++ tailWord_420722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420743 : List Nat := [1, 1, 4, 2, 3, 1, 8]
def baseStart_420743 : Nat := 118140960795 + 420743 * 2 ^ 59
def prefixEnd_420743 : Nat := 4983230072969 + 3 ^ 40 * 420743 * 2
def baseEnd_420743 : Nat := 21337618865654575286671

theorem tailTrace_420743 : CollatzResearch.WordTrace tailWord_420743 prefixEnd_420743 21337618865654575286671 := by
  unfold tailWord_420743
  simp only [CollatzResearch.WordTrace]
  refine ⟨15345757914727443028666883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10230505276484962019111255 15345757914727443028666883)
  ·
    refine ⟨23018636872091164543000325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15345757914727443028666883 23018636872091164543000325)
    ·
      refine ⟨4315994413517093351812561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23018636872091164543000325 4315994413517093351812561)
      ·
        refine ⟨3236995810137820013859421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4315994413517093351812561 3236995810137820013859421)
        ·
          refine ⟨1213873428801682505197283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3236995810137820013859421 1213873428801682505197283)
          ·
            refine ⟨1820810143202523757795925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1213873428801682505197283 1820810143202523757795925)
            ·
              refine ⟨21337618865654575286671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1820810143202523757795925 21337618865654575286671)
              ·
                rfl

theorem cell20_420743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 8].length) (baseStart_420743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420743 prefixEnd_420743 := by exact prefixLift 420743
  have htrace : WordTrace (prefixWord ++ tailWord_420743) baseStart_420743 baseEnd_420743 := by
    simpa [prefixWord, tailWord_420743, baseEnd_420743] using wordTrace_append hprefix tailTrace_420743
  have hstable : (prefixWord ++ tailWord_420743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420743).length < 2 ^ (prefixWord ++ tailWord_420743).sum := by decide
  have hdescent : baseEnd_420743 < baseStart_420743 := by decide
  rcases family_descends (prefixWord ++ tailWord_420743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420808 : List Nat := [2, 1, 3, 1, 5, 1, 1, 4, 2]
def baseStart_420808 : Nat := 118140960795 + 420808 * 2 ^ 59
def prefixEnd_420808 : Nat := 4983230072969 + 3 ^ 40 * 420808 * 2
def baseEnd_420808 : Nat := 192068237562039840413107

theorem tailTrace_420808 : CollatzResearch.WordTrace tailWord_420808 prefixEnd_420808 192068237562039840413107 := by
  unfold tailWord_420808
  simp only [CollatzResearch.WordTrace]
  refine ⟨7674064329745979564891539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10232085772994639419855385 7674064329745979564891539)
  ·
    refine ⟨11511096494618969347337309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7674064329745979564891539 11511096494618969347337309)
    ·
      refine ⟨4316661185482113505251491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11511096494618969347337309 4316661185482113505251491)
      ·
        refine ⟨6474991778223170257877237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4316661185482113505251491 6474991778223170257877237)
        ·
          refine ⟨607030479208422211675991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6474991778223170257877237 607030479208422211675991)
          ·
            refine ⟨910545718812633317513987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607030479208422211675991 910545718812633317513987)
            ·
              refine ⟨1365818578218949976270981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910545718812633317513987 1365818578218949976270981)
              ·
                refine ⟨256090983416053120550809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1365818578218949976270981 256090983416053120550809)
                ·
                  refine ⟨192068237562039840413107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256090983416053120550809 192068237562039840413107)
                  ·
                    rfl

theorem cell20_420808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 2].length) (baseStart_420808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420808 prefixEnd_420808 := by exact prefixLift 420808
  have htrace : WordTrace (prefixWord ++ tailWord_420808) baseStart_420808 baseEnd_420808 := by
    simpa [prefixWord, tailWord_420808, baseEnd_420808] using wordTrace_append hprefix tailTrace_420808
  have hstable : (prefixWord ++ tailWord_420808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420808).length < 2 ^ (prefixWord ++ tailWord_420808).sum := by decide
  have hdescent : baseEnd_420808 < baseStart_420808 := by decide
  rcases family_descends (prefixWord ++ tailWord_420808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420812 : List Nat := [2, 2, 1, 4, 1, 1, 2, 3, 4]
def baseStart_420812 : Nat := 118140960795 + 420812 * 2 ^ 59
def prefixEnd_420812 : Nat := 4983230072969 + 3 ^ 40 * 420812 * 2
def baseEnd_420812 : Nat := 192070063271033604279757

theorem tailTrace_420812 : CollatzResearch.WordTrace tailWord_420812 prefixEnd_420812 192070063271033604279757 := by
  unfold tailWord_420812
  simp only [CollatzResearch.WordTrace]
  refine ⟨7674137275738733906464345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10232183034318311875285793 7674137275738733906464345)
  ·
    refine ⟨5755602956804050429848259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7674137275738733906464345 5755602956804050429848259)
    ·
      refine ⟨8633404435206075644772389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5755602956804050429848259 8633404435206075644772389)
      ·
        refine ⟨1618763331601139183394823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8633404435206075644772389 1618763331601139183394823)
        ·
          refine ⟨2428144997401708775092235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1618763331601139183394823 2428144997401708775092235)
          ·
            refine ⟨3642217496102563162638353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2428144997401708775092235 3642217496102563162638353)
            ·
              refine ⟨2731663122076922371978765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3642217496102563162638353 2731663122076922371978765)
              ·
                refine ⟨1024373670778845889492037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2731663122076922371978765 1024373670778845889492037)
                ·
                  refine ⟨192070063271033604279757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1024373670778845889492037 192070063271033604279757)
                  ·
                    rfl

theorem cell20_420812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_420812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420812 prefixEnd_420812 := by exact prefixLift 420812
  have htrace : WordTrace (prefixWord ++ tailWord_420812) baseStart_420812 baseEnd_420812 := by
    simpa [prefixWord, tailWord_420812, baseEnd_420812] using wordTrace_append hprefix tailTrace_420812
  have hstable : (prefixWord ++ tailWord_420812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420812).length < 2 ^ (prefixWord ++ tailWord_420812).sum := by decide
  have hdescent : baseEnd_420812 < baseStart_420812 := by decide
  rcases family_descends (prefixWord ++ tailWord_420812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420829 : List Nat := [1, 4, 3, 1, 2, 2, 1, 2, 4]
def baseStart_420829 : Nat := 118140960795 + 420829 * 2 ^ 59
def prefixEnd_420829 : Nat := 4983230072969 + 3 ^ 40 * 420829 * 2
def baseEnd_420829 : Nat := 192077822534257100713021

theorem tailTrace_420829 : CollatzResearch.WordTrace tailWord_420829 prefixEnd_420829 192077822534257100713021 := by
  unfold tailWord_420829
  simp only [CollatzResearch.WordTrace]
  refine ⟨15348894592415879716297541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10232596394943919810865027 15348894592415879716297541)
  ·
    refine ⟨2877917736077977446805789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15348894592415879716297541 2877917736077977446805789)
    ·
      refine ⟨1079219151029241542552171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2877917736077977446805789 1079219151029241542552171)
      ·
        refine ⟨1618828726543862313828257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1079219151029241542552171 1618828726543862313828257)
        ·
          refine ⟨1214121544907896735371193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1618828726543862313828257 1214121544907896735371193)
          ·
            refine ⟨910591158680922551528395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1214121544907896735371193 910591158680922551528395)
            ·
              refine ⟨1365886738021383827292593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910591158680922551528395 1365886738021383827292593)
              ·
                refine ⟨1024415053516037870469445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1365886738021383827292593 1024415053516037870469445)
                ·
                  refine ⟨192077822534257100713021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1024415053516037870469445 192077822534257100713021)
                  ·
                    rfl

theorem cell20_420829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_420829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420829 prefixEnd_420829 := by exact prefixLift 420829
  have htrace : WordTrace (prefixWord ++ tailWord_420829) baseStart_420829 baseEnd_420829 := by
    simpa [prefixWord, tailWord_420829, baseEnd_420829] using wordTrace_append hprefix tailTrace_420829
  have hstable : (prefixWord ++ tailWord_420829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420829).length < 2 ^ (prefixWord ++ tailWord_420829).sum := by decide
  have hdescent : baseEnd_420829 < baseStart_420829 := by decide
  rcases family_descends (prefixWord ++ tailWord_420829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420852 : List Nat := [2, 6, 2, 1, 1, 2, 1, 2, 3]
def baseStart_420852 : Nat := 118140960795 + 420852 * 2 ^ 59
def prefixEnd_420852 : Nat := 4983230072969 + 3 ^ 40 * 420852 * 2
def baseEnd_420852 : Nat := 192088320360971242946261

theorem tailTrace_420852 : CollatzResearch.WordTrace tailWord_420852 prefixEnd_420852 192088320360971242946261 := by
  unfold tailWord_420852
  simp only [CollatzResearch.WordTrace]
  refine ⟨7674866735666277322192405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10233155647555036429589873 7674866735666277322192405)
  ·
    refine ⟨359759378234356749477769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7674866735666277322192405 359759378234356749477769)
    ·
      refine ⟨269819533675767562108327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359759378234356749477769 269819533675767562108327)
      ·
        refine ⟨404729300513651343162491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269819533675767562108327 404729300513651343162491)
        ·
          refine ⟨607093950770477014743737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404729300513651343162491 607093950770477014743737)
          ·
            refine ⟨455320463077857761057803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 607093950770477014743737 455320463077857761057803)
            ·
              refine ⟨682980694616786641586705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455320463077857761057803 682980694616786641586705)
              ·
                refine ⟨512235520962589981190029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682980694616786641586705 512235520962589981190029)
                ·
                  refine ⟨192088320360971242946261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 512235520962589981190029 192088320360971242946261)
                  ·
                    rfl

theorem cell20_420852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_420852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420852 prefixEnd_420852 := by exact prefixLift 420852
  have htrace : WordTrace (prefixWord ++ tailWord_420852) baseStart_420852 baseEnd_420852 := by
    simpa [prefixWord, tailWord_420852, baseEnd_420852] using wordTrace_append hprefix tailTrace_420852
  have hstable : (prefixWord ++ tailWord_420852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420852).length < 2 ^ (prefixWord ++ tailWord_420852).sum := by decide
  have hdescent : baseEnd_420852 < baseStart_420852 := by decide
  rcases family_descends (prefixWord ++ tailWord_420852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420853 : List Nat := [1, 3, 5, 2, 1, 1, 7]
def baseStart_420853 : Nat := 118140960795 + 420853 * 2 ^ 59
def prefixEnd_420853 : Nat := 4983230072969 + 3 ^ 40 * 420853 * 2
def baseEnd_420853 : Nat := 21343197420913298212547

theorem tailTrace_420853 : CollatzResearch.WordTrace tailWord_420853 prefixEnd_420853 21343197420913298212547 := by
  unfold tailWord_420853
  simp only [CollatzResearch.WordTrace]
  refine ⟨15349769944328931815171213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10233179962885954543447475 15349769944328931815171213)
  ·
    refine ⟨5756163729123349430689205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15349769944328931815171213 5756163729123349430689205)
    ·
      refine ⟨539640349605314009127113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5756163729123349430689205 539640349605314009127113)
      ·
        refine ⟨404730262203985506845335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539640349605314009127113 404730262203985506845335)
        ·
          refine ⟨607095393305978260268003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404730262203985506845335 607095393305978260268003)
          ·
            refine ⟨910643089958967390402005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607095393305978260268003 910643089958967390402005)
            ·
              refine ⟨21343197420913298212547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 910643089958967390402005 21343197420913298212547)
              ·
                rfl

theorem cell20_420853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 7].length) (baseStart_420853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420853 prefixEnd_420853 := by exact prefixLift 420853
  have htrace : WordTrace (prefixWord ++ tailWord_420853) baseStart_420853 baseEnd_420853 := by
    simpa [prefixWord, tailWord_420853, baseEnd_420853] using wordTrace_append hprefix tailTrace_420853
  have hstable : (prefixWord ++ tailWord_420853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420853).length < 2 ^ (prefixWord ++ tailWord_420853).sum := by decide
  have hdescent : baseEnd_420853 < baseStart_420853 := by decide
  rcases family_descends (prefixWord ++ tailWord_420853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420860 : List Nat := [2, 2, 2, 1, 2, 5, 1, 2, 3]
def baseStart_420860 : Nat := 118140960795 + 420860 * 2 ^ 59
def prefixEnd_420860 : Nat := 4983230072969 + 3 ^ 40 * 420860 * 2
def baseEnd_420860 : Nat := 192091971778958770679561

theorem tailTrace_420860 : CollatzResearch.WordTrace tailWord_420860 prefixEnd_420860 192091971778958770679561 := by
  unfold tailWord_420860
  simp only [CollatzResearch.WordTrace]
  refine ⟨7675012627651786005338017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10233350170202381340450689 7675012627651786005338017)
  ·
    refine ⟨5756259470738839504003513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7675012627651786005338017 5756259470738839504003513)
    ·
      refine ⟨4317194603054129628002635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5756259470738839504003513 4317194603054129628002635)
      ·
        refine ⟨6475791904581194442003953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4317194603054129628002635 6475791904581194442003953)
        ·
          refine ⟨4856843928435895831502965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6475791904581194442003953 4856843928435895831502965)
          ·
            refine ⟨455329118290865234203403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4856843928435895831502965 455329118290865234203403)
            ·
              refine ⟨682993677436297851305105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455329118290865234203403 682993677436297851305105)
              ·
                refine ⟨512245258077223388478829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682993677436297851305105 512245258077223388478829)
                ·
                  refine ⟨192091971778958770679561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 512245258077223388478829 192091971778958770679561)
                  ·
                    rfl

theorem cell20_420860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_420860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420860 prefixEnd_420860 := by exact prefixLift 420860
  have htrace : WordTrace (prefixWord ++ tailWord_420860) baseStart_420860 baseEnd_420860 := by
    simpa [prefixWord, tailWord_420860, baseEnd_420860] using wordTrace_append hprefix tailTrace_420860
  have hstable : (prefixWord ++ tailWord_420860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420860).length < 2 ^ (prefixWord ++ tailWord_420860).sum := by decide
  have hdescent : baseEnd_420860 < baseStart_420860 := by decide
  rcases family_descends (prefixWord ++ tailWord_420860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420888 : List Nat := [2, 1, 2, 3, 2, 2, 2, 2, 4]
def baseStart_420888 : Nat := 118140960795 + 420888 * 2 ^ 59
def prefixEnd_420888 : Nat := 4983230072969 + 3 ^ 40 * 420888 * 2
def baseEnd_420888 : Nat := 192104751741915117746113

theorem tailTrace_420888 : CollatzResearch.WordTrace tailWord_420888 prefixEnd_420888 192104751741915117746113 := by
  unfold tailWord_420888
  simp only [CollatzResearch.WordTrace]
  refine ⟨7675523249601066396347659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10234030999468088528463545 7675523249601066396347659)
  ·
    refine ⟨11513284874401599594521489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7675523249601066396347659 11513284874401599594521489)
    ·
      refine ⟨8634963655801199695891117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11513284874401599594521489 8634963655801199695891117)
      ·
        refine ⟨3238111370925449885959169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8634963655801199695891117 3238111370925449885959169)
        ·
          refine ⟨2428583528194087414469377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3238111370925449885959169 2428583528194087414469377)
          ·
            refine ⟨1821437646145565560852033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2428583528194087414469377 1821437646145565560852033)
            ·
              refine ⟨1366078234609174170639025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1821437646145565560852033 1366078234609174170639025)
              ·
                refine ⟨1024558675956880627979269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1366078234609174170639025 1024558675956880627979269)
                ·
                  refine ⟨192104751741915117746113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1024558675956880627979269 192104751741915117746113)
                  ·
                    rfl

theorem cell20_420888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_420888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420888 prefixEnd_420888 := by exact prefixLift 420888
  have htrace : WordTrace (prefixWord ++ tailWord_420888) baseStart_420888 baseEnd_420888 := by
    simpa [prefixWord, tailWord_420888, baseEnd_420888] using wordTrace_append hprefix tailTrace_420888
  have hstable : (prefixWord ++ tailWord_420888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420888).length < 2 ^ (prefixWord ++ tailWord_420888).sum := by decide
  have hdescent : baseEnd_420888 < baseStart_420888 := by decide
  rcases family_descends (prefixWord ++ tailWord_420888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420895 : List Nat := [1, 1, 2, 4, 1, 4, 1, 6]
def baseStart_420895 : Nat := 118140960795 + 420895 * 2 ^ 59
def prefixEnd_420895 : Nat := 4983230072969 + 3 ^ 40 * 420895 * 2
def baseEnd_420895 : Nat := 64035982244218068170917

theorem tailTrace_420895 : CollatzResearch.WordTrace tailWord_420895 prefixEnd_420895 64035982244218068170917 := by
  unfold tailWord_420895
  simp only [CollatzResearch.WordTrace]
  refine ⟨15351301810176772988200139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10234201206784515325466759 15351301810176772988200139)
  ·
    refine ⟨23026952715265159482300209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15351301810176772988200139 23026952715265159482300209)
    ·
      refine ⟨17270214536448869611725157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23026952715265159482300209 17270214536448869611725157)
      ·
        refine ⟨3238165225584163052198467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17270214536448869611725157 3238165225584163052198467)
        ·
          refine ⟨4857247838376244578297701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3238165225584163052198467 4857247838376244578297701)
          ·
            refine ⟨910733969695545858430819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4857247838376244578297701 910733969695545858430819)
            ·
              refine ⟨1366100954543318787646229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910733969695545858430819 1366100954543318787646229)
              ·
                refine ⟨64035982244218068170917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1366100954543318787646229 64035982244218068170917)
                ·
                  rfl

theorem cell20_420895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 6].length) (baseStart_420895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420895 prefixEnd_420895 := by exact prefixLift 420895
  have htrace : WordTrace (prefixWord ++ tailWord_420895) baseStart_420895 baseEnd_420895 := by
    simpa [prefixWord, tailWord_420895, baseEnd_420895] using wordTrace_append hprefix tailTrace_420895
  have hstable : (prefixWord ++ tailWord_420895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420895).length < 2 ^ (prefixWord ++ tailWord_420895).sum := by decide
  have hdescent : baseEnd_420895 < baseStart_420895 := by decide
  rcases family_descends (prefixWord ++ tailWord_420895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420974 : List Nat := [4, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_420974 : Nat := 118140960795 + 420974 * 2 ^ 59
def prefixEnd_420974 : Nat := 4983230072969 + 3 ^ 40 * 420974 * 2
def baseEnd_420974 : Nat := 192144004485281040879095

theorem tailTrace_420974 : CollatzResearch.WordTrace tailWord_420974 prefixEnd_420974 192144004485281040879095 := by
  unfold tailWord_420974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1919272897111321185040747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10236122117927046320217317 1919272897111321185040747)
  ·
    refine ⟨2878909345666981777561121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1919272897111321185040747 2878909345666981777561121)
    ·
      refine ⟨2159182009250236333170841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2878909345666981777561121 2159182009250236333170841)
      ·
        refine ⟨1619386506937677249878131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2159182009250236333170841 1619386506937677249878131)
        ·
          refine ⟨2429079760406515874817197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1619386506937677249878131 2429079760406515874817197)
          ·
            refine ⟨910904910152443453056449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2429079760406515874817197 910904910152443453056449)
            ·
              refine ⟨683178682614332589792337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 910904910152443453056449 683178682614332589792337)
              ·
                refine ⟨512384011960749442344253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 683178682614332589792337 512384011960749442344253)
                ·
                  refine ⟨192144004485281040879095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 512384011960749442344253 192144004485281040879095)
                  ·
                    rfl

theorem cell20_420974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_420974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_420974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_420974 prefixEnd_420974 := by exact prefixLift 420974
  have htrace : WordTrace (prefixWord ++ tailWord_420974) baseStart_420974 baseEnd_420974 := by
    simpa [prefixWord, tailWord_420974, baseEnd_420974] using wordTrace_append hprefix tailTrace_420974
  have hstable : (prefixWord ++ tailWord_420974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420974).length < 2 ^ (prefixWord ++ tailWord_420974).sum := by decide
  have hdescent : baseEnd_420974 < baseStart_420974 := by decide
  rcases family_descends (prefixWord ++ tailWord_420974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421002 : List Nat := [3, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_421002 : Nat := 118140960795 + 421002 * 2 ^ 59
def prefixEnd_421002 : Nat := 4983230072969 + 3 ^ 40 * 421002 * 2
def baseEnd_421002 : Nat := 192156784448237387945647

theorem tailTrace_421002 : CollatzResearch.WordTrace tailWord_421002 prefixEnd_421002 192156784448237387945647 := by
  unfold tailWord_421002
  simp only [CollatzResearch.WordTrace]
  refine ⟨3838801105197282565586315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10236802947192753508230173 3838801105197282565586315)
  ·
    refine ⟨5758201657795923848379473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3838801105197282565586315 5758201657795923848379473)
    ·
      refine ⟨4318651243346942886284605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5758201657795923848379473 4318651243346942886284605)
      ·
        refine ⟨1619494216255103582356727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4318651243346942886284605 1619494216255103582356727)
        ·
          refine ⟨2429241324382655373535091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1619494216255103582356727 2429241324382655373535091)
          ·
            refine ⟨3643861986573983060302637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2429241324382655373535091 3643861986573983060302637)
            ·
              refine ⟨1366448244965243647613489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3643861986573983060302637 1366448244965243647613489)
              ·
                refine ⟨1024836183723932735710117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1366448244965243647613489 1024836183723932735710117)
                ·
                  refine ⟨192156784448237387945647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1024836183723932735710117 192156784448237387945647)
                  ·
                    rfl

theorem cell20_421002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_421002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421002 prefixEnd_421002 := by exact prefixLift 421002
  have htrace : WordTrace (prefixWord ++ tailWord_421002) baseStart_421002 baseEnd_421002 := by
    simpa [prefixWord, tailWord_421002, baseEnd_421002] using wordTrace_append hprefix tailTrace_421002
  have hstable : (prefixWord ++ tailWord_421002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421002).length < 2 ^ (prefixWord ++ tailWord_421002).sum := by decide
  have hdescent : baseEnd_421002 < baseStart_421002 := by decide
  rcases family_descends (prefixWord ++ tailWord_421002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421026 : List Nat := [3, 3, 1, 3, 2, 1, 7]
def baseStart_421026 : Nat := 118140960795 + 421026 * 2 ^ 59
def prefixEnd_421026 : Nat := 4983230072969 + 3 ^ 40 * 421026 * 2
def baseEnd_421026 : Nat := 21351970966911107905061

theorem tailTrace_421026 : CollatzResearch.WordTrace tailWord_421026 prefixEnd_421026 21351970966911107905061 := by
  unfold tailWord_421026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3839019943175545590304733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10237386515134788240812621 3839019943175545590304733)
  ·
    refine ⟨1439632478690829596364275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3839019943175545590304733 1439632478690829596364275)
    ·
      refine ⟨2159448718036244394546413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1439632478690829596364275 2159448718036244394546413)
      ·
        refine ⟨809793269263591647954905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2159448718036244394546413 809793269263591647954905)
        ·
          refine ⟨607344951947693735966179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 809793269263591647954905 607344951947693735966179)
          ·
            refine ⟨911017427921540603949269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607344951947693735966179 911017427921540603949269)
            ·
              refine ⟨21351970966911107905061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 911017427921540603949269 21351970966911107905061)
              ·
                rfl

theorem cell20_421026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 7].length) (baseStart_421026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421026 prefixEnd_421026 := by exact prefixLift 421026
  have htrace : WordTrace (prefixWord ++ tailWord_421026) baseStart_421026 baseEnd_421026 := by
    simpa [prefixWord, tailWord_421026, baseEnd_421026] using wordTrace_append hprefix tailTrace_421026
  have hstable : (prefixWord ++ tailWord_421026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421026).length < 2 ^ (prefixWord ++ tailWord_421026).sum := by decide
  have hdescent : baseEnd_421026 < baseStart_421026 := by decide
  rcases family_descends (prefixWord ++ tailWord_421026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421057 : List Nat := [1, 2, 6, 1, 1, 1, 2, 2, 4]
def baseStart_421057 : Nat := 118140960795 + 421057 * 2 ^ 59
def prefixEnd_421057 : Nat := 4983230072969 + 3 ^ 40 * 421057 * 2
def baseEnd_421057 : Nat := 192181887946901641112089

theorem tailTrace_421057 : CollatzResearch.WordTrace tailWord_421057 prefixEnd_421057 192181887946901641112089 := by
  unfold tailWord_421057
  simp only [CollatzResearch.WordTrace]
  refine ⟨15357210435589874655597425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10238140290393249770398283 15357210435589874655597425)
  ·
    refine ⟨11517907826692405991698069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15357210435589874655597425 11517907826692405991698069)
    ·
      refine ⟨539901929376206530860847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11517907826692405991698069 539901929376206530860847)
      ·
        refine ⟨809852894064309796291271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539901929376206530860847 809852894064309796291271)
        ·
          refine ⟨1214779341096464694436907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 809852894064309796291271 1214779341096464694436907)
          ·
            refine ⟨1822169011644697041655361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214779341096464694436907 1822169011644697041655361)
            ·
              refine ⟨1366626758733522781241521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1822169011644697041655361 1366626758733522781241521)
              ·
                refine ⟨1024970069050142085931141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1366626758733522781241521 1024970069050142085931141)
                ·
                  refine ⟨192181887946901641112089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1024970069050142085931141 192181887946901641112089)
                  ·
                    rfl

theorem cell20_421057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_421057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421057 prefixEnd_421057 := by exact prefixLift 421057
  have htrace : WordTrace (prefixWord ++ tailWord_421057) baseStart_421057 baseEnd_421057 := by
    simpa [prefixWord, tailWord_421057, baseEnd_421057] using wordTrace_append hprefix tailTrace_421057
  have hstable : (prefixWord ++ tailWord_421057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421057).length < 2 ^ (prefixWord ++ tailWord_421057).sum := by decide
  have hdescent : baseEnd_421057 < baseStart_421057 := by decide
  rcases family_descends (prefixWord ++ tailWord_421057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421060 : List Nat := [2, 3, 3, 1, 4, 1, 2, 4]
def baseStart_421060 : Nat := 118140960795 + 421060 * 2 ^ 59
def prefixEnd_421060 : Nat := 4983230072969 + 3 ^ 40 * 421060 * 2
def baseEnd_421060 : Nat := 64061085742882321337359

theorem tailTrace_421060 : CollatzResearch.WordTrace tailWord_421060 prefixEnd_421060 64061085742882321337359 := by
  unfold tailWord_421060
  simp only [CollatzResearch.WordTrace]
  refine ⟨7678659927289503083978317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10238213236386004111971089 7678659927289503083978317)
  ·
    refine ⟨2879497472733563656491869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7678659927289503083978317 2879497472733563656491869)
    ·
      refine ⟨1079811552275086371184451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2879497472733563656491869 1079811552275086371184451)
      ·
        refine ⟨1619717328412629556776677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1079811552275086371184451 1619717328412629556776677)
        ·
          refine ⟨303696999077368041895627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1619717328412629556776677 303696999077368041895627)
          ·
            refine ⟨455545498616052062843441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303696999077368041895627 455545498616052062843441)
            ·
              refine ⟨341659123962039047132581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455545498616052062843441 341659123962039047132581)
              ·
                refine ⟨64061085742882321337359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 341659123962039047132581 64061085742882321337359)
                ·
                  rfl

theorem cell20_421060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 4].length) (baseStart_421060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421060 prefixEnd_421060 := by exact prefixLift 421060
  have htrace : WordTrace (prefixWord ++ tailWord_421060) baseStart_421060 baseEnd_421060 := by
    simpa [prefixWord, tailWord_421060, baseEnd_421060] using wordTrace_append hprefix tailTrace_421060
  have hstable : (prefixWord ++ tailWord_421060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421060).length < 2 ^ (prefixWord ++ tailWord_421060).sum := by decide
  have hdescent : baseEnd_421060 < baseStart_421060 := by decide
  rcases family_descends (prefixWord ++ tailWord_421060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421092 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 5]
def baseStart_421092 : Nat := 118140960795 + 421092 * 2 ^ 59
def prefixEnd_421092 : Nat := 4983230072969 + 3 ^ 40 * 421092 * 2
def baseEnd_421092 : Nat := 192197862900597074945279

theorem tailTrace_421092 : CollatzResearch.WordTrace tailWord_421092 prefixEnd_421092 192197862900597074945279 := by
  unfold tailWord_421092
  simp only [CollatzResearch.WordTrace]
  refine ⟨7679243495231537816560765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10238991326975383755414353 7679243495231537816560765)
  ·
    refine ⟨2879716310711826681210287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7679243495231537816560765 2879716310711826681210287)
    ·
      refine ⟨4319574466067740021815431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2879716310711826681210287 4319574466067740021815431)
      ·
        refine ⟨6479361699101610032723147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4319574466067740021815431 6479361699101610032723147)
        ·
          refine ⟨9719042548652415049084721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6479361699101610032723147 9719042548652415049084721)
          ·
            refine ⟨7289281911489311286813541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9719042548652415049084721 7289281911489311286813541)
            ·
              refine ⟨1366740358404245866277539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7289281911489311286813541 1366740358404245866277539)
              ·
                refine ⟨2050110537606368799416309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366740358404245866277539 2050110537606368799416309)
                ·
                  refine ⟨192197862900597074945279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2050110537606368799416309 192197862900597074945279)
                  ·
                    rfl

theorem cell20_421092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_421092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421092 prefixEnd_421092 := by exact prefixLift 421092
  have htrace : WordTrace (prefixWord ++ tailWord_421092) baseStart_421092 baseEnd_421092 := by
    simpa [prefixWord, tailWord_421092, baseEnd_421092] using wordTrace_append hprefix tailTrace_421092
  have hstable : (prefixWord ++ tailWord_421092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421092).length < 2 ^ (prefixWord ++ tailWord_421092).sum := by decide
  have hdescent : baseEnd_421092 < baseStart_421092 := by decide
  rcases family_descends (prefixWord ++ tailWord_421092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421144 : List Nat := [2, 1, 2, 3, 1, 11]
def baseStart_421144 : Nat := 118140960795 + 421144 * 2 ^ 59
def prefixEnd_421144 : Nat := 4983230072969 + 3 ^ 40 * 421144 * 2
def baseEnd_421144 : Nat := 7119318411759852044879

theorem tailTrace_421144 : CollatzResearch.WordTrace tailWord_421144 prefixEnd_421144 7119318411759852044879 := by
  unfold tailWord_421144
  simp only [CollatzResearch.WordTrace]
  refine ⟨7680191793137344257007243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10240255724183125676009657 7680191793137344257007243)
  ·
    refine ⟨11520287689706016385510865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7680191793137344257007243 11520287689706016385510865)
    ·
      refine ⟨8640215767279512289133149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11520287689706016385510865 8640215767279512289133149)
      ·
        refine ⟨3240080912729817108424931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8640215767279512289133149 3240080912729817108424931)
        ·
          refine ⟨4860121369094725662637397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3240080912729817108424931 4860121369094725662637397)
          ·
            refine ⟨7119318411759852044879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4860121369094725662637397 7119318411759852044879)
            ·
              rfl

theorem cell20_421144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 11].length) (baseStart_421144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421144 prefixEnd_421144 := by exact prefixLift 421144
  have htrace : WordTrace (prefixWord ++ tailWord_421144) baseStart_421144 baseEnd_421144 := by
    simpa [prefixWord, tailWord_421144, baseEnd_421144] using wordTrace_append hprefix tailTrace_421144
  have hstable : (prefixWord ++ tailWord_421144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421144).length < 2 ^ (prefixWord ++ tailWord_421144).sum := by decide
  have hdescent : baseEnd_421144 < baseStart_421144 := by decide
  rcases family_descends (prefixWord ++ tailWord_421144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421168 : List Nat := [2, 1, 1, 1, 2, 2, 3, 5, 3]
def baseStart_421168 : Nat := 118140960795 + 421168 * 2 ^ 59
def prefixEnd_421168 : Nat := 4983230072969 + 3 ^ 40 * 421168 * 2
def baseEnd_421168 : Nat := 192232551371478588411635

theorem tailTrace_421168 : CollatzResearch.WordTrace tailWord_421168 prefixEnd_421168 192232551371478588411635 := by
  unfold tailWord_421168
  simp only [CollatzResearch.WordTrace]
  refine ⟨7680629469093870306444079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10240839292125160408592105 7680629469093870306444079)
  ·
    refine ⟨11520944203640805459666119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7680629469093870306444079 11520944203640805459666119)
    ·
      refine ⟨17281416305461208189499179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11520944203640805459666119 17281416305461208189499179)
      ·
        refine ⟨25922124458191812284248769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17281416305461208189499179 25922124458191812284248769)
        ·
          refine ⟨19441593343643859213186577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25922124458191812284248769 19441593343643859213186577)
          ·
            refine ⟨14581195007732894409889933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19441593343643859213186577 14581195007732894409889933)
            ·
              refine ⟨5467948127899835403708725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14581195007732894409889933 5467948127899835403708725)
              ·
                refine ⟨512620136990609569097693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5467948127899835403708725 512620136990609569097693)
                ·
                  refine ⟨192232551371478588411635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 512620136990609569097693 192232551371478588411635)
                  ·
                    rfl

theorem cell20_421168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_421168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421168 prefixEnd_421168 := by exact prefixLift 421168
  have htrace : WordTrace (prefixWord ++ tailWord_421168) baseStart_421168 baseEnd_421168 := by
    simpa [prefixWord, tailWord_421168, baseEnd_421168] using wordTrace_append hprefix tailTrace_421168
  have hstable : (prefixWord ++ tailWord_421168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421168).length < 2 ^ (prefixWord ++ tailWord_421168).sum := by decide
  have hdescent : baseEnd_421168 < baseStart_421168 := by decide
  rcases family_descends (prefixWord ++ tailWord_421168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421174 : List Nat := [5, 1, 2, 3, 1, 1, 3, 4]
def baseStart_421174 : Nat := 118140960795 + 421174 * 2 ^ 59
def prefixEnd_421174 : Nat := 4983230072969 + 3 ^ 40 * 421174 * 2
def baseEnd_421174 : Nat := 64078429978323078070537

theorem tailTrace_421174 : CollatzResearch.WordTrace tailWord_421174 prefixEnd_421174 64078429978323078070537 := by
  unfold tailWord_421174
  simp only [CollatzResearch.WordTrace]
  refine ⟨960092361010375227350411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10240985184110669091737717 960092361010375227350411)
  ·
    refine ⟨1440138541515562841025617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 960092361010375227350411 1440138541515562841025617)
    ·
      refine ⟨1080103906136672130769213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1440138541515562841025617 1080103906136672130769213)
      ·
        refine ⟨405038964801252049038455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1080103906136672130769213 405038964801252049038455)
        ·
          refine ⟨607558447201878073557683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405038964801252049038455 607558447201878073557683)
          ·
            refine ⟨911337670802817110336525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607558447201878073557683 911337670802817110336525)
            ·
              refine ⟨341751626551056416376197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 911337670802817110336525 341751626551056416376197)
              ·
                refine ⟨64078429978323078070537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 341751626551056416376197 64078429978323078070537)
                ·
                  rfl

theorem cell20_421174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_421174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421174 prefixEnd_421174 := by exact prefixLift 421174
  have htrace : WordTrace (prefixWord ++ tailWord_421174) baseStart_421174 baseEnd_421174 := by
    simpa [prefixWord, tailWord_421174, baseEnd_421174] using wordTrace_append hprefix tailTrace_421174
  have hstable : (prefixWord ++ tailWord_421174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421174).length < 2 ^ (prefixWord ++ tailWord_421174).sum := by decide
  have hdescent : baseEnd_421174 < baseStart_421174 := by decide
  rcases family_descends (prefixWord ++ tailWord_421174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421188 : List Nat := [2, 3, 4, 1, 1, 1, 1, 5, 2]
def baseStart_421188 : Nat := 118140960795 + 421188 * 2 ^ 59
def prefixEnd_421188 : Nat := 4983230072969 + 3 ^ 40 * 421188 * 2
def baseEnd_421188 : Nat := 192241679916447407744887

theorem tailTrace_421188 : CollatzResearch.WordTrace tailWord_421188 prefixEnd_421188 192241679916447407744887 := by
  unfold tailWord_421188
  simp only [CollatzResearch.WordTrace]
  refine ⟨7680994199057642014308109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10241325598743522685744145 7680994199057642014308109)
  ·
    refine ⟨2880372824646615755365541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7680994199057642014308109 2880372824646615755365541)
    ·
      refine ⟨540069904621240454131039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2880372824646615755365541 540069904621240454131039)
      ·
        refine ⟨810104856931860681196559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540069904621240454131039 810104856931860681196559)
        ·
          refine ⟨1215157285397791021794839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810104856931860681196559 1215157285397791021794839)
          ·
            refine ⟨1822735928096686532692259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215157285397791021794839 1822735928096686532692259)
            ·
              refine ⟨2734103892145029799038389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1822735928096686532692259 2734103892145029799038389)
              ·
                refine ⟨256322239888596543659849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2734103892145029799038389 256322239888596543659849)
                ·
                  refine ⟨192241679916447407744887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256322239888596543659849 192241679916447407744887)
                  ·
                    rfl

theorem cell20_421188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_421188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421188 prefixEnd_421188 := by exact prefixLift 421188
  have htrace : WordTrace (prefixWord ++ tailWord_421188) baseStart_421188 baseEnd_421188 := by
    simpa [prefixWord, tailWord_421188, baseEnd_421188] using wordTrace_append hprefix tailTrace_421188
  have hstable : (prefixWord ++ tailWord_421188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421188).length < 2 ^ (prefixWord ++ tailWord_421188).sum := by decide
  have hdescent : baseEnd_421188 < baseStart_421188 := by decide
  rcases family_descends (prefixWord ++ tailWord_421188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421227 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 9]
def baseStart_421227 : Nat := 118140960795 + 421227 * 2 ^ 59
def prefixEnd_421227 : Nat := 4983230072969 + 3 ^ 40 * 421227 * 2
def baseEnd_421227 : Nat := 192259480579136605444727

theorem tailTrace_421227 : CollatzResearch.WordTrace tailWord_421227 prefixEnd_421227 192259480579136605444727 := by
  unfold tailWord_421227
  simp only [CollatzResearch.WordTrace]
  refine ⟨15363410844973993689285935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10242273896649329126190623 15363410844973993689285935)
  ·
    refine ⟨23045116267460990533928903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15363410844973993689285935 23045116267460990533928903)
    ·
      refine ⟨34567674401191485800893355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23045116267460990533928903 34567674401191485800893355)
      ·
        refine ⟨51851511601787228701340033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34567674401191485800893355 51851511601787228701340033)
        ·
          refine ⟨38888633701340421526005025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51851511601787228701340033 38888633701340421526005025)
          ·
            refine ⟨29166475276005316144503769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38888633701340421526005025 29166475276005316144503769)
            ·
              refine ⟨21874856457003987108377827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29166475276005316144503769 21874856457003987108377827)
              ·
                refine ⟨32812284685505980662566741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21874856457003987108377827 32812284685505980662566741)
                ·
                  refine ⟨192259480579136605444727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32812284685505980662566741 192259480579136605444727)
                  ·
                    rfl

theorem cell20_421227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_421227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421227 prefixEnd_421227 := by exact prefixLift 421227
  have htrace : WordTrace (prefixWord ++ tailWord_421227) baseStart_421227 baseEnd_421227 := by
    simpa [prefixWord, tailWord_421227, baseEnd_421227] using wordTrace_append hprefix tailTrace_421227
  have hstable : (prefixWord ++ tailWord_421227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421227).length < 2 ^ (prefixWord ++ tailWord_421227).sum := by decide
  have hdescent : baseEnd_421227 < baseStart_421227 := by decide
  rcases family_descends (prefixWord ++ tailWord_421227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421313 : List Nat := [1, 2, 7, 10]
def baseStart_421313 : Nat := 118140960795 + 421313 * 2 ^ 59
def prefixEnd_421313 : Nat := 4983230072969 + 3 ^ 40 * 421313 * 2
def baseEnd_421313 : Nat := 791352812026759376863

theorem tailTrace_421313 : CollatzResearch.WordTrace tailWord_421313 prefixEnd_421313 791352812026759376863 := by
  unfold tailWord_421313
  simp only [CollatzResearch.WordTrace]
  refine ⟨15366547522662430376916593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10244365015108286917944395 15366547522662430376916593)
  ·
    refine ⟨11524910641996822782687445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15366547522662430376916593 11524910641996822782687445)
    ·
      refine ⟨270115093171800533969237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 11524910641996822782687445 270115093171800533969237)
      ·
        refine ⟨791352812026759376863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 270115093171800533969237 791352812026759376863)
        ·
          rfl

theorem cell20_421313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 10].length) (baseStart_421313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421313 prefixEnd_421313 := by exact prefixLift 421313
  have htrace : WordTrace (prefixWord ++ tailWord_421313) baseStart_421313 baseEnd_421313 := by
    simpa [prefixWord, tailWord_421313, baseEnd_421313] using wordTrace_append hprefix tailTrace_421313
  have hstable : (prefixWord ++ tailWord_421313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421313).length < 2 ^ (prefixWord ++ tailWord_421313).sum := by decide
  have hdescent : baseEnd_421313 < baseStart_421313 := by decide
  rcases family_descends (prefixWord ++ tailWord_421313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421316 : List Nat := [2, 3, 3, 2, 1, 2, 2, 2, 3]
def baseStart_421316 : Nat := 118140960795 + 421316 * 2 ^ 59
def prefixEnd_421316 : Nat := 4983230072969 + 3 ^ 40 * 421316 * 2
def baseEnd_421316 : Nat := 192300102604247851477697

theorem tailTrace_421316 : CollatzResearch.WordTrace tailWord_421316 prefixEnd_421316 192300102604247851477697 := by
  unfold tailWord_421316
  simp only [CollatzResearch.WordTrace]
  refine ⟨7683328470825780944637901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10244437961101041259517201 7683328470825780944637901)
  ·
    refine ⟨2881248176559667854239213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7683328470825780944637901 2881248176559667854239213)
    ·
      refine ⟨1080468066209875445339705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2881248176559667854239213 1080468066209875445339705)
      ·
        refine ⟨810351049657406584004779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1080468066209875445339705 810351049657406584004779)
        ·
          refine ⟨1215526574486109876007169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810351049657406584004779 1215526574486109876007169)
          ·
            refine ⟨911644930864582407005377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1215526574486109876007169 911644930864582407005377)
            ·
              refine ⟨683733698148436805254033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 911644930864582407005377 683733698148436805254033)
              ·
                refine ⟨512800273611327603940525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 683733698148436805254033 512800273611327603940525)
                ·
                  refine ⟨192300102604247851477697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 512800273611327603940525 192300102604247851477697)
                  ·
                    rfl

theorem cell20_421316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_421316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421316 prefixEnd_421316 := by exact prefixLift 421316
  have htrace : WordTrace (prefixWord ++ tailWord_421316) baseStart_421316 baseEnd_421316 := by
    simpa [prefixWord, tailWord_421316, baseEnd_421316] using wordTrace_append hprefix tailTrace_421316
  have hstable : (prefixWord ++ tailWord_421316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421316).length < 2 ^ (prefixWord ++ tailWord_421316).sum := by decide
  have hdescent : baseEnd_421316 < baseStart_421316 := by decide
  rcases family_descends (prefixWord ++ tailWord_421316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421323 : List Nat := [1, 1, 1, 1, 3, 3, 6, 2, 2]
def baseStart_421323 : Nat := 118140960795 + 421323 * 2 ^ 59
def prefixEnd_421323 : Nat := 4983230072969 + 3 ^ 40 * 421323 * 2
def baseEnd_421323 : Nat := 192303297594986938244335

theorem tailTrace_421323 : CollatzResearch.WordTrace tailWord_421323 prefixEnd_421323 192303297594986938244335 := by
  unfold tailWord_421323
  simp only [CollatzResearch.WordTrace]
  refine ⟨15366912252626202084780623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10244608168417468056520415 15366912252626202084780623)
  ·
    refine ⟨23050368378939303127170935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15366912252626202084780623 23050368378939303127170935)
    ·
      refine ⟨34575552568408954690756403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23050368378939303127170935 34575552568408954690756403)
      ·
        refine ⟨51863328852613432036134605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34575552568408954690756403 51863328852613432036134605)
        ·
          refine ⟨19448748319730037013550477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51863328852613432036134605 19448748319730037013550477)
          ·
            refine ⟨7293280619898763880081429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19448748319730037013550477 7293280619898763880081429)
            ·
              refine ⟨341872529057754556878817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7293280619898763880081429 341872529057754556878817)
              ·
                refine ⟨256404396793315917659113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 341872529057754556878817 256404396793315917659113)
                ·
                  refine ⟨192303297594986938244335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256404396793315917659113 192303297594986938244335)
                  ·
                    rfl

theorem cell20_421323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 2].length) (baseStart_421323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421323 prefixEnd_421323 := by exact prefixLift 421323
  have htrace : WordTrace (prefixWord ++ tailWord_421323) baseStart_421323 baseEnd_421323 := by
    simpa [prefixWord, tailWord_421323, baseEnd_421323] using wordTrace_append hprefix tailTrace_421323
  have hstable : (prefixWord ++ tailWord_421323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421323).length < 2 ^ (prefixWord ++ tailWord_421323).sum := by decide
  have hdescent : baseEnd_421323 < baseStart_421323 := by decide
  rcases family_descends (prefixWord ++ tailWord_421323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421358 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_421358 : Nat := 118140960795 + 421358 * 2 ^ 59
def prefixEnd_421358 : Nat := 4983230072969 + 3 ^ 40 * 421358 * 2
def baseEnd_421358 : Nat := 192319272548682372077525

theorem tailTrace_421358 : CollatzResearch.WordTrace tailWord_421358 prefixEnd_421358 192319272548682372077525 := by
  unfold tailWord_421358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1921023600937425382788091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10245459204999602041536485 1921023600937425382788091)
  ·
    refine ⟨2881535401406138074182137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1921023600937425382788091 2881535401406138074182137)
    ·
      refine ⟨2161151551054603555636603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2881535401406138074182137 2161151551054603555636603)
      ·
        refine ⟨3241727326581905333454905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2161151551054603555636603 3241727326581905333454905)
        ·
          refine ⟨2431295494936429000091179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3241727326581905333454905 2431295494936429000091179)
          ·
            refine ⟨3646943242404643500136769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2431295494936429000091179 3646943242404643500136769)
            ·
              refine ⟨2735207431803482625102577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3646943242404643500136769 2735207431803482625102577)
              ·
                refine ⟨2051405573852611968826933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2735207431803482625102577 2051405573852611968826933)
                ·
                  refine ⟨192319272548682372077525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2051405573852611968826933 192319272548682372077525)
                  ·
                    rfl

theorem cell20_421358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_421358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421358 prefixEnd_421358 := by exact prefixLift 421358
  have htrace : WordTrace (prefixWord ++ tailWord_421358) baseStart_421358 baseEnd_421358 := by
    simpa [prefixWord, tailWord_421358, baseEnd_421358] using wordTrace_append hprefix tailTrace_421358
  have hstable : (prefixWord ++ tailWord_421358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421358).length < 2 ^ (prefixWord ++ tailWord_421358).sum := by decide
  have hdescent : baseEnd_421358 < baseStart_421358 := by decide
  rcases family_descends (prefixWord ++ tailWord_421358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421361 : List Nat := [1, 2, 2, 2, 3, 3, 2, 3, 2]
def baseStart_421361 : Nat := 118140960795 + 421361 * 2 ^ 59
def prefixEnd_421361 : Nat := 4983230072969 + 3 ^ 40 * 421361 * 2
def baseEnd_421361 : Nat := 192320641830427694977513

theorem tailTrace_421361 : CollatzResearch.WordTrace tailWord_421361 prefixEnd_421361 192320641830427694977513 := by
  unfold tailWord_421361
  simp only [CollatzResearch.WordTrace]
  refine ⟨15368298226488534574663937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10245532150992356383109291 15368298226488534574663937)
  ·
    refine ⟨11526223669866400930997953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15368298226488534574663937 11526223669866400930997953)
    ·
      refine ⟨8644667752399800698248465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11526223669866400930997953 8644667752399800698248465)
      ·
        refine ⟨6483500814299850523686349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8644667752399800698248465 6483500814299850523686349)
        ·
          refine ⟨2431312805362443946382381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6483500814299850523686349 2431312805362443946382381)
          ·
            refine ⟨911742302010916479893393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2431312805362443946382381 911742302010916479893393)
            ·
              refine ⟨683806726508187359920045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 911742302010916479893393 683806726508187359920045)
              ·
                refine ⟨256427522440570259970017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 683806726508187359920045 256427522440570259970017)
                ·
                  refine ⟨192320641830427694977513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256427522440570259970017 192320641830427694977513)
                  ·
                    rfl

theorem cell20_421361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 2].length) (baseStart_421361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421361 prefixEnd_421361 := by exact prefixLift 421361
  have htrace : WordTrace (prefixWord ++ tailWord_421361) baseStart_421361 baseEnd_421361 := by
    simpa [prefixWord, tailWord_421361, baseEnd_421361] using wordTrace_append hprefix tailTrace_421361
  have hstable : (prefixWord ++ tailWord_421361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421361).length < 2 ^ (prefixWord ++ tailWord_421361).sum := by decide
  have hdescent : baseEnd_421361 < baseStart_421361 := by decide
  rcases family_descends (prefixWord ++ tailWord_421361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421378 : List Nat := [3, 4, 1, 2, 1, 1, 2, 4, 2]
def baseStart_421378 : Nat := 118140960795 + 421378 * 2 ^ 59
def prefixEnd_421378 : Nat := 4983230072969 + 3 ^ 40 * 421378 * 2
def baseEnd_421378 : Nat := 192328401093651191410777

theorem tailTrace_421378 : CollatzResearch.WordTrace tailWord_421378 prefixEnd_421378 192328401093651191410777 := by
  unfold tailWord_421378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3842229566856736619508197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10245945511617964318688525 3842229566856736619508197)
  ·
    refine ⟨720418043785638116157787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3842229566856736619508197 720418043785638116157787)
    ·
      refine ⟨1080627065678457174236681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 720418043785638116157787 1080627065678457174236681)
      ·
        refine ⟨810470299258842880677511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1080627065678457174236681 810470299258842880677511)
        ·
          refine ⟨1215705448888264321016267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810470299258842880677511 1215705448888264321016267)
          ·
            refine ⟨1823558173332396481524401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215705448888264321016267 1823558173332396481524401)
            ·
              refine ⟨1367668629999297361143301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1823558173332396481524401 1367668629999297361143301)
              ·
                refine ⟨256437868124868255214369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1367668629999297361143301 256437868124868255214369)
                ·
                  refine ⟨192328401093651191410777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256437868124868255214369 192328401093651191410777)
                  ·
                    rfl

theorem cell20_421378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_421378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421378 prefixEnd_421378 := by exact prefixLift 421378
  have htrace : WordTrace (prefixWord ++ tailWord_421378) baseStart_421378 baseEnd_421378 := by
    simpa [prefixWord, tailWord_421378, baseEnd_421378] using wordTrace_append hprefix tailTrace_421378
  have hstable : (prefixWord ++ tailWord_421378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421378).length < 2 ^ (prefixWord ++ tailWord_421378).sum := by decide
  have hdescent : baseEnd_421378 < baseStart_421378 := by decide
  rcases family_descends (prefixWord ++ tailWord_421378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421434 : List Nat := [3, 1, 1, 1, 3, 2, 2, 4, 3]
def baseStart_421434 : Nat := 118140960795 + 421434 * 2 ^ 59
def prefixEnd_421434 : Nat := 4983230072969 + 3 ^ 40 * 421434 * 2
def baseEnd_421434 : Nat := 192353961019563885543881

theorem tailTrace_421434 : CollatzResearch.WordTrace tailWord_421434 prefixEnd_421434 192353961019563885543881 := by
  unfold tailWord_421434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3842740188806017010517839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10247307170149378694714237 3842740188806017010517839)
  ·
    refine ⟨5764110283209025515776759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3842740188806017010517839 5764110283209025515776759)
    ·
      refine ⟨8646165424813538273665139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5764110283209025515776759 8646165424813538273665139)
      ·
        refine ⟨12969248137220307410497709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8646165424813538273665139 12969248137220307410497709)
        ·
          refine ⟨4863468051457615278936641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12969248137220307410497709 4863468051457615278936641)
          ·
            refine ⟨3647601038593211459202481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4863468051457615278936641 3647601038593211459202481)
            ·
              refine ⟨2735700778944908594401861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3647601038593211459202481 2735700778944908594401861)
              ·
                refine ⟨512943896052170361450349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2735700778944908594401861 512943896052170361450349)
                ·
                  refine ⟨192353961019563885543881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 512943896052170361450349 192353961019563885543881)
                  ·
                    rfl

theorem cell20_421434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_421434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421434 prefixEnd_421434 := by exact prefixLift 421434
  have htrace : WordTrace (prefixWord ++ tailWord_421434) baseStart_421434 baseEnd_421434 := by
    simpa [prefixWord, tailWord_421434, baseEnd_421434] using wordTrace_append hprefix tailTrace_421434
  have hstable : (prefixWord ++ tailWord_421434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421434).length < 2 ^ (prefixWord ++ tailWord_421434).sum := by decide
  have hdescent : baseEnd_421434 < baseStart_421434 := by decide
  rcases family_descends (prefixWord ++ tailWord_421434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421437 : List Nat := [1, 4, 1, 3, 3, 2, 1, 1, 4]
def baseStart_421437 : Nat := 118140960795 + 421437 * 2 ^ 59
def prefixEnd_421437 : Nat := 4983230072969 + 3 ^ 40 * 421437 * 2
def baseEnd_421437 : Nat := 192355330301309208443869

theorem tailTrace_421437 : CollatzResearch.WordTrace tailWord_421437 prefixEnd_421437 192355330301309208443869 := by
  unfold tailWord_421437
  simp only [CollatzResearch.WordTrace]
  refine ⟨15371070174213199554430565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10247380116142133036287043 15371070174213199554430565)
  ·
    refine ⟨2882075657664974916455731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15371070174213199554430565 2882075657664974916455731)
    ·
      refine ⟨4323113486497462374683597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2882075657664974916455731 4323113486497462374683597)
      ·
        refine ⟨1621167557436548390506349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4323113486497462374683597 1621167557436548390506349)
        ·
          refine ⟨607937834038705646439881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1621167557436548390506349 607937834038705646439881)
          ·
            refine ⟨455953375529029234829911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 607937834038705646439881 455953375529029234829911)
            ·
              refine ⟨683930063293543852244867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455953375529029234829911 683930063293543852244867)
              ·
                refine ⟨1025895094940315778367301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683930063293543852244867 1025895094940315778367301)
                ·
                  refine ⟨192355330301309208443869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1025895094940315778367301 192355330301309208443869)
                  ·
                    rfl

theorem cell20_421437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_421437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421437 prefixEnd_421437 := by exact prefixLift 421437
  have htrace : WordTrace (prefixWord ++ tailWord_421437) baseStart_421437 baseEnd_421437 := by
    simpa [prefixWord, tailWord_421437, baseEnd_421437] using wordTrace_append hprefix tailTrace_421437
  have hstable : (prefixWord ++ tailWord_421437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421437).length < 2 ^ (prefixWord ++ tailWord_421437).sum := by decide
  have hdescent : baseEnd_421437 < baseStart_421437 := by decide
  rcases family_descends (prefixWord ++ tailWord_421437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421447 : List Nat := [1, 1, 4, 1, 6, 1, 2, 1, 3]
def baseStart_421447 : Nat := 118140960795 + 421447 * 2 ^ 59
def prefixEnd_421447 : Nat := 4983230072969 + 3 ^ 40 * 421447 * 2
def baseEnd_421447 : Nat := 192359894573793618110495

theorem tailTrace_421447 : CollatzResearch.WordTrace tailWord_421447 prefixEnd_421447 192359894573793618110495 := by
  unfold tailWord_421447
  simp only [CollatzResearch.WordTrace]
  refine ⟨15371434904176971262294595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10247623269451314174863063 15371434904176971262294595)
  ·
    refine ⟨23057152356265456893441893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15371434904176971262294595 23057152356265456893441893)
    ·
      refine ⟨4323216066799773167520355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23057152356265456893441893 4323216066799773167520355)
      ·
        refine ⟨6484824100199659751280533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4323216066799773167520355 6484824100199659751280533)
        ·
          refine ⟨303976129696859050841275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6484824100199659751280533 303976129696859050841275)
          ·
            refine ⟨455964194545288576261913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303976129696859050841275 455964194545288576261913)
            ·
              refine ⟨341973145908966432196435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455964194545288576261913 341973145908966432196435)
              ·
                refine ⟨512959718863449648294653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341973145908966432196435 512959718863449648294653)
                ·
                  refine ⟨192359894573793618110495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 512959718863449648294653 192359894573793618110495)
                  ·
                    rfl

theorem cell20_421447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 3].length) (baseStart_421447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421447 prefixEnd_421447 := by exact prefixLift 421447
  have htrace : WordTrace (prefixWord ++ tailWord_421447) baseStart_421447 baseEnd_421447 := by
    simpa [prefixWord, tailWord_421447, baseEnd_421447] using wordTrace_append hprefix tailTrace_421447
  have hstable : (prefixWord ++ tailWord_421447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421447).length < 2 ^ (prefixWord ++ tailWord_421447).sum := by decide
  have hdescent : baseEnd_421447 < baseStart_421447 := by decide
  rcases family_descends (prefixWord ++ tailWord_421447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421486 : List Nat := [4, 1, 2, 2, 11]
def baseStart_421486 : Nat := 118140960795 + 421486 * 2 ^ 59
def prefixEnd_421486 : Nat := 4983230072969 + 3 ^ 40 * 421486 * 2
def baseEnd_421486 : Nat := 2375033274524479207535

theorem tailTrace_421486 : CollatzResearch.WordTrace tailWord_421486 prefixEnd_421486 2375033274524479207535 := by
  unfold tailWord_421486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1921607168879460115370539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10248571567357120615309541 1921607168879460115370539)
  ·
    refine ⟨2882410753319190173055809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1921607168879460115370539 2882410753319190173055809)
    ·
      refine ⟨2161808064989392629791857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2882410753319190173055809 2161808064989392629791857)
      ·
        refine ⟨1621356048742044472343893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2161808064989392629791857 1621356048742044472343893)
        ·
          refine ⟨2375033274524479207535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1621356048742044472343893 2375033274524479207535)
          ·
            rfl

theorem cell20_421486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 11].length) (baseStart_421486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421486 prefixEnd_421486 := by exact prefixLift 421486
  have htrace : WordTrace (prefixWord ++ tailWord_421486) baseStart_421486 baseEnd_421486 := by
    simpa [prefixWord, tailWord_421486, baseEnd_421486] using wordTrace_append hprefix tailTrace_421486
  have hstable : (prefixWord ++ tailWord_421486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421486).length < 2 ^ (prefixWord ++ tailWord_421486).sum := by decide
  have hdescent : baseEnd_421486 < baseStart_421486 := by decide
  rcases family_descends (prefixWord ++ tailWord_421486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421555 : List Nat := [1, 1, 1, 2, 3, 3, 4, 1, 4]
def baseStart_421555 : Nat := 118140960795 + 421555 * 2 ^ 59
def prefixEnd_421555 : Nat := 4983230072969 + 3 ^ 40 * 421555 * 2
def baseEnd_421555 : Nat := 192409188716625242510053

theorem tailTrace_421555 : CollatzResearch.WordTrace tailWord_421555 prefixEnd_421555 192409188716625242510053 := by
  unfold tailWord_421555
  simp only [CollatzResearch.WordTrace]
  refine ⟨15375373987785705707226119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10250249325190470471484079 15375373987785705707226119)
  ·
    refine ⟨23063060981678558560839179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15375373987785705707226119 23063060981678558560839179)
    ·
      refine ⟨34594591472517837841258769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23063060981678558560839179 34594591472517837841258769)
      ·
        refine ⟨25945943604388378380944077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34594591472517837841258769 25945943604388378380944077)
        ·
          refine ⟨9729728851645641892854029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25945943604388378380944077 9729728851645641892854029)
          ·
            refine ⟨3648648319367115709820261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9729728851645641892854029 3648648319367115709820261)
            ·
              refine ⟨684121559881334195591299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3648648319367115709820261 684121559881334195591299)
              ·
                refine ⟨1026182339822001293386949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684121559881334195591299 1026182339822001293386949)
                ·
                  refine ⟨192409188716625242510053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1026182339822001293386949 192409188716625242510053)
                  ·
                    rfl

theorem cell20_421555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 4].length) (baseStart_421555 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421555 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421555 prefixEnd_421555 := by exact prefixLift 421555
  have htrace : WordTrace (prefixWord ++ tailWord_421555) baseStart_421555 baseEnd_421555 := by
    simpa [prefixWord, tailWord_421555, baseEnd_421555] using wordTrace_append hprefix tailTrace_421555
  have hstable : (prefixWord ++ tailWord_421555).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421555).length < 2 ^ (prefixWord ++ tailWord_421555).sum := by decide
  have hdescent : baseEnd_421555 < baseStart_421555 := by decide
  rcases family_descends (prefixWord ++ tailWord_421555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421565 : List Nat := [1, 4, 1, 2, 1, 2, 5, 1, 3]
def baseStart_421565 : Nat := 118140960795 + 421565 * 2 ^ 59
def prefixEnd_421565 : Nat := 4983230072969 + 3 ^ 40 * 421565 * 2
def baseEnd_421565 : Nat := 192413752989109652176679

theorem tailTrace_421565 : CollatzResearch.WordTrace tailWord_421565 prefixEnd_421565 192413752989109652176679 := by
  unfold tailWord_421565
  simp only [CollatzResearch.WordTrace]
  refine ⟨15375738717749477415090149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10250492478499651610060099 15375738717749477415090149)
  ·
    refine ⟨2882951009578027015329403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15375738717749477415090149 2882951009578027015329403)
    ·
      refine ⟨4324426514367040522994105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2882951009578027015329403 4324426514367040522994105)
      ·
        refine ⟨3243319885775280392245579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4324426514367040522994105 3243319885775280392245579)
        ·
          refine ⟨4864979828662920588368369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3243319885775280392245579 4864979828662920588368369)
          ·
            refine ⟨3648734871497190441276277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4864979828662920588368369 3648734871497190441276277)
            ·
              refine ⟨342068894202861603869651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3648734871497190441276277 342068894202861603869651)
              ·
                refine ⟨513103341304292405804477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342068894202861603869651 513103341304292405804477)
                ·
                  refine ⟨192413752989109652176679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 513103341304292405804477 192413752989109652176679)
                  ·
                    rfl

theorem cell20_421565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_421565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421565 prefixEnd_421565 := by exact prefixLift 421565
  have htrace : WordTrace (prefixWord ++ tailWord_421565) baseStart_421565 baseEnd_421565 := by
    simpa [prefixWord, tailWord_421565, baseEnd_421565] using wordTrace_append hprefix tailTrace_421565
  have hstable : (prefixWord ++ tailWord_421565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421565).length < 2 ^ (prefixWord ++ tailWord_421565).sum := by decide
  have hdescent : baseEnd_421565 < baseStart_421565 := by decide
  rcases family_descends (prefixWord ++ tailWord_421565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421586 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_421586 : Nat := 118140960795 + 421586 * 2 ^ 59
def prefixEnd_421586 : Nat := 4983230072969 + 3 ^ 40 * 421586 * 2
def baseEnd_421586 : Nat := 192423337961326912476593

theorem tailTrace_421586 : CollatzResearch.WordTrace tailWord_421586 prefixEnd_421586 192423337961326912476593 := by
  unfold tailWord_421586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3844126162668349500401153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10251003100448932001069741 3844126162668349500401153)
  ·
    refine ⟨2883094622001262125300865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3844126162668349500401153 2883094622001262125300865)
    ·
      refine ⟨2162320966500946593975649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2883094622001262125300865 2162320966500946593975649)
      ·
        refine ⟨1621740724875709945481737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2162320966500946593975649 1621740724875709945481737)
        ·
          refine ⟨1216305543656782459111303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1621740724875709945481737 1216305543656782459111303)
          ·
            refine ⟨1824458315485173688666955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216305543656782459111303 1824458315485173688666955)
            ·
              refine ⟨2736687473227760533000433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1824458315485173688666955 2736687473227760533000433)
              ·
                refine ⟨2052515604920820399750325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2736687473227760533000433 2052515604920820399750325)
                ·
                  refine ⟨192423337961326912476593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2052515604920820399750325 192423337961326912476593)
                  ·
                    rfl

theorem cell20_421586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_421586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421586 prefixEnd_421586 := by exact prefixLift 421586
  have htrace : WordTrace (prefixWord ++ tailWord_421586) baseStart_421586 baseEnd_421586 := by
    simpa [prefixWord, tailWord_421586, baseEnd_421586] using wordTrace_append hprefix tailTrace_421586
  have hstable : (prefixWord ++ tailWord_421586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421586).length < 2 ^ (prefixWord ++ tailWord_421586).sum := by decide
  have hdescent : baseEnd_421586 < baseStart_421586 := by decide
  rcases family_descends (prefixWord ++ tailWord_421586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421596 : List Nat := [2, 2, 5, 1, 2, 2, 6]
def baseStart_421596 : Nat := 118140960795 + 421596 * 2 ^ 59
def prefixEnd_421596 : Nat := 4983230072969 + 3 ^ 40 * 421596 * 2
def baseEnd_421596 : Nat := 21380878025979035793691

theorem tailTrace_421596 : CollatzResearch.WordTrace tailWord_421596 prefixEnd_421596 21380878025979035793691 := by
  unfold tailWord_421596
  simp only [CollatzResearch.WordTrace]
  refine ⟨7688434690318584854734321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10251246253758113139645761 7688434690318584854734321)
  ·
    refine ⟨5766326017738938641050741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7688434690318584854734321 5766326017738938641050741)
    ·
      refine ⟨540593064163025497598507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5766326017738938641050741 540593064163025497598507)
      ·
        refine ⟨810889596244538246397761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540593064163025497598507 810889596244538246397761)
        ·
          refine ⟨608167197183403684798321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 810889596244538246397761 608167197183403684798321)
          ·
            refine ⟨456125397887552763598741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 608167197183403684798321 456125397887552763598741)
            ·
              refine ⟨21380878025979035793691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 456125397887552763598741 21380878025979035793691)
              ·
                rfl

theorem cell20_421596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 6].length) (baseStart_421596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421596 prefixEnd_421596 := by exact prefixLift 421596
  have htrace : WordTrace (prefixWord ++ tailWord_421596) baseStart_421596 baseEnd_421596 := by
    simpa [prefixWord, tailWord_421596, baseEnd_421596] using wordTrace_append hprefix tailTrace_421596
  have hstable : (prefixWord ++ tailWord_421596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421596).length < 2 ^ (prefixWord ++ tailWord_421596).sum := by decide
  have hdescent : baseEnd_421596 < baseStart_421596 := by decide
  rcases family_descends (prefixWord ++ tailWord_421596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421610 : List Nat := [3, 1, 3, 1, 1, 1, 2, 6, 2]
def baseStart_421610 : Nat := 118140960795 + 421610 * 2 ^ 59
def prefixEnd_421610 : Nat := 4983230072969 + 3 ^ 40 * 421610 * 2
def baseEnd_421610 : Nat := 192434292215289495676495

theorem tailTrace_421610 : CollatzResearch.WordTrace tailWord_421610 prefixEnd_421610 192434292215289495676495 := by
  unfold tailWord_421610
  simp only [CollatzResearch.WordTrace]
  refine ⟨3844345000646612525119571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10251586668390966733652189 3844345000646612525119571)
  ·
    refine ⟨5766517500969918787679357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3844345000646612525119571 5766517500969918787679357)
    ·
      refine ⟨2162444062863719545379759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5766517500969918787679357 2162444062863719545379759)
      ·
        refine ⟨3243666094295579318069639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2162444062863719545379759 3243666094295579318069639)
        ·
          refine ⟨4865499141443368977104459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3243666094295579318069639 4865499141443368977104459)
          ·
            refine ⟨7298248712165053465656689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4865499141443368977104459 7298248712165053465656689)
            ·
              refine ⟨5473686534123790099242517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7298248712165053465656689 5473686534123790099242517)
              ·
                refine ⟨256579056287052660901993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5473686534123790099242517 256579056287052660901993)
                ·
                  refine ⟨192434292215289495676495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256579056287052660901993 192434292215289495676495)
                  ·
                    rfl

theorem cell20_421610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_421610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421610 prefixEnd_421610 := by exact prefixLift 421610
  have htrace : WordTrace (prefixWord ++ tailWord_421610) baseStart_421610 baseEnd_421610 := by
    simpa [prefixWord, tailWord_421610, baseEnd_421610] using wordTrace_append hprefix tailTrace_421610
  have hstable : (prefixWord ++ tailWord_421610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421610).length < 2 ^ (prefixWord ++ tailWord_421610).sum := by decide
  have hdescent : baseEnd_421610 < baseStart_421610 := by decide
  rcases family_descends (prefixWord ++ tailWord_421610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421665 : List Nat := [1, 2, 3, 2, 1, 3, 4, 2, 2]
def baseStart_421665 : Nat := 118140960795 + 421665 * 2 ^ 59
def prefixEnd_421665 : Nat := 4983230072969 + 3 ^ 40 * 421665 * 2
def baseEnd_421665 : Nat := 192459395713953748842937

theorem tailTrace_421665 : CollatzResearch.WordTrace tailWord_421665 prefixEnd_421665 192459395713953748842937 := by
  unfold tailWord_421665
  simp only [CollatzResearch.WordTrace]
  refine ⟨15379386017387194493730449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10252924011591462995820299 15379386017387194493730449)
  ·
    refine ⟨11534539513040395870297837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15379386017387194493730449 11534539513040395870297837)
    ·
      refine ⟨4325452317390148451361689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11534539513040395870297837 4325452317390148451361689)
      ·
        refine ⟨3244089238042611338521267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4325452317390148451361689 3244089238042611338521267)
        ·
          refine ⟨4866133857063917007781901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3244089238042611338521267 4866133857063917007781901)
          ·
            refine ⟨1824800196398968877918213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4866133857063917007781901 1824800196398968877918213)
            ·
              refine ⟨342150036824806664609665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1824800196398968877918213 342150036824806664609665)
              ·
                refine ⟨256612527618604998457249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342150036824806664609665 256612527618604998457249)
                ·
                  refine ⟨192459395713953748842937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256612527618604998457249 192459395713953748842937)
                  ·
                    rfl

theorem cell20_421665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 2].length) (baseStart_421665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421665 prefixEnd_421665 := by exact prefixLift 421665
  have htrace : WordTrace (prefixWord ++ tailWord_421665) baseStart_421665 baseEnd_421665 := by
    simpa [prefixWord, tailWord_421665, baseEnd_421665] using wordTrace_append hprefix tailTrace_421665
  have hstable : (prefixWord ++ tailWord_421665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421665).length < 2 ^ (prefixWord ++ tailWord_421665).sum := by decide
  have hdescent : baseEnd_421665 < baseStart_421665 := by decide
  rcases family_descends (prefixWord ++ tailWord_421665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421676 : List Nat := [2, 2, 1, 1, 1, 5, 3, 5]
def baseStart_421676 : Nat := 118140960795 + 421676 * 2 ^ 59
def prefixEnd_421676 : Nat := 4983230072969 + 3 ^ 40 * 421676 * 2
def baseEnd_421676 : Nat := 64154805471228866492075

theorem tailTrace_421676 : CollatzResearch.WordTrace tailWord_421676 prefixEnd_421676 64154805471228866492075 := by
  unfold tailWord_421676
  simp only [CollatzResearch.WordTrace]
  refine ⟨7689893610173671686190441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10253191480231562248253921 7689893610173671686190441)
  ·
    refine ⟨5767420207630253764642831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7689893610173671686190441 5767420207630253764642831)
    ·
      refine ⟨8651130311445380646964247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5767420207630253764642831 8651130311445380646964247)
      ·
        refine ⟨12976695467168070970446371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8651130311445380646964247 12976695467168070970446371)
        ·
          refine ⟨19465043200752106455669557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12976695467168070970446371 19465043200752106455669557)
          ·
            refine ⟨1824847800070509980219021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19465043200752106455669557 1824847800070509980219021)
            ·
              refine ⟨684317925026441242582133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1824847800070509980219021 684317925026441242582133)
              ·
                refine ⟨64154805471228866492075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 684317925026441242582133 64154805471228866492075)
                ·
                  rfl

theorem cell20_421676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_421676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421676 prefixEnd_421676 := by exact prefixLift 421676
  have htrace : WordTrace (prefixWord ++ tailWord_421676) baseStart_421676 baseEnd_421676 := by
    simpa [prefixWord, tailWord_421676, baseEnd_421676] using wordTrace_append hprefix tailTrace_421676
  have hstable : (prefixWord ++ tailWord_421676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421676).length < 2 ^ (prefixWord ++ tailWord_421676).sum := by decide
  have hdescent : baseEnd_421676 < baseStart_421676 := by decide
  rcases family_descends (prefixWord ++ tailWord_421676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421686 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_421686 : Nat := 118140960795 + 421686 * 2 ^ 59
def prefixEnd_421686 : Nat := 4983230072969 + 3 ^ 40 * 421686 * 2
def baseEnd_421686 : Nat := 192468980686171009142851

theorem tailTrace_421686 : CollatzResearch.WordTrace tailWord_421686 prefixEnd_421686 192468980686171009142851 := by
  unfold tailWord_421686
  simp only [CollatzResearch.WordTrace]
  refine ⟨961259496894444692515307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10253434633540743386829941 961259496894444692515307)
  ·
    refine ⟨1441889245341667038772961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 961259496894444692515307 1441889245341667038772961)
    ·
      refine ⟨1081416934006250279079721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1441889245341667038772961 1081416934006250279079721)
      ·
        refine ⟨811062700504687709309791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1081416934006250279079721 811062700504687709309791)
        ·
          refine ⟨1216594050757031563964687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811062700504687709309791 1216594050757031563964687)
          ·
            refine ⟨1824891076135547345947031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216594050757031563964687 1824891076135547345947031)
            ·
              refine ⟨2737336614203321018920547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1824891076135547345947031 2737336614203321018920547)
              ·
                refine ⟨4106004921304981528380821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2737336614203321018920547 4106004921304981528380821)
                ·
                  refine ⟨192468980686171009142851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4106004921304981528380821 192468980686171009142851)
                  ·
                    rfl

theorem cell20_421686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_421686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421686 prefixEnd_421686 := by exact prefixLift 421686
  have htrace : WordTrace (prefixWord ++ tailWord_421686) baseStart_421686 baseEnd_421686 := by
    simpa [prefixWord, tailWord_421686, baseEnd_421686] using wordTrace_append hprefix tailTrace_421686
  have hstable : (prefixWord ++ tailWord_421686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421686).length < 2 ^ (prefixWord ++ tailWord_421686).sum := by decide
  have hdescent : baseEnd_421686 < baseStart_421686 := by decide
  rcases family_descends (prefixWord ++ tailWord_421686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421714 : List Nat := [3, 2, 2, 1, 1, 4, 7]
def baseStart_421714 : Nat := 118140960795 + 421714 * 2 ^ 59
def prefixEnd_421714 : Nat := 4983230072969 + 3 ^ 40 * 421714 * 2
def baseEnd_421714 : Nat := 21386862294347484023267

theorem tailTrace_421714 : CollatzResearch.WordTrace tailWord_421714 prefixEnd_421714 21386862294347484023267 := by
  unfold tailWord_421714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3845293298552418965566049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10254115462806450574842797 3845293298552418965566049)
  ·
    refine ⟨2883969973914314224174537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3845293298552418965566049 2883969973914314224174537)
    ·
      refine ⟨2162977480435735668130903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2883969973914314224174537 2162977480435735668130903)
      ·
        refine ⟨3244466220653603502196355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2162977480435735668130903 3244466220653603502196355)
        ·
          refine ⟨4866699330980405253294533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3244466220653603502196355 4866699330980405253294533)
          ·
            refine ⟨912506124558825984992725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4866699330980405253294533 912506124558825984992725)
            ·
              refine ⟨21386862294347484023267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 912506124558825984992725 21386862294347484023267)
              ·
                rfl

theorem cell20_421714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 7].length) (baseStart_421714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421714 prefixEnd_421714 := by exact prefixLift 421714
  have htrace : WordTrace (prefixWord ++ tailWord_421714) baseStart_421714 baseEnd_421714 := by
    simpa [prefixWord, tailWord_421714, baseEnd_421714] using wordTrace_append hprefix tailTrace_421714
  have hstable : (prefixWord ++ tailWord_421714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421714).length < 2 ^ (prefixWord ++ tailWord_421714).sum := by decide
  have hdescent : baseEnd_421714 < baseStart_421714 := by decide
  rcases family_descends (prefixWord ++ tailWord_421714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421717 : List Nat := [1, 3, 2, 2, 2, 4, 1, 2, 3]
def baseStart_421717 : Nat := 118140960795 + 421717 * 2 ^ 59
def prefixEnd_421717 : Nat := 4983230072969 + 3 ^ 40 * 421717 * 2
def baseEnd_421717 : Nat := 192483129930872679109391

theorem tailTrace_421717 : CollatzResearch.WordTrace tailWord_421717 prefixEnd_421717 192483129930872679109391 := by
  unfold tailWord_421717
  simp only [CollatzResearch.WordTrace]
  refine ⟨15381282613198807374623405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10254188408799204916415603 15381282613198807374623405)
  ·
    refine ⟨5767980979949552765483777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15381282613198807374623405 5767980979949552765483777)
    ·
      refine ⟨4325985734962164574112833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5767980979949552765483777 4325985734962164574112833)
      ·
        refine ⟨3244489301221623430584625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4325985734962164574112833 3244489301221623430584625)
        ·
          refine ⟨2433366975916217572938469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3244489301221623430584625 2433366975916217572938469)
          ·
            refine ⟨456256307984290794925963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2433366975916217572938469 456256307984290794925963)
            ·
              refine ⟨684384461976436192388945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456256307984290794925963 684384461976436192388945)
              ·
                refine ⟨513288346482327144291709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684384461976436192388945 513288346482327144291709)
                ·
                  refine ⟨192483129930872679109391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 513288346482327144291709 192483129930872679109391)
                  ·
                    rfl

theorem cell20_421717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_421717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421717 prefixEnd_421717 := by exact prefixLift 421717
  have htrace : WordTrace (prefixWord ++ tailWord_421717) baseStart_421717 baseEnd_421717 := by
    simpa [prefixWord, tailWord_421717, baseEnd_421717] using wordTrace_append hprefix tailTrace_421717
  have hstable : (prefixWord ++ tailWord_421717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421717).length < 2 ^ (prefixWord ++ tailWord_421717).sum := by decide
  have hdescent : baseEnd_421717 < baseStart_421717 := by decide
  rcases family_descends (prefixWord ++ tailWord_421717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421721 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 5]
def baseStart_421721 : Nat := 118140960795 + 421721 * 2 ^ 59
def prefixEnd_421721 : Nat := 4983230072969 + 3 ^ 40 * 421721 * 2
def baseEnd_421721 : Nat := 192484955639866442976041

theorem tailTrace_421721 : CollatzResearch.WordTrace tailWord_421721 prefixEnd_421721 192484955639866442976041 := by
  unfold tailWord_421721
  simp only [CollatzResearch.WordTrace]
  refine ⟨15381428505184316057769017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10254285670122877371846011 15381428505184316057769017)
  ·
    refine ⟨11536071378888237043326763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15381428505184316057769017 11536071378888237043326763)
    ·
      refine ⟨17304107068332355564990145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11536071378888237043326763 17304107068332355564990145)
      ·
        refine ⟨12978080301249266673742609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17304107068332355564990145 12978080301249266673742609)
        ·
          refine ⟨9733560225936950005306957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12978080301249266673742609 9733560225936950005306957)
          ·
            refine ⟨3650085084726356251990109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9733560225936950005306957 3650085084726356251990109)
            ·
              refine ⟨1368781906772383594496291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3650085084726356251990109 1368781906772383594496291)
              ·
                refine ⟨2053172860158575391744437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1368781906772383594496291 2053172860158575391744437)
                ·
                  refine ⟨192484955639866442976041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2053172860158575391744437 192484955639866442976041)
                  ·
                    rfl

theorem cell20_421721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_421721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421721 prefixEnd_421721 := by exact prefixLift 421721
  have htrace : WordTrace (prefixWord ++ tailWord_421721) baseStart_421721 baseEnd_421721 := by
    simpa [prefixWord, tailWord_421721, baseEnd_421721] using wordTrace_append hprefix tailTrace_421721
  have hstable : (prefixWord ++ tailWord_421721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421721).length < 2 ^ (prefixWord ++ tailWord_421721).sum := by decide
  have hdescent : baseEnd_421721 < baseStart_421721 := by decide
  rcases family_descends (prefixWord ++ tailWord_421721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421758 : List Nat := [4, 2, 3, 1, 1, 1, 3, 3, 2]
def baseStart_421758 : Nat := 118140960795 + 421758 * 2 ^ 59
def prefixEnd_421758 : Nat := 4983230072969 + 3 ^ 40 * 421758 * 2
def baseEnd_421758 : Nat := 192501843448058758742557

theorem tailTrace_421758 : CollatzResearch.WordTrace tailWord_421758 prefixEnd_421758 192501843448058758742557 := by
  unfold tailWord_421758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1922847250756283922108241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10255185337366847584577285 1922847250756283922108241)
  ·
    refine ⟨1442135438067212941581181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1922847250756283922108241 1442135438067212941581181)
    ·
      refine ⟨540800789275204853092943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1442135438067212941581181 540800789275204853092943)
      ·
        refine ⟨811201183912807279639415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540800789275204853092943 811201183912807279639415)
        ·
          refine ⟨1216801775869210919459123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811201183912807279639415 1216801775869210919459123)
          ·
            refine ⟨1825202663803816379188685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216801775869210919459123 1825202663803816379188685)
            ·
              refine ⟨684450998926431142195757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1825202663803816379188685 684450998926431142195757)
              ·
                refine ⟨256669124597411678323409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 684450998926431142195757 256669124597411678323409)
                ·
                  refine ⟨192501843448058758742557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256669124597411678323409 192501843448058758742557)
                  ·
                    rfl

theorem cell20_421758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_421758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421758 prefixEnd_421758 := by exact prefixLift 421758
  have htrace : WordTrace (prefixWord ++ tailWord_421758) baseStart_421758 baseEnd_421758 := by
    simpa [prefixWord, tailWord_421758, baseEnd_421758] using wordTrace_append hprefix tailTrace_421758
  have hstable : (prefixWord ++ tailWord_421758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421758).length < 2 ^ (prefixWord ++ tailWord_421758).sum := by decide
  have hdescent : baseEnd_421758 < baseStart_421758 := by decide
  rcases family_descends (prefixWord ++ tailWord_421758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421783 : List Nat := [1, 1, 3, 3, 1, 3, 3, 1, 4]
def baseStart_421783 : Nat := 118140960795 + 421783 * 2 ^ 59
def prefixEnd_421783 : Nat := 4983230072969 + 3 ^ 40 * 421783 * 2
def baseEnd_421783 : Nat := 192513254129269782909121

theorem tailTrace_421783 : CollatzResearch.WordTrace tailWord_421783 prefixEnd_421783 192513254129269782909121 := by
  unfold tailWord_421783
  simp only [CollatzResearch.WordTrace]
  refine ⟨15383689830959700646526003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10255793220639800431017335 15383689830959700646526003)
  ·
    refine ⟨23075534746439550969789005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15383689830959700646526003 23075534746439550969789005)
    ·
      refine ⟨8653325529914831613670877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23075534746439550969789005 8653325529914831613670877)
      ·
        refine ⟨3244997073718061855126579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8653325529914831613670877 3244997073718061855126579)
        ·
          refine ⟨4867495610577092782689869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3244997073718061855126579 4867495610577092782689869)
          ·
            refine ⟨1825310853966409793508701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4867495610577092782689869 1825310853966409793508701)
            ·
              refine ⟨684491570237403672565763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1825310853966409793508701 684491570237403672565763)
              ·
                refine ⟨1026737355356105508848645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684491570237403672565763 1026737355356105508848645)
                ·
                  refine ⟨192513254129269782909121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1026737355356105508848645 192513254129269782909121)
                  ·
                    rfl

theorem cell20_421783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 4].length) (baseStart_421783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421783 prefixEnd_421783 := by exact prefixLift 421783
  have htrace : WordTrace (prefixWord ++ tailWord_421783) baseStart_421783 baseEnd_421783 := by
    simpa [prefixWord, tailWord_421783, baseEnd_421783] using wordTrace_append hprefix tailTrace_421783
  have hstable : (prefixWord ++ tailWord_421783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421783).length < 2 ^ (prefixWord ++ tailWord_421783).sum := by decide
  have hdescent : baseEnd_421783 < baseStart_421783 := by decide
  rcases family_descends (prefixWord ++ tailWord_421783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421793 : List Nat := [1, 2, 3, 4, 2, 1, 1, 3, 3]
def baseStart_421793 : Nat := 118140960795 + 421793 * 2 ^ 59
def prefixEnd_421793 : Nat := 4983230072969 + 3 ^ 40 * 421793 * 2
def baseEnd_421793 : Nat := 192517818401754192575747

theorem tailTrace_421793 : CollatzResearch.WordTrace tailWord_421793 prefixEnd_421793 192517818401754192575747 := by
  unfold tailWord_421793
  simp only [CollatzResearch.WordTrace]
  refine ⟨15384054560923472354390033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10256036373948981569593355 15384054560923472354390033)
  ·
    refine ⟨11538040920692604265792525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15384054560923472354390033 11538040920692604265792525)
    ·
      refine ⟨4326765345259726599672197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11538040920692604265792525 4326765345259726599672197)
      ·
        refine ⟨811268502236198737438537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4326765345259726599672197 811268502236198737438537)
        ·
          refine ⟨608451376677149053078903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 811268502236198737438537 608451376677149053078903)
          ·
            refine ⟨912677065015723579618355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608451376677149053078903 912677065015723579618355)
            ·
              refine ⟨1369015597523585369427533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 912677065015723579618355 1369015597523585369427533)
              ·
                refine ⟨513380849071344513535325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1369015597523585369427533 513380849071344513535325)
                ·
                  refine ⟨192517818401754192575747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 513380849071344513535325 192517818401754192575747)
                  ·
                    rfl

theorem cell20_421793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_421793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421793 prefixEnd_421793 := by exact prefixLift 421793
  have htrace : WordTrace (prefixWord ++ tailWord_421793) baseStart_421793 baseEnd_421793 := by
    simpa [prefixWord, tailWord_421793, baseEnd_421793] using wordTrace_append hprefix tailTrace_421793
  have hstable : (prefixWord ++ tailWord_421793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421793).length < 2 ^ (prefixWord ++ tailWord_421793).sum := by decide
  have hdescent : baseEnd_421793 < baseStart_421793 := by decide
  rcases family_descends (prefixWord ++ tailWord_421793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421811 : List Nat := [1, 1, 1, 2, 3, 1, 3, 8]
def baseStart_421811 : Nat := 118140960795 + 421811 * 2 ^ 59
def prefixEnd_421811 : Nat := 4983230072969 + 3 ^ 40 * 421811 * 2
def baseEnd_421811 : Nat := 64175344697408709991891

theorem tailTrace_421811 : CollatzResearch.WordTrace tailWord_421811 prefixEnd_421811 64175344697408709991891 := by
  unfold tailWord_421811
  simp only [CollatzResearch.WordTrace]
  refine ⟨15384711074858261428545287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10256474049905507619030191 15384711074858261428545287)
  ·
    refine ⟨23077066612287392142817931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15384711074858261428545287 23077066612287392142817931)
    ·
      refine ⟨34615599918431088214226897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23077066612287392142817931 34615599918431088214226897)
      ·
        refine ⟨25961699938823316160670173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34615599918431088214226897 25961699938823316160670173)
        ·
          refine ⟨9735637477058743560251315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25961699938823316160670173 9735637477058743560251315)
          ·
            refine ⟨14603456215588115340376973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9735637477058743560251315 14603456215588115340376973)
            ·
              refine ⟨5476296080845543252641365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14603456215588115340376973 5476296080845543252641365)
              ·
                refine ⟨64175344697408709991891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5476296080845543252641365 64175344697408709991891)
                ·
                  rfl

theorem cell20_421811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 8].length) (baseStart_421811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421811 prefixEnd_421811 := by exact prefixLift 421811
  have htrace : WordTrace (prefixWord ++ tailWord_421811) baseStart_421811 baseEnd_421811 := by
    simpa [prefixWord, tailWord_421811, baseEnd_421811] using wordTrace_append hprefix tailTrace_421811
  have hstable : (prefixWord ++ tailWord_421811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421811).length < 2 ^ (prefixWord ++ tailWord_421811).sum := by decide
  have hdescent : baseEnd_421811 < baseStart_421811 := by decide
  rcases family_descends (prefixWord ++ tailWord_421811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421838 : List Nat := [4, 1, 1, 1, 2, 2, 3, 4, 2]
def baseStart_421838 : Nat := 118140960795 + 421838 * 2 ^ 59
def prefixEnd_421838 : Nat := 4983230072969 + 3 ^ 40 * 421838 * 2
def baseEnd_421838 : Nat := 192538357627934036075563

theorem tailTrace_421838 : CollatzResearch.WordTrace tailWord_421838 prefixEnd_421838 192538357627934036075563 := by
  unfold tailWord_421838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1923211980720055629972271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10257130563840296693185445 1923211980720055629972271)
  ·
    refine ⟨2884817971080083444958407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1923211980720055629972271 2884817971080083444958407)
    ·
      refine ⟨4327226956620125167437611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2884817971080083444958407 4327226956620125167437611)
      ·
        refine ⟨6490840434930187751156417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4327226956620125167437611 6490840434930187751156417)
        ·
          refine ⟨4868130326197640813367313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6490840434930187751156417 4868130326197640813367313)
          ·
            refine ⟨3651097744648230610025485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4868130326197640813367313 3651097744648230610025485)
            ·
              refine ⟨1369161654243086478759557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3651097744648230610025485 1369161654243086478759557)
              ·
                refine ⟨256717810170578714767417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1369161654243086478759557 256717810170578714767417)
                ·
                  refine ⟨192538357627934036075563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256717810170578714767417 192538357627934036075563)
                  ·
                    rfl

theorem cell20_421838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_421838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421838 prefixEnd_421838 := by exact prefixLift 421838
  have htrace : WordTrace (prefixWord ++ tailWord_421838) baseStart_421838 baseEnd_421838 := by
    simpa [prefixWord, tailWord_421838, baseEnd_421838] using wordTrace_append hprefix tailTrace_421838
  have hstable : (prefixWord ++ tailWord_421838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421838).length < 2 ^ (prefixWord ++ tailWord_421838).sum := by decide
  have hdescent : baseEnd_421838 < baseStart_421838 := by decide
  rcases family_descends (prefixWord ++ tailWord_421838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421845 : List Nat := [1, 3, 2, 3, 2, 3, 1, 5]
def baseStart_421845 : Nat := 118140960795 + 421845 * 2 ^ 59
def prefixEnd_421845 : Nat := 4983230072969 + 3 ^ 40 * 421845 * 2
def baseEnd_421845 : Nat := 64180517539557707614067

theorem tailTrace_421845 : CollatzResearch.WordTrace tailWord_421845 prefixEnd_421845 64180517539557707614067 := by
  unfold tailWord_421845
  simp only [CollatzResearch.WordTrace]
  refine ⟨15385951156735085235282989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10257300771156723490188659 15385951156735085235282989)
  ·
    refine ⟨5769731683775656963231121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15385951156735085235282989 5769731683775656963231121)
    ·
      refine ⟨4327298762831742722423341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5769731683775656963231121 4327298762831742722423341)
      ·
        refine ⟨1622737036061903520908753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4327298762831742722423341 1622737036061903520908753)
        ·
          refine ⟨1217052777046427640681565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1622737036061903520908753 1217052777046427640681565)
          ·
            refine ⟨456394791392410365255587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1217052777046427640681565 456394791392410365255587)
            ·
              refine ⟨684592187088615547883381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456394791392410365255587 684592187088615547883381)
              ·
                refine ⟨64180517539557707614067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 684592187088615547883381 64180517539557707614067)
                ·
                  rfl

theorem cell20_421845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 5].length) (baseStart_421845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421845 prefixEnd_421845 := by exact prefixLift 421845
  have htrace : WordTrace (prefixWord ++ tailWord_421845) baseStart_421845 baseEnd_421845 := by
    simpa [prefixWord, tailWord_421845, baseEnd_421845] using wordTrace_append hprefix tailTrace_421845
  have hstable : (prefixWord ++ tailWord_421845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421845).length < 2 ^ (prefixWord ++ tailWord_421845).sum := by decide
  have hdescent : baseEnd_421845 < baseStart_421845 := by decide
  rcases family_descends (prefixWord ++ tailWord_421845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421859 : List Nat := [1, 1, 1, 6, 1, 3, 1, 2, 4]
def baseStart_421859 : Nat := 118140960795 + 421859 * 2 ^ 59
def prefixEnd_421859 : Nat := 4983230072969 + 3 ^ 40 * 421859 * 2
def baseEnd_421859 : Nat := 192547942600151296375477

theorem tailTrace_421859 : CollatzResearch.WordTrace tailWord_421859 prefixEnd_421859 192547942600151296375477 := by
  unfold tailWord_421859
  simp only [CollatzResearch.WordTrace]
  refine ⟨15386461778684365626292631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10257641185789577084195087 15386461778684365626292631)
  ·
    refine ⟨23079692668026548439438947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15386461778684365626292631 23079692668026548439438947)
    ·
      refine ⟨34619539002039822659158421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23079692668026548439438947 34619539002039822659158421)
      ·
        refine ⟨1622790890720616687148051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34619539002039822659158421 1622790890720616687148051)
        ·
          refine ⟨2434186336080925030722077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1622790890720616687148051 2434186336080925030722077)
          ·
            refine ⟨912819876030346886520779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2434186336080925030722077 912819876030346886520779)
            ·
              refine ⟨1369229814045520329781169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 912819876030346886520779 1369229814045520329781169)
              ·
                refine ⟨1026922360534140247335877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1369229814045520329781169 1026922360534140247335877)
                ·
                  refine ⟨192547942600151296375477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1026922360534140247335877 192547942600151296375477)
                  ·
                    rfl

theorem cell20_421859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 4].length) (baseStart_421859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421859 prefixEnd_421859 := by exact prefixLift 421859
  have htrace : WordTrace (prefixWord ++ tailWord_421859) baseStart_421859 baseEnd_421859 := by
    simpa [prefixWord, tailWord_421859, baseEnd_421859] using wordTrace_append hprefix tailTrace_421859
  have hstable : (prefixWord ++ tailWord_421859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421859).length < 2 ^ (prefixWord ++ tailWord_421859).sum := by decide
  have hdescent : baseEnd_421859 < baseStart_421859 := by decide
  rcases family_descends (prefixWord ++ tailWord_421859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421886 : List Nat := [4, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_421886 : Nat := 118140960795 + 421886 * 2 ^ 59
def prefixEnd_421886 : Nat := 4983230072969 + 3 ^ 40 * 421886 * 2
def baseEnd_421886 : Nat := 192560266135859202475367

theorem tailTrace_421886 : CollatzResearch.WordTrace tailWord_421886 prefixEnd_421886 192560266135859202475367 := by
  unfold tailWord_421886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1923430818698318654690689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10258297699724366158350341 1923430818698318654690689)
  ·
    refine ⟨1442573114023738991018017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1923430818698318654690689 1442573114023738991018017)
    ·
      refine ⟨1081929835517804243263513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1442573114023738991018017 1081929835517804243263513)
      ·
        refine ⟨811447376638353182447635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1081929835517804243263513 811447376638353182447635)
        ·
          refine ⟨1217171064957529773671453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811447376638353182447635 1217171064957529773671453)
          ·
            refine ⟨456439149359073665126795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1217171064957529773671453 456439149359073665126795)
            ·
              refine ⟨684658724038610497690193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456439149359073665126795 684658724038610497690193)
              ·
                refine ⟨513494043028957873267645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684658724038610497690193 513494043028957873267645)
                ·
                  refine ⟨192560266135859202475367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 513494043028957873267645 192560266135859202475367)
                  ·
                    rfl

theorem cell20_421886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_421886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421886 prefixEnd_421886 := by exact prefixLift 421886
  have htrace : WordTrace (prefixWord ++ tailWord_421886) baseStart_421886 baseEnd_421886 := by
    simpa [prefixWord, tailWord_421886, baseEnd_421886] using wordTrace_append hprefix tailTrace_421886
  have hstable : (prefixWord ++ tailWord_421886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421886).length < 2 ^ (prefixWord ++ tailWord_421886).sum := by decide
  have hdescent : baseEnd_421886 < baseStart_421886 := by decide
  rcases family_descends (prefixWord ++ tailWord_421886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421927 : List Nat := [1, 1, 7, 1, 3, 1, 1, 3, 2]
def baseStart_421927 : Nat := 118140960795 + 421927 * 2 ^ 59
def prefixEnd_421927 : Nat := 4983230072969 + 3 ^ 40 * 421927 * 2
def baseEnd_421927 : Nat := 192578979653045282108533

theorem tailTrace_421927 : CollatzResearch.WordTrace tailWord_421927 prefixEnd_421927 192578979653045282108533 := by
  unfold tailWord_421927
  simp only [CollatzResearch.WordTrace]
  refine ⟨15388941942438013239768035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10259294628292008826512023 15388941942438013239768035)
  ·
    refine ⟨23083412913657019859652053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15388941942438013239768035 23083412913657019859652053)
    ·
      refine ⟨541017490163836402960595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 23083412913657019859652053 541017490163836402960595)
      ·
        refine ⟨811526235245754604440893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541017490163836402960595 811526235245754604440893)
        ·
          refine ⟨304322338217157976665335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 811526235245754604440893 304322338217157976665335)
          ·
            refine ⟨456483507325736964998003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304322338217157976665335 456483507325736964998003)
            ·
              refine ⟨684725260988605447497005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456483507325736964998003 684725260988605447497005)
              ·
                refine ⟨256771972870727042811377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 684725260988605447497005 256771972870727042811377)
                ·
                  refine ⟨192578979653045282108533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256771972870727042811377 192578979653045282108533)
                  ·
                    rfl

theorem cell20_421927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 2].length) (baseStart_421927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421927 prefixEnd_421927 := by exact prefixLift 421927
  have htrace : WordTrace (prefixWord ++ tailWord_421927) baseStart_421927 baseEnd_421927 := by
    simpa [prefixWord, tailWord_421927, baseEnd_421927] using wordTrace_append hprefix tailTrace_421927
  have hstable : (prefixWord ++ tailWord_421927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421927).length < 2 ^ (prefixWord ++ tailWord_421927).sum := by decide
  have hdescent : baseEnd_421927 < baseStart_421927 := by decide
  rcases family_descends (prefixWord ++ tailWord_421927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421935 : List Nat := [1, 1, 2, 1, 2, 1, 1, 9, 2]
def baseStart_421935 : Nat := 118140960795 + 421935 * 2 ^ 59
def prefixEnd_421935 : Nat := 4983230072969 + 3 ^ 40 * 421935 * 2
def baseEnd_421935 : Nat := 192582631071032809841833

theorem tailTrace_421935 : CollatzResearch.WordTrace tailWord_421935 prefixEnd_421935 192582631071032809841833 := by
  unfold tailWord_421935
  simp only [CollatzResearch.WordTrace]
  refine ⟨15389233726409030606059259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10259489150939353737372839 15389233726409030606059259)
  ·
    refine ⟨23083850589613545909088889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15389233726409030606059259 23083850589613545909088889)
    ·
      refine ⟨17312887942210159431816667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23083850589613545909088889 17312887942210159431816667)
      ·
        refine ⟨25969331913315239147725001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17312887942210159431816667 25969331913315239147725001)
        ·
          refine ⟨19476998934986429360793751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25969331913315239147725001 19476998934986429360793751)
          ·
            refine ⟨29215498402479644041190627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19476998934986429360793751 29215498402479644041190627)
            ·
              refine ⟨43823247603719466061785941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29215498402479644041190627 43823247603719466061785941)
              ·
                refine ⟨256776841428043746455777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 43823247603719466061785941 256776841428043746455777)
                ·
                  refine ⟨192582631071032809841833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256776841428043746455777 192582631071032809841833)
                  ·
                    rfl

theorem cell20_421935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 2].length) (baseStart_421935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421935 prefixEnd_421935 := by exact prefixLift 421935
  have htrace : WordTrace (prefixWord ++ tailWord_421935) baseStart_421935 baseEnd_421935 := by
    simpa [prefixWord, tailWord_421935, baseEnd_421935] using wordTrace_append hprefix tailTrace_421935
  have hstable : (prefixWord ++ tailWord_421935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421935).length < 2 ^ (prefixWord ++ tailWord_421935).sum := by decide
  have hdescent : baseEnd_421935 < baseStart_421935 := by decide
  rcases family_descends (prefixWord ++ tailWord_421935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421949 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 5]
def baseStart_421949 : Nat := 118140960795 + 421949 * 2 ^ 59
def prefixEnd_421949 : Nat := 4983230072969 + 3 ^ 40 * 421949 * 2
def baseEnd_421949 : Nat := 192589021052510983375109

theorem tailTrace_421949 : CollatzResearch.WordTrace tailWord_421949 prefixEnd_421949 192589021052510983375109 := by
  unfold tailWord_421949
  simp only [CollatzResearch.WordTrace]
  refine ⟨15389744348358310997068901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10259829565572207331379267 15389744348358310997068901)
  ·
    refine ⟨2885577065317183311950419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15389744348358310997068901 2885577065317183311950419)
    ·
      refine ⟨4328365597975774967925629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2885577065317183311950419 4328365597975774967925629)
      ·
        refine ⟨1623137099240915612972111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4328365597975774967925629 1623137099240915612972111)
        ·
          refine ⟨2434705648861373419458167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1623137099240915612972111 2434705648861373419458167)
          ·
            refine ⟨3652058473292060129187251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2434705648861373419458167 3652058473292060129187251)
            ·
              refine ⟨5478087709938090193780877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3652058473292060129187251 5478087709938090193780877)
              ·
                refine ⟨2054282891226783822667829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5478087709938090193780877 2054282891226783822667829)
                ·
                  refine ⟨192589021052510983375109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2054282891226783822667829 192589021052510983375109)
                  ·
                    rfl

theorem cell20_421949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_421949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421949 prefixEnd_421949 := by exact prefixLift 421949
  have htrace : WordTrace (prefixWord ++ tailWord_421949) baseStart_421949 baseEnd_421949 := by
    simpa [prefixWord, tailWord_421949, baseEnd_421949] using wordTrace_append hprefix tailTrace_421949
  have hstable : (prefixWord ++ tailWord_421949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421949).length < 2 ^ (prefixWord ++ tailWord_421949).sum := by decide
  have hdescent : baseEnd_421949 < baseStart_421949 := by decide
  rcases family_descends (prefixWord ++ tailWord_421949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421966 : List Nat := [4, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_421966 : Nat := 118140960795 + 421966 * 2 ^ 59
def prefixEnd_421966 : Nat := 4983230072969 + 3 ^ 40 * 421966 * 2
def baseEnd_421966 : Nat := 192596780315734479808373

theorem tailTrace_421966 : CollatzResearch.WordTrace tailWord_421966 prefixEnd_421966 192596780315734479808373 := by
  unfold tailWord_421966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1923795548662090362554719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10260242926197815266958501 1923795548662090362554719)
  ·
    refine ⟨2885693322993135543832079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1923795548662090362554719 2885693322993135543832079)
    ·
      refine ⟨4328539984489703315748119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2885693322993135543832079 4328539984489703315748119)
      ·
        refine ⟨6492809976734554973622179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4328539984489703315748119 6492809976734554973622179)
        ·
          refine ⟨9739214965101832460433269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6492809976734554973622179 9739214965101832460433269)
          ·
            refine ⟨913051402978296793165619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9739214965101832460433269 913051402978296793165619)
            ·
              refine ⟨1369577104467445189748429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913051402978296793165619 1369577104467445189748429)
              ·
                refine ⟨513591414175291946155661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1369577104467445189748429 513591414175291946155661)
                ·
                  refine ⟨192596780315734479808373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 513591414175291946155661 192596780315734479808373)
                  ·
                    rfl

theorem cell20_421966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_421966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421966 prefixEnd_421966 := by exact prefixLift 421966
  have htrace : WordTrace (prefixWord ++ tailWord_421966) baseStart_421966 baseEnd_421966 := by
    simpa [prefixWord, tailWord_421966, baseEnd_421966] using wordTrace_append hprefix tailTrace_421966
  have hstable : (prefixWord ++ tailWord_421966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421966).length < 2 ^ (prefixWord ++ tailWord_421966).sum := by decide
  have hdescent : baseEnd_421966 < baseStart_421966 := by decide
  rcases family_descends (prefixWord ++ tailWord_421966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421980 : List Nat := [2, 2, 4, 1, 1, 2, 2, 6]
def baseStart_421980 : Nat := 118140960795 + 421980 * 2 ^ 59
def prefixEnd_421980 : Nat := 4983230072969 + 3 ^ 40 * 421980 * 2
def baseEnd_421980 : Nat := 64201056765737551113883

theorem tailTrace_421980 : CollatzResearch.WordTrace tailWord_421980 prefixEnd_421980 64201056765737551113883 := by
  unfold tailWord_421980
  simp only [CollatzResearch.WordTrace]
  refine ⟨7695437505623001645723697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10260583340830668860964929 7695437505623001645723697)
  ·
    refine ⟨5771578129217251234292773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7695437505623001645723697 5771578129217251234292773)
    ·
      refine ⟨1082170899228234606429895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5771578129217251234292773 1082170899228234606429895)
      ·
        refine ⟨1623256348842351909644843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082170899228234606429895 1623256348842351909644843)
        ·
          refine ⟨2434884523263527864467265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1623256348842351909644843 2434884523263527864467265)
          ·
            refine ⟨1826163392447645898350449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2434884523263527864467265 1826163392447645898350449)
            ·
              refine ⟨1369622544335734423762837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1826163392447645898350449 1369622544335734423762837)
              ·
                refine ⟨64201056765737551113883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1369622544335734423762837 64201056765737551113883)
                ·
                  rfl

theorem cell20_421980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_421980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_421980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_421980 prefixEnd_421980 := by exact prefixLift 421980
  have htrace : WordTrace (prefixWord ++ tailWord_421980) baseStart_421980 baseEnd_421980 := by
    simpa [prefixWord, tailWord_421980, baseEnd_421980] using wordTrace_append hprefix tailTrace_421980
  have hstable : (prefixWord ++ tailWord_421980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421980).length < 2 ^ (prefixWord ++ tailWord_421980).sum := by decide
  have hdescent : baseEnd_421980 < baseStart_421980 := by decide
  rcases family_descends (prefixWord ++ tailWord_421980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422007 : List Nat := [1, 1, 3, 1, 1, 7, 2, 2, 2]
def baseStart_422007 : Nat := 118140960795 + 422007 * 2 ^ 59
def prefixEnd_422007 : Nat := 4983230072969 + 3 ^ 40 * 422007 * 2
def baseEnd_422007 : Nat := 192615493832920559441539

theorem tailTrace_422007 : CollatzResearch.WordTrace tailWord_422007 prefixEnd_422007 192615493832920559441539 := by
  unfold tailWord_422007
  simp only [CollatzResearch.WordTrace]
  refine ⟨15391859782148186902680275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10261239854765457935120183 15391859782148186902680275)
  ·
    refine ⟨23087789673222280354020413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15391859782148186902680275 23087789673222280354020413)
    ·
      refine ⟨8657921127458355132757655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23087789673222280354020413 8657921127458355132757655)
      ·
        refine ⟨12986881691187532699136483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8657921127458355132757655 12986881691187532699136483)
        ·
          refine ⟨19480322536781299048704725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12986881691187532699136483 19480322536781299048704725)
          ·
            refine ⟨456570059455811696454017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 19480322536781299048704725 456570059455811696454017)
            ·
              refine ⟨342427544591858772340513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 456570059455811696454017 342427544591858772340513)
              ·
                refine ⟨256820658443894079255385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342427544591858772340513 256820658443894079255385)
                ·
                  refine ⟨192615493832920559441539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256820658443894079255385 192615493832920559441539)
                  ·
                    rfl

theorem cell20_422007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 2].length) (baseStart_422007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422007 prefixEnd_422007 := by exact prefixLift 422007
  have htrace : WordTrace (prefixWord ++ tailWord_422007) baseStart_422007 baseEnd_422007 := by
    simpa [prefixWord, tailWord_422007, baseEnd_422007] using wordTrace_append hprefix tailTrace_422007
  have hstable : (prefixWord ++ tailWord_422007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422007).length < 2 ^ (prefixWord ++ tailWord_422007).sum := by decide
  have hdescent : baseEnd_422007 < baseStart_422007 := by decide
  rcases family_descends (prefixWord ++ tailWord_422007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422025 : List Nat := [1, 2, 1, 1, 4, 2, 1, 5, 3]
def baseStart_422025 : Nat := 118140960795 + 422025 * 2 ^ 59
def prefixEnd_422025 : Nat := 4983230072969 + 3 ^ 40 * 422025 * 2
def baseEnd_422025 : Nat := 192623709523392496841465

theorem tailTrace_422025 : CollatzResearch.WordTrace tailWord_422025 prefixEnd_422025 192623709523392496841465 := by
  unfold tailWord_422025
  simp only [CollatzResearch.WordTrace]
  refine ⟨15392516296082975976835529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10261677530721983984557019 15392516296082975976835529)
  ·
    refine ⟨11544387222062231982626647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15392516296082975976835529 11544387222062231982626647)
    ·
      refine ⟨17316580833093347973939971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11544387222062231982626647 17316580833093347973939971)
      ·
        refine ⟨25974871249640021960909957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17316580833093347973939971 25974871249640021960909957)
        ·
          refine ⟨4870288359307504117670617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25974871249640021960909957 4870288359307504117670617)
          ·
            refine ⟨3652716269480628088252963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4870288359307504117670617 3652716269480628088252963)
            ·
              refine ⟨5479074404220942132379445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3652716269480628088252963 5479074404220942132379445)
              ·
                refine ⟨513663225395713324910573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5479074404220942132379445 513663225395713324910573)
                ·
                  refine ⟨192623709523392496841465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 513663225395713324910573 192623709523392496841465)
                  ·
                    rfl

theorem cell20_422025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_422025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422025 prefixEnd_422025 := by exact prefixLift 422025
  have htrace : WordTrace (prefixWord ++ tailWord_422025) baseStart_422025 baseEnd_422025 := by
    simpa [prefixWord, tailWord_422025, baseEnd_422025] using wordTrace_append hprefix tailTrace_422025
  have hstable : (prefixWord ++ tailWord_422025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422025).length < 2 ^ (prefixWord ++ tailWord_422025).sum := by decide
  have hdescent : baseEnd_422025 < baseStart_422025 := by decide
  rcases family_descends (prefixWord ++ tailWord_422025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422032 : List Nat := [2, 1, 1, 1, 1, 1, 7, 2, 4]
def baseStart_422032 : Nat := 118140960795 + 422032 * 2 ^ 59
def prefixEnd_422032 : Nat := 4983230072969 + 3 ^ 40 * 422032 * 2
def baseEnd_422032 : Nat := 192626904514131583608103

theorem tailTrace_422032 : CollatzResearch.WordTrace tailWord_422032 prefixEnd_422032 192626904514131583608103 := by
  unfold tailWord_422032
  simp only [CollatzResearch.WordTrace]
  refine ⟨7696385803528808086170175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10261847738038410781560233 7696385803528808086170175)
  ·
    refine ⟨11544578705293212129255263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7696385803528808086170175 11544578705293212129255263)
    ·
      refine ⟨17316868057939818193882895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11544578705293212129255263 17316868057939818193882895)
      ·
        refine ⟨25975302086909727290824343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17316868057939818193882895 25975302086909727290824343)
        ·
          refine ⟨38962953130364590936236515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25975302086909727290824343 38962953130364590936236515)
          ·
            refine ⟨58444429695546886404354773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38962953130364590936236515 58444429695546886404354773)
            ·
              refine ⟨1369791320989380150102065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 58444429695546886404354773 1369791320989380150102065)
              ·
                refine ⟨1027343490742035112576549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1369791320989380150102065 1027343490742035112576549)
                ·
                  refine ⟨192626904514131583608103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1027343490742035112576549 192626904514131583608103)
                  ·
                    rfl

theorem cell20_422032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_422032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422032 prefixEnd_422032 := by exact prefixLift 422032
  have htrace : WordTrace (prefixWord ++ tailWord_422032) baseStart_422032 baseEnd_422032 := by
    simpa [prefixWord, tailWord_422032, baseEnd_422032] using wordTrace_append hprefix tailTrace_422032
  have hstable : (prefixWord ++ tailWord_422032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422032).length < 2 ^ (prefixWord ++ tailWord_422032).sum := by decide
  have hdescent : baseEnd_422032 < baseStart_422032 := by decide
  rcases family_descends (prefixWord ++ tailWord_422032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422077 : List Nat := [1, 4, 1, 2, 1, 1, 1, 9]
def baseStart_422077 : Nat := 118140960795 + 422077 * 2 ^ 59
def prefixEnd_422077 : Nat := 4983230072969 + 3 ^ 40 * 422077 * 2
def baseEnd_422077 : Nat := 64215814580103809035973

theorem tailTrace_422077 : CollatzResearch.WordTrace tailWord_422077 prefixEnd_422077 64215814580103809035973 := by
  unfold tailWord_422077
  simp only [CollatzResearch.WordTrace]
  refine ⟨15394412891894588857728485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10262941927929725905152323 15394412891894588857728485)
  ·
    refine ⟨2886452417230235410824091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15394412891894588857728485 2886452417230235410824091)
    ·
      refine ⟨4329678625845353116236137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2886452417230235410824091 4329678625845353116236137)
      ·
        refine ⟨3247258969384014837177103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4329678625845353116236137 3247258969384014837177103)
        ·
          refine ⟨4870888454076022255765655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3247258969384014837177103 4870888454076022255765655)
          ·
            refine ⟨7306332681114033383648483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4870888454076022255765655 7306332681114033383648483)
            ·
              refine ⟨10959499021671050075472725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7306332681114033383648483 10959499021671050075472725)
              ·
                refine ⟨64215814580103809035973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10959499021671050075472725 64215814580103809035973)
                ·
                  rfl

theorem cell20_422077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 9].length) (baseStart_422077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422077 prefixEnd_422077 := by exact prefixLift 422077
  have htrace : WordTrace (prefixWord ++ tailWord_422077) baseStart_422077 baseEnd_422077 := by
    simpa [prefixWord, tailWord_422077, baseEnd_422077] using wordTrace_append hprefix tailTrace_422077
  have hstable : (prefixWord ++ tailWord_422077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422077).length < 2 ^ (prefixWord ++ tailWord_422077).sum := by decide
  have hdescent : baseEnd_422077 < baseStart_422077 := by decide
  rcases family_descends (prefixWord ++ tailWord_422077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422094 : List Nat := [4, 1, 1, 1, 4, 2, 1, 6]
def baseStart_422094 : Nat := 118140960795 + 422094 * 2 ^ 59
def prefixEnd_422094 : Nat := 4983230072969 + 3 ^ 40 * 422094 * 2
def baseEnd_422094 : Nat := 64218401001178307847061

theorem tailTrace_422094 : CollatzResearch.WordTrace tailWord_422094 prefixEnd_422094 64218401001178307847061 := by
  unfold tailWord_422094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1924379116604125095137167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10263355288555333840731557 1924379116604125095137167)
  ·
    refine ⟨2886568674906187642705751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1924379116604125095137167 2886568674906187642705751)
    ·
      refine ⟨4329853012359281464058627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2886568674906187642705751 4329853012359281464058627)
      ·
        refine ⟨6494779518538922196087941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4329853012359281464058627 6494779518538922196087941)
        ·
          refine ⟨1217771159726047911766489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6494779518538922196087941 1217771159726047911766489)
          ·
            refine ⟨913328369794535933824867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1217771159726047911766489 913328369794535933824867)
            ·
              refine ⟨1369992554691803900737301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913328369794535933824867 1369992554691803900737301)
              ·
                refine ⟨64218401001178307847061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1369992554691803900737301 64218401001178307847061)
                ·
                  rfl

theorem cell20_422094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_422094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422094 prefixEnd_422094 := by exact prefixLift 422094
  have htrace : WordTrace (prefixWord ++ tailWord_422094) baseStart_422094 baseEnd_422094 := by
    simpa [prefixWord, tailWord_422094, baseEnd_422094] using wordTrace_append hprefix tailTrace_422094
  have hstable : (prefixWord ++ tailWord_422094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422094).length < 2 ^ (prefixWord ++ tailWord_422094).sum := by decide
  have hdescent : baseEnd_422094 < baseStart_422094 := by decide
  rcases family_descends (prefixWord ++ tailWord_422094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422104 : List Nat := [2, 1, 2, 2, 4, 1, 3, 3, 2]
def baseStart_422104 : Nat := 118140960795 + 422104 * 2 ^ 59
def prefixEnd_422104 : Nat := 4983230072969 + 3 ^ 40 * 422104 * 2
def baseEnd_422104 : Nat := 192659767276019333207809

theorem tailTrace_422104 : CollatzResearch.WordTrace tailWord_422104 prefixEnd_422104 192659767276019333207809 := by
  unfold tailWord_422104
  simp only [CollatzResearch.WordTrace]
  refine ⟨7697698831398386234480683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10263598441864514979307577 7697698831398386234480683)
  ·
    refine ⟨11546548247097579351721025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7697698831398386234480683 11546548247097579351721025)
    ·
      refine ⟨8659911185323184513790769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11546548247097579351721025 8659911185323184513790769)
      ·
        refine ⟨6494933388992388385343077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8659911185323184513790769 6494933388992388385343077)
        ·
          refine ⟨1217800010436072822251827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6494933388992388385343077 1217800010436072822251827)
          ·
            refine ⟨1826700015654109233377741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217800010436072822251827 1826700015654109233377741)
            ·
              refine ⟨685012505870290962516653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1826700015654109233377741 685012505870290962516653)
              ·
                refine ⟨256879689701359110943745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 685012505870290962516653 256879689701359110943745)
                ·
                  refine ⟨192659767276019333207809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256879689701359110943745 192659767276019333207809)
                  ·
                    rfl

theorem cell20_422104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 2].length) (baseStart_422104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422104 prefixEnd_422104 := by exact prefixLift 422104
  have htrace : WordTrace (prefixWord ++ tailWord_422104) baseStart_422104 baseEnd_422104 := by
    simpa [prefixWord, tailWord_422104, baseEnd_422104] using wordTrace_append hprefix tailTrace_422104
  have hstable : (prefixWord ++ tailWord_422104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422104).length < 2 ^ (prefixWord ++ tailWord_422104).sum := by decide
  have hdescent : baseEnd_422104 < baseStart_422104 := by decide
  rcases family_descends (prefixWord ++ tailWord_422104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422153 : List Nat := [1, 2, 1, 1, 3, 4, 2, 6]
def baseStart_422153 : Nat := 118140960795 + 422153 * 2 ^ 59
def prefixEnd_422153 : Nat := 4983230072969 + 3 ^ 40 * 422153 * 2
def baseEnd_422153 : Nat := 64227377403730980191425

theorem tailTrace_422153 : CollatzResearch.WordTrace tailWord_422153 prefixEnd_422153 64227377403730980191425 := by
  unfold tailWord_422153
  simp only [CollatzResearch.WordTrace]
  refine ⟨15397184839619253837495113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10264789893079502558330075 15397184839619253837495113)
  ·
    refine ⟨11547888629714440378121335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15397184839619253837495113 11547888629714440378121335)
    ·
      refine ⟨17321832944571660567182003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11547888629714440378121335 17321832944571660567182003)
      ·
        refine ⟨25982749416857490850773005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17321832944571660567182003 25982749416857490850773005)
        ·
          refine ⟨9743531031321559069039877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25982749416857490850773005 9743531031321559069039877)
          ·
            refine ⟨1826912068372792325444977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9743531031321559069039877 1826912068372792325444977)
            ·
              refine ⟨1370184051279594244083733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1826912068372792325444977 1370184051279594244083733)
              ·
                refine ⟨64227377403730980191425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1370184051279594244083733 64227377403730980191425)
                ·
                  rfl

theorem cell20_422153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 6].length) (baseStart_422153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422153 prefixEnd_422153 := by exact prefixLift 422153
  have htrace : WordTrace (prefixWord ++ tailWord_422153) baseStart_422153 baseEnd_422153 := by
    simpa [prefixWord, tailWord_422153, baseEnd_422153] using wordTrace_append hprefix tailTrace_422153
  have hstable : (prefixWord ++ tailWord_422153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422153).length < 2 ^ (prefixWord ++ tailWord_422153).sum := by decide
  have hdescent : baseEnd_422153 < baseStart_422153 := by decide
  rcases family_descends (prefixWord ++ tailWord_422153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422170 : List Nat := [3, 1, 1, 3, 5, 7]
def baseStart_422170 : Nat := 118140960795 + 422170 * 2 ^ 59
def prefixEnd_422170 : Nat := 4983230072969 + 3 ^ 40 * 422170 * 2
def baseEnd_422170 : Nat := 7136662647200608778057

theorem tailTrace_422170 : CollatzResearch.WordTrace tailWord_422170 prefixEnd_422170 7136662647200608778057 := by
  unfold tailWord_422170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3849451220139416435215991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10265203253705110493909309 3849451220139416435215991)
  ·
    refine ⟨5774176830209124652823987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3849451220139416435215991 5774176830209124652823987)
    ·
      refine ⟨8661265245313686979235981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5774176830209124652823987 8661265245313686979235981)
      ·
        refine ⟨3247974466992632617213493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8661265245313686979235981 3247974466992632617213493)
        ·
          refine ⟨304497606280559307863765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3247974466992632617213493 304497606280559307863765)
          ·
            refine ⟨7136662647200608778057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 304497606280559307863765 7136662647200608778057)
            ·
              rfl

theorem cell20_422170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 7].length) (baseStart_422170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422170 prefixEnd_422170 := by exact prefixLift 422170
  have htrace : WordTrace (prefixWord ++ tailWord_422170) baseStart_422170 baseEnd_422170 := by
    simpa [prefixWord, tailWord_422170, baseEnd_422170] using wordTrace_append hprefix tailTrace_422170
  have hstable : (prefixWord ++ tailWord_422170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422170).length < 2 ^ (prefixWord ++ tailWord_422170).sum := by decide
  have hdescent : baseEnd_422170 < baseStart_422170 := by decide
  rcases family_descends (prefixWord ++ tailWord_422170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422173 : List Nat := [1, 4, 2, 3, 2, 1, 2, 2, 3]
def baseStart_422173 : Nat := 118140960795 + 422173 * 2 ^ 59
def prefixEnd_422173 : Nat := 4983230072969 + 3 ^ 40 * 422173 * 2
def baseEnd_422173 : Nat := 192691260756161759907527

theorem tailTrace_422173 : CollatzResearch.WordTrace tailWord_422173 prefixEnd_422173 192691260756161759907527 := by
  unfold tailWord_422173
  simp only [CollatzResearch.WordTrace]
  refine ⟨15397914299546797253223173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10265276199697864835482115 15397914299546797253223173)
  ·
    refine ⟨2887108931165024484979345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15397914299546797253223173 2887108931165024484979345)
    ·
      refine ⟨2165331698373768363734509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2887108931165024484979345 2165331698373768363734509)
      ·
        refine ⟨811999386890163136400441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2165331698373768363734509 811999386890163136400441)
        ·
          refine ⟨608999540167622352300331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 811999386890163136400441 608999540167622352300331)
          ·
            refine ⟨913499310251433528450497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608999540167622352300331 913499310251433528450497)
            ·
              refine ⟨685124482688575146337873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 913499310251433528450497 685124482688575146337873)
              ·
                refine ⟨513843362016431359753405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 685124482688575146337873 513843362016431359753405)
                ·
                  refine ⟨192691260756161759907527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 513843362016431359753405 192691260756161759907527)
                  ·
                    rfl

theorem cell20_422173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_422173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422173 prefixEnd_422173 := by exact prefixLift 422173
  have htrace : WordTrace (prefixWord ++ tailWord_422173) baseStart_422173 baseEnd_422173 := by
    simpa [prefixWord, tailWord_422173, baseEnd_422173] using wordTrace_append hprefix tailTrace_422173
  have hstable : (prefixWord ++ tailWord_422173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422173).length < 2 ^ (prefixWord ++ tailWord_422173).sum := by decide
  have hdescent : baseEnd_422173 < baseStart_422173 := by decide
  rcases family_descends (prefixWord ++ tailWord_422173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422177 : List Nat := [1, 2, 3, 2, 1, 1, 3, 4, 3]
def baseStart_422177 : Nat := 118140960795 + 422177 * 2 ^ 59
def prefixEnd_422177 : Nat := 4983230072969 + 3 ^ 40 * 422177 * 2
def baseEnd_422177 : Nat := 192693086465155523774177

theorem tailTrace_422177 : CollatzResearch.WordTrace tailWord_422177 prefixEnd_422177 192693086465155523774177 := by
  unfold tailWord_422177
  simp only [CollatzResearch.WordTrace]
  refine ⟨15398060191532305936368785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10265373461021537290912523 15398060191532305936368785)
  ·
    refine ⟨11548545143649229452276589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15398060191532305936368785 11548545143649229452276589)
    ·
      refine ⟨4330704428868461044603721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11548545143649229452276589 4330704428868461044603721)
      ·
        refine ⟨3248028321651345783452791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4330704428868461044603721 3248028321651345783452791)
        ·
          refine ⟨4872042482477018675179187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3248028321651345783452791 4872042482477018675179187)
          ·
            refine ⟨7308063723715528012768781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4872042482477018675179187 7308063723715528012768781)
            ·
              refine ⟨2740523896393323004788293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7308063723715528012768781 2740523896393323004788293)
              ·
                refine ⟨513848230573748063397805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2740523896393323004788293 513848230573748063397805)
                ·
                  refine ⟨192693086465155523774177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 513848230573748063397805 192693086465155523774177)
                  ·
                    rfl

theorem cell20_422177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_422177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422177 prefixEnd_422177 := by exact prefixLift 422177
  have htrace : WordTrace (prefixWord ++ tailWord_422177) baseStart_422177 baseEnd_422177 := by
    simpa [prefixWord, tailWord_422177, baseEnd_422177] using wordTrace_append hprefix tailTrace_422177
  have hstable : (prefixWord ++ tailWord_422177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422177).length < 2 ^ (prefixWord ++ tailWord_422177).sum := by decide
  have hdescent : baseEnd_422177 < baseStart_422177 := by decide
  rcases family_descends (prefixWord ++ tailWord_422177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422180 : List Nat := [2, 3, 1, 3, 1, 3, 1, 4, 2]
def baseStart_422180 : Nat := 118140960795 + 422180 * 2 ^ 59
def prefixEnd_422180 : Nat := 4983230072969 + 3 ^ 40 * 422180 * 2
def baseEnd_422180 : Nat := 192694455746900846674165

theorem tailTrace_422180 : CollatzResearch.WordTrace tailWord_422180 prefixEnd_422180 192694455746900846674165 := by
  unfold tailWord_422180
  simp only [CollatzResearch.WordTrace]
  refine ⟨7699084805260718724363997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10265446407014291632485329 7699084805260718724363997)
  ·
    refine ⟨2887156801972769521636499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7699084805260718724363997 2887156801972769521636499)
    ·
      refine ⟨4330735202959154282454749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2887156801972769521636499 4330735202959154282454749)
      ·
        refine ⟨1624025701109682855920531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4330735202959154282454749 1624025701109682855920531)
        ·
          refine ⟨2436038551664524283880797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1624025701109682855920531 2436038551664524283880797)
          ·
            refine ⟨913514456874196606455299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2436038551664524283880797 913514456874196606455299)
            ·
              refine ⟨1370271685311294909682949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913514456874196606455299 1370271685311294909682949)
              ·
                refine ⟨256925940995867795565553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1370271685311294909682949 256925940995867795565553)
                ·
                  refine ⟨192694455746900846674165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256925940995867795565553 192694455746900846674165)
                  ·
                    rfl

theorem cell20_422180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_422180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422180 prefixEnd_422180 := by exact prefixLift 422180
  have htrace : WordTrace (prefixWord ++ tailWord_422180) baseStart_422180 baseEnd_422180 := by
    simpa [prefixWord, tailWord_422180, baseEnd_422180] using wordTrace_append hprefix tailTrace_422180
  have hstable : (prefixWord ++ tailWord_422180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422180).length < 2 ^ (prefixWord ++ tailWord_422180).sum := by decide
  have hdescent : baseEnd_422180 < baseStart_422180 := by decide
  rcases family_descends (prefixWord ++ tailWord_422180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422183 : List Nat := [1, 1, 8, 1, 1, 2, 1, 5]
def baseStart_422183 : Nat := 118140960795 + 422183 * 2 ^ 59
def prefixEnd_422183 : Nat := 4983230072969 + 3 ^ 40 * 422183 * 2
def baseEnd_422183 : Nat := 64231941676215389858051

theorem tailTrace_422183 : CollatzResearch.WordTrace tailWord_422183 prefixEnd_422183 64231941676215389858051 := by
  unfold tailWord_422183
  simp only [CollatzResearch.WordTrace]
  refine ⟨15398279029510568961087203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10265519353007045974058135 15398279029510568961087203)
  ·
    refine ⟨23097418544265853441630805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15398279029510568961087203 23097418544265853441630805)
    ·
      refine ⟨270672873565615470019111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 23097418544265853441630805 270672873565615470019111)
      ·
        refine ⟨406009310348423205028667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270672873565615470019111 406009310348423205028667)
        ·
          refine ⟨609013965522634807543001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406009310348423205028667 609013965522634807543001)
          ·
            refine ⟨456760474141976105657251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609013965522634807543001 456760474141976105657251)
            ·
              refine ⟨685140711212964158485877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456760474141976105657251 685140711212964158485877)
              ·
                refine ⟨64231941676215389858051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 685140711212964158485877 64231941676215389858051)
                ·
                  rfl

theorem cell20_422183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 5].length) (baseStart_422183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422183 prefixEnd_422183 := by exact prefixLift 422183
  have htrace : WordTrace (prefixWord ++ tailWord_422183) baseStart_422183 baseEnd_422183 := by
    simpa [prefixWord, tailWord_422183, baseEnd_422183] using wordTrace_append hprefix tailTrace_422183
  have hstable : (prefixWord ++ tailWord_422183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422183).length < 2 ^ (prefixWord ++ tailWord_422183).sum := by decide
  have hdescent : baseEnd_422183 < baseStart_422183 := by decide
  rcases family_descends (prefixWord ++ tailWord_422183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422191 : List Nat := [1, 1, 2, 1, 2, 1, 7, 5]
def baseStart_422191 : Nat := 118140960795 + 422191 * 2 ^ 59
def prefixEnd_422191 : Nat := 4983230072969 + 3 ^ 40 * 422191 * 2
def baseEnd_422191 : Nat := 64233158815544565769151

theorem tailTrace_422191 : CollatzResearch.WordTrace tailWord_422191 prefixEnd_422191 64233158815544565769151 := by
  unfold tailWord_422191
  simp only [CollatzResearch.WordTrace]
  refine ⟨15398570813481586327378427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10265713875654390884918951 15398570813481586327378427)
  ·
    refine ⟨23097856220222379491067641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15398570813481586327378427 23097856220222379491067641)
    ·
      refine ⟨17323392165166784618300731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23097856220222379491067641 17323392165166784618300731)
      ·
        refine ⟨25985088247750176927451097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17323392165166784618300731 25985088247750176927451097)
        ·
          refine ⟨19488816185812632695588323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25985088247750176927451097 19488816185812632695588323)
          ·
            refine ⟨29233224278718949043382485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19488816185812632695588323 29233224278718949043382485)
            ·
              refine ⟨685153694032475368204277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 29233224278718949043382485 685153694032475368204277)
              ·
                refine ⟨64233158815544565769151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 685153694032475368204277 64233158815544565769151)
                ·
                  rfl

theorem cell20_422191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 5].length) (baseStart_422191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422191 prefixEnd_422191 := by exact prefixLift 422191
  have htrace : WordTrace (prefixWord ++ tailWord_422191) baseStart_422191 baseEnd_422191 := by
    simpa [prefixWord, tailWord_422191, baseEnd_422191] using wordTrace_append hprefix tailTrace_422191
  have hstable : (prefixWord ++ tailWord_422191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422191).length < 2 ^ (prefixWord ++ tailWord_422191).sum := by decide
  have hdescent : baseEnd_422191 < baseStart_422191 := by decide
  rcases family_descends (prefixWord ++ tailWord_422191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422201 : List Nat := [1, 2, 1, 6, 1, 2, 1, 2, 4]
def baseStart_422201 : Nat := 118140960795 + 422201 * 2 ^ 59
def prefixEnd_422201 : Nat := 4983230072969 + 3 ^ 40 * 422201 * 2
def baseEnd_422201 : Nat := 192704040719118106974079

theorem tailTrace_422201 : CollatzResearch.WordTrace tailWord_422201 prefixEnd_422201 192704040719118106974079 := by
  unfold tailWord_422201
  simp only [CollatzResearch.WordTrace]
  refine ⟨15398935543445358035242457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10265957028963572023494971 15398935543445358035242457)
  ·
    refine ⟨11549201657584018526431843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15398935543445358035242457 11549201657584018526431843)
    ·
      refine ⟨17323802486376027789647765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11549201657584018526431843 17323802486376027789647765)
      ·
        refine ⟨812053241548876302639739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17323802486376027789647765 812053241548876302639739)
        ·
          refine ⟨1218079862323314453959609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812053241548876302639739 1218079862323314453959609)
          ·
            refine ⟨913559896742485840469707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1218079862323314453959609 913559896742485840469707)
            ·
              refine ⟨1370339845113728760704561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913559896742485840469707 1370339845113728760704561)
              ·
                refine ⟨1027754883835296570528421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1370339845113728760704561 1027754883835296570528421)
                ·
                  refine ⟨192704040719118106974079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1027754883835296570528421 192704040719118106974079)
                  ·
                    rfl

theorem cell20_422201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_422201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422201 prefixEnd_422201 := by exact prefixLift 422201
  have htrace : WordTrace (prefixWord ++ tailWord_422201) baseStart_422201 baseEnd_422201 := by
    simpa [prefixWord, tailWord_422201, baseEnd_422201] using wordTrace_append hprefix tailTrace_422201
  have hstable : (prefixWord ++ tailWord_422201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422201).length < 2 ^ (prefixWord ++ tailWord_422201).sum := by decide
  have hdescent : baseEnd_422201 < baseStart_422201 := by decide
  rcases family_descends (prefixWord ++ tailWord_422201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422239 : List Nat := [1, 1, 2, 3, 1, 2, 4, 4, 2]
def baseStart_422239 : Nat := 118140960795 + 422239 * 2 ^ 59
def prefixEnd_422239 : Nat := 4983230072969 + 3 ^ 40 * 422239 * 2
def baseEnd_422239 : Nat := 192721384954558863707257

theorem tailTrace_422239 : CollatzResearch.WordTrace tailWord_422239 prefixEnd_422239 192721384954558863707257 := by
  unfold tailWord_422239
  simp only [CollatzResearch.WordTrace]
  refine ⟨15400321517307690525125771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10266881011538460350083847 15400321517307690525125771)
  ·
    refine ⟨23100482275961535787688657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15400321517307690525125771 23100482275961535787688657)
    ·
      refine ⟨17325361706971151840766493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23100482275961535787688657 17325361706971151840766493)
      ·
        refine ⟨6497010640114181940287435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17325361706971151840766493 6497010640114181940287435)
        ·
          refine ⟨9745515960171272910431153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6497010640114181940287435 9745515960171272910431153)
          ·
            refine ⟨7309136970128454682823365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9745515960171272910431153 7309136970128454682823365)
            ·
              refine ⟨1370463181899085253029381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7309136970128454682823365 1370463181899085253029381)
              ·
                refine ⟨256961846606078484943009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1370463181899085253029381 256961846606078484943009)
                ·
                  refine ⟨192721384954558863707257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256961846606078484943009 192721384954558863707257)
                  ·
                    rfl

theorem cell20_422239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 2].length) (baseStart_422239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422239 prefixEnd_422239 := by exact prefixLift 422239
  have htrace : WordTrace (prefixWord ++ tailWord_422239) baseStart_422239 baseEnd_422239 := by
    simpa [prefixWord, tailWord_422239, baseEnd_422239] using wordTrace_append hprefix tailTrace_422239
  have hstable : (prefixWord ++ tailWord_422239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422239).length < 2 ^ (prefixWord ++ tailWord_422239).sum := by decide
  have hdescent : baseEnd_422239 < baseStart_422239 := by decide
  rcases family_descends (prefixWord ++ tailWord_422239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422267 : List Nat := [1, 1, 1, 1, 1, 8, 1, 6]
def baseStart_422267 : Nat := 118140960795 + 422267 * 2 ^ 59
def prefixEnd_422267 : Nat := 4983230072969 + 3 ^ 40 * 422267 * 2
def baseEnd_422267 : Nat := 64244721639171736924603

theorem tailTrace_422267 : CollatzResearch.WordTrace tailWord_422267 prefixEnd_422267 64244721639171736924603 := by
  unfold tailWord_422267
  simp only [CollatzResearch.WordTrace]
  refine ⟨15401342761206251307145055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10267561840804167538096703 15401342761206251307145055)
  ·
    refine ⟨23102014141809376960717583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15401342761206251307145055 23102014141809376960717583)
    ·
      refine ⟨34653021212714065441076375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23102014141809376960717583 34653021212714065441076375)
      ·
        refine ⟨51979531819071098161614563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34653021212714065441076375 51979531819071098161614563)
        ·
          refine ⟨77969297728606647242421845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51979531819071098161614563 77969297728606647242421845)
          ·
            refine ⟨913702707757109147372131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 77969297728606647242421845 913702707757109147372131)
            ·
              refine ⟨1370554061635663721058197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913702707757109147372131 1370554061635663721058197)
              ·
                refine ⟨64244721639171736924603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1370554061635663721058197 64244721639171736924603)
                ·
                  rfl

theorem cell20_422267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 6].length) (baseStart_422267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422267 prefixEnd_422267 := by exact prefixLift 422267
  have htrace : WordTrace (prefixWord ++ tailWord_422267) baseStart_422267 baseEnd_422267 := by
    simpa [prefixWord, tailWord_422267, baseEnd_422267] using wordTrace_append hprefix tailTrace_422267
  have hstable : (prefixWord ++ tailWord_422267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422267).length < 2 ^ (prefixWord ++ tailWord_422267).sum := by decide
  have hdescent : baseEnd_422267 < baseStart_422267 := by decide
  rcases family_descends (prefixWord ++ tailWord_422267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422273 : List Nat := [1, 2, 4, 3, 1, 3, 1, 3, 2]
def baseStart_422273 : Nat := 118140960795 + 422273 * 2 ^ 59
def prefixEnd_422273 : Nat := 4983230072969 + 3 ^ 40 * 422273 * 2
def baseEnd_422273 : Nat := 192736903481005856573785

theorem tailTrace_422273 : CollatzResearch.WordTrace tailWord_422273 prefixEnd_422273 192736903481005856573785 := by
  unfold tailWord_422273
  simp only [CollatzResearch.WordTrace]
  refine ⟨15401561599184514331863473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10267707732789676221242315 15401561599184514331863473)
  ·
    refine ⟨11551171199388385748897605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15401561599184514331863473 11551171199388385748897605)
    ·
      refine ⟨2165844599885322327918301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11551171199388385748897605 2165844599885322327918301)
      ·
        refine ⟨812191724956995872969363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2165844599885322327918301 812191724956995872969363)
        ·
          refine ⟨1218287587435493809454045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812191724956995872969363 1218287587435493809454045)
          ·
            refine ⟨456857845288310178545267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1218287587435493809454045 456857845288310178545267)
            ·
              refine ⟨685286767932465267817901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456857845288310178545267 685286767932465267817901)
              ·
                refine ⟨256982537974674475431713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 685286767932465267817901 256982537974674475431713)
                ·
                  refine ⟨192736903481005856573785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256982537974674475431713 192736903481005856573785)
                  ·
                    rfl

theorem cell20_422273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 2].length) (baseStart_422273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422273 prefixEnd_422273 := by exact prefixLift 422273
  have htrace : WordTrace (prefixWord ++ tailWord_422273) baseStart_422273 baseEnd_422273 := by
    simpa [prefixWord, tailWord_422273, baseEnd_422273] using wordTrace_append hprefix tailTrace_422273
  have hstable : (prefixWord ++ tailWord_422273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422273).length < 2 ^ (prefixWord ++ tailWord_422273).sum := by decide
  have hdescent : baseEnd_422273 < baseStart_422273 := by decide
  rcases family_descends (prefixWord ++ tailWord_422273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422308 : List Nat := [2, 3, 1, 2, 1, 1, 6, 1, 3]
def baseStart_422308 : Nat := 118140960795 + 422308 * 2 ^ 59
def prefixEnd_422308 : Nat := 4983230072969 + 3 ^ 40 * 422308 * 2
def baseEnd_422308 : Nat := 192752878434701290406975

theorem tailTrace_422308 : CollatzResearch.WordTrace tailWord_422308 prefixEnd_422308 192752878434701290406975 := by
  unfold tailWord_422308
  simp only [CollatzResearch.WordTrace]
  refine ⟨7701419077028857654693789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10268558769371810206258385 7701419077028857654693789)
  ·
    refine ⟨2888032153885821620510171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7701419077028857654693789 2888032153885821620510171)
    ·
      refine ⟨4332048230828732430765257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2888032153885821620510171 4332048230828732430765257)
      ·
        refine ⟨3249036173121549323073943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4332048230828732430765257 3249036173121549323073943)
        ·
          refine ⟨4873554259682323984610915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3249036173121549323073943 4873554259682323984610915)
          ·
            refine ⟨7310331389523485976916373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4873554259682323984610915 7310331389523485976916373)
            ·
              refine ⟨342671783883913405167955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7310331389523485976916373 342671783883913405167955)
              ·
                refine ⟨514007675825870107751933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342671783883913405167955 514007675825870107751933)
                ·
                  refine ⟨192752878434701290406975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 514007675825870107751933 192752878434701290406975)
                  ·
                    rfl

theorem cell20_422308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_422308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422308 prefixEnd_422308 := by exact prefixLift 422308
  have htrace : WordTrace (prefixWord ++ tailWord_422308) baseStart_422308 baseEnd_422308 := by
    simpa [prefixWord, tailWord_422308, baseEnd_422308] using wordTrace_append hprefix tailTrace_422308
  have hstable : (prefixWord ++ tailWord_422308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422308).length < 2 ^ (prefixWord ++ tailWord_422308).sum := by decide
  have hdescent : baseEnd_422308 < baseStart_422308 := by decide
  rcases family_descends (prefixWord ++ tailWord_422308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422367 : List Nat := [1, 1, 2, 3, 3, 2, 2, 3, 3]
def baseStart_422367 : Nat := 118140960795 + 422367 * 2 ^ 59
def prefixEnd_422367 : Nat := 4983230072969 + 3 ^ 40 * 422367 * 2
def baseEnd_422367 : Nat := 192779807642359307440067

theorem tailTrace_422367 : CollatzResearch.WordTrace tailWord_422367 prefixEnd_422367 192779807642359307440067 := by
  unfold tailWord_422367
  simp only [CollatzResearch.WordTrace]
  refine ⟨15404990060843968385785355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10269993373895978923856903 15404990060843968385785355)
  ·
    refine ⟨23107485091265952578678033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15404990060843968385785355 23107485091265952578678033)
    ·
      refine ⟨17330613818449464434008525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23107485091265952578678033 17330613818449464434008525)
      ·
        refine ⟨6498980181918549162753197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17330613818449464434008525 6498980181918549162753197)
        ·
          refine ⟨2437117568219455936032449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6498980181918549162753197 2437117568219455936032449)
          ·
            refine ⟨1827838176164591952024337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2437117568219455936032449 1827838176164591952024337)
            ·
              refine ⟨1370878632123443964018253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1827838176164591952024337 1370878632123443964018253)
              ·
                refine ⟨514079487046291486506845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1370878632123443964018253 514079487046291486506845)
                ·
                  refine ⟨192779807642359307440067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 514079487046291486506845 192779807642359307440067)
                  ·
                    rfl

theorem cell20_422367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 3].length) (baseStart_422367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422367 prefixEnd_422367 := by exact prefixLift 422367
  have htrace : WordTrace (prefixWord ++ tailWord_422367) baseStart_422367 baseEnd_422367 := by
    simpa [prefixWord, tailWord_422367, baseEnd_422367] using wordTrace_append hprefix tailTrace_422367
  have hstable : (prefixWord ++ tailWord_422367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422367).length < 2 ^ (prefixWord ++ tailWord_422367).sum := by decide
  have hdescent : baseEnd_422367 < baseStart_422367 := by decide
  rcases family_descends (prefixWord ++ tailWord_422367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422405 : List Nat := [1, 3, 1, 1, 2, 2, 5, 2, 3]
def baseStart_422405 : Nat := 118140960795 + 422405 * 2 ^ 59
def prefixEnd_422405 : Nat := 4983230072969 + 3 ^ 40 * 422405 * 2
def baseEnd_422405 : Nat := 192797151877800064173245

theorem tailTrace_422405 : CollatzResearch.WordTrace tailWord_422405 prefixEnd_422405 192797151877800064173245 := by
  unfold tailWord_422405
  simp only [CollatzResearch.WordTrace]
  refine ⟨15406376034706300875668669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10270917356470867250445779 15406376034706300875668669)
  ·
    refine ⟨5777391013014862828375751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15406376034706300875668669 5777391013014862828375751)
    ·
      refine ⟨8666086519522294242563627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5777391013014862828375751 8666086519522294242563627)
      ·
        refine ⟨12999129779283441363845441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8666086519522294242563627 12999129779283441363845441)
        ·
          refine ⟨9749347334462581022884081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12999129779283441363845441 9749347334462581022884081)
          ·
            refine ⟨7312010500846935767163061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9749347334462581022884081 7312010500846935767163061)
            ·
              refine ⟨685500984454400228171537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7312010500846935767163061 685500984454400228171537)
              ·
                refine ⟨514125738340800171128653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 685500984454400228171537 514125738340800171128653)
                ·
                  refine ⟨192797151877800064173245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 514125738340800171128653 192797151877800064173245)
                  ·
                    rfl

theorem cell20_422405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_422405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422405 prefixEnd_422405 := by exact prefixLift 422405
  have htrace : WordTrace (prefixWord ++ tailWord_422405) baseStart_422405 baseEnd_422405 := by
    simpa [prefixWord, tailWord_422405, baseEnd_422405] using wordTrace_append hprefix tailTrace_422405
  have hstable : (prefixWord ++ tailWord_422405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422405).length < 2 ^ (prefixWord ++ tailWord_422405).sum := by decide
  have hdescent : baseEnd_422405 < baseStart_422405 := by decide
  rcases family_descends (prefixWord ++ tailWord_422405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422412 : List Nat := [2, 2, 1, 2, 4, 1, 1, 3, 4]
def baseStart_422412 : Nat := 118140960795 + 422412 * 2 ^ 59
def prefixEnd_422412 : Nat := 4983230072969 + 3 ^ 40 * 422412 * 2
def baseEnd_422412 : Nat := 192800346868539150939883

theorem tailTrace_422412 : CollatzResearch.WordTrace tailWord_422412 prefixEnd_422412 192800346868539150939883 := by
  unfold tailWord_422412
  simp only [CollatzResearch.WordTrace]
  refine ⟨7703315672840470535586745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10271087563787294047448993 7703315672840470535586745)
  ·
    refine ⟨5777486754630352901690059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7703315672840470535586745 5777486754630352901690059)
    ·
      refine ⟨8666230131945529352535089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5777486754630352901690059 8666230131945529352535089)
      ·
        refine ⟨6499672598959147014401317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8666230131945529352535089 6499672598959147014401317)
        ·
          refine ⟨1218688612304840065200247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6499672598959147014401317 1218688612304840065200247)
          ·
            refine ⟨1828032918457260097800371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1218688612304840065200247 1828032918457260097800371)
            ·
              refine ⟨2742049377685890146700557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1828032918457260097800371 2742049377685890146700557)
              ·
                refine ⟨1028268516632208805012709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2742049377685890146700557 1028268516632208805012709)
                ·
                  refine ⟨192800346868539150939883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1028268516632208805012709 192800346868539150939883)
                  ·
                    rfl

theorem cell20_422412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_422412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422412 prefixEnd_422412 := by exact prefixLift 422412
  have htrace : WordTrace (prefixWord ++ tailWord_422412) baseStart_422412 baseEnd_422412 := by
    simpa [prefixWord, tailWord_422412, baseEnd_422412] using wordTrace_append hprefix tailTrace_422412
  have hstable : (prefixWord ++ tailWord_422412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422412).length < 2 ^ (prefixWord ++ tailWord_422412).sum := by decide
  have hdescent : baseEnd_422412 < baseStart_422412 := by decide
  rcases family_descends (prefixWord ++ tailWord_422412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422432 : List Nat := [2, 1, 1, 6, 3, 1, 2, 4]
def baseStart_422432 : Nat := 118140960795 + 422432 * 2 ^ 59
def prefixEnd_422432 : Nat := 4983230072969 + 3 ^ 40 * 422432 * 2
def baseEnd_422432 : Nat := 64269825137835990091045

theorem tailTrace_422432 : CollatzResearch.WordTrace tailWord_422432 prefixEnd_422432 64269825137835990091045 := by
  unfold tailWord_422432
  simp only [CollatzResearch.WordTrace]
  refine ⟨7703680402804242243450775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10271573870405656324601033 7703680402804242243450775)
  ·
    refine ⟨11555520604206363365176163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7703680402804242243450775 11555520604206363365176163)
    ·
      refine ⟨17333280906309545047764245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11555520604206363365176163 17333280906309545047764245)
      ·
        refine ⟨812497542483259924113949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17333280906309545047764245 812497542483259924113949)
        ·
          refine ⟨304686578431222471542731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 812497542483259924113949 304686578431222471542731)
          ·
            refine ⟨457029867646833707314097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304686578431222471542731 457029867646833707314097)
            ·
              refine ⟨342772400735125280485573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457029867646833707314097 342772400735125280485573)
              ·
                refine ⟨64269825137835990091045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 342772400735125280485573 64269825137835990091045)
                ·
                  rfl

theorem cell20_422432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 4].length) (baseStart_422432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422432 prefixEnd_422432 := by exact prefixLift 422432
  have htrace : WordTrace (prefixWord ++ tailWord_422432) baseStart_422432 baseEnd_422432 := by
    simpa [prefixWord, tailWord_422432, baseEnd_422432] using wordTrace_append hprefix tailTrace_422432
  have hstable : (prefixWord ++ tailWord_422432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422432).length < 2 ^ (prefixWord ++ tailWord_422432).sum := by decide
  have hdescent : baseEnd_422432 < baseStart_422432 := by decide
  rcases family_descends (prefixWord ++ tailWord_422432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422464 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 5]
def baseStart_422464 : Nat := 118140960795 + 422464 * 2 ^ 59
def prefixEnd_422464 : Nat := 4983230072969 + 3 ^ 40 * 422464 * 2
def baseEnd_422464 : Nat := 192824081085458081206337

theorem tailTrace_422464 : CollatzResearch.WordTrace tailWord_422464 prefixEnd_422464 192824081085458081206337 := by
  unfold tailWord_422464
  simp only [CollatzResearch.WordTrace]
  refine ⟨7704263970746276976033223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10272351960995035968044297 7704263970746276976033223)
  ·
    refine ⟨11556395956119415464049835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7704263970746276976033223 11556395956119415464049835)
    ·
      refine ⟨17334593934179123196074753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11556395956119415464049835 17334593934179123196074753)
      ·
        refine ⟨13000945450634342397056065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17334593934179123196074753 13000945450634342397056065)
        ·
          refine ⟨9750709087975756797792049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13000945450634342397056065 9750709087975756797792049)
          ·
            refine ⟨7313031815981817598344037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9750709087975756797792049 7313031815981817598344037)
            ·
              refine ⟨1371193465496590799689507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7313031815981817598344037 1371193465496590799689507)
              ·
                refine ⟨2056790198244886199534261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371193465496590799689507 2056790198244886199534261)
                ·
                  refine ⟨192824081085458081206337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2056790198244886199534261 192824081085458081206337)
                  ·
                    rfl

theorem cell20_422464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_422464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422464 prefixEnd_422464 := by exact prefixLift 422464
  have htrace : WordTrace (prefixWord ++ tailWord_422464) baseStart_422464 baseEnd_422464 := by
    simpa [prefixWord, tailWord_422464, baseEnd_422464] using wordTrace_append hprefix tailTrace_422464
  have hstable : (prefixWord ++ tailWord_422464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422464).length < 2 ^ (prefixWord ++ tailWord_422464).sum := by decide
  have hdescent : baseEnd_422464 < baseStart_422464 := by decide
  rcases family_descends (prefixWord ++ tailWord_422464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422477 : List Nat := [1, 6, 1, 1, 2, 1, 4, 1, 3]
def baseStart_422477 : Nat := 118140960795 + 422477 * 2 ^ 59
def prefixEnd_422477 : Nat := 4983230072969 + 3 ^ 40 * 422477 * 2
def baseEnd_422477 : Nat := 192830014639687813772951

theorem tailTrace_422477 : CollatzResearch.WordTrace tailWord_422477 prefixEnd_422477 192830014639687813772951 := by
  unfold tailWord_422477
  simp only [CollatzResearch.WordTrace]
  refine ⟨15409002090445457172289685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10272668060296971448193123 15409002090445457172289685)
  ·
    refine ⟨722296972989630804951079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15409002090445457172289685 722296972989630804951079)
    ·
      refine ⟨1083445459484446207426619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 722296972989630804951079 1083445459484446207426619)
      ·
        refine ⟨1625168189226669311139929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1083445459484446207426619 1625168189226669311139929)
        ·
          refine ⟨1218876141920001983354947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1625168189226669311139929 1218876141920001983354947)
          ·
            refine ⟨1828314212880002975032421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1218876141920001983354947 1828314212880002975032421)
            ·
              refine ⟨342808914915000557818579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1828314212880002975032421 342808914915000557818579)
              ·
                refine ⟨514213372372500836727869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342808914915000557818579 514213372372500836727869)
                ·
                  refine ⟨192830014639687813772951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 514213372372500836727869 192830014639687813772951)
                  ·
                    rfl

theorem cell20_422477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_422477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422477 prefixEnd_422477 := by exact prefixLift 422477
  have htrace : WordTrace (prefixWord ++ tailWord_422477) baseStart_422477 baseEnd_422477 := by
    simpa [prefixWord, tailWord_422477, baseEnd_422477] using wordTrace_append hprefix tailTrace_422477
  have hstable : (prefixWord ++ tailWord_422477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422477).length < 2 ^ (prefixWord ++ tailWord_422477).sum := by decide
  have hdescent : baseEnd_422477 < baseStart_422477 := by decide
  rcases family_descends (prefixWord ++ tailWord_422477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422481 : List Nat := [1, 2, 2, 1, 3, 4, 1, 3, 3]
def baseStart_422481 : Nat := 118140960795 + 422481 * 2 ^ 59
def prefixEnd_422481 : Nat := 4983230072969 + 3 ^ 40 * 422481 * 2
def baseEnd_422481 : Nat := 192831840348681577639601

theorem tailTrace_422481 : CollatzResearch.WordTrace tailWord_422481 prefixEnd_422481 192831840348681577639601 := by
  unfold tailWord_422481
  simp only [CollatzResearch.WordTrace]
  refine ⟨15409147982430965855435297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10272765321620643903623531 15409147982430965855435297)
  ·
    refine ⟨11556860986823224391576473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15409147982430965855435297 11556860986823224391576473)
    ·
      refine ⟨8667645740117418293682355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11556860986823224391576473 8667645740117418293682355)
      ·
        refine ⟨13001468610176127440523533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8667645740117418293682355 13001468610176127440523533)
        ·
          refine ⟨4875550728816047790196325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13001468610176127440523533 4875550728816047790196325)
          ·
            refine ⟨914165761653008960661811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4875550728816047790196325 914165761653008960661811)
            ·
              refine ⟨1371248642479513440992717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 914165761653008960661811 1371248642479513440992717)
              ·
                refine ⟨514218240929817540372269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1371248642479513440992717 514218240929817540372269)
                ·
                  refine ⟨192831840348681577639601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 514218240929817540372269 192831840348681577639601)
                  ·
                    rfl

theorem cell20_422481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_422481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422481 prefixEnd_422481 := by exact prefixLift 422481
  have htrace : WordTrace (prefixWord ++ tailWord_422481) baseStart_422481 baseEnd_422481 := by
    simpa [prefixWord, tailWord_422481, baseEnd_422481] using wordTrace_append hprefix tailTrace_422481
  have hstable : (prefixWord ++ tailWord_422481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422481).length < 2 ^ (prefixWord ++ tailWord_422481).sum := by decide
  have hdescent : baseEnd_422481 < baseStart_422481 := by decide
  rcases family_descends (prefixWord ++ tailWord_422481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422518 : List Nat := [5, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_422518 : Nat := 118140960795 + 422518 * 2 ^ 59
def prefixEnd_422518 : Nat := 4983230072969 + 3 ^ 40 * 422518 * 2
def baseEnd_422518 : Nat := 192848728156873893406117

theorem tailTrace_422518 : CollatzResearch.WordTrace tailWord_422518 prefixEnd_422518 192848728156873893406117 := by
  unfold tailWord_422518
  simp only [CollatzResearch.WordTrace]
  refine ⟨963156092706057573408263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10273664988864614116354805 963156092706057573408263)
  ·
    refine ⟨1444734139059086360112395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 963156092706057573408263 1444734139059086360112395)
    ·
      refine ⟨2167101208588629540168593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1444734139059086360112395 2167101208588629540168593)
      ·
        refine ⟨1625325906441472155126445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2167101208588629540168593 1625325906441472155126445)
        ·
          refine ⟨609497214915552058172417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1625325906441472155126445 609497214915552058172417)
          ·
            refine ⟨457122911186664043629313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609497214915552058172417 457122911186664043629313)
            ·
              refine ⟨342842183389998032721985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457122911186664043629313 342842183389998032721985)
              ·
                refine ⟨257131637542498524541489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342842183389998032721985 257131637542498524541489)
                ·
                  refine ⟨192848728156873893406117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257131637542498524541489 192848728156873893406117)
                  ·
                    rfl

theorem cell20_422518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_422518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422518 prefixEnd_422518 := by exact prefixLift 422518
  have htrace : WordTrace (prefixWord ++ tailWord_422518) baseStart_422518 baseEnd_422518 := by
    simpa [prefixWord, tailWord_422518, baseEnd_422518] using wordTrace_append hprefix tailTrace_422518
  have hstable : (prefixWord ++ tailWord_422518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422518).length < 2 ^ (prefixWord ++ tailWord_422518).sum := by decide
  have hdescent : baseEnd_422518 < baseStart_422518 := by decide
  rcases family_descends (prefixWord ++ tailWord_422518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422533 : List Nat := [1, 3, 1, 1, 4, 2, 3, 5]
def baseStart_422533 : Nat := 118140960795 + 422533 * 2 ^ 59
def prefixEnd_422533 : Nat := 4983230072969 + 3 ^ 40 * 422533 * 2
def baseEnd_422533 : Nat := 64285191521866835968685

theorem tailTrace_422533 : CollatzResearch.WordTrace tailWord_422533 prefixEnd_422533 64285191521866835968685 := by
  unfold tailWord_422533
  simp only [CollatzResearch.WordTrace]
  refine ⟨15411044578242578736328253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10274029718828385824218835 15411044578242578736328253)
  ·
    refine ⟨5779141716840967026123095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15411044578242578736328253 5779141716840967026123095)
    ·
      refine ⟨8668712575261450539184643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5779141716840967026123095 8668712575261450539184643)
      ·
        refine ⟨13003068862892175808776965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8668712575261450539184643 13003068862892175808776965)
        ·
          refine ⟨2438075411792282964145681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13003068862892175808776965 2438075411792282964145681)
          ·
            refine ⟨1828556558844212223109261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2438075411792282964145681 1828556558844212223109261)
            ·
              refine ⟨685708709566579583665973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1828556558844212223109261 685708709566579583665973)
              ·
                refine ⟨64285191521866835968685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 685708709566579583665973 64285191521866835968685)
                ·
                  rfl

theorem cell20_422533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 5].length) (baseStart_422533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422533 prefixEnd_422533 := by exact prefixLift 422533
  have htrace : WordTrace (prefixWord ++ tailWord_422533) baseStart_422533 baseEnd_422533 := by
    simpa [prefixWord, tailWord_422533, baseEnd_422533] using wordTrace_append hprefix tailTrace_422533
  have hstable : (prefixWord ++ tailWord_422533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422533).length < 2 ^ (prefixWord ++ tailWord_422533).sum := by decide
  have hdescent : baseEnd_422533 < baseStart_422533 := by decide
  rcases family_descends (prefixWord ++ tailWord_422533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422547 : List Nat := [1, 1, 1, 2, 1, 2, 2, 6, 4]
def baseStart_422547 : Nat := 118140960795 + 422547 * 2 ^ 59
def prefixEnd_422547 : Nat := 4983230072969 + 3 ^ 40 * 422547 * 2
def baseEnd_422547 : Nat := 192861964547078681439331

theorem tailTrace_422547 : CollatzResearch.WordTrace tailWord_422547 prefixEnd_422547 192861964547078681439331 := by
  unfold tailWord_422547
  simp only [CollatzResearch.WordTrace]
  refine ⟨15411555200191859127337895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10274370133461239418225263 15411555200191859127337895)
  ·
    refine ⟨23117332800287788691006843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15411555200191859127337895 23117332800287788691006843)
    ·
      refine ⟨34675999200431683036510265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23117332800287788691006843 34675999200431683036510265)
      ·
        refine ⟨26006999400323762277382699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34675999200431683036510265 26006999400323762277382699)
        ·
          refine ⟨39010499100485643416074049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26006999400323762277382699 39010499100485643416074049)
          ·
            refine ⟨29257874325364232562055537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39010499100485643416074049 29257874325364232562055537)
            ·
              refine ⟨21943405744023174421541653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29257874325364232562055537 21943405744023174421541653)
              ·
                refine ⟨1028597144251086301009765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21943405744023174421541653 1028597144251086301009765)
                ·
                  refine ⟨192861964547078681439331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1028597144251086301009765 192861964547078681439331)
                  ·
                    rfl

theorem cell20_422547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_422547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422547 prefixEnd_422547 := by exact prefixLift 422547
  have htrace : WordTrace (prefixWord ++ tailWord_422547) baseStart_422547 baseEnd_422547 := by
    simpa [prefixWord, tailWord_422547, baseEnd_422547] using wordTrace_append hprefix tailTrace_422547
  have hstable : (prefixWord ++ tailWord_422547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422547).length < 2 ^ (prefixWord ++ tailWord_422547).sum := by decide
  have hdescent : baseEnd_422547 < baseStart_422547 := by decide
  rcases family_descends (prefixWord ++ tailWord_422547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422560 : List Nat := [2, 1, 1, 4, 4, 1, 2, 3, 2]
def baseStart_422560 : Nat := 118140960795 + 422560 * 2 ^ 59
def prefixEnd_422560 : Nat := 4983230072969 + 3 ^ 40 * 422560 * 2
def baseEnd_422560 : Nat := 192867898101308414005945

theorem tailTrace_422560 : CollatzResearch.WordTrace tailWord_422560 prefixEnd_422560 192867898101308414005945 := by
  unfold tailWord_422560
  simp only [CollatzResearch.WordTrace]
  refine ⟨7706014674572381173780567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10274686232763174898374089 7706014674572381173780567)
  ·
    refine ⟨11559022011858571760670851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7706014674572381173780567 11559022011858571760670851)
    ·
      refine ⟨17338533017787857641006277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11559022011858571760670851 17338533017787857641006277)
      ·
        refine ⟨3250974940835223307688677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17338533017787857641006277 3250974940835223307688677)
        ·
          refine ⟨609557801406604370191627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3250974940835223307688677 609557801406604370191627)
          ·
            refine ⟨914336702109906555287441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609557801406604370191627 914336702109906555287441)
            ·
              refine ⟨685752526582429916465581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 914336702109906555287441 685752526582429916465581)
              ·
                refine ⟨257157197468411218674593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 685752526582429916465581 257157197468411218674593)
                ·
                  refine ⟨192867898101308414005945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257157197468411218674593 192867898101308414005945)
                  ·
                    rfl

theorem cell20_422560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 2].length) (baseStart_422560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422560 prefixEnd_422560 := by exact prefixLift 422560
  have htrace : WordTrace (prefixWord ++ tailWord_422560) baseStart_422560 baseEnd_422560 := by
    simpa [prefixWord, tailWord_422560, baseEnd_422560] using wordTrace_append hprefix tailTrace_422560
  have hstable : (prefixWord ++ tailWord_422560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422560).length < 2 ^ (prefixWord ++ tailWord_422560).sum := by decide
  have hdescent : baseEnd_422560 < baseStart_422560 := by decide
  rcases family_descends (prefixWord ++ tailWord_422560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422570 : List Nat := [3, 1, 5, 2, 1, 2, 1, 2, 3]
def baseStart_422570 : Nat := 118140960795 + 422570 * 2 ^ 59
def prefixEnd_422570 : Nat := 4983230072969 + 3 ^ 40 * 422570 * 2
def baseEnd_422570 : Nat := 192872462373792823672571

theorem tailTrace_422570 : CollatzResearch.WordTrace tailWord_422570 prefixEnd_422570 192872462373792823672571 := by
  unfold tailWord_422570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3853098519777133513856291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10274929386072356036950109 3853098519777133513856291)
  ·
    refine ⟨5779647779665700270784437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3853098519777133513856291 5779647779665700270784437)
    ·
      refine ⟨541841979343659400386041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5779647779665700270784437 541841979343659400386041)
      ·
        refine ⟨406381484507744550289531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541841979343659400386041 406381484507744550289531)
        ·
          refine ⟨609572226761616825434297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406381484507744550289531 609572226761616825434297)
          ·
            refine ⟨457179170071212619075723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609572226761616825434297 457179170071212619075723)
            ·
              refine ⟨685768755106818928613585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457179170071212619075723 685768755106818928613585)
              ·
                refine ⟨514326566330114196460189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 685768755106818928613585 514326566330114196460189)
                ·
                  refine ⟨192872462373792823672571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 514326566330114196460189 192872462373792823672571)
                  ·
                    rfl

theorem cell20_422570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_422570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422570 prefixEnd_422570 := by exact prefixLift 422570
  have htrace : WordTrace (prefixWord ++ tailWord_422570) baseStart_422570 baseEnd_422570 := by
    simpa [prefixWord, tailWord_422570, baseEnd_422570] using wordTrace_append hprefix tailTrace_422570
  have hstable : (prefixWord ++ tailWord_422570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422570).length < 2 ^ (prefixWord ++ tailWord_422570).sum := by decide
  have hdescent : baseEnd_422570 < baseStart_422570 := by decide
  rcases family_descends (prefixWord ++ tailWord_422570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422574 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_422574 : Nat := 118140960795 + 422574 * 2 ^ 59
def prefixEnd_422574 : Nat := 4983230072969 + 3 ^ 40 * 422574 * 2
def baseEnd_422574 : Nat := 192874288082786587539221

theorem tailTrace_422574 : CollatzResearch.WordTrace tailWord_422574 prefixEnd_422574 192874288082786587539221 := by
  unfold tailWord_422574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1926567496386755342321347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10275026647396028492380517 1926567496386755342321347)
  ·
    refine ⟨2889851244580133013482021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1926567496386755342321347 2889851244580133013482021)
    ·
      refine ⟨541847108358774940027879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2889851244580133013482021 541847108358774940027879)
      ·
        refine ⟨812770662538162410041819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541847108358774940027879 812770662538162410041819)
        ·
          refine ⟨1219155993807243615062729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812770662538162410041819 1219155993807243615062729)
          ·
            refine ⟨914366995355432711297047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1219155993807243615062729 914366995355432711297047)
            ·
              refine ⟨1371550493033149066945571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 914366995355432711297047 1371550493033149066945571)
              ·
                refine ⟨2057325739549723600418357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371550493033149066945571 2057325739549723600418357)
                ·
                  refine ⟨192874288082786587539221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2057325739549723600418357 192874288082786587539221)
                  ·
                    rfl

theorem cell20_422574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_422574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422574 prefixEnd_422574 := by exact prefixLift 422574
  have htrace : WordTrace (prefixWord ++ tailWord_422574) baseStart_422574 baseEnd_422574 := by
    simpa [prefixWord, tailWord_422574, baseEnd_422574] using wordTrace_append hprefix tailTrace_422574
  have hstable : (prefixWord ++ tailWord_422574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422574).length < 2 ^ (prefixWord ++ tailWord_422574).sum := by decide
  have hdescent : baseEnd_422574 < baseStart_422574 := by decide
  rcases family_descends (prefixWord ++ tailWord_422574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422581 : List Nat := [1, 3, 3, 3, 1, 2, 2, 1, 4]
def baseStart_422581 : Nat := 118140960795 + 422581 * 2 ^ 59
def prefixEnd_422581 : Nat := 4983230072969 + 3 ^ 40 * 422581 * 2
def baseEnd_422581 : Nat := 192877483073525674305859

theorem tailTrace_422581 : CollatzResearch.WordTrace tailWord_422581 prefixEnd_422581 192877483073525674305859 := by
  unfold tailWord_422581
  simp only [CollatzResearch.WordTrace]
  refine ⟨15412795282068682934075597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10275196854712455289383731 15412795282068682934075597)
  ·
    refine ⟨5779798230775756100278349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15412795282068682934075597 5779798230775756100278349)
    ·
      refine ⟨2167424336540908537604381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5779798230775756100278349 2167424336540908537604381)
      ·
        refine ⟨812784126202840701601643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2167424336540908537604381 812784126202840701601643)
        ·
          refine ⟨1219176189304261052402465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812784126202840701601643 1219176189304261052402465)
          ·
            refine ⟨914382141978195789301849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1219176189304261052402465 914382141978195789301849)
            ·
              refine ⟨685786606483646841976387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 914382141978195789301849 685786606483646841976387)
              ·
                refine ⟨1028679909725470262964581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685786606483646841976387 1028679909725470262964581)
                ·
                  refine ⟨192877483073525674305859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1028679909725470262964581 192877483073525674305859)
                  ·
                    rfl

theorem cell20_422581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_422581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422581 prefixEnd_422581 := by exact prefixLift 422581
  have htrace : WordTrace (prefixWord ++ tailWord_422581) baseStart_422581 baseEnd_422581 := by
    simpa [prefixWord, tailWord_422581, baseEnd_422581] using wordTrace_append hprefix tailTrace_422581
  have hstable : (prefixWord ++ tailWord_422581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422581).length < 2 ^ (prefixWord ++ tailWord_422581).sum := by decide
  have hdescent : baseEnd_422581 < baseStart_422581 := by decide
  rcases family_descends (prefixWord ++ tailWord_422581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422602 : List Nat := [3, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_422602 : Nat := 118140960795 + 422602 * 2 ^ 59
def prefixEnd_422602 : Nat := 4983230072969 + 3 ^ 40 * 422602 * 2
def baseEnd_422602 : Nat := 192887068045742934605773

theorem tailTrace_422602 : CollatzResearch.WordTrace tailWord_422602 prefixEnd_422602 192887068045742934605773 := by
  unfold tailWord_422602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3853390303748150880147515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10275707476661735680393373 3853390303748150880147515)
  ·
    refine ⟨5780085455622226320221273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3853390303748150880147515 5780085455622226320221273)
    ·
      refine ⟨4335064091716669740165955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5780085455622226320221273 4335064091716669740165955)
      ·
        refine ⟨6502596137575004610248933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4335064091716669740165955 6502596137575004610248933)
        ·
          refine ⟨1219236775795313364421675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6502596137575004610248933 1219236775795313364421675)
          ·
            refine ⟨1828855163692970046632513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219236775795313364421675 1828855163692970046632513)
            ·
              refine ⟨1371641372769727534974385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1828855163692970046632513 1371641372769727534974385)
              ·
                refine ⟨1028731029577295651230789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1371641372769727534974385 1028731029577295651230789)
                ·
                  refine ⟨192887068045742934605773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1028731029577295651230789 192887068045742934605773)
                  ·
                    rfl

theorem cell20_422602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_422602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422602 prefixEnd_422602 := by exact prefixLift 422602
  have htrace : WordTrace (prefixWord ++ tailWord_422602) baseStart_422602 baseEnd_422602 := by
    simpa [prefixWord, tailWord_422602, baseEnd_422602] using wordTrace_append hprefix tailTrace_422602
  have hstable : (prefixWord ++ tailWord_422602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422602).length < 2 ^ (prefixWord ++ tailWord_422602).sum := by decide
  have hdescent : baseEnd_422602 < baseStart_422602 := by decide
  rcases family_descends (prefixWord ++ tailWord_422602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422605 : List Nat := [1, 6, 2, 1, 2, 1, 1, 6]
def baseStart_422605 : Nat := 118140960795 + 422605 * 2 ^ 59
def prefixEnd_422605 : Nat := 4983230072969 + 3 ^ 40 * 422605 * 2
def baseEnd_422605 : Nat := 64296145775829419168587

theorem tailTrace_422605 : CollatzResearch.WordTrace tailWord_422605 prefixEnd_422605 64296145775829419168587 := by
  unfold tailWord_422605
  simp only [CollatzResearch.WordTrace]
  refine ⟨15413670633981735032949269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10275780422654490021966179 15413670633981735032949269)
  ·
    refine ⟨722515810967893829669497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15413670633981735032949269 722515810967893829669497)
    ·
      refine ⟨541886858225920372252123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 722515810967893829669497 541886858225920372252123)
      ·
        refine ⟨812830287338880558378185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541886858225920372252123 812830287338880558378185)
        ·
          refine ⟨609622715504160418783639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 812830287338880558378185 609622715504160418783639)
          ·
            refine ⟨914434073256240628175459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609622715504160418783639 914434073256240628175459)
            ·
              refine ⟨1371651109884360942263189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 914434073256240628175459 1371651109884360942263189)
              ·
                refine ⟨64296145775829419168587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1371651109884360942263189 64296145775829419168587)
                ·
                  rfl

theorem cell20_422605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 6].length) (baseStart_422605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422605 prefixEnd_422605 := by exact prefixLift 422605
  have htrace : WordTrace (prefixWord ++ tailWord_422605) baseStart_422605 baseEnd_422605 := by
    simpa [prefixWord, tailWord_422605, baseEnd_422605] using wordTrace_append hprefix tailTrace_422605
  have hstable : (prefixWord ++ tailWord_422605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422605).length < 2 ^ (prefixWord ++ tailWord_422605).sum := by decide
  have hdescent : baseEnd_422605 < baseStart_422605 := by decide
  rcases family_descends (prefixWord ++ tailWord_422605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422616 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 5]
def baseStart_422616 : Nat := 118140960795 + 422616 * 2 ^ 59
def prefixEnd_422616 : Nat := 4983230072969 + 3 ^ 40 * 422616 * 2
def baseEnd_422616 : Nat := 192893458027221108139049

theorem tailTrace_422616 : CollatzResearch.WordTrace tailWord_422616 prefixEnd_422616 192893458027221108139049 := by
  unfold tailWord_422616
  simp only [CollatzResearch.WordTrace]
  refine ⟨7707035918470941955799851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10276047891294589274399801 7707035918470941955799851)
  ·
    refine ⟨11560553877706412933699777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7707035918470941955799851 11560553877706412933699777)
    ·
      refine ⟨8670415408279809700274833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11560553877706412933699777 8670415408279809700274833)
      ·
        refine ⟨6502811556209857275206125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8670415408279809700274833 6502811556209857275206125)
        ·
          refine ⟨2438554333578696478202297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6502811556209857275206125 2438554333578696478202297)
          ·
            refine ⟨1828915750184022358651723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2438554333578696478202297 1828915750184022358651723)
            ·
              refine ⟨2743373625276033537977585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1828915750184022358651723 2743373625276033537977585)
              ·
                refine ⟨2057530218957025153483189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2743373625276033537977585 2057530218957025153483189)
                ·
                  refine ⟨192893458027221108139049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2057530218957025153483189 192893458027221108139049)
                  ·
                    rfl

theorem cell20_422616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_422616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422616 prefixEnd_422616 := by exact prefixLift 422616
  have htrace : WordTrace (prefixWord ++ tailWord_422616) baseStart_422616 baseEnd_422616 := by
    simpa [prefixWord, tailWord_422616, baseEnd_422616] using wordTrace_append hprefix tailTrace_422616
  have hstable : (prefixWord ++ tailWord_422616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422616).length < 2 ^ (prefixWord ++ tailWord_422616).sum := by decide
  have hdescent : baseEnd_422616 < baseStart_422616 := by decide
  rcases family_descends (prefixWord ++ tailWord_422616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422661 : List Nat := [1, 3, 1, 1, 2, 1, 1, 6, 4]
def baseStart_422661 : Nat := 118140960795 + 422661 * 2 ^ 59
def prefixEnd_422661 : Nat := 4983230072969 + 3 ^ 40 * 422661 * 2
def baseEnd_422661 : Nat := 192913997253400951638865

theorem tailTrace_422661 : CollatzResearch.WordTrace tailWord_422661 prefixEnd_422661 192913997253400951638865 := by
  unfold tailWord_422661
  simp only [CollatzResearch.WordTrace]
  refine ⟨15415713121778856596987837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10277142081185904397991891 15415713121778856596987837)
  ·
    refine ⟨5780892420667071223870439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15415713121778856596987837 5780892420667071223870439)
    ·
      refine ⟨8671338631000606835805659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5780892420667071223870439 8671338631000606835805659)
      ·
        refine ⟨13007007946500910253708489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8671338631000606835805659 13007007946500910253708489)
        ·
          refine ⟨9755255959875682690281367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13007007946500910253708489 9755255959875682690281367)
          ·
            refine ⟨14632883939813524035422051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9755255959875682690281367 14632883939813524035422051)
            ·
              refine ⟨21949325909720286053133077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14632883939813524035422051 21949325909720286053133077)
              ·
                refine ⟨1028874652018138408740613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21949325909720286053133077 1028874652018138408740613)
                ·
                  refine ⟨192913997253400951638865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1028874652018138408740613 192913997253400951638865)
                  ·
                    rfl

theorem cell20_422661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_422661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422661 prefixEnd_422661 := by exact prefixLift 422661
  have htrace : WordTrace (prefixWord ++ tailWord_422661) baseStart_422661 baseEnd_422661 := by
    simpa [prefixWord, tailWord_422661, baseEnd_422661] using wordTrace_append hprefix tailTrace_422661
  have hstable : (prefixWord ++ tailWord_422661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422661).length < 2 ^ (prefixWord ++ tailWord_422661).sum := by decide
  have hdescent : baseEnd_422661 < baseStart_422661 := by decide
  rcases family_descends (prefixWord ++ tailWord_422661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422685 : List Nat := [1, 4, 2, 4, 9]
def baseStart_422685 : Nat := 118140960795 + 422685 * 2 ^ 59
def prefixEnd_422685 : Nat := 4983230072969 + 3 ^ 40 * 422685 * 2
def baseEnd_422685 : Nat := 2381789524782265862207

theorem tailTrace_422685 : CollatzResearch.WordTrace tailWord_422685 prefixEnd_422685 2381789524782265862207 := by
  unfold tailWord_422685
  simp only [CollatzResearch.WordTrace]
  refine ⟨15416588473691908695861509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10277725649127939130574339 15416588473691908695861509)
  ·
    refine ⟨2890610338817232880474033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15416588473691908695861509 2890610338817232880474033)
    ·
      refine ⟨2167957754112924660355525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2890610338817232880474033 2167957754112924660355525)
      ·
        refine ⟨406492078896173373816661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2167957754112924660355525 406492078896173373816661)
        ·
          refine ⟨2381789524782265862207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 406492078896173373816661 2381789524782265862207)
          ·
            rfl

theorem cell20_422685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 9].length) (baseStart_422685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422685 prefixEnd_422685 := by exact prefixLift 422685
  have htrace : WordTrace (prefixWord ++ tailWord_422685) baseStart_422685 baseEnd_422685 := by
    simpa [prefixWord, tailWord_422685, baseEnd_422685] using wordTrace_append hprefix tailTrace_422685
  have hstable : (prefixWord ++ tailWord_422685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422685).length < 2 ^ (prefixWord ++ tailWord_422685).sum := by decide
  have hdescent : baseEnd_422685 < baseStart_422685 := by decide
  rcases family_descends (prefixWord ++ tailWord_422685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422698 : List Nat := [3, 1, 4, 3, 2, 1, 1, 5]
def baseStart_422698 : Nat := 118140960795 + 422698 * 2 ^ 59
def prefixEnd_422698 : Nat := 4983230072969 + 3 ^ 40 * 422698 * 2
def baseEnd_422698 : Nat := 64310295020531089135127

theorem tailTrace_422698 : CollatzResearch.WordTrace tailWord_422698 prefixEnd_422698 64310295020531089135127 := by
  unfold tailWord_422698
  simp only [CollatzResearch.WordTrace]
  refine ⟨3854265655661202979021187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10278041748429874610723165 3854265655661202979021187)
  ·
    refine ⟨5781398483491804468531781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3854265655661202979021187 5781398483491804468531781)
    ·
      refine ⟨1084012215654713337849709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5781398483491804468531781 1084012215654713337849709)
      ·
        refine ⟨406504580870517501693641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1084012215654713337849709 406504580870517501693641)
        ·
          refine ⟨304878435652888126270231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406504580870517501693641 304878435652888126270231)
          ·
            refine ⟨457317653479332189405347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304878435652888126270231 457317653479332189405347)
            ·
              refine ⟨685976480218998284108021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457317653479332189405347 685976480218998284108021)
              ·
                refine ⟨64310295020531089135127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 685976480218998284108021 64310295020531089135127)
                ·
                  rfl

theorem cell20_422698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_422698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422698 prefixEnd_422698 := by exact prefixLift 422698
  have htrace : WordTrace (prefixWord ++ tailWord_422698) baseStart_422698 baseEnd_422698 := by
    simpa [prefixWord, tailWord_422698, baseEnd_422698] using wordTrace_append hprefix tailTrace_422698
  have hstable : (prefixWord ++ tailWord_422698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422698).length < 2 ^ (prefixWord ++ tailWord_422698).sum := by decide
  have hdescent : baseEnd_422698 < baseStart_422698 := by decide
  rcases family_descends (prefixWord ++ tailWord_422698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422702 : List Nat := [4, 1, 3, 2, 1, 1, 3, 5]
def baseStart_422702 : Nat := 118140960795 + 422702 * 2 ^ 59
def prefixEnd_422702 : Nat := 4983230072969 + 3 ^ 40 * 422702 * 2
def baseEnd_422702 : Nat := 64310903590195677090677

theorem tailTrace_422702 : CollatzResearch.WordTrace tailWord_422702 prefixEnd_422702 64310903590195677090677 := by
  unfold tailWord_422702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1927151064328790074903795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10278139009753547066153573 1927151064328790074903795)
  ·
    refine ⟨2890726596493185112355693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1927151064328790074903795 2890726596493185112355693)
    ·
      refine ⟨1084022473684944417133385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2890726596493185112355693 1084022473684944417133385)
      ·
        refine ⟨813016855263708312850039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1084022473684944417133385 813016855263708312850039)
        ·
          refine ⟨1219525282895562469275059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813016855263708312850039 1219525282895562469275059)
          ·
            refine ⟨1829287924343343703912589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219525282895562469275059 1829287924343343703912589)
            ·
              refine ⟨685982971628753888967221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1829287924343343703912589 685982971628753888967221)
              ·
                refine ⟨64310903590195677090677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 685982971628753888967221 64310903590195677090677)
                ·
                  rfl

theorem cell20_422702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_422702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422702 prefixEnd_422702 := by exact prefixLift 422702
  have htrace : WordTrace (prefixWord ++ tailWord_422702) baseStart_422702 baseEnd_422702 := by
    simpa [prefixWord, tailWord_422702, baseEnd_422702] using wordTrace_append hprefix tailTrace_422702
  have hstable : (prefixWord ++ tailWord_422702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422702).length < 2 ^ (prefixWord ++ tailWord_422702).sum := by decide
  have hdescent : baseEnd_422702 < baseStart_422702 := by decide
  rcases family_descends (prefixWord ++ tailWord_422702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422709 : List Nat := [1, 3, 3, 1, 3, 1, 2, 3, 3]
def baseStart_422709 : Nat := 118140960795 + 422709 * 2 ^ 59
def prefixEnd_422709 : Nat := 4983230072969 + 3 ^ 40 * 422709 * 2
def baseEnd_422709 : Nat := 192935905761326118038669

theorem tailTrace_422709 : CollatzResearch.WordTrace tailWord_422709 prefixEnd_422709 192935905761326118038669 := by
  unfold tailWord_422709
  simp only [CollatzResearch.WordTrace]
  refine ⟨15417463825604960794735181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10278309217069973863156787 15417463825604960794735181)
  ·
    refine ⟨5781548934601860298025693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15417463825604960794735181 5781548934601860298025693)
    ·
      refine ⟨2168080850475697611759635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5781548934601860298025693 2168080850475697611759635)
      ·
        refine ⟨3252121275713546417639453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2168080850475697611759635 3252121275713546417639453)
        ·
          refine ⟨1219545478392579906614795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3252121275713546417639453 1219545478392579906614795)
          ·
            refine ⟨1829318217588869859922193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219545478392579906614795 1829318217588869859922193)
            ·
              refine ⟨1371988663191652394941645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1829318217588869859922193 1371988663191652394941645)
              ·
                refine ⟨514495748696869648103117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1371988663191652394941645 514495748696869648103117)
                ·
                  refine ⟨192935905761326118038669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 514495748696869648103117 192935905761326118038669)
                  ·
                    rfl

theorem cell20_422709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_422709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422709 prefixEnd_422709 := by exact prefixLift 422709
  have htrace : WordTrace (prefixWord ++ tailWord_422709) baseStart_422709 baseEnd_422709 := by
    simpa [prefixWord, tailWord_422709, baseEnd_422709] using wordTrace_append hprefix tailTrace_422709
  have hstable : (prefixWord ++ tailWord_422709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422709).length < 2 ^ (prefixWord ++ tailWord_422709).sum := by decide
  have hdescent : baseEnd_422709 < baseStart_422709 := by decide
  rcases family_descends (prefixWord ++ tailWord_422709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422723 : List Nat := [1, 1, 1, 3, 1, 4, 5, 4]
def baseStart_422723 : Nat := 118140960795 + 422723 * 2 ^ 59
def prefixEnd_422723 : Nat := 4983230072969 + 3 ^ 40 * 422723 * 2
def baseEnd_422723 : Nat := 64314098580934763857315

theorem tailTrace_422723 : CollatzResearch.WordTrace tailWord_422723 prefixEnd_422723 64314098580934763857315 := by
  unfold tailWord_422723
  simp only [CollatzResearch.WordTrace]
  refine ⟨15417974447554241185744823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10278649631702827457163215 15417974447554241185744823)
  ·
    refine ⟨23126961671331361778617235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15417974447554241185744823 23126961671331361778617235)
    ·
      refine ⟨34690442506997042667925853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23126961671331361778617235 34690442506997042667925853)
      ·
        refine ⟨13008915940123891000472195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34690442506997042667925853 13008915940123891000472195)
        ·
          refine ⟨19513373910185836500708293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13008915940123891000472195 19513373910185836500708293)
          ·
            refine ⟨3658757608159844343882805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19513373910185836500708293 3658757608159844343882805)
            ·
              refine ⟨343008525764985407239013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3658757608159844343882805 343008525764985407239013)
              ·
                refine ⟨64314098580934763857315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 343008525764985407239013 64314098580934763857315)
                ·
                  rfl

theorem cell20_422723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 4].length) (baseStart_422723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422723 prefixEnd_422723 := by exact prefixLift 422723
  have htrace : WordTrace (prefixWord ++ tailWord_422723) baseStart_422723 baseEnd_422723 := by
    simpa [prefixWord, tailWord_422723, baseEnd_422723] using wordTrace_append hprefix tailTrace_422723
  have hstable : (prefixWord ++ tailWord_422723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422723).length < 2 ^ (prefixWord ++ tailWord_422723).sum := by decide
  have hdescent : baseEnd_422723 < baseStart_422723 := by decide
  rcases family_descends (prefixWord ++ tailWord_422723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422768 : List Nat := [2, 1, 1, 1, 4, 1, 2, 5, 3]
def baseStart_422768 : Nat := 118140960795 + 422768 * 2 ^ 59
def prefixEnd_422768 : Nat := 4983230072969 + 3 ^ 40 * 422768 * 2
def baseEnd_422768 : Nat := 192962834968984135071761

theorem tailTrace_422768 : CollatzResearch.WordTrace tailWord_422768 prefixEnd_422768 192962834968984135071761 := by
  unfold tailWord_422768
  simp only [CollatzResearch.WordTrace]
  refine ⟨7709807866195606935566479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10279743821594142580755305 7709807866195606935566479)
  ·
    refine ⟨11564711799293410403349719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7709807866195606935566479 11564711799293410403349719)
    ·
      refine ⟨17347067698940115605024579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11564711799293410403349719 17347067698940115605024579)
      ·
        refine ⟨26020601548410173407536869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17347067698940115605024579 26020601548410173407536869)
        ·
          refine ⟨4878862790326907513913163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26020601548410173407536869 4878862790326907513913163)
          ·
            refine ⟨7318294185490361270869745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4878862790326907513913163 7318294185490361270869745)
            ·
              refine ⟨5488720639117770953152309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7318294185490361270869745 5488720639117770953152309)
              ·
                refine ⟨514567559917291026858029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5488720639117770953152309 514567559917291026858029)
                ·
                  refine ⟨192962834968984135071761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 514567559917291026858029 192962834968984135071761)
                  ·
                    rfl

theorem cell20_422768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_422768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422768 prefixEnd_422768 := by exact prefixLift 422768
  have htrace : WordTrace (prefixWord ++ tailWord_422768) baseStart_422768 baseEnd_422768 := by
    simpa [prefixWord, tailWord_422768, baseEnd_422768] using wordTrace_append hprefix tailTrace_422768
  have hstable : (prefixWord ++ tailWord_422768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422768).length < 2 ^ (prefixWord ++ tailWord_422768).sum := by decide
  have hdescent : baseEnd_422768 < baseStart_422768 := by decide
  rcases family_descends (prefixWord ++ tailWord_422768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422885 : List Nat := [1, 3, 1, 6, 1, 1, 1, 2, 4]
def baseStart_422885 : Nat := 118140960795 + 422885 * 2 ^ 59
def prefixEnd_422885 : Nat := 4983230072969 + 3 ^ 40 * 422885 * 2
def baseEnd_422885 : Nat := 193016236957051728171283

theorem tailTrace_422885 : CollatzResearch.WordTrace tailWord_422885 prefixEnd_422885 193016236957051728171283 := by
  unfold tailWord_422885
  simp only [CollatzResearch.WordTrace]
  refine ⟨15423883072967342853142109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10282588715311561902094739 15423883072967342853142109)
  ·
    refine ⟨5783956152362753569928291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15423883072967342853142109 5783956152362753569928291)
    ·
      refine ⟨8675934228544130354892437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5783956152362753569928291 8675934228544130354892437)
      ·
        refine ⟨406684416963006110385583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8675934228544130354892437 406684416963006110385583)
        ·
          refine ⟨610026625444509165578375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406684416963006110385583 610026625444509165578375)
          ·
            refine ⟨915039938166763748367563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610026625444509165578375 915039938166763748367563)
            ·
              refine ⟨1372559907250145622551345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915039938166763748367563 1372559907250145622551345)
              ·
                refine ⟨1029419930437609216913509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1372559907250145622551345 1029419930437609216913509)
                ·
                  refine ⟨193016236957051728171283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1029419930437609216913509 193016236957051728171283)
                  ·
                    rfl

theorem cell20_422885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_422885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422885 prefixEnd_422885 := by exact prefixLift 422885
  have htrace : WordTrace (prefixWord ++ tailWord_422885) baseStart_422885 baseEnd_422885 := by
    simpa [prefixWord, tailWord_422885, baseEnd_422885] using wordTrace_append hprefix tailTrace_422885
  have hstable : (prefixWord ++ tailWord_422885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422885).length < 2 ^ (prefixWord ++ tailWord_422885).sum := by decide
  have hdescent : baseEnd_422885 < baseStart_422885 := by decide
  rcases family_descends (prefixWord ++ tailWord_422885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422902 : List Nat := [5, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_422902 : Nat := 118140960795 + 422902 * 2 ^ 59
def prefixEnd_422902 : Nat := 4983230072969 + 3 ^ 40 * 422902 * 2
def baseEnd_422902 : Nat := 193023996220275224604547

theorem tailTrace_422902 : CollatzResearch.WordTrace tailWord_422902 prefixEnd_422902 193023996220275224604547 := by
  unfold tailWord_422902
  simp only [CollatzResearch.WordTrace]
  refine ⟨964031444619109672281935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10283002075937169837673973 964031444619109672281935)
  ·
    refine ⟨1446047166928664508422903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 964031444619109672281935 1446047166928664508422903)
    ·
      refine ⟨2169070750392996762634355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1446047166928664508422903 2169070750392996762634355)
      ·
        refine ⟨3253606125589495143951533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2169070750392996762634355 3253606125589495143951533)
        ·
          refine ⟨1220102297096060678981825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3253606125589495143951533 1220102297096060678981825)
          ·
            refine ⟨915076722822045509236369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1220102297096060678981825 915076722822045509236369)
            ·
              refine ⟨686307542116534131927277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 915076722822045509236369 686307542116534131927277)
              ·
                refine ⟨257365328293700299472729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 686307542116534131927277 257365328293700299472729)
                ·
                  refine ⟨193023996220275224604547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257365328293700299472729 193023996220275224604547)
                  ·
                    rfl

theorem cell20_422902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_422902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422902 prefixEnd_422902 := by exact prefixLift 422902
  have htrace : WordTrace (prefixWord ++ tailWord_422902) baseStart_422902 baseEnd_422902 := by
    simpa [prefixWord, tailWord_422902, baseEnd_422902] using wordTrace_append hprefix tailTrace_422902
  have hstable : (prefixWord ++ tailWord_422902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422902).length < 2 ^ (prefixWord ++ tailWord_422902).sum := by decide
  have hdescent : baseEnd_422902 < baseStart_422902 := by decide
  rcases family_descends (prefixWord ++ tailWord_422902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422920 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 5]
def baseStart_422920 : Nat := 118140960795 + 422920 * 2 ^ 59
def prefixEnd_422920 : Nat := 4983230072969 + 3 ^ 40 * 422920 * 2
def baseEnd_422920 : Nat := 193032211910747162004473

theorem tailTrace_422920 : CollatzResearch.WordTrace tailWord_422920 prefixEnd_422920 193032211910747162004473 := by
  unfold tailWord_422920
  simp only [CollatzResearch.WordTrace]
  refine ⟨7712579813920271915333107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10283439751893695887110809 7712579813920271915333107)
  ·
    refine ⟨11568869720880407872999661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7712579813920271915333107 11568869720880407872999661)
    ·
      refine ⟨4338326145330152952374873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11568869720880407872999661 4338326145330152952374873)
      ·
        refine ⟨3253744608997614714281155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4338326145330152952374873 3253744608997614714281155)
        ·
          refine ⟨4880616913496422071421733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3253744608997614714281155 4880616913496422071421733)
          ·
            refine ⟨915115671280579138391575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4880616913496422071421733 915115671280579138391575)
            ·
              refine ⟨1372673506920868707587363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915115671280579138391575 1372673506920868707587363)
              ·
                refine ⟨2059010260381303061381045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1372673506920868707587363 2059010260381303061381045)
                ·
                  refine ⟨193032211910747162004473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2059010260381303061381045 193032211910747162004473)
                  ·
                    rfl

theorem cell20_422920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_422920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422920 prefixEnd_422920 := by exact prefixLift 422920
  have htrace : WordTrace (prefixWord ++ tailWord_422920) baseStart_422920 baseEnd_422920 := by
    simpa [prefixWord, tailWord_422920, baseEnd_422920] using wordTrace_append hprefix tailTrace_422920
  have hstable : (prefixWord ++ tailWord_422920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422920).length < 2 ^ (prefixWord ++ tailWord_422920).sum := by decide
  have hdescent : baseEnd_422920 < baseStart_422920 := by decide
  rcases family_descends (prefixWord ++ tailWord_422920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422958 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_422958 : Nat := 118140960795 + 422958 * 2 ^ 59
def prefixEnd_422958 : Nat := 4983230072969 + 3 ^ 40 * 422958 * 2
def baseEnd_422958 : Nat := 193049556146187918737651

theorem tailTrace_422958 : CollatzResearch.WordTrace tailWord_422958 prefixEnd_422958 193049556146187918737651 := by
  unfold tailWord_422958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1928318200212859540068691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10284363734468584213699685 1928318200212859540068691)
  ·
    refine ⟨2892477300319289310103037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1928318200212859540068691 2892477300319289310103037)
    ·
      refine ⟨1084678987619733491288639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2892477300319289310103037 1084678987619733491288639)
      ·
        refine ⟨1627018481429600236932959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084678987619733491288639 1627018481429600236932959)
        ·
          refine ⟨2440527722144400355399439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1627018481429600236932959 2440527722144400355399439)
          ·
            refine ⟨3660791583216600533099159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2440527722144400355399439 3660791583216600533099159)
            ·
              refine ⟨5491187374824900799648739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3660791583216600533099159 5491187374824900799648739)
              ·
                refine ⟨8236781062237351199473109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5491187374824900799648739 8236781062237351199473109)
                ·
                  refine ⟨193049556146187918737651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8236781062237351199473109 193049556146187918737651)
                  ·
                    rfl

theorem cell20_422958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_422958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422958 prefixEnd_422958 := by exact prefixLift 422958
  have htrace : WordTrace (prefixWord ++ tailWord_422958) baseStart_422958 baseEnd_422958 := by
    simpa [prefixWord, tailWord_422958, baseEnd_422958] using wordTrace_append hprefix tailTrace_422958
  have hstable : (prefixWord ++ tailWord_422958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422958).length < 2 ^ (prefixWord ++ tailWord_422958).sum := by decide
  have hdescent : baseEnd_422958 < baseStart_422958 := by decide
  rcases family_descends (prefixWord ++ tailWord_422958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422972 : List Nat := [2, 2, 2, 2, 2, 2, 8]
def baseStart_422972 : Nat := 118140960795 + 422972 * 2 ^ 59
def prefixEnd_422972 : Nat := 4983230072969 + 3 ^ 40 * 422972 * 2
def baseEnd_422972 : Nat := 21450660680851788030103

theorem tailTrace_422972 : CollatzResearch.WordTrace tailWord_422972 prefixEnd_422972 21450660680851788030103 := by
  unfold tailWord_422972
  simp only [CollatzResearch.WordTrace]
  refine ⟨7713528111826078355779585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10284704149101437807706113 7713528111826078355779585)
  ·
    refine ⟨5785146083869558766834689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7713528111826078355779585 5785146083869558766834689)
    ·
      refine ⟨4338859562902169075126017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5785146083869558766834689 4338859562902169075126017)
      ·
        refine ⟨3254144672176626806344513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4338859562902169075126017 3254144672176626806344513)
        ·
          refine ⟨2440608504132470104758385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3254144672176626806344513 2440608504132470104758385)
          ·
            refine ⟨1830456378099352578568789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2440608504132470104758385 1830456378099352578568789)
            ·
              refine ⟨21450660680851788030103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1830456378099352578568789 21450660680851788030103)
              ·
                rfl

theorem cell20_422972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 8].length) (baseStart_422972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422972 prefixEnd_422972 := by exact prefixLift 422972
  have htrace : WordTrace (prefixWord ++ tailWord_422972) baseStart_422972 baseEnd_422972 := by
    simpa [prefixWord, tailWord_422972, baseEnd_422972] using wordTrace_append hprefix tailTrace_422972
  have hstable : (prefixWord ++ tailWord_422972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422972).length < 2 ^ (prefixWord ++ tailWord_422972).sum := by decide
  have hdescent : baseEnd_422972 < baseStart_422972 := by decide
  rcases family_descends (prefixWord ++ tailWord_422972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422979 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 5]
def baseStart_422979 : Nat := 118140960795 + 422979 * 2 ^ 59
def prefixEnd_422979 : Nat := 4983230072969 + 3 ^ 40 * 422979 * 2
def baseEnd_422979 : Nat := 193059141118405179037565

theorem tailTrace_422979 : CollatzResearch.WordTrace tailWord_422979 prefixEnd_422979 193059141118405179037565 := by
  unfold tailWord_422979
  simp only [CollatzResearch.WordTrace]
  refine ⟨15427311534626796907063991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10284874356417864604709327 15427311534626796907063991)
  ·
    refine ⟨23140967301940195360595987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15427311534626796907063991 23140967301940195360595987)
    ·
      refine ⟨34711450952910293040893981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23140967301940195360595987 34711450952910293040893981)
      ·
        refine ⟨13016794107341359890335243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34711450952910293040893981 13016794107341359890335243)
        ·
          refine ⟨19525191161012039835502865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13016794107341359890335243 19525191161012039835502865)
          ·
            refine ⟨14643893370759029876627149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19525191161012039835502865 14643893370759029876627149)
            ·
              refine ⟨5491460014034636203735181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14643893370759029876627149 5491460014034636203735181)
              ·
                refine ⟨2059297505262988576400693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5491460014034636203735181 2059297505262988576400693)
                ·
                  refine ⟨193059141118405179037565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2059297505262988576400693 193059141118405179037565)
                  ·
                    rfl

theorem cell20_422979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_422979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422979 prefixEnd_422979 := by exact prefixLift 422979
  have htrace : WordTrace (prefixWord ++ tailWord_422979) baseStart_422979 baseEnd_422979 := by
    simpa [prefixWord, tailWord_422979, baseEnd_422979] using wordTrace_append hprefix tailTrace_422979
  have hstable : (prefixWord ++ tailWord_422979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422979).length < 2 ^ (prefixWord ++ tailWord_422979).sum := by decide
  have hdescent : baseEnd_422979 < baseStart_422979 := by decide
  rcases family_descends (prefixWord ++ tailWord_422979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422989 : List Nat := [1, 6, 1, 1, 1, 2, 1, 7]
def baseStart_422989 : Nat := 118140960795 + 422989 * 2 ^ 59
def prefixEnd_422989 : Nat := 4983230072969 + 3 ^ 40 * 422989 * 2
def baseEnd_422989 : Nat := 64354568463629862901397

theorem tailTrace_422989 : CollatzResearch.WordTrace tailWord_422989 prefixEnd_422989 64354568463629862901397 := by
  unfold tailWord_422989
  simp only [CollatzResearch.WordTrace]
  refine ⟨15427676264590568614928021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10285117509727045743285347 15427676264590568614928021)
  ·
    refine ⟨723172324902682903824751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15427676264590568614928021 723172324902682903824751)
    ·
      refine ⟨1084758487354024355737127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 723172324902682903824751 1084758487354024355737127)
      ·
        refine ⟨1627137731031036533605691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084758487354024355737127 1627137731031036533605691)
        ·
          refine ⟨2440706596546554800408537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1627137731031036533605691 2440706596546554800408537)
          ·
            refine ⟨1830529947409916100306403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2440706596546554800408537 1830529947409916100306403)
            ·
              refine ⟨2745794921114874150459605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830529947409916100306403 2745794921114874150459605)
              ·
                refine ⟨64354568463629862901397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2745794921114874150459605 64354568463629862901397)
                ·
                  rfl

theorem cell20_422989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 7].length) (baseStart_422989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_422989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_422989 prefixEnd_422989 := by exact prefixLift 422989
  have htrace : WordTrace (prefixWord ++ tailWord_422989) baseStart_422989 baseEnd_422989 := by
    simpa [prefixWord, tailWord_422989, baseEnd_422989] using wordTrace_append hprefix tailTrace_422989
  have hstable : (prefixWord ++ tailWord_422989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422989).length < 2 ^ (prefixWord ++ tailWord_422989).sum := by decide
  have hdescent : baseEnd_422989 < baseStart_422989 := by decide
  rcases family_descends (prefixWord ++ tailWord_422989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423020 : List Nat := [2, 2, 1, 1, 3, 2, 2, 5, 2]
def baseStart_423020 : Nat := 118140960795 + 423020 * 2 ^ 59
def prefixEnd_423020 : Nat := 4983230072969 + 3 ^ 40 * 423020 * 2
def baseEnd_423020 : Nat := 193077854635591258670731

theorem tailTrace_423020 : CollatzResearch.WordTrace tailWord_423020 prefixEnd_423020 193077854635591258670731 := by
  unfold tailWord_423020
  simp only [CollatzResearch.WordTrace]
  refine ⟨7714403463739130454653257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10285871284985507272871009 7714403463739130454653257)
  ·
    refine ⟨5785802597804347840989943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7714403463739130454653257 5785802597804347840989943)
    ·
      refine ⟨8678703896706521761484915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5785802597804347840989943 8678703896706521761484915)
      ·
        refine ⟨13018055845059782642227373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8678703896706521761484915 13018055845059782642227373)
        ·
          refine ⟨4881770941897418490835265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13018055845059782642227373 4881770941897418490835265)
          ·
            refine ⟨3661328206423063868126449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4881770941897418490835265 3661328206423063868126449)
            ·
              refine ⟨2745996154817297901094837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3661328206423063868126449 2745996154817297901094837)
              ·
                refine ⟨257437139514121678227641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2745996154817297901094837 257437139514121678227641)
                ·
                  refine ⟨193077854635591258670731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257437139514121678227641 193077854635591258670731)
                  ·
                    rfl

theorem cell20_423020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_423020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423020 prefixEnd_423020 := by exact prefixLift 423020
  have htrace : WordTrace (prefixWord ++ tailWord_423020) baseStart_423020 baseEnd_423020 := by
    simpa [prefixWord, tailWord_423020, baseEnd_423020] using wordTrace_append hprefix tailTrace_423020
  have hstable : (prefixWord ++ tailWord_423020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423020).length < 2 ^ (prefixWord ++ tailWord_423020).sum := by decide
  have hdescent : baseEnd_423020 < baseStart_423020 := by decide
  rcases family_descends (prefixWord ++ tailWord_423020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423033 : List Nat := [1, 2, 1, 3, 6, 1, 2, 2, 2]
def baseStart_423033 : Nat := 118140960795 + 423033 * 2 ^ 59
def prefixEnd_423033 : Nat := 4983230072969 + 3 ^ 40 * 423033 * 2
def baseEnd_423033 : Nat := 193083788189820991237345

theorem tailTrace_423033 : CollatzResearch.WordTrace tailWord_423033 prefixEnd_423033 193083788189820991237345 := by
  unfold tailWord_423033
  simp only [CollatzResearch.WordTrace]
  refine ⟨15429281076431164129529753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10286187384287442753019835 15429281076431164129529753)
  ·
    refine ⟨11571960807323373097147315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15429281076431164129529753 11571960807323373097147315)
    ·
      refine ⟨17357941210985059645720973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11571960807323373097147315 17357941210985059645720973)
      ·
        refine ⟨6509227954119397367145365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17357941210985059645720973 6509227954119397367145365)
        ·
          refine ⟨305120060349346751584939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6509227954119397367145365 305120060349346751584939)
          ·
            refine ⟨457680090524020127377409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305120060349346751584939 457680090524020127377409)
            ·
              refine ⟨343260067893015095533057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457680090524020127377409 343260067893015095533057)
              ·
                refine ⟨257445050919761321649793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 343260067893015095533057 257445050919761321649793)
                ·
                  refine ⟨193083788189820991237345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257445050919761321649793 193083788189820991237345)
                  ·
                    rfl

theorem cell20_423033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 2].length) (baseStart_423033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423033 prefixEnd_423033 := by exact prefixLift 423033
  have htrace : WordTrace (prefixWord ++ tailWord_423033) baseStart_423033 baseEnd_423033 := by
    simpa [prefixWord, tailWord_423033, baseEnd_423033] using wordTrace_append hprefix tailTrace_423033
  have hstable : (prefixWord ++ tailWord_423033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423033).length < 2 ^ (prefixWord ++ tailWord_423033).sum := by decide
  have hdescent : baseEnd_423033 < baseStart_423033 := by decide
  rcases family_descends (prefixWord ++ tailWord_423033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423058 : List Nat := [3, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_423058 : Nat := 118140960795 + 423058 * 2 ^ 59
def prefixEnd_423058 : Nat := 4983230072969 + 3 ^ 40 * 423058 * 2
def baseEnd_423058 : Nat := 193095198871032015403909

theorem tailTrace_423058 : CollatzResearch.WordTrace tailWord_423058 prefixEnd_423058 193095198871032015403909 := by
  unfold tailWord_423058
  simp only [CollatzResearch.WordTrace]
  refine ⟨3857548225335148349797457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10286795267560395599459885 3857548225335148349797457)
  ·
    refine ⟨2893161169001361262348093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3857548225335148349797457 2893161169001361262348093)
    ·
      refine ⟨1084935438375510473380535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2893161169001361262348093 1084935438375510473380535)
      ·
        refine ⟨1627403157563265710070803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084935438375510473380535 1627403157563265710070803)
        ·
          refine ⟨2441104736344898565106205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1627403157563265710070803 2441104736344898565106205)
          ·
            refine ⟨915414276129336961914827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2441104736344898565106205 915414276129336961914827)
            ·
              refine ⟨1373121414194005442872241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915414276129336961914827 1373121414194005442872241)
              ·
                refine ⟨1029841060645504082154181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373121414194005442872241 1029841060645504082154181)
                ·
                  refine ⟨193095198871032015403909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1029841060645504082154181 193095198871032015403909)
                  ·
                    rfl

theorem cell20_423058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_423058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423058 prefixEnd_423058 := by exact prefixLift 423058
  have htrace : WordTrace (prefixWord ++ tailWord_423058) baseStart_423058 baseEnd_423058 := by
    simpa [prefixWord, tailWord_423058, baseEnd_423058] using wordTrace_append hprefix tailTrace_423058
  have hstable : (prefixWord ++ tailWord_423058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423058).length < 2 ^ (prefixWord ++ tailWord_423058).sum := by decide
  have hdescent : baseEnd_423058 < baseStart_423058 := by decide
  rcases family_descends (prefixWord ++ tailWord_423058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423085 : List Nat := [1, 5, 2, 1, 4, 1, 1, 2, 3]
def baseStart_423085 : Nat := 118140960795 + 423085 * 2 ^ 59
def prefixEnd_423085 : Nat := 4983230072969 + 3 ^ 40 * 423085 * 2
def baseEnd_423085 : Nat := 193107522406739921503799

theorem tailTrace_423085 : CollatzResearch.WordTrace tailWord_423085 prefixEnd_423085 193107522406739921503799 := by
  unfold tailWord_423085
  simp only [CollatzResearch.WordTrace]
  refine ⟨15431177672242777010422709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10287451781495184673615139 15431177672242777010422709)
  ·
    refine ⟨1446672906772760344727129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15431177672242777010422709 1446672906772760344727129)
    ·
      refine ⟨1085004680079570258545347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1446672906772760344727129 1085004680079570258545347)
      ·
        refine ⟨1627507020119355387818021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1085004680079570258545347 1627507020119355387818021)
        ·
          refine ⟨305157566272379135215879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1627507020119355387818021 305157566272379135215879)
          ·
            refine ⟨457736349408568702823819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305157566272379135215879 457736349408568702823819)
            ·
              refine ⟨686604524112853054235729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457736349408568702823819 686604524112853054235729)
              ·
                refine ⟨514953393084639790676797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 686604524112853054235729 514953393084639790676797)
                ·
                  refine ⟨193107522406739921503799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 514953393084639790676797 193107522406739921503799)
                  ·
                    rfl

theorem cell20_423085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_423085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423085 prefixEnd_423085 := by exact prefixLift 423085
  have htrace : WordTrace (prefixWord ++ tailWord_423085) baseStart_423085 baseEnd_423085 := by
    simpa [prefixWord, tailWord_423085, baseEnd_423085] using wordTrace_append hprefix tailTrace_423085
  have hstable : (prefixWord ++ tailWord_423085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423085).length < 2 ^ (prefixWord ++ tailWord_423085).sum := by decide
  have hdescent : baseEnd_423085 < baseStart_423085 := by decide
  rcases family_descends (prefixWord ++ tailWord_423085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423089 : List Nat := [1, 2, 2, 5, 1, 1, 3, 2, 3]
def baseStart_423089 : Nat := 118140960795 + 423089 * 2 ^ 59
def prefixEnd_423089 : Nat := 4983230072969 + 3 ^ 40 * 423089 * 2
def baseEnd_423089 : Nat := 193109348115733685370449

theorem tailTrace_423089 : CollatzResearch.WordTrace tailWord_423089 prefixEnd_423089 193109348115733685370449 := by
  unfold tailWord_423089
  simp only [CollatzResearch.WordTrace]
  refine ⟨15431323564228285693568321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10287549042818857129045547 15431323564228285693568321)
  ·
    refine ⟨11573492673171214270176241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15431323564228285693568321 11573492673171214270176241)
    ·
      refine ⟨8680119504878410702632181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11573492673171214270176241 8680119504878410702632181)
      ·
        refine ⟨813761203582351003371767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8680119504878410702632181 813761203582351003371767)
        ·
          refine ⟨1220641805373526505057651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813761203582351003371767 1220641805373526505057651)
          ·
            refine ⟨1830962708060289757586477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220641805373526505057651 1830962708060289757586477)
            ·
              refine ⟨686611015522608659094929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1830962708060289757586477 686611015522608659094929)
              ·
                refine ⟨514958261641956494321197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 686611015522608659094929 514958261641956494321197)
                ·
                  refine ⟨193109348115733685370449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 514958261641956494321197 193109348115733685370449)
                  ·
                    rfl

theorem cell20_423089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_423089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423089 prefixEnd_423089 := by exact prefixLift 423089
  have htrace : WordTrace (prefixWord ++ tailWord_423089) baseStart_423089 baseEnd_423089 := by
    simpa [prefixWord, tailWord_423089, baseEnd_423089] using wordTrace_append hprefix tailTrace_423089
  have hstable : (prefixWord ++ tailWord_423089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423089).length < 2 ^ (prefixWord ++ tailWord_423089).sum := by decide
  have hdescent : baseEnd_423089 < baseStart_423089 := by decide
  rcases family_descends (prefixWord ++ tailWord_423089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423126 : List Nat := [5, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_423126 : Nat := 118140960795 + 423126 * 2 ^ 59
def prefixEnd_423126 : Nat := 4983230072969 + 3 ^ 40 * 423126 * 2
def baseEnd_423126 : Nat := 193126235923926001136965

theorem tailTrace_423126 : CollatzResearch.WordTrace tailWord_423126 prefixEnd_423126 193126235923926001136965 := by
  unfold tailWord_423126
  simp only [CollatzResearch.WordTrace]
  refine ⟨964542066568390063291577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10288448710062827341776821 964542066568390063291577)
  ·
    refine ⟨723406549926292547468683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 964542066568390063291577 723406549926292547468683)
    ·
      refine ⟨1085109824889438821203025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 723406549926292547468683 1085109824889438821203025)
      ·
        refine ⟨813832368667079115902269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1085109824889438821203025 813832368667079115902269)
        ·
          refine ⟨305187138250154668463351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 813832368667079115902269 305187138250154668463351)
          ·
            refine ⟨457780707375232002695027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305187138250154668463351 457780707375232002695027)
            ·
              refine ⟨686671061062848004042541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457780707375232002695027 686671061062848004042541)
              ·
                refine ⟨257501647898568001515953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 686671061062848004042541 257501647898568001515953)
                ·
                  refine ⟨193126235923926001136965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257501647898568001515953 193126235923926001136965)
                  ·
                    rfl

theorem cell20_423126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_423126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423126 prefixEnd_423126 := by exact prefixLift 423126
  have htrace : WordTrace (prefixWord ++ tailWord_423126) baseStart_423126 baseEnd_423126 := by
    simpa [prefixWord, tailWord_423126, baseEnd_423126] using wordTrace_append hprefix tailTrace_423126
  have hstable : (prefixWord ++ tailWord_423126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423126).length < 2 ^ (prefixWord ++ tailWord_423126).sum := by decide
  have hdescent : baseEnd_423126 < baseStart_423126 := by decide
  rcases family_descends (prefixWord ++ tailWord_423126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423141 : List Nat := [1, 3, 1, 4, 3, 2, 6]
def baseStart_423141 : Nat := 118140960795 + 423141 * 2 ^ 59
def prefixEnd_423141 : Nat := 4983230072969 + 3 ^ 40 * 423141 * 2
def baseEnd_423141 : Nat := 21459231370294735070767

theorem tailTrace_423141 : CollatzResearch.WordTrace tailWord_423141 prefixEnd_423141 21459231370294735070767 := by
  unfold tailWord_423141
  simp only [CollatzResearch.WordTrace]
  refine ⟨15433220160039898574461277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10288813440026599049640851 15433220160039898574461277)
  ·
    refine ⟨5787457560014961965422979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15433220160039898574461277 5787457560014961965422979)
    ·
      refine ⟨8681186340022442948134469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5787457560014961965422979 8681186340022442948134469)
      ·
        refine ⟨1627722438754208052775213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8681186340022442948134469 1627722438754208052775213)
        ·
          refine ⟨610395914532828019790705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1627722438754208052775213 610395914532828019790705)
          ·
            refine ⟨457796935899621014843029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 610395914532828019790705 457796935899621014843029)
            ·
              refine ⟨21459231370294735070767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 457796935899621014843029 21459231370294735070767)
              ·
                rfl

theorem cell20_423141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 6].length) (baseStart_423141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423141 prefixEnd_423141 := by exact prefixLift 423141
  have htrace : WordTrace (prefixWord ++ tailWord_423141) baseStart_423141 baseEnd_423141 := by
    simpa [prefixWord, tailWord_423141, baseEnd_423141] using wordTrace_append hprefix tailTrace_423141
  have hstable : (prefixWord ++ tailWord_423141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423141).length < 2 ^ (prefixWord ++ tailWord_423141).sum := by decide
  have hdescent : baseEnd_423141 < baseStart_423141 := by decide
  rcases family_descends (prefixWord ++ tailWord_423141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423151 : List Nat := [1, 1, 2, 1, 8, 1, 1, 1, 4]
def baseStart_423151 : Nat := 118140960795 + 423151 * 2 ^ 59
def prefixEnd_423151 : Nat := 4983230072969 + 3 ^ 40 * 423151 * 2
def baseEnd_423151 : Nat := 193137646605137025303529

theorem tailTrace_423151 : CollatzResearch.WordTrace tailWord_423151 prefixEnd_423151 193137646605137025303529 := by
  unfold tailWord_423151
  simp only [CollatzResearch.WordTrace]
  refine ⟨15433584890003670282325307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10289056593335780188216871 15433584890003670282325307)
  ·
    refine ⟨23150377335005505423487961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15433584890003670282325307 23150377335005505423487961)
    ·
      refine ⟨17362783001254129067615971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23150377335005505423487961 17362783001254129067615971)
      ·
        refine ⟨26044174501881193601423957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17362783001254129067615971 26044174501881193601423957)
        ·
          refine ⟨305205169943920237516687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 26044174501881193601423957 305205169943920237516687)
          ·
            refine ⟨457807754915880356275031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305205169943920237516687 457807754915880356275031)
            ·
              refine ⟨686711632373820534412547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457807754915880356275031 686711632373820534412547)
              ·
                refine ⟨1030067448560730801618821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686711632373820534412547 1030067448560730801618821)
                ·
                  refine ⟨193137646605137025303529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1030067448560730801618821 193137646605137025303529)
                  ·
                    rfl

theorem cell20_423151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 4].length) (baseStart_423151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423151 prefixEnd_423151 := by exact prefixLift 423151
  have htrace : WordTrace (prefixWord ++ tailWord_423151) baseStart_423151 baseEnd_423151 := by
    simpa [prefixWord, tailWord_423151, baseEnd_423151] using wordTrace_append hprefix tailTrace_423151
  have hstable : (prefixWord ++ tailWord_423151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423151).length < 2 ^ (prefixWord ++ tailWord_423151).sum := by decide
  have hdescent : baseEnd_423151 < baseStart_423151 := by decide
  rcases family_descends (prefixWord ++ tailWord_423151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423155 : List Nat := [1, 1, 1, 2, 2, 5, 3, 1, 4]
def baseStart_423155 : Nat := 118140960795 + 423155 * 2 ^ 59
def prefixEnd_423155 : Nat := 4983230072969 + 3 ^ 40 * 423155 * 2
def baseEnd_423155 : Nat := 193139472314130789170179

theorem tailTrace_423155 : CollatzResearch.WordTrace tailWord_423155 prefixEnd_423155 193139472314130789170179 := by
  unfold tailWord_423155
  simp only [CollatzResearch.WordTrace]
  refine ⟨15433730781989178965470919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10289153854659452643647279 15433730781989178965470919)
  ·
    refine ⟨23150596172983768448206379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15433730781989178965470919 23150596172983768448206379)
    ·
      refine ⟨34725894259475652672309569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23150596172983768448206379 34725894259475652672309569)
      ·
        refine ⟨26044420694606739504232177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34725894259475652672309569 26044420694606739504232177)
        ·
          refine ⟨19533315520955054628174133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26044420694606739504232177 19533315520955054628174133)
          ·
            refine ⟨1831248330089536371391325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19533315520955054628174133 1831248330089536371391325)
            ·
              refine ⟨686718123783576139271747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1831248330089536371391325 686718123783576139271747)
              ·
                refine ⟨1030077185675364208907621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686718123783576139271747 1030077185675364208907621)
                ·
                  refine ⟨193139472314130789170179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1030077185675364208907621 193139472314130789170179)
                  ·
                    rfl

theorem cell20_423155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 4].length) (baseStart_423155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423155 prefixEnd_423155 := by exact prefixLift 423155
  have htrace : WordTrace (prefixWord ++ tailWord_423155) baseStart_423155 baseEnd_423155 := by
    simpa [prefixWord, tailWord_423155, baseEnd_423155] using wordTrace_append hprefix tailTrace_423155
  have hstable : (prefixWord ++ tailWord_423155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423155).length < 2 ^ (prefixWord ++ tailWord_423155).sum := by decide
  have hdescent : baseEnd_423155 < baseStart_423155 := by decide
  rcases family_descends (prefixWord ++ tailWord_423155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423162 : List Nat := [3, 1, 1, 1, 1, 4, 4, 5]
def baseStart_423162 : Nat := 118140960795 + 423162 * 2 ^ 59
def prefixEnd_423162 : Nat := 4983230072969 + 3 ^ 40 * 423162 * 2
def baseEnd_423162 : Nat := 64380889101623291978939

theorem tailTrace_423162 : CollatzResearch.WordTrace tailWord_423162 prefixEnd_423162 64380889101623291978939 := by
  unfold tailWord_423162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3858496523240954790243935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10289324061975879440650493 3858496523240954790243935)
  ·
    refine ⟨5787744784861432185365903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3858496523240954790243935 5787744784861432185365903)
    ·
      refine ⟨8681617177292148278048855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5787744784861432185365903 8681617177292148278048855)
      ·
        refine ⟨13022425765938222417073283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8681617177292148278048855 13022425765938222417073283)
        ·
          refine ⟨19533638648907333625609925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13022425765938222417073283 19533638648907333625609925)
          ·
            refine ⟨3662557246670125054801861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19533638648907333625609925 3662557246670125054801861)
            ·
              refine ⟨686729483750648447775349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3662557246670125054801861 686729483750648447775349)
              ·
                refine ⟨64380889101623291978939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 686729483750648447775349 64380889101623291978939)
                ·
                  rfl

theorem cell20_423162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_423162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423162 prefixEnd_423162 := by exact prefixLift 423162
  have htrace : WordTrace (prefixWord ++ tailWord_423162) baseStart_423162 baseEnd_423162 := by
    simpa [prefixWord, tailWord_423162, baseEnd_423162] using wordTrace_append hprefix tailTrace_423162
  have hstable : (prefixWord ++ tailWord_423162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423162).length < 2 ^ (prefixWord ++ tailWord_423162).sum := by decide
  have hdescent : baseEnd_423162 < baseStart_423162 := by decide
  rcases family_descends (prefixWord ++ tailWord_423162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423200 : List Nat := [2, 1, 1, 5, 3, 8]
def baseStart_423200 : Nat := 118140960795 + 423200 * 2 ^ 59
def prefixEnd_423200 : Nat := 4983230072969 + 3 ^ 40 * 423200 * 2
def baseEnd_423200 : Nat := 7154074501492986395185

theorem tailTrace_423200 : CollatzResearch.WordTrace tailWord_423200 prefixEnd_423200 7154074501492986395185 := by
  unfold tailWord_423200
  simp only [CollatzResearch.WordTrace]
  refine ⟨7717686033413075825429527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10290248044550767767239369 7717686033413075825429527)
  ·
    refine ⟨11576529050119613738144291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7717686033413075825429527 11576529050119613738144291)
    ·
      refine ⟨17364793575179420607216437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11576529050119613738144291 17364793575179420607216437)
      ·
        refine ⟨1627949397673070681926541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17364793575179420607216437 1627949397673070681926541)
        ·
          refine ⟨610481024127401505722453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1627949397673070681926541 610481024127401505722453)
          ·
            refine ⟨7154074501492986395185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 610481024127401505722453 7154074501492986395185)
            ·
              rfl

theorem cell20_423200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 8].length) (baseStart_423200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423200 prefixEnd_423200 := by exact prefixLift 423200
  have htrace : WordTrace (prefixWord ++ tailWord_423200) baseStart_423200 baseEnd_423200 := by
    simpa [prefixWord, tailWord_423200, baseEnd_423200] using wordTrace_append hprefix tailTrace_423200
  have hstable : (prefixWord ++ tailWord_423200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423200).length < 2 ^ (prefixWord ++ tailWord_423200).sum := by decide
  have hdescent : baseEnd_423200 < baseStart_423200 := by decide
  rcases family_descends (prefixWord ++ tailWord_423200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423217 : List Nat := [1, 2, 2, 3, 3, 3, 1, 5]
def baseStart_423217 : Nat := 118140960795 + 423217 * 2 ^ 59
def prefixEnd_423217 : Nat := 4983230072969 + 3 ^ 40 * 423217 * 2
def baseEnd_423217 : Nat := 64389256934511376367753

theorem tailTrace_423217 : CollatzResearch.WordTrace tailWord_423217 prefixEnd_423217 64389256934511376367753 := by
  unfold tailWord_423217
  simp only [CollatzResearch.WordTrace]
  refine ⟨15435992107764563554227905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10290661405176375702818603 15435992107764563554227905)
  ·
    refine ⟨11576994080823422665670929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15435992107764563554227905 11576994080823422665670929)
    ·
      refine ⟨8682745560617566999253197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11576994080823422665670929 8682745560617566999253197)
      ·
        refine ⟨3256029585231587624719949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8682745560617566999253197 3256029585231587624719949)
        ·
          refine ⟨1221011094461845359269981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3256029585231587624719949 1221011094461845359269981)
          ·
            refine ⟨457879160423192009726243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1221011094461845359269981 457879160423192009726243)
            ·
              refine ⟨686818740634788014589365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457879160423192009726243 686818740634788014589365)
              ·
                refine ⟨64389256934511376367753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 686818740634788014589365 64389256934511376367753)
                ·
                  rfl

theorem cell20_423217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 5].length) (baseStart_423217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423217 prefixEnd_423217 := by exact prefixLift 423217
  have htrace : WordTrace (prefixWord ++ tailWord_423217) baseStart_423217 baseEnd_423217 := by
    simpa [prefixWord, tailWord_423217, baseEnd_423217] using wordTrace_append hprefix tailTrace_423217
  have hstable : (prefixWord ++ tailWord_423217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423217).length < 2 ^ (prefixWord ++ tailWord_423217).sum := by decide
  have hdescent : baseEnd_423217 < baseStart_423217 := by decide
  rcases family_descends (prefixWord ++ tailWord_423217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423231 : List Nat := [1, 1, 2, 2, 4, 3, 1, 2, 4]
def baseStart_423231 : Nat := 118140960795 + 423231 * 2 ^ 59
def prefixEnd_423231 : Nat := 4983230072969 + 3 ^ 40 * 423231 * 2
def baseEnd_423231 : Nat := 193174160785012302636535

theorem tailTrace_423231 : CollatzResearch.WordTrace tailWord_423231 prefixEnd_423231 193174160785012302636535 := by
  unfold tailWord_423231
  simp only [CollatzResearch.WordTrace]
  refine ⟨15436502729713843945237547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10291001819809229296825031 15436502729713843945237547)
  ·
    refine ⟨23154754094570765917856321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15436502729713843945237547 23154754094570765917856321)
    ·
      refine ⟨17366065570928074438392241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23154754094570765917856321 17366065570928074438392241)
      ·
        refine ⟨13024549178196055828794181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17366065570928074438392241 13024549178196055828794181)
        ·
          refine ⟨2442102970911760467898909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13024549178196055828794181 2442102970911760467898909)
          ·
            refine ⟨915788614091910175462091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2442102970911760467898909 915788614091910175462091)
            ·
              refine ⟨1373682921137865263193137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915788614091910175462091 1373682921137865263193137)
              ·
                refine ⟨1030262190853398947394853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373682921137865263193137 1030262190853398947394853)
                ·
                  refine ⟨193174160785012302636535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1030262190853398947394853 193174160785012302636535)
                  ·
                    rfl

theorem cell20_423231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 4].length) (baseStart_423231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423231 prefixEnd_423231 := by exact prefixLift 423231
  have htrace : WordTrace (prefixWord ++ tailWord_423231) baseStart_423231 baseEnd_423231 := by
    simpa [prefixWord, tailWord_423231, baseEnd_423231] using wordTrace_append hprefix tailTrace_423231
  have hstable : (prefixWord ++ tailWord_423231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423231).length < 2 ^ (prefixWord ++ tailWord_423231).sum := by decide
  have hdescent : baseEnd_423231 < baseStart_423231 := by decide
  rcases family_descends (prefixWord ++ tailWord_423231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423248 : List Nat := [2, 1, 1, 1, 1, 5, 4, 3, 2]
def baseStart_423248 : Nat := 118140960795 + 423248 * 2 ^ 59
def prefixEnd_423248 : Nat := 4983230072969 + 3 ^ 40 * 423248 * 2
def baseEnd_423248 : Nat := 193181920048235799069799

theorem tailTrace_423248 : CollatzResearch.WordTrace tailWord_423248 prefixEnd_423248 193181920048235799069799 := by
  unfold tailWord_423248
  simp only [CollatzResearch.WordTrace]
  refine ⟨7718561385326127924303199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10291415180434837232404265 7718561385326127924303199)
  ·
    refine ⟨11577842077989191886454799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7718561385326127924303199 11577842077989191886454799)
    ·
      refine ⟨17366763116983787829682199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11577842077989191886454799 17366763116983787829682199)
      ·
        refine ⟨26050144675475681744523299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17366763116983787829682199 26050144675475681744523299)
        ·
          refine ⟨39075217013213522616784949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26050144675475681744523299 39075217013213522616784949)
          ·
            refine ⟨3663301594988767745323589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39075217013213522616784949 3663301594988767745323589)
            ·
              refine ⟨686869049060393952248173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3663301594988767745323589 686869049060393952248173)
              ·
                refine ⟨257575893397647732093065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 686869049060393952248173 257575893397647732093065)
                ·
                  refine ⟨193181920048235799069799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257575893397647732093065 193181920048235799069799)
                  ·
                    rfl

theorem cell20_423248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 2].length) (baseStart_423248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423248 prefixEnd_423248 := by exact prefixLift 423248
  have htrace : WordTrace (prefixWord ++ tailWord_423248) baseStart_423248 baseEnd_423248 := by
    simpa [prefixWord, tailWord_423248, baseEnd_423248] using wordTrace_append hprefix tailTrace_423248
  have hstable : (prefixWord ++ tailWord_423248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423248).length < 2 ^ (prefixWord ++ tailWord_423248).sum := by decide
  have hdescent : baseEnd_423248 < baseStart_423248 := by decide
  rcases family_descends (prefixWord ++ tailWord_423248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423269 : List Nat := [1, 3, 1, 3, 1, 2, 4, 1, 4]
def baseStart_423269 : Nat := 118140960795 + 423269 * 2 ^ 59
def prefixEnd_423269 : Nat := 4983230072969 + 3 ^ 40 * 423269 * 2
def baseEnd_423269 : Nat := 193191505020453059369713

theorem tailTrace_423269 : CollatzResearch.WordTrace tailWord_423269 prefixEnd_423269 193191505020453059369713 := by
  unfold tailWord_423269
  simp only [CollatzResearch.WordTrace]
  refine ⟨15437888703576176435120861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10291925802384117623413907 15437888703576176435120861)
  ·
    refine ⟨5789208263841066163170323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15437888703576176435120861 5789208263841066163170323)
    ·
      refine ⟨8683812395761599244755485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5789208263841066163170323 8683812395761599244755485)
      ·
        refine ⟨3256429648410599716783307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8683812395761599244755485 3256429648410599716783307)
        ·
          refine ⟨4884644472615899575174961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3256429648410599716783307 4884644472615899575174961)
          ·
            refine ⟨3663483354461924681381221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4884644472615899575174961 3663483354461924681381221)
            ·
              refine ⟨686903128961610877758979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3663483354461924681381221 686903128961610877758979)
              ·
                refine ⟨1030354693442416316638469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686903128961610877758979 1030354693442416316638469)
                ·
                  refine ⟨193191505020453059369713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1030354693442416316638469 193191505020453059369713)
                  ·
                    rfl

theorem cell20_423269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_423269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423269 prefixEnd_423269 := by exact prefixLift 423269
  have htrace : WordTrace (prefixWord ++ tailWord_423269) baseStart_423269 baseEnd_423269 := by
    simpa [prefixWord, tailWord_423269, baseEnd_423269] using wordTrace_append hprefix tailTrace_423269
  have hstable : (prefixWord ++ tailWord_423269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423269).length < 2 ^ (prefixWord ++ tailWord_423269).sum := by decide
  have hdescent : baseEnd_423269 < baseStart_423269 := by decide
  rcases family_descends (prefixWord ++ tailWord_423269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423303 : List Nat := [1, 1, 4, 2, 2, 4, 1, 3, 2]
def baseStart_423303 : Nat := 118140960795 + 423303 * 2 ^ 59
def prefixEnd_423303 : Nat := 4983230072969 + 3 ^ 40 * 423303 * 2
def baseEnd_423303 : Nat := 193207023546900052236241

theorem tailTrace_423303 : CollatzResearch.WordTrace tailWord_423303 prefixEnd_423303 193207023546900052236241 := by
  unfold tailWord_423303
  simp only [CollatzResearch.WordTrace]
  refine ⟨15439128785453000241858563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10292752523635333494572375 15439128785453000241858563)
  ·
    refine ⟨23158693178179500362787845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15439128785453000241858563 23158693178179500362787845)
    ·
      refine ⟨4342254970908656318022721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23158693178179500362787845 4342254970908656318022721)
      ·
        refine ⟨3256691228181492238517041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4342254970908656318022721 3256691228181492238517041)
        ·
          refine ⟨2442518421136119178887781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3256691228181492238517041 2442518421136119178887781)
          ·
            refine ⟨457972203963022346041459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2442518421136119178887781 457972203963022346041459)
            ·
              refine ⟨686958305944533519062189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457972203963022346041459 686958305944533519062189)
              ·
                refine ⟨257609364729200069648321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 686958305944533519062189 257609364729200069648321)
                ·
                  refine ⟨193207023546900052236241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257609364729200069648321 193207023546900052236241)
                  ·
                    rfl

theorem cell20_423303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 2].length) (baseStart_423303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423303 prefixEnd_423303 := by exact prefixLift 423303
  have htrace : WordTrace (prefixWord ++ tailWord_423303) baseStart_423303 baseEnd_423303 := by
    simpa [prefixWord, tailWord_423303, baseEnd_423303] using wordTrace_append hprefix tailTrace_423303
  have hstable : (prefixWord ++ tailWord_423303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423303).length < 2 ^ (prefixWord ++ tailWord_423303).sum := by decide
  have hdescent : baseEnd_423303 < baseStart_423303 := by decide
  rcases family_descends (prefixWord ++ tailWord_423303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423310 : List Nat := [4, 1, 1, 4, 3, 1, 6]
def baseStart_423310 : Nat := 118140960795 + 423310 * 2 ^ 59
def prefixEnd_423310 : Nat := 4983230072969 + 3 ^ 40 * 423310 * 2
def baseEnd_423310 : Nat := 21467802059737682111431

theorem tailTrace_423310 : CollatzResearch.WordTrace tailWord_423310 prefixEnd_423310 21467802059737682111431 := by
  unfold tailWord_423310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1929923012053455054670423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10292922730951760291575589 1929923012053455054670423)
  ·
    refine ⟨2894884518080182582005635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1929923012053455054670423 2894884518080182582005635)
    ·
      refine ⟨4342326777120273873008453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2894884518080182582005635 4342326777120273873008453)
      ·
        refine ⟨814186270710051351189085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4342326777120273873008453 814186270710051351189085)
        ·
          refine ⟨305319851516269256695907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 814186270710051351189085 305319851516269256695907)
          ·
            refine ⟨457979777274403885043861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305319851516269256695907 457979777274403885043861)
            ·
              refine ⟨21467802059737682111431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 457979777274403885043861 21467802059737682111431)
              ·
                rfl

theorem cell20_423310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 6].length) (baseStart_423310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423310 prefixEnd_423310 := by exact prefixLift 423310
  have htrace : WordTrace (prefixWord ++ tailWord_423310) baseStart_423310 baseEnd_423310 := by
    simpa [prefixWord, tailWord_423310, baseEnd_423310] using wordTrace_append hprefix tailTrace_423310
  have hstable : (prefixWord ++ tailWord_423310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423310).length < 2 ^ (prefixWord ++ tailWord_423310).sum := by decide
  have hdescent : baseEnd_423310 < baseStart_423310 := by decide
  rcases family_descends (prefixWord ++ tailWord_423310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423320 : List Nat := [2, 1, 2, 5, 2, 1, 3, 2, 2]
def baseStart_423320 : Nat := 118140960795 + 423320 * 2 ^ 59
def prefixEnd_423320 : Nat := 4983230072969 + 3 ^ 40 * 423320 * 2
def baseEnd_423320 : Nat := 193214782810123548669505

theorem tailTrace_423320 : CollatzResearch.WordTrace tailWord_423320 prefixEnd_423320 193214782810123548669505 := by
  unfold tailWord_423320
  simp only [CollatzResearch.WordTrace]
  refine ⟨7719874413195706072613707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10293165884260941430151609 7719874413195706072613707)
  ·
    refine ⟨11579811619793559108920561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7719874413195706072613707 11579811619793559108920561)
    ·
      refine ⟨8684858714845169331690421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11579811619793559108920561 8684858714845169331690421)
      ·
        refine ⟨814205504516734624845977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8684858714845169331690421 814205504516734624845977)
        ·
          refine ⟨610654128387550968634483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 814205504516734624845977 610654128387550968634483)
          ·
            refine ⟨915981192581326452951725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610654128387550968634483 915981192581326452951725)
            ·
              refine ⟨343492947217997419856897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 915981192581326452951725 343492947217997419856897)
              ·
                refine ⟨257619710413498064892673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 343492947217997419856897 257619710413498064892673)
                ·
                  refine ⟨193214782810123548669505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257619710413498064892673 193214782810123548669505)
                  ·
                    rfl

theorem cell20_423320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 2].length) (baseStart_423320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423320 prefixEnd_423320 := by exact prefixLift 423320
  have htrace : WordTrace (prefixWord ++ tailWord_423320) baseStart_423320 baseEnd_423320 := by
    simpa [prefixWord, tailWord_423320, baseEnd_423320] using wordTrace_append hprefix tailTrace_423320
  have hstable : (prefixWord ++ tailWord_423320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423320).length < 2 ^ (prefixWord ++ tailWord_423320).sum := by decide
  have hdescent : baseEnd_423320 < baseStart_423320 := by decide
  rcases family_descends (prefixWord ++ tailWord_423320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423321 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 5]
def baseStart_423321 : Nat := 118140960795 + 423321 * 2 ^ 59
def prefixEnd_423321 : Nat := 4983230072969 + 3 ^ 40 * 423321 * 2
def baseEnd_423321 : Nat := 193215239237371989636167

theorem tailTrace_423321 : CollatzResearch.WordTrace tailWord_423321 prefixEnd_423321 193215239237371989636167 := by
  unfold tailWord_423321
  simp only [CollatzResearch.WordTrace]
  refine ⟨15439785299387789316013817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10293190199591859544009211 15439785299387789316013817)
  ·
    refine ⟨11579838974540841987010363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15439785299387789316013817 11579838974540841987010363)
    ·
      refine ⟨17369758461811262980515545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11579838974540841987010363 17369758461811262980515545)
      ·
        refine ⟨13027318846358447235386659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17369758461811262980515545 13027318846358447235386659)
        ·
          refine ⟨19540978269537670853079989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13027318846358447235386659 19540978269537670853079989)
          ·
            refine ⟨1831966712769156642476249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19540978269537670853079989 1831966712769156642476249)
            ·
              refine ⟨1373975034576867481857187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1831966712769156642476249 1373975034576867481857187)
              ·
                refine ⟨2060962551865301222785781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373975034576867481857187 2060962551865301222785781)
                ·
                  refine ⟨193215239237371989636167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2060962551865301222785781 193215239237371989636167)
                  ·
                    rfl

theorem cell20_423321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_423321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423321 prefixEnd_423321 := by exact prefixLift 423321
  have htrace : WordTrace (prefixWord ++ tailWord_423321) baseStart_423321 baseEnd_423321 := by
    simpa [prefixWord, tailWord_423321, baseEnd_423321] using wordTrace_append hprefix tailTrace_423321
  have hstable : (prefixWord ++ tailWord_423321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423321).length < 2 ^ (prefixWord ++ tailWord_423321).sum := by decide
  have hdescent : baseEnd_423321 < baseStart_423321 := by decide
  rcases family_descends (prefixWord ++ tailWord_423321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423431 : List Nat := [1, 1, 4, 3, 2, 3, 1, 2, 3]
def baseStart_423431 : Nat := 118140960795 + 423431 * 2 ^ 59
def prefixEnd_423431 : Nat := 4983230072969 + 3 ^ 40 * 423431 * 2
def baseEnd_423431 : Nat := 193265446234700495969051

theorem tailTrace_423431 : CollatzResearch.WordTrace tailWord_423431 prefixEnd_423431 193265446234700495969051 := by
  unfold tailWord_423431
  simp only [CollatzResearch.WordTrace]
  refine ⟨15443797328989278102518147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10295864885992852068345431 15443797328989278102518147)
  ·
    refine ⟨23165695993483917153777221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15443797328989278102518147 23165695993483917153777221)
    ·
      refine ⟨4343567998778234466333229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23165695993483917153777221 4343567998778234466333229)
      ·
        refine ⟨1628837999541837924874961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4343567998778234466333229 1628837999541837924874961)
        ·
          refine ⟨1221628499656378443656221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1628837999541837924874961 1221628499656378443656221)
          ·
            refine ⟨458110687371141916371083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1221628499656378443656221 458110687371141916371083)
            ·
              refine ⟨687166031056712874556625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458110687371141916371083 687166031056712874556625)
              ·
                refine ⟨515374523292534655917469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 687166031056712874556625 515374523292534655917469)
                ·
                  refine ⟨193265446234700495969051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 515374523292534655917469 193265446234700495969051)
                  ·
                    rfl

theorem cell20_423431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 3].length) (baseStart_423431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423431 prefixEnd_423431 := by exact prefixLift 423431
  have htrace : WordTrace (prefixWord ++ tailWord_423431) baseStart_423431 baseEnd_423431 := by
    simpa [prefixWord, tailWord_423431, baseEnd_423431] using wordTrace_append hprefix tailTrace_423431
  have hstable : (prefixWord ++ tailWord_423431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423431).length < 2 ^ (prefixWord ++ tailWord_423431).sum := by decide
  have hdescent : baseEnd_423431 < baseStart_423431 := by decide
  rcases family_descends (prefixWord ++ tailWord_423431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423438 : List Nat := [4, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_423438 : Nat := 118140960795 + 423438 * 2 ^ 59
def prefixEnd_423438 : Nat := 4983230072969 + 3 ^ 40 * 423438 * 2
def baseEnd_423438 : Nat := 193268641225439582735689

theorem tailTrace_423438 : CollatzResearch.WordTrace tailWord_423438 prefixEnd_423438 193268641225439582735689 := by
  unfold tailWord_423438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1930506579995489787252871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10296035093309278865348645 1930506579995489787252871)
  ·
    refine ⟨2895759869993234680879307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1930506579995489787252871 2895759869993234680879307)
    ·
      refine ⟨4343639804989852021318961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2895759869993234680879307 4343639804989852021318961)
      ·
        refine ⟨3257729853742389015989221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4343639804989852021318961 3257729853742389015989221)
        ·
          refine ⟨610824347576697940497979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3257729853742389015989221 610824347576697940497979)
          ·
            refine ⟨916236521365046910746969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610824347576697940497979 916236521365046910746969)
            ·
              refine ⟨687177391023785183060227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 916236521365046910746969 687177391023785183060227)
              ·
                refine ⟨1030766086535677774590341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687177391023785183060227 1030766086535677774590341)
                ·
                  refine ⟨193268641225439582735689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1030766086535677774590341 193268641225439582735689)
                  ·
                    rfl

theorem cell20_423438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_423438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423438 prefixEnd_423438 := by exact prefixLift 423438
  have htrace : WordTrace (prefixWord ++ tailWord_423438) baseStart_423438 baseEnd_423438 := by
    simpa [prefixWord, tailWord_423438, baseEnd_423438] using wordTrace_append hprefix tailTrace_423438
  have hstable : (prefixWord ++ tailWord_423438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423438).length < 2 ^ (prefixWord ++ tailWord_423438).sum := by decide
  have hdescent : baseEnd_423438 < baseStart_423438 := by decide
  rcases family_descends (prefixWord ++ tailWord_423438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423466 : List Nat := [3, 1, 4, 1, 1, 1, 3, 6]
def baseStart_423466 : Nat := 118140960795 + 423466 * 2 ^ 59
def prefixEnd_423466 : Nat := 4983230072969 + 3 ^ 40 * 423466 * 2
def baseEnd_423466 : Nat := 64427140396131976600747

theorem tailTrace_423466 : CollatzResearch.WordTrace tailWord_423466 prefixEnd_423466 64427140396131976600747 := by
  unfold tailWord_423466
  simp only [CollatzResearch.WordTrace]
  refine ⟨3861268470965619770010563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10296715922574986053361501 3861268470965619770010563)
  ·
    refine ⟨5791902706448429655015845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3861268470965619770010563 5791902706448429655015845)
    ·
      refine ⟨1085981757459080560315471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5791902706448429655015845 1085981757459080560315471)
      ·
        refine ⟨1628972636188620840473207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1085981757459080560315471 1628972636188620840473207)
        ·
          refine ⟨2443458954282931260709811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628972636188620840473207 2443458954282931260709811)
          ·
            refine ⟨3665188431424396891064717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2443458954282931260709811 3665188431424396891064717)
            ·
              refine ⟨1374445661784148834149269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3665188431424396891064717 1374445661784148834149269)
              ·
                refine ⟨64427140396131976600747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1374445661784148834149269 64427140396131976600747)
                ·
                  rfl

theorem cell20_423466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_423466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423466 prefixEnd_423466 := by exact prefixLift 423466
  have htrace : WordTrace (prefixWord ++ tailWord_423466) baseStart_423466 baseEnd_423466 := by
    simpa [prefixWord, tailWord_423466, baseEnd_423466] using wordTrace_append hprefix tailTrace_423466
  have hstable : (prefixWord ++ tailWord_423466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423466).length < 2 ^ (prefixWord ++ tailWord_423466).sum := by decide
  have hdescent : baseEnd_423466 < baseStart_423466 := by decide
  rcases family_descends (prefixWord ++ tailWord_423466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423487 : List Nat := [1, 1, 2, 2, 3, 3, 8]
def baseStart_423487 : Nat := 118140960795 + 423487 * 2 ^ 59
def prefixEnd_423487 : Nat := 4983230072969 + 3 ^ 40 * 423487 * 2
def baseEnd_423487 : Nat := 21476778462290354455795

theorem tailTrace_423487 : CollatzResearch.WordTrace tailWord_423487 prefixEnd_423487 21476778462290354455795 := by
  unfold tailWord_423487
  simp only [CollatzResearch.WordTrace]
  refine ⟨15445839816786399666556715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10297226544524266444371143 15445839816786399666556715)
  ·
    refine ⟨23168759725179599499835073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15445839816786399666556715 23168759725179599499835073)
    ·
      refine ⟨17376569793884699624876305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23168759725179599499835073 17376569793884699624876305)
      ·
        refine ⟨13032427345413524718657229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17376569793884699624876305 13032427345413524718657229)
        ·
          refine ⟨4887160254530071769496461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13032427345413524718657229 4887160254530071769496461)
          ·
            refine ⟨1832685095448776913561173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4887160254530071769496461 1832685095448776913561173)
            ·
              refine ⟨21476778462290354455795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1832685095448776913561173 21476778462290354455795)
              ·
                rfl

theorem cell20_423487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 8].length) (baseStart_423487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423487 prefixEnd_423487 := by exact prefixLift 423487
  have htrace : WordTrace (prefixWord ++ tailWord_423487) baseStart_423487 baseEnd_423487 := by
    simpa [prefixWord, tailWord_423487, baseEnd_423487] using wordTrace_append hprefix tailTrace_423487
  have hstable : (prefixWord ++ tailWord_423487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423487).length < 2 ^ (prefixWord ++ tailWord_423487).sum := by decide
  have hdescent : baseEnd_423487 < baseStart_423487 := by decide
  rcases family_descends (prefixWord ++ tailWord_423487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423497 : List Nat := [1, 2, 1, 1, 2, 2, 1, 8, 2]
def baseStart_423497 : Nat := 118140960795 + 423497 * 2 ^ 59
def prefixEnd_423497 : Nat := 4983230072969 + 3 ^ 40 * 423497 * 2
def baseEnd_423497 : Nat := 193295570433097599768781

theorem tailTrace_423497 : CollatzResearch.WordTrace tailWord_423497 prefixEnd_423497 193295570433097599768781 := by
  unfold tailWord_423497
  simp only [CollatzResearch.WordTrace]
  refine ⟨15446204546750171374420745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10297469697833447582947163 15446204546750171374420745)
  ·
    refine ⟨11584653410062628530815559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15446204546750171374420745 11584653410062628530815559)
    ·
      refine ⟨17376980115093942796223339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11584653410062628530815559 17376980115093942796223339)
      ·
        refine ⟨26065470172640914194335009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17376980115093942796223339 26065470172640914194335009)
        ·
          refine ⟨19549102629480685645751257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26065470172640914194335009 19549102629480685645751257)
          ·
            refine ⟨14661826972110514234313443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19549102629480685645751257 14661826972110514234313443)
            ·
              refine ⟨21992740458165771351470165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14661826972110514234313443 21992740458165771351470165)
              ·
                refine ⟨257727427244130133025041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 21992740458165771351470165 257727427244130133025041)
                ·
                  refine ⟨193295570433097599768781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257727427244130133025041 193295570433097599768781)
                  ·
                    rfl

theorem cell20_423497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 2].length) (baseStart_423497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423497 prefixEnd_423497 := by exact prefixLift 423497
  have htrace : WordTrace (prefixWord ++ tailWord_423497) baseStart_423497 baseEnd_423497 := by
    simpa [prefixWord, tailWord_423497, baseEnd_423497] using wordTrace_append hprefix tailTrace_423497
  have hstable : (prefixWord ++ tailWord_423497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423497).length < 2 ^ (prefixWord ++ tailWord_423497).sum := by decide
  have hdescent : baseEnd_423497 < baseStart_423497 := by decide
  rcases family_descends (prefixWord ++ tailWord_423497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423535 : List Nat := [1, 1, 2, 1, 3, 2, 1, 7, 2]
def baseStart_423535 : Nat := 118140960795 + 423535 * 2 ^ 59
def prefixEnd_423535 : Nat := 4983230072969 + 3 ^ 40 * 423535 * 2
def baseEnd_423535 : Nat := 193312914668538356501959

theorem tailTrace_423535 : CollatzResearch.WordTrace tailWord_423535 prefixEnd_423535 193312914668538356501959 := by
  unfold tailWord_423535
  simp only [CollatzResearch.WordTrace]
  refine ⟨15447590520612503864304059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10298393680408335909536039 15447590520612503864304059)
  ·
    refine ⟨23171385780918755796456089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15447590520612503864304059 23171385780918755796456089)
    ·
      refine ⟨17378539335689066847342067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23171385780918755796456089 17378539335689066847342067)
      ·
        refine ⟨26067809003533600271013101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17378539335689066847342067 26067809003533600271013101)
        ·
          refine ⟨9775428376325100101629913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26067809003533600271013101 9775428376325100101629913)
          ·
            refine ⟨7331571282243825076222435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9775428376325100101629913 7331571282243825076222435)
            ·
              refine ⟨10997356923365737614333653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7331571282243825076222435 10997356923365737614333653)
              ·
                refine ⟨257750552891384475335945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10997356923365737614333653 257750552891384475335945)
                ·
                  refine ⟨193312914668538356501959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257750552891384475335945 193312914668538356501959)
                  ·
                    rfl

theorem cell20_423535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 2].length) (baseStart_423535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423535 prefixEnd_423535 := by exact prefixLift 423535
  have htrace : WordTrace (prefixWord ++ tailWord_423535) baseStart_423535 baseEnd_423535 := by
    simpa [prefixWord, tailWord_423535, baseEnd_423535] using wordTrace_append hprefix tailTrace_423535
  have hstable : (prefixWord ++ tailWord_423535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423535).length < 2 ^ (prefixWord ++ tailWord_423535).sum := by decide
  have hdescent : baseEnd_423535 < baseStart_423535 := by decide
  rcases family_descends (prefixWord ++ tailWord_423535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423542 : List Nat := [5, 1, 1, 2, 2, 9]
def baseStart_423542 : Nat := 118140960795 + 423542 * 2 ^ 59
def prefixEnd_423542 : Nat := 4983230072969 + 3 ^ 40 * 423542 * 2
def baseEnd_423542 : Nat := 7159855913306571972911

theorem tailTrace_423542 : CollatzResearch.WordTrace tailWord_423542 prefixEnd_423542 7159855913306571972911 := by
  unfold tailWord_423542
  simp only [CollatzResearch.WordTrace]
  refine ⟨965490364474196503738055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10298563887724762706539253 965490364474196503738055)
  ·
    refine ⟨1448235546711294755607083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 965490364474196503738055 1448235546711294755607083)
    ·
      refine ⟨2172353320066942133410625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1448235546711294755607083 2172353320066942133410625)
      ·
        refine ⟨1629264990050206600057969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2172353320066942133410625 1629264990050206600057969)
        ·
          refine ⟨1221948742537654950043477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1629264990050206600057969 1221948742537654950043477)
          ·
            refine ⟨7159855913306571972911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1221948742537654950043477 7159855913306571972911)
            ·
              rfl

theorem cell20_423542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 9].length) (baseStart_423542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423542 prefixEnd_423542 := by exact prefixLift 423542
  have htrace : WordTrace (prefixWord ++ tailWord_423542) baseStart_423542 baseEnd_423542 := by
    simpa [prefixWord, tailWord_423542, baseEnd_423542] using wordTrace_append hprefix tailTrace_423542
  have hstable : (prefixWord ++ tailWord_423542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423542).length < 2 ^ (prefixWord ++ tailWord_423542).sum := by decide
  have hdescent : baseEnd_423542 < baseStart_423542 := by decide
  rcases family_descends (prefixWord ++ tailWord_423542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423566 : List Nat := [4, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_423566 : Nat := 118140960795 + 423566 * 2 ^ 59
def prefixEnd_423566 : Nat := 4983230072969 + 3 ^ 40 * 423566 * 2
def baseEnd_423566 : Nat := 193327063913240026468499

theorem tailTrace_423566 : CollatzResearch.WordTrace tailWord_423566 prefixEnd_423566 193327063913240026468499 := by
  unfold tailWord_423566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1931090147937524519835319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10299147455666797439121701 1931090147937524519835319)
  ·
    refine ⟨2896635221906286779752979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1931090147937524519835319 2896635221906286779752979)
    ·
      refine ⟨4344952832859430169629469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2896635221906286779752979 4344952832859430169629469)
      ·
        refine ⟨1629357312322286313611051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4344952832859430169629469 1629357312322286313611051)
        ·
          refine ⟨2444035968483429470416577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1629357312322286313611051 2444035968483429470416577)
          ·
            refine ⟨1833026976362572102812433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2444035968483429470416577 1833026976362572102812433)
            ·
              refine ⟨1374770232271929077109325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1833026976362572102812433 1374770232271929077109325)
              ·
                refine ⟨515538837101973403915997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1374770232271929077109325 515538837101973403915997)
                ·
                  refine ⟨193327063913240026468499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 515538837101973403915997 193327063913240026468499)
                  ·
                    rfl

theorem cell20_423566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_423566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423566 prefixEnd_423566 := by exact prefixLift 423566
  have htrace : WordTrace (prefixWord ++ tailWord_423566) baseStart_423566 baseEnd_423566 := by
    simpa [prefixWord, tailWord_423566, baseEnd_423566] using wordTrace_append hprefix tailTrace_423566
  have hstable : (prefixWord ++ tailWord_423566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423566).length < 2 ^ (prefixWord ++ tailWord_423566).sum := by decide
  have hdescent : baseEnd_423566 < baseStart_423566 := by decide
  rcases family_descends (prefixWord ++ tailWord_423566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423586 : List Nat := [3, 3, 1, 4, 1, 1, 2, 3, 2]
def baseStart_423586 : Nat := 118140960795 + 423586 * 2 ^ 59
def prefixEnd_423586 : Nat := 4983230072969 + 3 ^ 40 * 423586 * 2
def baseEnd_423586 : Nat := 193336192458208845801751

theorem tailTrace_423586 : CollatzResearch.WordTrace tailWord_423586 prefixEnd_423586 193336192458208845801751 := by
  unfold tailWord_423586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3862362660856934893602653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10299633762285159716273741 3862362660856934893602653)
  ·
    refine ⟨1448385997821350585100995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3862362660856934893602653 1448385997821350585100995)
    ·
      refine ⟨2172578996732025877651493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1448385997821350585100995 2172578996732025877651493)
      ·
        refine ⟨407358561887254852059655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2172578996732025877651493 407358561887254852059655)
        ·
          refine ⟨611037842830882278089483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407358561887254852059655 611037842830882278089483)
          ·
            refine ⟨916556764246323417134225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611037842830882278089483 916556764246323417134225)
            ·
              refine ⟨687417573184742562850669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 916556764246323417134225 687417573184742562850669)
              ·
                refine ⟨257781589944278461069001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 687417573184742562850669 257781589944278461069001)
                ·
                  refine ⟨193336192458208845801751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257781589944278461069001 193336192458208845801751)
                  ·
                    rfl

theorem cell20_423586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_423586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423586 prefixEnd_423586 := by exact prefixLift 423586
  have htrace : WordTrace (prefixWord ++ tailWord_423586) baseStart_423586 baseEnd_423586 := by
    simpa [prefixWord, tailWord_423586, baseEnd_423586] using wordTrace_append hprefix tailTrace_423586
  have hstable : (prefixWord ++ tailWord_423586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423586).length < 2 ^ (prefixWord ++ tailWord_423586).sum := by decide
  have hdescent : baseEnd_423586 < baseStart_423586 := by decide
  rcases family_descends (prefixWord ++ tailWord_423586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423639 : List Nat := [1, 1, 3, 2, 1, 3, 3, 6]
def baseStart_423639 : Nat := 118140960795 + 423639 * 2 ^ 59
def prefixEnd_423639 : Nat := 4983230072969 + 3 ^ 40 * 423639 * 2
def baseEnd_423639 : Nat := 64453461034125405678289

theorem tailTrace_423639 : CollatzResearch.WordTrace tailWord_423639 prefixEnd_423639 64453461034125405678289 := by
  unfold tailWord_423639
  simp only [CollatzResearch.WordTrace]
  refine ⟨15451383712235729626089971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10300922474823819750726647 15451383712235729626089971)
  ·
    refine ⟨23177075568353594439134957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15451383712235729626089971 23177075568353594439134957)
    ·
      refine ⟨8691403338132597914675609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23177075568353594439134957 8691403338132597914675609)
      ·
        refine ⟨6518552503599448436006707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8691403338132597914675609 6518552503599448436006707)
        ·
          refine ⟨9777828755399172654010061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6518552503599448436006707 9777828755399172654010061)
          ·
            refine ⟨3666685783274689745253773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9777828755399172654010061 3666685783274689745253773)
            ·
              refine ⟨1375007168728008654470165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3666685783274689745253773 1375007168728008654470165)
              ·
                refine ⟨64453461034125405678289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1375007168728008654470165 64453461034125405678289)
                ·
                  rfl

theorem cell20_423639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 6].length) (baseStart_423639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423639 prefixEnd_423639 := by exact prefixLift 423639
  have htrace : WordTrace (prefixWord ++ tailWord_423639) baseStart_423639 baseEnd_423639 := by
    simpa [prefixWord, tailWord_423639, baseEnd_423639] using wordTrace_append hprefix tailTrace_423639
  have hstable : (prefixWord ++ tailWord_423639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423639).length < 2 ^ (prefixWord ++ tailWord_423639).sum := by decide
  have hdescent : baseEnd_423639 < baseStart_423639 := by decide
  rcases family_descends (prefixWord ++ tailWord_423639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423656 : List Nat := [2, 1, 4, 1, 3, 3, 6]
def baseStart_423656 : Nat := 118140960795 + 423656 * 2 ^ 59
def prefixEnd_423656 : Nat := 4983230072969 + 3 ^ 40 * 423656 * 2
def baseEnd_423656 : Nat := 21485349151733301496459

theorem tailTrace_423656 : CollatzResearch.WordTrace tailWord_423656 prefixEnd_423656 21485349151733301496459 := by
  unfold tailWord_423656
  simp only [CollatzResearch.WordTrace]
  refine ⟨7726001876587070764729411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10301335835449427686305881 7726001876587070764729411)
  ·
    refine ⟨11589002814880606147094117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7726001876587070764729411 11589002814880606147094117)
    ·
      refine ⟨2172938027790113652580147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11589002814880606147094117 2172938027790113652580147)
      ·
        refine ⟨3259407041685170478870221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2172938027790113652580147 3259407041685170478870221)
        ·
          refine ⟨1222277640631938929576333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3259407041685170478870221 1222277640631938929576333)
          ·
            refine ⟨458354115236977098591125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1222277640631938929576333 458354115236977098591125)
            ·
              refine ⟨21485349151733301496459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 458354115236977098591125 21485349151733301496459)
              ·
                rfl

theorem cell20_423656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 6].length) (baseStart_423656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423656 prefixEnd_423656 := by exact prefixLift 423656
  have htrace : WordTrace (prefixWord ++ tailWord_423656) baseStart_423656 baseEnd_423656 := by
    simpa [prefixWord, tailWord_423656, baseEnd_423656] using wordTrace_append hprefix tailTrace_423656
  have hstable : (prefixWord ++ tailWord_423656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423656).length < 2 ^ (prefixWord ++ tailWord_423656).sum := by decide
  have hdescent : baseEnd_423656 < baseStart_423656 := by decide
  rcases family_descends (prefixWord ++ tailWord_423656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423663 : List Nat := [1, 1, 2, 1, 5, 1, 2, 4, 3]
def baseStart_423663 : Nat := 118140960795 + 423663 * 2 ^ 59
def prefixEnd_423663 : Nat := 4983230072969 + 3 ^ 40 * 423663 * 2
def baseEnd_423663 : Nat := 193371337356338800234769

theorem tailTrace_423663 : CollatzResearch.WordTrace tailWord_423663 prefixEnd_423663 193371337356338800234769 := by
  unfold tailWord_423663
  simp only [CollatzResearch.WordTrace]
  refine ⟨15452259064148781724963643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10301506042765854483309095 15452259064148781724963643)
  ·
    refine ⟨23178388596223172587445465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15452259064148781724963643 23178388596223172587445465)
    ·
      refine ⟨17383791447167379440584099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23178388596223172587445465 17383791447167379440584099)
      ·
        refine ⟨26075687170751069160876149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17383791447167379440584099 26075687170751069160876149)
        ·
          refine ⟨2444595672257912733832139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26075687170751069160876149 2444595672257912733832139)
          ·
            refine ⟨3666893508386869100748209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2444595672257912733832139 3666893508386869100748209)
            ·
              refine ⟨2750170131290151825561157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3666893508386869100748209 2750170131290151825561157)
              ·
                refine ⟨515656899616903467292717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2750170131290151825561157 515656899616903467292717)
                ·
                  refine ⟨193371337356338800234769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 515656899616903467292717 193371337356338800234769)
                  ·
                    rfl

theorem cell20_423663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 3].length) (baseStart_423663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423663 prefixEnd_423663 := by exact prefixLift 423663
  have htrace : WordTrace (prefixWord ++ tailWord_423663) baseStart_423663 baseEnd_423663 := by
    simpa [prefixWord, tailWord_423663, baseEnd_423663] using wordTrace_append hprefix tailTrace_423663
  have hstable : (prefixWord ++ tailWord_423663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423663).length < 2 ^ (prefixWord ++ tailWord_423663).sum := by decide
  have hdescent : baseEnd_423663 < baseStart_423663 := by decide
  rcases family_descends (prefixWord ++ tailWord_423663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423760 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 5]
def baseStart_423760 : Nat := 118140960795 + 423760 * 2 ^ 59
def prefixEnd_423760 : Nat := 4983230072969 + 3 ^ 40 * 423760 * 2
def baseEnd_423760 : Nat := 193415610799437574001039

theorem tailTrace_423760 : CollatzResearch.WordTrace tailWord_423760 prefixEnd_423760 193415610799437574001039 := by
  unfold tailWord_423760
  simp only [CollatzResearch.WordTrace]
  refine ⟨7727898472398683645622367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10303864629864911527496489 7727898472398683645622367)
  ·
    refine ⟨11591847708598025468433551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7727898472398683645622367 11591847708598025468433551)
    ·
      refine ⟨17387771562897038202650327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11591847708598025468433551 17387771562897038202650327)
      ·
        refine ⟨26081657344345557303975491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17387771562897038202650327 26081657344345557303975491)
        ·
          refine ⟨39122486016518335955963237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26081657344345557303975491 39122486016518335955963237)
          ·
            refine ⟨7335466128097187991743107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39122486016518335955963237 7335466128097187991743107)
            ·
              refine ⟨11003199192145781987614661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7335466128097187991743107 11003199192145781987614661)
              ·
                refine ⟨2063099848527334122677749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11003199192145781987614661 2063099848527334122677749)
                ·
                  refine ⟨193415610799437574001039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2063099848527334122677749 193415610799437574001039)
                  ·
                    rfl

theorem cell20_423760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_423760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423760 prefixEnd_423760 := by exact prefixLift 423760
  have htrace : WordTrace (prefixWord ++ tailWord_423760) baseStart_423760 baseEnd_423760 := by
    simpa [prefixWord, tailWord_423760, baseEnd_423760] using wordTrace_append hprefix tailTrace_423760
  have hstable : (prefixWord ++ tailWord_423760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423760).length < 2 ^ (prefixWord ++ tailWord_423760).sum := by decide
  have hdescent : baseEnd_423760 < baseStart_423760 := by decide
  rcases family_descends (prefixWord ++ tailWord_423760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423881 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 6]
def baseStart_423881 : Nat := 118140960795 + 423881 * 2 ^ 59
def prefixEnd_423881 : Nat := 4983230072969 + 3 ^ 40 * 423881 * 2
def baseEnd_423881 : Nat := 193470838496498930967211

theorem tailTrace_423881 : CollatzResearch.WordTrace tailWord_423881 prefixEnd_423881 193470838496498930967211 := by
  unfold tailWord_423881
  simp only [CollatzResearch.WordTrace]
  refine ⟨15460210177359004956399497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10306806784906003304266331 15460210177359004956399497)
  ·
    refine ⟨11595157633019253717299623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15460210177359004956399497 11595157633019253717299623)
    ·
      refine ⟨17392736449528880575949435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11595157633019253717299623 17392736449528880575949435)
      ·
        refine ⟨26089104674293320863924153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17392736449528880575949435 26089104674293320863924153)
        ·
          refine ⟨19566828505719990647943115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26089104674293320863924153 19566828505719990647943115)
          ·
            refine ⟨29350242758579985971914673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19566828505719990647943115 29350242758579985971914673)
            ·
              refine ⟨22012682068934989478936005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29350242758579985971914673 22012682068934989478936005)
              ·
                refine ⟨4127377887925310527300501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22012682068934989478936005 4127377887925310527300501)
                ·
                  refine ⟨193470838496498930967211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4127377887925310527300501 193470838496498930967211)
                  ·
                    rfl

theorem cell20_423881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_423881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423881 prefixEnd_423881 := by exact prefixLift 423881
  have htrace : WordTrace (prefixWord ++ tailWord_423881) baseStart_423881 baseEnd_423881 := by
    simpa [prefixWord, tailWord_423881, baseEnd_423881] using wordTrace_append hprefix tailTrace_423881
  have hstable : (prefixWord ++ tailWord_423881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423881).length < 2 ^ (prefixWord ++ tailWord_423881).sum := by decide
  have hdescent : baseEnd_423881 < baseStart_423881 := by decide
  rcases family_descends (prefixWord ++ tailWord_423881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423890 : List Nat := [3, 2, 2, 3, 2, 2, 2, 2, 2]
def baseStart_423890 : Nat := 118140960795 + 423890 * 2 ^ 59
def prefixEnd_423890 : Nat := 4983230072969 + 3 ^ 40 * 423890 * 2
def baseEnd_423890 : Nat := 193474946341734899667175

theorem tailTrace_423890 : CollatzResearch.WordTrace tailWord_423890 prefixEnd_423890 193474946341734899667175 := by
  unfold tailWord_423890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3865134608581599873369281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10307025622884266328984749 3865134608581599873369281)
  ·
    refine ⟨2898850956436199905026961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3865134608581599873369281 2898850956436199905026961)
    ·
      refine ⟨2174138217327149928770221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2898850956436199905026961 2174138217327149928770221)
      ·
        refine ⟨815301831497681223288833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2174138217327149928770221 815301831497681223288833)
        ·
          refine ⟨611476373623260917466625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 815301831497681223288833 611476373623260917466625)
          ·
            refine ⟨458607280217445688099969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 611476373623260917466625 458607280217445688099969)
            ·
              refine ⟨343955460163084266074977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458607280217445688099969 343955460163084266074977)
              ·
                refine ⟨257966595122313199556233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 343955460163084266074977 257966595122313199556233)
                ·
                  refine ⟨193474946341734899667175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257966595122313199556233 193474946341734899667175)
                  ·
                    rfl

theorem cell20_423890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_423890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423890 prefixEnd_423890 := by exact prefixLift 423890
  have htrace : WordTrace (prefixWord ++ tailWord_423890) baseStart_423890 baseEnd_423890 := by
    simpa [prefixWord, tailWord_423890, baseEnd_423890] using wordTrace_append hprefix tailTrace_423890
  have hstable : (prefixWord ++ tailWord_423890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423890).length < 2 ^ (prefixWord ++ tailWord_423890).sum := by decide
  have hdescent : baseEnd_423890 < baseStart_423890 := by decide
  rcases family_descends (prefixWord ++ tailWord_423890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423901 : List Nat := [1, 4, 3, 1, 3, 2, 1, 5]
def baseStart_423901 : Nat := 118140960795 + 423901 * 2 ^ 59
def prefixEnd_423901 : Nat := 4983230072969 + 3 ^ 40 * 423901 * 2
def baseEnd_423901 : Nat := 64493322347155916766821

theorem tailTrace_423901 : CollatzResearch.WordTrace tailWord_423901 prefixEnd_423901 64493322347155916766821 := by
  unfold tailWord_423901
  simp only [CollatzResearch.WordTrace]
  refine ⟨15460939637286548372127557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10307293091524365581418371 15460939637286548372127557)
  ·
    refine ⟨2898926181991227819773917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15460939637286548372127557 2898926181991227819773917)
    ·
      refine ⟨1087097318246710432415219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2898926181991227819773917 1087097318246710432415219)
      ·
        refine ⟨1630645977370065648622829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1087097318246710432415219 1630645977370065648622829)
        ·
          refine ⟨611492241513774618233561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1630645977370065648622829 611492241513774618233561)
          ·
            refine ⟨458619181135330963675171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 611492241513774618233561 458619181135330963675171)
            ·
              refine ⟨687928771702996445512757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458619181135330963675171 687928771702996445512757)
              ·
                refine ⟨64493322347155916766821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 687928771702996445512757 64493322347155916766821)
                ·
                  rfl

theorem cell20_423901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 5].length) (baseStart_423901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423901 prefixEnd_423901 := by exact prefixLift 423901
  have htrace : WordTrace (prefixWord ++ tailWord_423901) baseStart_423901 baseEnd_423901 := by
    simpa [prefixWord, tailWord_423901, baseEnd_423901] using wordTrace_append hprefix tailTrace_423901
  have hstable : (prefixWord ++ tailWord_423901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423901).length < 2 ^ (prefixWord ++ tailWord_423901).sum := by decide
  have hdescent : baseEnd_423901 < baseStart_423901 := by decide
  rcases family_descends (prefixWord ++ tailWord_423901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423905 : List Nat := [1, 2, 3, 1, 2, 1, 5, 5]
def baseStart_423905 : Nat := 118140960795 + 423905 * 2 ^ 59
def prefixEnd_423905 : Nat := 4983230072969 + 3 ^ 40 * 423905 * 2
def baseEnd_423905 : Nat := 64493930916820504722371

theorem tailTrace_423905 : CollatzResearch.WordTrace tailWord_423905 prefixEnd_423905 64493930916820504722371 := by
  unfold tailWord_423905
  simp only [CollatzResearch.WordTrace]
  refine ⟨15461085529272057055273169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10307390352848038036848779 15461085529272057055273169)
  ·
    refine ⟨11595814146954042791454877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15461085529272057055273169 11595814146954042791454877)
    ·
      refine ⟨4348430305107766046795579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11595814146954042791454877 4348430305107766046795579)
      ·
        refine ⟨6522645457661649070193369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4348430305107766046795579 6522645457661649070193369)
        ·
          refine ⟨4891984093246236802645027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6522645457661649070193369 4891984093246236802645027)
          ·
            refine ⟨7337976139869355203967541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4891984093246236802645027 7337976139869355203967541)
            ·
              refine ⟨687935263112752050371957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7337976139869355203967541 687935263112752050371957)
              ·
                refine ⟨64493930916820504722371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 687935263112752050371957 64493930916820504722371)
                ·
                  rfl

theorem cell20_423905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 5].length) (baseStart_423905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423905 prefixEnd_423905 := by exact prefixLift 423905
  have htrace : WordTrace (prefixWord ++ tailWord_423905) baseStart_423905 baseEnd_423905 := by
    simpa [prefixWord, tailWord_423905, baseEnd_423905] using wordTrace_append hprefix tailTrace_423905
  have hstable : (prefixWord ++ tailWord_423905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423905).length < 2 ^ (prefixWord ++ tailWord_423905).sum := by decide
  have hdescent : baseEnd_423905 < baseStart_423905 := by decide
  rcases family_descends (prefixWord ++ tailWord_423905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423912 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 7]
def baseStart_423912 : Nat := 118140960795 + 423912 * 2 ^ 59
def prefixEnd_423912 : Nat := 4983230072969 + 3 ^ 40 * 423912 * 2
def baseEnd_423912 : Nat := 193484987741200600933751

theorem tailTrace_423912 : CollatzResearch.WordTrace tailWord_423912 prefixEnd_423912 193484987741200600933751 := by
  unfold tailWord_423912
  simp only [CollatzResearch.WordTrace]
  refine ⟨7730670420123348625388995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10307560560164464833851993 7730670420123348625388995)
  ·
    refine ⟨11596005630185022938083493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7730670420123348625388995 11596005630185022938083493)
    ·
      refine ⟨2174251055659691800890655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11596005630185022938083493 2174251055659691800890655)
      ·
        refine ⟨3261376583489537701335983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2174251055659691800890655 3261376583489537701335983)
        ·
          refine ⟨4892064875234306552003975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3261376583489537701335983 4892064875234306552003975)
          ·
            refine ⟨7338097312851459828005963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4892064875234306552003975 7338097312851459828005963)
            ·
              refine ⟨11007145969277189742008945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7338097312851459828005963 11007145969277189742008945)
              ·
                refine ⟨8255359476957892306506709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11007145969277189742008945 8255359476957892306506709)
                ·
                  refine ⟨193484987741200600933751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8255359476957892306506709 193484987741200600933751)
                  ·
                    rfl

theorem cell20_423912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_423912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423912 prefixEnd_423912 := by exact prefixLift 423912
  have htrace : WordTrace (prefixWord ++ tailWord_423912) baseStart_423912 baseEnd_423912 := by
    simpa [prefixWord, tailWord_423912, baseEnd_423912] using wordTrace_append hprefix tailTrace_423912
  have hstable : (prefixWord ++ tailWord_423912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423912).length < 2 ^ (prefixWord ++ tailWord_423912).sum := by decide
  have hdescent : baseEnd_423912 < baseStart_423912 := by decide
  rcases family_descends (prefixWord ++ tailWord_423912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423943 : List Nat := [1, 1, 4, 3, 1, 3, 7]
def baseStart_423943 : Nat := 118140960795 + 423943 * 2 ^ 59
def prefixEnd_423943 : Nat := 4983230072969 + 3 ^ 40 * 423943 * 2
def baseEnd_423943 : Nat := 21499904109544696766699

theorem tailTrace_423943 : CollatzResearch.WordTrace tailWord_423943 prefixEnd_423943 21499904109544696766699 := by
  unfold tailWord_423943
  simp only [CollatzResearch.WordTrace]
  refine ⟨15462471503134389545156483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10308314335422926363437655 15462471503134389545156483)
  ·
    refine ⟨23193707254701584317734725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15462471503134389545156483 23193707254701584317734725)
    ·
      refine ⟨4348820110256547059575261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23193707254701584317734725 4348820110256547059575261)
      ·
        refine ⟨1630807541346205147340723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4348820110256547059575261 1630807541346205147340723)
        ·
          refine ⟨2446211312019307721011085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1630807541346205147340723 2446211312019307721011085)
          ·
            refine ⟨917329242007240395379157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2446211312019307721011085 917329242007240395379157)
            ·
              refine ⟨21499904109544696766699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 917329242007240395379157 21499904109544696766699)
              ·
                rfl

theorem cell20_423943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 7].length) (baseStart_423943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423943 prefixEnd_423943 := by exact prefixLift 423943
  have htrace : WordTrace (prefixWord ++ tailWord_423943) baseStart_423943 baseEnd_423943 := by
    simpa [prefixWord, tailWord_423943, baseEnd_423943] using wordTrace_append hprefix tailTrace_423943
  have hstable : (prefixWord ++ tailWord_423943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423943).length < 2 ^ (prefixWord ++ tailWord_423943).sum := by decide
  have hdescent : baseEnd_423943 < baseStart_423943 := by decide
  rcases family_descends (prefixWord ++ tailWord_423943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423991 : List Nat := [1, 1, 3, 1, 2, 2, 5, 3, 2]
def baseStart_423991 : Nat := 118140960795 + 423991 * 2 ^ 59
def prefixEnd_423991 : Nat := 4983230072969 + 3 ^ 40 * 423991 * 2
def baseEnd_423991 : Nat := 193521045493827437300095

theorem tailTrace_423991 : CollatzResearch.WordTrace tailWord_423991 prefixEnd_423991 193521045493827437300095 := by
  unfold tailWord_423991
  simp only [CollatzResearch.WordTrace]
  refine ⟨15464222206960493742903827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10309481471306995828602551 15464222206960493742903827)
  ·
    refine ⟨23196333310440740614355741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15464222206960493742903827 23196333310440740614355741)
    ·
      refine ⟨8698624991415277730383403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23196333310440740614355741 8698624991415277730383403)
      ·
        refine ⟨13047937487122916595575105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8698624991415277730383403 13047937487122916595575105)
        ·
          refine ⟨9785953115342187446681329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13047937487122916595575105 9785953115342187446681329)
          ·
            refine ⟨7339464836506640585010997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9785953115342187446681329 7339464836506640585010997)
            ·
              refine ⟨688074828422497554844781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7339464836506640585010997 688074828422497554844781)
              ·
                refine ⟨258028060658436583066793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 688074828422497554844781 258028060658436583066793)
                ·
                  refine ⟨193521045493827437300095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258028060658436583066793 193521045493827437300095)
                  ·
                    rfl

theorem cell20_423991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 2].length) (baseStart_423991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_423991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_423991 prefixEnd_423991 := by exact prefixLift 423991
  have htrace : WordTrace (prefixWord ++ tailWord_423991) baseStart_423991 baseEnd_423991 := by
    simpa [prefixWord, tailWord_423991, baseEnd_423991] using wordTrace_append hprefix tailTrace_423991
  have hstable : (prefixWord ++ tailWord_423991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423991).length < 2 ^ (prefixWord ++ tailWord_423991).sum := by decide
  have hdescent : baseEnd_423991 < baseStart_423991 := by decide
  rcases family_descends (prefixWord ++ tailWord_423991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424012 : List Nat := [2, 2, 1, 3, 1, 1, 5, 1, 4]
def baseStart_424012 : Nat := 118140960795 + 424012 * 2 ^ 59
def prefixEnd_424012 : Nat := 4983230072969 + 3 ^ 40 * 424012 * 2
def baseEnd_424012 : Nat := 193530630466044697600009

theorem tailTrace_424012 : CollatzResearch.WordTrace tailWord_424012 prefixEnd_424012 193530630466044697600009 := by
  unfold tailWord_424012
  simp only [CollatzResearch.WordTrace]
  refine ⟨7732494069942207164709145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10309992093256276219612193 7732494069942207164709145)
  ·
    refine ⟨5799370552456655373531859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7732494069942207164709145 5799370552456655373531859)
    ·
      refine ⟨8699055828684983060297789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5799370552456655373531859 8699055828684983060297789)
      ·
        refine ⟨3262145935756868647611671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8699055828684983060297789 3262145935756868647611671)
        ·
          refine ⟨4893218903635302971417507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3262145935756868647611671 4893218903635302971417507)
          ·
            refine ⟨7339828355452954457126261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4893218903635302971417507 7339828355452954457126261)
            ·
              refine ⟨688108908323714480355587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7339828355452954457126261 688108908323714480355587)
              ·
                refine ⟨1032163362485571720533381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688108908323714480355587 1032163362485571720533381)
                ·
                  refine ⟨193530630466044697600009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1032163362485571720533381 193530630466044697600009)
                  ·
                    rfl

theorem cell20_424012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_424012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424012 prefixEnd_424012 := by exact prefixLift 424012
  have htrace : WordTrace (prefixWord ++ tailWord_424012) baseStart_424012 baseEnd_424012 := by
    simpa [prefixWord, tailWord_424012, baseEnd_424012] using wordTrace_append hprefix tailTrace_424012
  have hstable : (prefixWord ++ tailWord_424012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424012).length < 2 ^ (prefixWord ++ tailWord_424012).sum := by decide
  have hdescent : baseEnd_424012 < baseStart_424012 := by decide
  rcases family_descends (prefixWord ++ tailWord_424012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424018 : List Nat := [3, 2, 2, 1, 5, 1, 2, 1, 3]
def baseStart_424018 : Nat := 118140960795 + 424018 * 2 ^ 59
def prefixEnd_424018 : Nat := 4983230072969 + 3 ^ 40 * 424018 * 2
def baseEnd_424018 : Nat := 193533369029535343399985

theorem tailTrace_424018 : CollatzResearch.WordTrace tailWord_424018 prefixEnd_424018 193533369029535343399985 := by
  unfold tailWord_424018
  simp only [CollatzResearch.WordTrace]
  refine ⟨3866301744465669338534177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10310137985241784902757805 3866301744465669338534177)
  ·
    refine ⟨2899726308349252003900633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3866301744465669338534177 2899726308349252003900633)
    ·
      refine ⟨2174794731261939002925475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2899726308349252003900633 2174794731261939002925475)
      ·
        refine ⟨3262192096892908504388213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2174794731261939002925475 3262192096892908504388213)
        ·
          refine ⟨305830509083710172286395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3262192096892908504388213 305830509083710172286395)
          ·
            refine ⟨458745763625565258429593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305830509083710172286395 458745763625565258429593)
            ·
              refine ⟨344059322719173943822195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458745763625565258429593 344059322719173943822195)
              ·
                refine ⟨516088984078760915733293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344059322719173943822195 516088984078760915733293)
                ·
                  refine ⟨193533369029535343399985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 516088984078760915733293 193533369029535343399985)
                  ·
                    rfl

theorem cell20_424018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_424018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424018 prefixEnd_424018 := by exact prefixLift 424018
  have htrace : WordTrace (prefixWord ++ tailWord_424018) baseStart_424018 baseEnd_424018 := by
    simpa [prefixWord, tailWord_424018, baseEnd_424018] using wordTrace_append hprefix tailTrace_424018
  have hstable : (prefixWord ++ tailWord_424018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424018).length < 2 ^ (prefixWord ++ tailWord_424018).sum := by decide
  have hdescent : baseEnd_424018 < baseStart_424018 := by decide
  rcases family_descends (prefixWord ++ tailWord_424018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424033 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 6]
def baseStart_424033 : Nat := 118140960795 + 424033 * 2 ^ 59
def prefixEnd_424033 : Nat := 4983230072969 + 3 ^ 40 * 424033 * 2
def baseEnd_424033 : Nat := 193540215438261957899923

theorem tailTrace_424033 : CollatzResearch.WordTrace tailWord_424033 prefixEnd_424033 193540215438261957899923 := by
  unfold tailWord_424033
  simp only [CollatzResearch.WordTrace]
  refine ⟨15465754072808334915932753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10310502715205556610621835 15465754072808334915932753)
  ·
    refine ⟨11599315554606251186949565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15465754072808334915932753 11599315554606251186949565)
    ·
      refine ⟨4349743332977344195106087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11599315554606251186949565 4349743332977344195106087)
      ·
        refine ⟨6524614999466016292659131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4349743332977344195106087 6524614999466016292659131)
        ·
          refine ⟨9786922499199024438988697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6524614999466016292659131 9786922499199024438988697)
          ·
            refine ⟨7340191874399268329241523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9786922499199024438988697 7340191874399268329241523)
            ·
              refine ⟨11010287811598902493862285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7340191874399268329241523 11010287811598902493862285)
              ·
                refine ⟨4128857929349588435198357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11010287811598902493862285 4128857929349588435198357)
                ·
                  refine ⟨193540215438261957899923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4128857929349588435198357 193540215438261957899923)
                  ·
                    rfl

theorem cell20_424033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_424033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424033 prefixEnd_424033 := by exact prefixLift 424033
  have htrace : WordTrace (prefixWord ++ tailWord_424033) baseStart_424033 baseEnd_424033 := by
    simpa [prefixWord, tailWord_424033, baseEnd_424033] using wordTrace_append hprefix tailTrace_424033
  have hstable : (prefixWord ++ tailWord_424033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424033).length < 2 ^ (prefixWord ++ tailWord_424033).sum := by decide
  have hdescent : baseEnd_424033 < baseStart_424033 := by decide
  rcases family_descends (prefixWord ++ tailWord_424033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424067 : List Nat := [1, 1, 1, 3, 3, 4, 1, 4, 2]
def baseStart_424067 : Nat := 118140960795 + 424067 * 2 ^ 59
def prefixEnd_424067 : Nat := 4983230072969 + 3 ^ 40 * 424067 * 2
def baseEnd_424067 : Nat := 193555733964708950766451

theorem tailTrace_424067 : CollatzResearch.WordTrace tailWord_424067 prefixEnd_424067 193555733964708950766451 := by
  unfold tailWord_424067
  simp only [CollatzResearch.WordTrace]
  refine ⟨15466994154685158722670455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10311329436456772481780303 15466994154685158722670455)
  ·
    refine ⟨23200491232027738084005683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15466994154685158722670455 23200491232027738084005683)
    ·
      refine ⟨34800736848041607126008525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23200491232027738084005683 34800736848041607126008525)
      ·
        refine ⟨13050276318015602672253197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34800736848041607126008525 13050276318015602672253197)
        ·
          refine ⟨4893853619255851002094949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13050276318015602672253197 4893853619255851002094949)
          ·
            refine ⟨917597553610472062892803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4893853619255851002094949 917597553610472062892803)
            ·
              refine ⟨1376396330415708094339205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917597553610472062892803 1376396330415708094339205)
              ·
                refine ⟨258074311952945267688601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1376396330415708094339205 258074311952945267688601)
                ·
                  refine ⟨193555733964708950766451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258074311952945267688601 193555733964708950766451)
                  ·
                    rfl

theorem cell20_424067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 2].length) (baseStart_424067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424067 prefixEnd_424067 := by exact prefixLift 424067
  have htrace : WordTrace (prefixWord ++ tailWord_424067) baseStart_424067 baseEnd_424067 := by
    simpa [prefixWord, tailWord_424067, baseEnd_424067] using wordTrace_append hprefix tailTrace_424067
  have hstable : (prefixWord ++ tailWord_424067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424067).length < 2 ^ (prefixWord ++ tailWord_424067).sum := by decide
  have hdescent : baseEnd_424067 < baseStart_424067 := by decide
  rcases family_descends (prefixWord ++ tailWord_424067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424074 : List Nat := [3, 1, 2, 3, 1, 4, 1, 5]
def baseStart_424074 : Nat := 118140960795 + 424074 * 2 ^ 59
def prefixEnd_424074 : Nat := 4983230072969 + 3 ^ 40 * 424074 * 2
def baseEnd_424074 : Nat := 64519642985149345844363

theorem tailTrace_424074 : CollatzResearch.WordTrace tailWord_424074 prefixEnd_424074 64519642985149345844363 := by
  unfold tailWord_424074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3866812366414949729543819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10311499643773199278783517 3866812366414949729543819)
  ·
    refine ⟨5800218549622424594315729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3866812366414949729543819 5800218549622424594315729)
    ·
      refine ⟨4350163912216818445736797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5800218549622424594315729 4350163912216818445736797)
      ·
        refine ⟨1631311467081306917151299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4350163912216818445736797 1631311467081306917151299)
        ·
          refine ⟨2446967200621960375726949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1631311467081306917151299 2446967200621960375726949)
          ·
            refine ⟨458806350116617570448803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2446967200621960375726949 458806350116617570448803)
            ·
              refine ⟨688209525174926355673205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458806350116617570448803 688209525174926355673205)
              ·
                refine ⟨64519642985149345844363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 688209525174926355673205 64519642985149345844363)
                ·
                  rfl

theorem cell20_424074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_424074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424074 prefixEnd_424074 := by exact prefixLift 424074
  have htrace : WordTrace (prefixWord ++ tailWord_424074) baseStart_424074 baseEnd_424074 := by
    simpa [prefixWord, tailWord_424074, baseEnd_424074] using wordTrace_append hprefix tailTrace_424074
  have hstable : (prefixWord ++ tailWord_424074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424074).length < 2 ^ (prefixWord ++ tailWord_424074).sum := by decide
  have hdescent : baseEnd_424074 < baseStart_424074 := by decide
  rcases family_descends (prefixWord ++ tailWord_424074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424084 : List Nat := [2, 4, 2, 3, 1, 1, 1, 2, 4]
def baseStart_424084 : Nat := 118140960795 + 424084 * 2 ^ 59
def prefixEnd_424084 : Nat := 4983230072969 + 3 ^ 40 * 424084 * 2
def baseEnd_424084 : Nat := 193563493227932447199715

theorem tailTrace_424084 : CollatzResearch.WordTrace tailWord_424084 prefixEnd_424084 193563493227932447199715 := by
  unfold tailWord_424084
  simp only [CollatzResearch.WordTrace]
  refine ⟨7733807097811785313019653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10311742797082380417359537 7733807097811785313019653)
  ·
    refine ⟨1450088830839709746191185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7733807097811785313019653 1450088830839709746191185)
    ·
      refine ⟨1087566623129782309643389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1450088830839709746191185 1087566623129782309643389)
      ·
        refine ⟨407837483673668366116271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1087566623129782309643389 407837483673668366116271)
        ·
          refine ⟨611756225510502549174407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407837483673668366116271 611756225510502549174407)
          ·
            refine ⟨917634338265753823761611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611756225510502549174407 917634338265753823761611)
            ·
              refine ⟨1376451507398630735642417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917634338265753823761611 1376451507398630735642417)
              ·
                refine ⟨1032338630548973051731813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1376451507398630735642417 1032338630548973051731813)
                ·
                  refine ⟨193563493227932447199715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1032338630548973051731813 193563493227932447199715)
                  ·
                    rfl

theorem cell20_424084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_424084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424084 prefixEnd_424084 := by exact prefixLift 424084
  have htrace : WordTrace (prefixWord ++ tailWord_424084) baseStart_424084 baseEnd_424084 := by
    simpa [prefixWord, tailWord_424084, baseEnd_424084] using wordTrace_append hprefix tailTrace_424084
  have hstable : (prefixWord ++ tailWord_424084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424084).length < 2 ^ (prefixWord ++ tailWord_424084).sum := by decide
  have hdescent : baseEnd_424084 < baseStart_424084 := by decide
  rcases family_descends (prefixWord ++ tailWord_424084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424119 : List Nat := [1, 1, 3, 1, 4, 2, 3, 2, 3]
def baseStart_424119 : Nat := 118140960795 + 424119 * 2 ^ 59
def prefixEnd_424119 : Nat := 4983230072969 + 3 ^ 40 * 424119 * 2
def baseEnd_424119 : Nat := 193579468181627881032905

theorem tailTrace_424119 : CollatzResearch.WordTrace tailWord_424119 prefixEnd_424119 193579468181627881032905 := by
  unfold tailWord_424119
  simp only [CollatzResearch.WordTrace]
  refine ⟨15468890750496771603563411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10312593833664514402375607 15468890750496771603563411)
  ·
    refine ⟨23203336125745157405345117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15468890750496771603563411 23203336125745157405345117)
    ·
      refine ⟨8701251047154434027004419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23203336125745157405345117 8701251047154434027004419)
      ·
        refine ⟨13051876570731651040506629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8701251047154434027004419 13051876570731651040506629)
        ·
          refine ⟨2447226857012184570094993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13051876570731651040506629 2447226857012184570094993)
          ·
            refine ⟨1835420142759138427571245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2447226857012184570094993 1835420142759138427571245)
            ·
              refine ⟨688282553534676910339217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1835420142759138427571245 688282553534676910339217)
              ·
                refine ⟨516211915151007682754413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688282553534676910339217 516211915151007682754413)
                ·
                  refine ⟨193579468181627881032905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 516211915151007682754413 193579468181627881032905)
                  ·
                    rfl

theorem cell20_424119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 3].length) (baseStart_424119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424119 prefixEnd_424119 := by exact prefixLift 424119
  have htrace : WordTrace (prefixWord ++ tailWord_424119) baseStart_424119 baseEnd_424119 := by
    simpa [prefixWord, tailWord_424119, baseEnd_424119] using wordTrace_append hprefix tailTrace_424119
  have hstable : (prefixWord ++ tailWord_424119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424119).length < 2 ^ (prefixWord ++ tailWord_424119).sum := by decide
  have hdescent : baseEnd_424119 < baseStart_424119 := by decide
  rcases family_descends (prefixWord ++ tailWord_424119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424156 : List Nat := [2, 2, 5, 2, 1, 2, 1, 3, 2]
def baseStart_424156 : Nat := 118140960795 + 424156 * 2 ^ 59
def prefixEnd_424156 : Nat := 4983230072969 + 3 ^ 40 * 424156 * 2
def baseEnd_424156 : Nat := 193596355989820196799421

theorem tailTrace_424156 : CollatzResearch.WordTrace tailWord_424156 prefixEnd_424156 193596355989820196799421 := by
  unfold tailWord_424156
  simp only [CollatzResearch.WordTrace]
  refine ⟨7735120125681363461330161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10313493500908484615106881 7735120125681363461330161)
  ·
    refine ⟨5801340094261022595997621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7735120125681363461330161 5801340094261022595997621)
    ·
      refine ⟨543875633836970868374777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5801340094261022595997621 543875633836970868374777)
      ·
        refine ⟨407906725377728151281083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543875633836970868374777 407906725377728151281083)
        ·
          refine ⟨611860088066592226921625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407906725377728151281083 611860088066592226921625)
          ·
            refine ⟨458895066049944170191219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 611860088066592226921625 458895066049944170191219)
            ·
              refine ⟨688342599074916255286829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458895066049944170191219 688342599074916255286829)
              ·
                refine ⟨258128474653093595732561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 688342599074916255286829 258128474653093595732561)
                ·
                  refine ⟨193596355989820196799421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258128474653093595732561 193596355989820196799421)
                  ·
                    rfl

theorem cell20_424156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_424156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424156 prefixEnd_424156 := by exact prefixLift 424156
  have htrace : WordTrace (prefixWord ++ tailWord_424156) baseStart_424156 baseEnd_424156 := by
    simpa [prefixWord, tailWord_424156, baseEnd_424156] using wordTrace_append hprefix tailTrace_424156
  have hstable : (prefixWord ++ tailWord_424156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424156).length < 2 ^ (prefixWord ++ tailWord_424156).sum := by decide
  have hdescent : baseEnd_424156 < baseStart_424156 := by decide
  rcases family_descends (prefixWord ++ tailWord_424156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424157 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 5]
def baseStart_424157 : Nat := 118140960795 + 424157 * 2 ^ 59
def prefixEnd_424157 : Nat := 4983230072969 + 3 ^ 40 * 424157 * 2
def baseEnd_424157 : Nat := 193596812417068637766083

theorem tailTrace_424157 : CollatzResearch.WordTrace tailWord_424157 prefixEnd_424157 193596812417068637766083 := by
  unfold tailWord_424157
  simp only [CollatzResearch.WordTrace]
  refine ⟨15470276724359104093446725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10313517816239402728964483 15470276724359104093446725)
  ·
    refine ⟨2900676885817332017521261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15470276724359104093446725 2900676885817332017521261)
    ·
      refine ⟨1087753832181499506570473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2900676885817332017521261 1087753832181499506570473)
      ·
        refine ⟨815815374136124629927855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1087753832181499506570473 815815374136124629927855)
        ·
          refine ⟨1223723061204186944891783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815815374136124629927855 1223723061204186944891783)
          ·
            refine ⟨1835584591806280417337675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1223723061204186944891783 1835584591806280417337675)
            ·
              refine ⟨2753376887709420626006513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835584591806280417337675 2753376887709420626006513)
              ·
                refine ⟨2065032665782065469504885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2753376887709420626006513 2065032665782065469504885)
                ·
                  refine ⟨193596812417068637766083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2065032665782065469504885 193596812417068637766083)
                  ·
                    rfl

theorem cell20_424157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_424157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424157 prefixEnd_424157 := by exact prefixLift 424157
  have htrace : WordTrace (prefixWord ++ tailWord_424157) baseStart_424157 baseEnd_424157 := by
    simpa [prefixWord, tailWord_424157, baseEnd_424157] using wordTrace_append hprefix tailTrace_424157
  have hstable : (prefixWord ++ tailWord_424157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424157).length < 2 ^ (prefixWord ++ tailWord_424157).sum := by decide
  have hdescent : baseEnd_424157 < baseStart_424157 := by decide
  rcases family_descends (prefixWord ++ tailWord_424157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424185 : List Nat := [1, 2, 1, 3, 1, 1, 2, 5, 4]
def baseStart_424185 : Nat := 118140960795 + 424185 * 2 ^ 59
def prefixEnd_424185 : Nat := 4983230072969 + 3 ^ 40 * 424185 * 2
def baseEnd_424185 : Nat := 193609592380024984832635

theorem tailTrace_424185 : CollatzResearch.WordTrace tailWord_424185 prefixEnd_424185 193609592380024984832635 := by
  unfold tailWord_424185
  simp only [CollatzResearch.WordTrace]
  refine ⟨15471297968257664875466009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10314198645505109916977339 15471297968257664875466009)
  ·
    refine ⟨11603473476193248656599507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15471297968257664875466009 11603473476193248656599507)
    ·
      refine ⟨17405210214289872984899261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11603473476193248656599507 17405210214289872984899261)
      ·
        refine ⟨6526953830358702369337223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17405210214289872984899261 6526953830358702369337223)
        ·
          refine ⟨9790430745538053554005835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6526953830358702369337223 9790430745538053554005835)
          ·
            refine ⟨14685646118307080331008753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9790430745538053554005835 14685646118307080331008753)
            ·
              refine ⟨11014234588730310248256565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14685646118307080331008753 11014234588730310248256565)
              ·
                refine ⟨1032584492693466585774053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11014234588730310248256565 1032584492693466585774053)
                ·
                  refine ⟨193609592380024984832635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1032584492693466585774053 193609592380024984832635)
                  ·
                    rfl

theorem cell20_424185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_424185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424185 prefixEnd_424185 := by exact prefixLift 424185
  have htrace : WordTrace (prefixWord ++ tailWord_424185) baseStart_424185 baseEnd_424185 := by
    simpa [prefixWord, tailWord_424185, baseEnd_424185] using wordTrace_append hprefix tailTrace_424185
  have hstable : (prefixWord ++ tailWord_424185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424185).length < 2 ^ (prefixWord ++ tailWord_424185).sum := by decide
  have hdescent : baseEnd_424185 < baseStart_424185 := by decide
  rcases family_descends (prefixWord ++ tailWord_424185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424192 : List Nat := [2, 1, 1, 2, 1, 1, 5, 7]
def baseStart_424192 : Nat := 118140960795 + 424192 * 2 ^ 59
def prefixEnd_424192 : Nat := 4983230072969 + 3 ^ 40 * 424192 * 2
def baseEnd_424192 : Nat := 64537595790254690533091

theorem tailTrace_424192 : CollatzResearch.WordTrace tailWord_424192 prefixEnd_424192 64537595790254690533091 := by
  unfold tailWord_424192
  simp only [CollatzResearch.WordTrace]
  refine ⟨7735776639616152535485415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10314368852821536713980553 7735776639616152535485415)
  ·
    refine ⟨11603664959424228803228123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7735776639616152535485415 11603664959424228803228123)
    ·
      refine ⟨17405497439136343204842185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11603664959424228803228123 17405497439136343204842185)
      ·
        refine ⟨13054123079352257403631639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17405497439136343204842185 13054123079352257403631639)
        ·
          refine ⟨19581184619028386105447459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13054123079352257403631639 19581184619028386105447459)
          ·
            refine ⟨29371776928542579158171189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19581184619028386105447459 29371776928542579158171189)
            ·
              refine ⟨2753604087050866796078549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29371776928542579158171189 2753604087050866796078549)
              ·
                refine ⟨64537595790254690533091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2753604087050866796078549 64537595790254690533091)
                ·
                  rfl

theorem cell20_424192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_424192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424192 prefixEnd_424192 := by exact prefixLift 424192
  have htrace : WordTrace (prefixWord ++ tailWord_424192) baseStart_424192 baseEnd_424192 := by
    simpa [prefixWord, tailWord_424192, baseEnd_424192] using wordTrace_append hprefix tailTrace_424192
  have hstable : (prefixWord ++ tailWord_424192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424192).length < 2 ^ (prefixWord ++ tailWord_424192).sum := by decide
  have hdescent : baseEnd_424192 < baseStart_424192 := by decide
  rcases family_descends (prefixWord ++ tailWord_424192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424232 : List Nat := [2, 1, 5, 1, 4, 1, 2, 2, 2]
def baseStart_424232 : Nat := 118140960795 + 424232 * 2 ^ 59
def prefixEnd_424232 : Nat := 4983230072969 + 3 ^ 40 * 424232 * 2
def baseEnd_424232 : Nat := 193631044460701710265777

theorem tailTrace_424232 : CollatzResearch.WordTrace tailWord_424232 prefixEnd_424232 193631044460701710265777 := by
  unfold tailWord_424232
  simp only [CollatzResearch.WordTrace]
  refine ⟨7736506099543695951213475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10315341466058261268284633 7736506099543695951213475)
  ·
    refine ⟨11604759149315543926820213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7736506099543695951213475 11604759149315543926820213)
    ·
      refine ⟨1087946170248332243139395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11604759149315543926820213 1087946170248332243139395)
      ·
        refine ⟨1631919255372498364709093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1087946170248332243139395 1631919255372498364709093)
        ·
          refine ⟨305984860382343443382955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1631919255372498364709093 305984860382343443382955)
          ·
            refine ⟨458977290573515165074433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305984860382343443382955 458977290573515165074433)
            ·
              refine ⟨344232967930136373805825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458977290573515165074433 344232967930136373805825)
              ·
                refine ⟨258174725947602280354369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344232967930136373805825 258174725947602280354369)
                ·
                  refine ⟨193631044460701710265777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258174725947602280354369 193631044460701710265777)
                  ·
                    rfl

theorem cell20_424232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 2].length) (baseStart_424232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424232 prefixEnd_424232 := by exact prefixLift 424232
  have htrace : WordTrace (prefixWord ++ tailWord_424232) baseStart_424232 baseEnd_424232 := by
    simpa [prefixWord, tailWord_424232, baseEnd_424232] using wordTrace_append hprefix tailTrace_424232
  have hstable : (prefixWord ++ tailWord_424232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424232).length < 2 ^ (prefixWord ++ tailWord_424232).sum := by decide
  have hdescent : baseEnd_424232 < baseStart_424232 := by decide
  rcases family_descends (prefixWord ++ tailWord_424232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424257 : List Nat := [1, 2, 5, 2, 2, 1, 1, 2, 4]
def baseStart_424257 : Nat := 118140960795 + 424257 * 2 ^ 59
def prefixEnd_424257 : Nat := 4983230072969 + 3 ^ 40 * 424257 * 2
def baseEnd_424257 : Nat := 193642455141912734432341

theorem tailTrace_424257 : CollatzResearch.WordTrace tailWord_424257 prefixEnd_424257 193642455141912734432341 := by
  unfold tailWord_424257
  simp only [CollatzResearch.WordTrace]
  refine ⟨15473924023996821172087025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10315949349331214114724683 15473924023996821172087025)
  ·
    refine ⟨11605443017997615879065269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15473924023996821172087025 11605443017997615879065269)
    ·
      refine ⟨1088010282937276488662369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11605443017997615879065269 1088010282937276488662369)
      ·
        refine ⟨816007712202957366496777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1088010282937276488662369 816007712202957366496777)
        ·
          refine ⟨612005784152218024872583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 816007712202957366496777 612005784152218024872583)
          ·
            refine ⟨918008676228327037308875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612005784152218024872583 918008676228327037308875)
            ·
              refine ⟨1377013014342490555963313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 918008676228327037308875 1377013014342490555963313)
              ·
                refine ⟨1032759760756867916972485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1377013014342490555963313 1032759760756867916972485)
                ·
                  refine ⟨193642455141912734432341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1032759760756867916972485 193642455141912734432341)
                  ·
                    rfl

theorem cell20_424257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_424257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424257 prefixEnd_424257 := by exact prefixLift 424257
  have htrace : WordTrace (prefixWord ++ tailWord_424257) baseStart_424257 baseEnd_424257 := by
    simpa [prefixWord, tailWord_424257, baseEnd_424257] using wordTrace_append hprefix tailTrace_424257
  have hstable : (prefixWord ++ tailWord_424257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424257).length < 2 ^ (prefixWord ++ tailWord_424257).sum := by decide
  have hdescent : baseEnd_424257 < baseStart_424257 := by decide
  rcases family_descends (prefixWord ++ tailWord_424257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424284 : List Nat := [2, 2, 4, 3, 2, 1, 1, 2, 3]
def baseStart_424284 : Nat := 118140960795 + 424284 * 2 ^ 59
def prefixEnd_424284 : Nat := 4983230072969 + 3 ^ 40 * 424284 * 2
def baseEnd_424284 : Nat := 193654778677620640532231

theorem tailTrace_424284 : CollatzResearch.WordTrace tailWord_424284 prefixEnd_424284 193654778677620640532231 := by
  unfold tailWord_424284
  simp only [CollatzResearch.WordTrace]
  refine ⟨7737454397449502391659953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10316605863266003188879937 7737454397449502391659953)
  ·
    refine ⟨5803090798087126793744965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7737454397449502391659953 5803090798087126793744965)
    ·
      refine ⟨1088079524641336273827181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5803090798087126793744965 1088079524641336273827181)
      ·
        refine ⟨408029821740501102685193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1088079524641336273827181 408029821740501102685193)
        ·
          refine ⟨306022366305375827013895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408029821740501102685193 306022366305375827013895)
          ·
            refine ⟨459033549458063740520843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306022366305375827013895 459033549458063740520843)
            ·
              refine ⟨688550324187095610781265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459033549458063740520843 688550324187095610781265)
              ·
                refine ⟨516412743140321708085949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688550324187095610781265 516412743140321708085949)
                ·
                  refine ⟨193654778677620640532231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 516412743140321708085949 193654778677620640532231)
                  ·
                    rfl

theorem cell20_424284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_424284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424284 prefixEnd_424284 := by exact prefixLift 424284
  have htrace : WordTrace (prefixWord ++ tailWord_424284) baseStart_424284 baseEnd_424284 := by
    simpa [prefixWord, tailWord_424284, baseEnd_424284] using wordTrace_append hprefix tailTrace_424284
  have hstable : (prefixWord ++ tailWord_424284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424284).length < 2 ^ (prefixWord ++ tailWord_424284).sum := by decide
  have hdescent : baseEnd_424284 < baseStart_424284 := by decide
  rcases family_descends (prefixWord ++ tailWord_424284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424288 : List Nat := [2, 1, 1, 3, 5, 2, 1, 2, 3]
def baseStart_424288 : Nat := 118140960795 + 424288 * 2 ^ 59
def prefixEnd_424288 : Nat := 4983230072969 + 3 ^ 40 * 424288 * 2
def baseEnd_424288 : Nat := 193656604386614404398881

theorem tailTrace_424288 : CollatzResearch.WordTrace tailWord_424288 prefixEnd_424288 193656604386614404398881 := by
  unfold tailWord_424288
  simp only [CollatzResearch.WordTrace]
  refine ⟨7737527343442256733232759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10316703124589675644310345 7737527343442256733232759)
  ·
    refine ⟨11606291015163385099849139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7737527343442256733232759 11606291015163385099849139)
    ·
      refine ⟨17409436522745077649773709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11606291015163385099849139 17409436522745077649773709)
      ·
        refine ⟨6528538696029404118665141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17409436522745077649773709 6528538696029404118665141)
        ·
          refine ⟨612050502752756636124857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6528538696029404118665141 612050502752756636124857)
          ·
            refine ⟨459037877064567477093643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 612050502752756636124857 459037877064567477093643)
            ·
              refine ⟨688556815596851215640465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459037877064567477093643 688556815596851215640465)
              ·
                refine ⟨516417611697638411730349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688556815596851215640465 516417611697638411730349)
                ·
                  refine ⟨193656604386614404398881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 516417611697638411730349 193656604386614404398881)
                  ·
                    rfl

theorem cell20_424288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 3].length) (baseStart_424288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424288 prefixEnd_424288 := by exact prefixLift 424288
  have htrace : WordTrace (prefixWord ++ tailWord_424288) baseStart_424288 baseEnd_424288 := by
    simpa [prefixWord, tailWord_424288, baseEnd_424288] using wordTrace_append hprefix tailTrace_424288
  have hstable : (prefixWord ++ tailWord_424288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424288).length < 2 ^ (prefixWord ++ tailWord_424288).sum := by decide
  have hdescent : baseEnd_424288 < baseStart_424288 := by decide
  rcases family_descends (prefixWord ++ tailWord_424288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424292 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 5]
def baseStart_424292 : Nat := 118140960795 + 424292 * 2 ^ 59
def prefixEnd_424292 : Nat := 4983230072969 + 3 ^ 40 * 424292 * 2
def baseEnd_424292 : Nat := 193658430095608168265531

theorem tailTrace_424292 : CollatzResearch.WordTrace tailWord_424292 prefixEnd_424292 193658430095608168265531 := by
  unfold tailWord_424292
  simp only [CollatzResearch.WordTrace]
  refine ⟨7737600289435011074805565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10316800385913348099740753 7737600289435011074805565)
  ·
    refine ⟨2901600108538129153052087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7737600289435011074805565 2901600108538129153052087)
    ·
      refine ⟨4352400162807193729578131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2901600108538129153052087 4352400162807193729578131)
      ·
        refine ⟨6528600244210790594367197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4352400162807193729578131 6528600244210790594367197)
        ·
          refine ⟨2448225091579046472887699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6528600244210790594367197 2448225091579046472887699)
          ·
            refine ⟨3672337637368569709331549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2448225091579046472887699 3672337637368569709331549)
            ·
              refine ⟨1377126614013213640999331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3672337637368569709331549 1377126614013213640999331)
              ·
                refine ⟨2065689921019820461498997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1377126614013213640999331 2065689921019820461498997)
                ·
                  refine ⟨193658430095608168265531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2065689921019820461498997 193658430095608168265531)
                  ·
                    rfl

theorem cell20_424292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_424292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424292 prefixEnd_424292 := by exact prefixLift 424292
  have htrace : WordTrace (prefixWord ++ tailWord_424292) baseStart_424292 baseEnd_424292 := by
    simpa [prefixWord, tailWord_424292, baseEnd_424292] using wordTrace_append hprefix tailTrace_424292
  have hstable : (prefixWord ++ tailWord_424292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424292).length < 2 ^ (prefixWord ++ tailWord_424292).sum := by decide
  have hdescent : baseEnd_424292 < baseStart_424292 := by decide
  rcases family_descends (prefixWord ++ tailWord_424292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424295 : List Nat := [1, 1, 5, 1, 3, 1, 2, 4, 2]
def baseStart_424295 : Nat := 118140960795 + 424295 * 2 ^ 59
def prefixEnd_424295 : Nat := 4983230072969 + 3 ^ 40 * 424295 * 2
def baseEnd_424295 : Nat := 193659799377353491165519

theorem tailTrace_424295 : CollatzResearch.WordTrace tailWord_424295 prefixEnd_424295 193659799377353491165519 := by
  unfold tailWord_424295
  simp only [CollatzResearch.WordTrace]
  refine ⟨15475309997859153661970339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10316873331906102441313559 15475309997859153661970339)
  ·
    refine ⟨23212964996788730492955509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15475309997859153661970339 23212964996788730492955509)
    ·
      refine ⟨2176215468448943483714579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23212964996788730492955509 2176215468448943483714579)
      ·
        refine ⟨3264323202673415225571869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2176215468448943483714579 3264323202673415225571869)
        ·
          refine ⟨1224121201002530709589451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3264323202673415225571869 1224121201002530709589451)
          ·
            refine ⟨1836181801503796064384177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224121201002530709589451 1836181801503796064384177)
            ·
              refine ⟨1377136351127847048288133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1836181801503796064384177 1377136351127847048288133)
              ·
                refine ⟨258213065836471321554025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1377136351127847048288133 258213065836471321554025)
                ·
                  refine ⟨193659799377353491165519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258213065836471321554025 193659799377353491165519)
                  ·
                    rfl

theorem cell20_424295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 2].length) (baseStart_424295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424295 prefixEnd_424295 := by exact prefixLift 424295
  have htrace : WordTrace (prefixWord ++ tailWord_424295) baseStart_424295 baseEnd_424295 := by
    simpa [prefixWord, tailWord_424295, baseEnd_424295] using wordTrace_append hprefix tailTrace_424295
  have hstable : (prefixWord ++ tailWord_424295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424295).length < 2 ^ (prefixWord ++ tailWord_424295).sum := by decide
  have hdescent : baseEnd_424295 < baseStart_424295 := by decide
  rcases family_descends (prefixWord ++ tailWord_424295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424323 : List Nat := [1, 1, 1, 3, 6, 1, 1, 6]
def baseStart_424323 : Nat := 118140960795 + 424323 * 2 ^ 59
def prefixEnd_424323 : Nat := 4983230072969 + 3 ^ 40 * 424323 * 2
def baseEnd_424323 : Nat := 64557526446769946077357

theorem tailTrace_424323 : CollatzResearch.WordTrace tailWord_424323 prefixEnd_424323 64557526446769946077357 := by
  unfold tailWord_424323
  simp only [CollatzResearch.WordTrace]
  refine ⟨15476331241757714443989623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10317554161171809629326415 15476331241757714443989623)
  ·
    refine ⟨23214496862636571665984435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15476331241757714443989623 23214496862636571665984435)
    ·
      refine ⟨34821745293954857498976653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23214496862636571665984435 34821745293954857498976653)
      ·
        refine ⟨13058154485233071562116245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34821745293954857498976653 13058154485233071562116245)
        ·
          refine ⟨612100991495300229474199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13058154485233071562116245 612100991495300229474199)
          ·
            refine ⟨918151487242950344211299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612100991495300229474199 918151487242950344211299)
            ·
              refine ⟨1377227230864425516316949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 918151487242950344211299 1377227230864425516316949)
              ·
                refine ⟨64557526446769946077357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1377227230864425516316949 64557526446769946077357)
                ·
                  rfl

theorem cell20_424323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 6].length) (baseStart_424323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424323 prefixEnd_424323 := by exact prefixLift 424323
  have htrace : WordTrace (prefixWord ++ tailWord_424323) baseStart_424323 baseEnd_424323 := by
    simpa [prefixWord, tailWord_424323, baseEnd_424323] using wordTrace_append hprefix tailTrace_424323
  have hstable : (prefixWord ++ tailWord_424323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424323).length < 2 ^ (prefixWord ++ tailWord_424323).sum := by decide
  have hdescent : baseEnd_424323 < baseStart_424323 := by decide
  rcases family_descends (prefixWord ++ tailWord_424323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424340 : List Nat := [2, 4, 2, 1, 3, 2, 6]
def baseStart_424340 : Nat := 118140960795 + 424340 * 2 ^ 59
def prefixEnd_424340 : Nat := 4983230072969 + 3 ^ 40 * 424340 * 2
def baseEnd_424340 : Nat := 21520037622614814962815

theorem tailTrace_424340 : CollatzResearch.WordTrace tailWord_424340 prefixEnd_424340 21520037622614814962815 := by
  unfold tailWord_424340
  simp only [CollatzResearch.WordTrace]
  refine ⟨7738475641348063173679237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10317967521797417564905649 7738475641348063173679237)
  ·
    refine ⟨1450964182752761845064857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7738475641348063173679237 1450964182752761845064857)
    ·
      refine ⟨1088223137064571383798643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1450964182752761845064857 1088223137064571383798643)
      ·
        refine ⟨1632334705596857075697965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1088223137064571383798643 1632334705596857075697965)
        ·
          refine ⟨612125514598821403386737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1632334705596857075697965 612125514598821403386737)
          ·
            refine ⟨459094135949116052540053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 612125514598821403386737 459094135949116052540053)
            ·
              refine ⟨21520037622614814962815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 459094135949116052540053 21520037622614814962815)
              ·
                rfl

theorem cell20_424340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 6].length) (baseStart_424340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424340 prefixEnd_424340 := by exact prefixLift 424340
  have htrace : WordTrace (prefixWord ++ tailWord_424340) baseStart_424340 baseEnd_424340 := by
    simpa [prefixWord, tailWord_424340, baseEnd_424340] using wordTrace_append hprefix tailTrace_424340
  have hstable : (prefixWord ++ tailWord_424340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424340).length < 2 ^ (prefixWord ++ tailWord_424340).sum := by decide
  have hdescent : baseEnd_424340 < baseStart_424340 := by decide
  rcases family_descends (prefixWord ++ tailWord_424340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424350 : List Nat := [4, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_424350 : Nat := 118140960795 + 424350 * 2 ^ 59
def prefixEnd_424350 : Nat := 4983230072969 + 3 ^ 40 * 424350 * 2
def baseEnd_424350 : Nat := 193684902876017744331961

theorem tailTrace_424350 : CollatzResearch.WordTrace tailWord_424350 prefixEnd_424350 193684902876017744331961 := by
  unfold tailWord_424350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1934664501582487256902813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10318210675106598703481669 1934664501582487256902813)
  ·
    refine ⟨725499188093432721338555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1934664501582487256902813 725499188093432721338555)
    ·
      refine ⟨1088248782140149082007833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 725499188093432721338555 1088248782140149082007833)
      ·
        refine ⟨816186586605111811505875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1088248782140149082007833 816186586605111811505875)
        ·
          refine ⟨1224279879907667717258813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816186586605111811505875 1224279879907667717258813)
          ·
            refine ⟨459104954965375393972055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1224279879907667717258813 459104954965375393972055)
            ·
              refine ⟨688657432448063090958083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459104954965375393972055 688657432448063090958083)
              ·
                refine ⟨1032986148672094636437125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688657432448063090958083 1032986148672094636437125)
                ·
                  refine ⟨193684902876017744331961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1032986148672094636437125 193684902876017744331961)
                  ·
                    rfl

theorem cell20_424350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_424350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424350 prefixEnd_424350 := by exact prefixLift 424350
  have htrace : WordTrace (prefixWord ++ tailWord_424350) baseStart_424350 baseEnd_424350 := by
    simpa [prefixWord, tailWord_424350, baseEnd_424350] using wordTrace_append hprefix tailTrace_424350
  have hstable : (prefixWord ++ tailWord_424350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424350).length < 2 ^ (prefixWord ++ tailWord_424350).sum := by decide
  have hdescent : baseEnd_424350 < baseStart_424350 := by decide
  rcases family_descends (prefixWord ++ tailWord_424350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424430 : List Nat := [4, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_424430 : Nat := 118140960795 + 424430 * 2 ^ 59
def prefixEnd_424430 : Nat := 4983230072969 + 3 ^ 40 * 424430 * 2
def baseEnd_424430 : Nat := 193721417055893021664967

theorem tailTrace_424430 : CollatzResearch.WordTrace tailWord_424430 prefixEnd_424430 193721417055893021664967 := by
  unfold tailWord_424430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935029231546258964766843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10320155901580047812089829 1935029231546258964766843)
  ·
    refine ⟨2902543847319388447150265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1935029231546258964766843 2902543847319388447150265)
    ·
      refine ⟨2176907885489541335362699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2902543847319388447150265 2176907885489541335362699)
      ·
        refine ⟨3265361828234312003044049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2176907885489541335362699 3265361828234312003044049)
        ·
          refine ⟨2449021371175734002283037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3265361828234312003044049 2449021371175734002283037)
          ·
            refine ⟨918383014190900250856139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2449021371175734002283037 918383014190900250856139)
            ·
              refine ⟨1377574521286350376284209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 918383014190900250856139 1377574521286350376284209)
              ·
                refine ⟨1033180890964762782213157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1377574521286350376284209 1033180890964762782213157)
                ·
                  refine ⟨193721417055893021664967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1033180890964762782213157 193721417055893021664967)
                  ·
                    rfl

theorem cell20_424430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_424430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424430 prefixEnd_424430 := by exact prefixLift 424430
  have htrace : WordTrace (prefixWord ++ tailWord_424430) baseStart_424430 baseEnd_424430 := by
    simpa [prefixWord, tailWord_424430, baseEnd_424430] using wordTrace_append hprefix tailTrace_424430
  have hstable : (prefixWord ++ tailWord_424430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424430).length < 2 ^ (prefixWord ++ tailWord_424430).sum := by decide
  have hdescent : baseEnd_424430 < baseStart_424430 := by decide
  rcases family_descends (prefixWord ++ tailWord_424430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424458 : List Nat := [3, 1, 2, 2, 2, 1, 9]
def baseStart_424458 : Nat := 118140960795 + 424458 * 2 ^ 59
def prefixEnd_424458 : Nat := 4983230072969 + 3 ^ 40 * 424458 * 2
def baseEnd_424458 : Nat := 21526021890983263192391

theorem tailTrace_424458 : CollatzResearch.WordTrace tailWord_424458 prefixEnd_424458 21526021890983263192391 := by
  unfold tailWord_424458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3870313774067158125038507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10320836730845755000102685 3870313774067158125038507)
  ·
    refine ⟨5805470661100737187557761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3870313774067158125038507 5805470661100737187557761)
    ·
      refine ⟨4354102995825552890668321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5805470661100737187557761 4354102995825552890668321)
      ·
        refine ⟨3265577246869164668001241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4354102995825552890668321 3265577246869164668001241)
        ·
          refine ⟨2449182935151873501000931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3265577246869164668001241 2449182935151873501000931)
          ·
            refine ⟨3673774402727810251501397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2449182935151873501000931 3673774402727810251501397)
            ·
              refine ⟨21526021890983263192391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3673774402727810251501397 21526021890983263192391)
              ·
                rfl

theorem cell20_424458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 9].length) (baseStart_424458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424458 prefixEnd_424458 := by exact prefixLift 424458
  have htrace : WordTrace (prefixWord ++ tailWord_424458) baseStart_424458 baseEnd_424458 := by
    simpa [prefixWord, tailWord_424458, baseEnd_424458] using wordTrace_append hprefix tailTrace_424458
  have hstable : (prefixWord ++ tailWord_424458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424458).length < 2 ^ (prefixWord ++ tailWord_424458).sum := by decide
  have hdescent : baseEnd_424458 < baseStart_424458 := by decide
  rcases family_descends (prefixWord ++ tailWord_424458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424502 : List Nat := [5, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_424502 : Nat := 118140960795 + 424502 * 2 ^ 59
def prefixEnd_424502 : Nat := 4983230072969 + 3 ^ 40 * 424502 * 2
def baseEnd_424502 : Nat := 193754279817780771264673

theorem tailTrace_424502 : CollatzResearch.WordTrace tailWord_424502 prefixEnd_424502 193754279817780771264673 := by
  unfold tailWord_424502
  simp only [CollatzResearch.WordTrace]
  refine ⟨967678744256826750922235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10321906605406152009837173 967678744256826750922235)
  ·
    refine ⟨1451518116385240126383353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 967678744256826750922235 1451518116385240126383353)
    ·
      refine ⟨1088638587288930094787515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1451518116385240126383353 1088638587288930094787515)
      ·
        refine ⟨1632957880933395142181273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1088638587288930094787515 1632957880933395142181273)
        ·
          refine ⟨1224718410700046356635955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1632957880933395142181273 1224718410700046356635955)
          ·
            refine ⟨1837077616050069534953933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224718410700046356635955 1837077616050069534953933)
            ·
              refine ⟨688904106018776075607725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1837077616050069534953933 688904106018776075607725)
              ·
                refine ⟨258339039757041028352897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 688904106018776075607725 258339039757041028352897)
                ·
                  refine ⟨193754279817780771264673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258339039757041028352897 193754279817780771264673)
                  ·
                    rfl

theorem cell20_424502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_424502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424502 prefixEnd_424502 := by exact prefixLift 424502
  have htrace : WordTrace (prefixWord ++ tailWord_424502) baseStart_424502 baseEnd_424502 := by
    simpa [prefixWord, tailWord_424502, baseEnd_424502] using wordTrace_append hprefix tailTrace_424502
  have hstable : (prefixWord ++ tailWord_424502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424502).length < 2 ^ (prefixWord ++ tailWord_424502).sum := by decide
  have hdescent : baseEnd_424502 < baseStart_424502 := by decide
  rcases family_descends (prefixWord ++ tailWord_424502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424503 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 7]
def baseStart_424503 : Nat := 118140960795 + 424503 * 2 ^ 59
def prefixEnd_424503 : Nat := 4983230072969 + 3 ^ 40 * 424503 * 2
def baseEnd_424503 : Nat := 193754736245029212231335

theorem tailTrace_424503 : CollatzResearch.WordTrace tailWord_424503 prefixEnd_424503 193754736245029212231335 := by
  unfold tailWord_424503
  simp only [CollatzResearch.WordTrace]
  refine ⟨15482896381105605185542163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10321930920737070123694775 15482896381105605185542163)
  ·
    refine ⟨23224344571658407778313245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15482896381105605185542163 23224344571658407778313245)
    ·
      refine ⟨8709129214371902916867467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23224344571658407778313245 8709129214371902916867467)
      ·
        refine ⟨13063693821557854375301201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8709129214371902916867467 13063693821557854375301201)
        ·
          refine ⟨9797770366168390781475901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13063693821557854375301201 9797770366168390781475901)
          ·
            refine ⟨3674163887313146543053463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9797770366168390781475901 3674163887313146543053463)
            ·
              refine ⟨5511245830969719814580195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3674163887313146543053463 5511245830969719814580195)
              ·
                refine ⟨8266868746454579721870293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5511245830969719814580195 8266868746454579721870293)
                ·
                  refine ⟨193754736245029212231335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8266868746454579721870293 193754736245029212231335)
                  ·
                    rfl

theorem cell20_424503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_424503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424503 prefixEnd_424503 := by exact prefixLift 424503
  have htrace : WordTrace (prefixWord ++ tailWord_424503) baseStart_424503 baseEnd_424503 := by
    simpa [prefixWord, tailWord_424503, baseEnd_424503] using wordTrace_append hprefix tailTrace_424503
  have hstable : (prefixWord ++ tailWord_424503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424503).length < 2 ^ (prefixWord ++ tailWord_424503).sum := by decide
  have hdescent : baseEnd_424503 < baseStart_424503 := by decide
  rcases family_descends (prefixWord ++ tailWord_424503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424513 : List Nat := [1, 2, 5, 1, 1, 4, 6]
def baseStart_424513 : Nat := 118140960795 + 424513 * 2 ^ 59
def prefixEnd_424513 : Nat := 4983230072969 + 3 ^ 40 * 424513 * 2
def baseEnd_424513 : Nat := 21528811168612624655329

theorem tailTrace_424513 : CollatzResearch.WordTrace tailWord_424513 prefixEnd_424513 21528811168612624655329 := by
  unfold tailWord_424513
  simp only [CollatzResearch.WordTrace]
  refine ⟨15483261111069376893406193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10322174074046251262270795 15483261111069376893406193)
  ·
    refine ⟨11612445833302032670054645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15483261111069376893406193 11612445833302032670054645)
    ·
      refine ⟨1088666796872065562817623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11612445833302032670054645 1088666796872065562817623)
      ·
        refine ⟨1633000195308098344226435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1088666796872065562817623 1633000195308098344226435)
        ·
          refine ⟨2449500292962147516339653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1633000195308098344226435 2449500292962147516339653)
          ·
            refine ⟨459281304930402659313685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2449500292962147516339653 459281304930402659313685)
            ·
              refine ⟨21528811168612624655329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 459281304930402659313685 21528811168612624655329)
              ·
                rfl

theorem cell20_424513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 6].length) (baseStart_424513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424513 prefixEnd_424513 := by exact prefixLift 424513
  have htrace : WordTrace (prefixWord ++ tailWord_424513) baseStart_424513 baseEnd_424513 := by
    simpa [prefixWord, tailWord_424513, baseEnd_424513] using wordTrace_append hprefix tailTrace_424513
  have hstable : (prefixWord ++ tailWord_424513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424513).length < 2 ^ (prefixWord ++ tailWord_424513).sum := by decide
  have hdescent : baseEnd_424513 < baseStart_424513 := by decide
  rcases family_descends (prefixWord ++ tailWord_424513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424527 : List Nat := [1, 1, 2, 1, 1, 2, 7, 1, 4]
def baseStart_424527 : Nat := 118140960795 + 424527 * 2 ^ 59
def prefixEnd_424527 : Nat := 4983230072969 + 3 ^ 40 * 424527 * 2
def baseEnd_424527 : Nat := 193765690498991795431237

theorem tailTrace_424527 : CollatzResearch.WordTrace tailWord_424527 prefixEnd_424527 193765690498991795431237 := by
  unfold tailWord_424527
  simp only [CollatzResearch.WordTrace]
  refine ⟨15483771733018657284415835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10322514488679104856277223 15483771733018657284415835)
  ·
    refine ⟨23225657599527985926623753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15483771733018657284415835 23225657599527985926623753)
    ·
      refine ⟨17419243199645989444967815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23225657599527985926623753 17419243199645989444967815)
      ·
        refine ⟨26128864799468984167451723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17419243199645989444967815 26128864799468984167451723)
        ·
          refine ⟨39193297199203476251177585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26128864799468984167451723 39193297199203476251177585)
          ·
            refine ⟨29394972899402607188383189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39193297199203476251177585 29394972899402607188383189)
            ·
              refine ⟨688944677329748605977731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 29394972899402607188383189 688944677329748605977731)
              ·
                refine ⟨1033417015994622908966597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688944677329748605977731 1033417015994622908966597)
                ·
                  refine ⟨193765690498991795431237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1033417015994622908966597 193765690498991795431237)
                  ·
                    rfl

theorem cell20_424527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 4].length) (baseStart_424527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424527 prefixEnd_424527 := by exact prefixLift 424527
  have htrace : WordTrace (prefixWord ++ tailWord_424527) baseStart_424527 baseEnd_424527 := by
    simpa [prefixWord, tailWord_424527, baseEnd_424527] using wordTrace_append hprefix tailTrace_424527
  have hstable : (prefixWord ++ tailWord_424527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424527).length < 2 ^ (prefixWord ++ tailWord_424527).sum := by decide
  have hdescent : baseEnd_424527 < baseStart_424527 := by decide
  rcases family_descends (prefixWord ++ tailWord_424527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424579 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 5]
def baseStart_424579 : Nat := 118140960795 + 424579 * 2 ^ 59
def prefixEnd_424579 : Nat := 4983230072969 + 3 ^ 40 * 424579 * 2
def baseEnd_424579 : Nat := 193789424715910725697691

theorem tailTrace_424579 : CollatzResearch.WordTrace tailWord_424579 prefixEnd_424579 193789424715910725697691 := by
  unfold tailWord_424579
  simp only [CollatzResearch.WordTrace]
  refine ⟨15485668328830270165308791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10323778885886846776872527 15485668328830270165308791)
  ·
    refine ⟨23228502493245405247963187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15485668328830270165308791 23228502493245405247963187)
    ·
      refine ⟨34842753739868107871944781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23228502493245405247963187 34842753739868107871944781)
      ·
        refine ⟨13066032652450540451979293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34842753739868107871944781 13066032652450540451979293)
        ·
          refine ⟨4899762244668952669492235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13066032652450540451979293 4899762244668952669492235)
          ·
            refine ⟨7349643367003429004238353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4899762244668952669492235 7349643367003429004238353)
            ·
              refine ⟨5512232525252571753178765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7349643367003429004238353 5512232525252571753178765)
              ·
                refine ⟨2067087196969714407442037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5512232525252571753178765 2067087196969714407442037)
                ·
                  refine ⟨193789424715910725697691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2067087196969714407442037 193789424715910725697691)
                  ·
                    rfl

theorem cell20_424579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_424579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424579 prefixEnd_424579 := by exact prefixLift 424579
  have htrace : WordTrace (prefixWord ++ tailWord_424579) baseStart_424579 baseEnd_424579 := by
    simpa [prefixWord, tailWord_424579, baseEnd_424579] using wordTrace_append hprefix tailTrace_424579
  have hstable : (prefixWord ++ tailWord_424579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424579).length < 2 ^ (prefixWord ++ tailWord_424579).sum := by decide
  have hdescent : baseEnd_424579 < baseStart_424579 := by decide
  rcases family_descends (prefixWord ++ tailWord_424579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424606 : List Nat := [4, 3, 1, 1, 1, 1, 5, 4]
def baseStart_424606 : Nat := 118140960795 + 424606 * 2 ^ 59
def prefixEnd_424606 : Nat := 4983230072969 + 3 ^ 40 * 424606 * 2
def baseEnd_424606 : Nat := 64600582750539543932527

theorem tailTrace_424606 : CollatzResearch.WordTrace tailWord_424606 prefixEnd_424606 64600582750539543932527 := by
  unfold tailWord_424606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935831637466556722067709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10324435399821635851027781 1935831637466556722067709)
  ·
    refine ⟨725936864049958770775391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1935831637466556722067709 725936864049958770775391)
    ·
      refine ⟨1088905296074938156163087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 725936864049958770775391 1088905296074938156163087)
      ·
        refine ⟨1633357944112407234244631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1088905296074938156163087 1633357944112407234244631)
        ·
          refine ⟨2450036916168610851366947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1633357944112407234244631 2450036916168610851366947)
          ·
            refine ⟨3675055374252916277050421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2450036916168610851366947 3675055374252916277050421)
            ·
              refine ⟨344536441336210900973477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3675055374252916277050421 344536441336210900973477)
              ·
                refine ⟨64600582750539543932527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 344536441336210900973477 64600582750539543932527)
                ·
                  rfl

theorem cell20_424606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_424606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424606 prefixEnd_424606 := by exact prefixLift 424606
  have htrace : WordTrace (prefixWord ++ tailWord_424606) baseStart_424606 baseEnd_424606 := by
    simpa [prefixWord, tailWord_424606, baseEnd_424606] using wordTrace_append hprefix tailTrace_424606
  have hstable : (prefixWord ++ tailWord_424606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424606).length < 2 ^ (prefixWord ++ tailWord_424606).sum := by decide
  have hdescent : baseEnd_424606 < baseStart_424606 := by decide
  rcases family_descends (prefixWord ++ tailWord_424606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424624 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 8]
def baseStart_424624 : Nat := 118140960795 + 424624 * 2 ^ 59
def prefixEnd_424624 : Nat := 4983230072969 + 3 ^ 40 * 424624 * 2
def baseEnd_424624 : Nat := 193809963942090569197507

theorem tailTrace_424624 : CollatzResearch.WordTrace tailWord_424624 prefixEnd_424624 193809963942090569197507 := by
  unfold tailWord_424624
  simp only [CollatzResearch.WordTrace]
  refine ⟨7743654806833621425348463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10324873075778161900464617 7743654806833621425348463)
  ·
    refine ⟨11615482210250432138022695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7743654806833621425348463 11615482210250432138022695)
    ·
      refine ⟨17423223315375648207034043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11615482210250432138022695 17423223315375648207034043)
      ·
        refine ⟨26134834973063472310551065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17423223315375648207034043 26134834973063472310551065)
        ·
          refine ⟨19601126229797604232913299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26134834973063472310551065 19601126229797604232913299)
          ·
            refine ⟨29401689344696406349369949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19601126229797604232913299 29401689344696406349369949)
            ·
              refine ⟨11025633504261152381013731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29401689344696406349369949 11025633504261152381013731)
              ·
                refine ⟨16538450256391728571520597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11025633504261152381013731 16538450256391728571520597)
                ·
                  refine ⟨193809963942090569197507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16538450256391728571520597 193809963942090569197507)
                  ·
                    rfl

theorem cell20_424624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_424624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424624 prefixEnd_424624 := by exact prefixLift 424624
  have htrace : WordTrace (prefixWord ++ tailWord_424624) baseStart_424624 baseEnd_424624 := by
    simpa [prefixWord, tailWord_424624, baseEnd_424624] using wordTrace_append hprefix tailTrace_424624
  have hstable : (prefixWord ++ tailWord_424624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424624).length < 2 ^ (prefixWord ++ tailWord_424624).sum := by decide
  have hdescent : baseEnd_424624 < baseStart_424624 := by decide
  rcases family_descends (prefixWord ++ tailWord_424624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424630 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_424630 : Nat := 118140960795 + 424630 * 2 ^ 59
def prefixEnd_424630 : Nat := 4983230072969 + 3 ^ 40 * 424630 * 2
def baseEnd_424630 : Nat := 193812702505581214997483

theorem tailTrace_424630 : CollatzResearch.WordTrace tailWord_424630 prefixEnd_424630 193812702505581214997483 := by
  unfold tailWord_424630
  simp only [CollatzResearch.WordTrace]
  refine ⟨967970528227844117213459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10325018967763670583610229 967970528227844117213459)
  ·
    refine ⟨1451955792341766175820189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 967970528227844117213459 1451955792341766175820189)
    ·
      refine ⟨544483422128162315932571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1451955792341766175820189 544483422128162315932571)
      ·
        refine ⟨816725133192243473898857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544483422128162315932571 816725133192243473898857)
        ·
          refine ⟨612543849894182605424143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 816725133192243473898857 612543849894182605424143)
          ·
            refine ⟨918815774841273908136215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612543849894182605424143 918815774841273908136215)
            ·
              refine ⟨1378223662261910862204323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 918815774841273908136215 1378223662261910862204323)
              ·
                refine ⟨2067335493392866293306485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378223662261910862204323 2067335493392866293306485)
                ·
                  refine ⟨193812702505581214997483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2067335493392866293306485 193812702505581214997483)
                  ·
                    rfl

theorem cell20_424630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_424630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424630 prefixEnd_424630 := by exact prefixLift 424630
  have htrace : WordTrace (prefixWord ++ tailWord_424630) baseStart_424630 baseEnd_424630 := by
    simpa [prefixWord, tailWord_424630, baseEnd_424630] using wordTrace_append hprefix tailTrace_424630
  have hstable : (prefixWord ++ tailWord_424630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424630).length < 2 ^ (prefixWord ++ tailWord_424630).sum := by decide
  have hdescent : baseEnd_424630 < baseStart_424630 := by decide
  rcases family_descends (prefixWord ++ tailWord_424630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424661 : List Nat := [1, 3, 2, 5, 1, 2, 2, 4]
def baseStart_424661 : Nat := 118140960795 + 424661 * 2 ^ 59
def prefixEnd_424661 : Nat := 4983230072969 + 3 ^ 40 * 424661 * 2
def baseEnd_424661 : Nat := 64608950583427628321341

theorem tailTrace_424661 : CollatzResearch.WordTrace tailWord_424661 prefixEnd_424661 64608950583427628321341 := by
  unfold tailWord_424661
  simp only [CollatzResearch.WordTrace]
  refine ⟨15488659114533198169793837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10325772743022132113195891 15488659114533198169793837)
  ·
    refine ⟨5808247167949949313672689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15488659114533198169793837 5808247167949949313672689)
    ·
      refine ⟨4356185375962461985254517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5808247167949949313672689 4356185375962461985254517)
      ·
        refine ⟨408392378996480811117611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4356185375962461985254517 408392378996480811117611)
        ·
          refine ⟨612588568494721216676417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408392378996480811117611 612588568494721216676417)
          ·
            refine ⟨459441426371040912507313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 612588568494721216676417 459441426371040912507313)
            ·
              refine ⟨344581069778280684380485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459441426371040912507313 344581069778280684380485)
              ·
                refine ⟨64608950583427628321341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 344581069778280684380485 64608950583427628321341)
                ·
                  rfl

theorem cell20_424661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 4].length) (baseStart_424661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424661 prefixEnd_424661 := by exact prefixLift 424661
  have htrace : WordTrace (prefixWord ++ tailWord_424661) baseStart_424661 baseEnd_424661 := by
    simpa [prefixWord, tailWord_424661, baseEnd_424661] using wordTrace_append hprefix tailTrace_424661
  have hstable : (prefixWord ++ tailWord_424661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424661).length < 2 ^ (prefixWord ++ tailWord_424661).sum := by decide
  have hdescent : baseEnd_424661 < baseStart_424661 := by decide
  rcases family_descends (prefixWord ++ tailWord_424661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424675 : List Nat := [1, 1, 1, 7, 1, 1, 3, 3, 2]
def baseStart_424675 : Nat := 118140960795 + 424675 * 2 ^ 59
def prefixEnd_424675 : Nat := 4983230072969 + 3 ^ 40 * 424675 * 2
def baseEnd_424675 : Nat := 193833241731761058497299

theorem tailTrace_424675 : CollatzResearch.WordTrace tailWord_424675 prefixEnd_424675 193833241731761058497299 := by
  unfold tailWord_424675
  simp only [CollatzResearch.WordTrace]
  refine ⟨15489169736482478560803479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10326113157654985707202319 15489169736482478560803479)
  ·
    refine ⟨23233754604723717841205219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15489169736482478560803479 23233754604723717841205219)
    ·
      refine ⟨34850631907085576761807829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23233754604723717841205219 34850631907085576761807829)
      ·
        refine ⟨816811685322318205354871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 34850631907085576761807829 816811685322318205354871)
        ·
          refine ⟨1225217527983477308032307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816811685322318205354871 1225217527983477308032307)
          ·
            refine ⟨1837826291975215962048461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225217527983477308032307 1837826291975215962048461)
            ·
              refine ⟨689184859490705985768173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1837826291975215962048461 689184859490705985768173)
              ·
                refine ⟨258444322309014744663065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 689184859490705985768173 258444322309014744663065)
                ·
                  refine ⟨193833241731761058497299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258444322309014744663065 193833241731761058497299)
                  ·
                    rfl

theorem cell20_424675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 2].length) (baseStart_424675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424675 prefixEnd_424675 := by exact prefixLift 424675
  have htrace : WordTrace (prefixWord ++ tailWord_424675) baseStart_424675 baseEnd_424675 := by
    simpa [prefixWord, tailWord_424675, baseEnd_424675] using wordTrace_append hprefix tailTrace_424675
  have hstable : (prefixWord ++ tailWord_424675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424675).length < 2 ^ (prefixWord ++ tailWord_424675).sum := by decide
  have hdescent : baseEnd_424675 < baseStart_424675 := by decide
  rcases family_descends (prefixWord ++ tailWord_424675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424686 : List Nat := [4, 1, 2, 1, 1, 3, 8]
def baseStart_424686 : Nat := 118140960795 + 424686 * 2 ^ 59
def prefixEnd_424686 : Nat := 4983230072969 + 3 ^ 40 * 424686 * 2
def baseEnd_424686 : Nat := 21537584714610434347843

theorem tailTrace_424686 : CollatzResearch.WordTrace tailWord_424686 prefixEnd_424686 21537584714610434347843 := by
  unfold tailWord_424686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1936196367430328429931739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10326380626295084959635941 1936196367430328429931739)
  ·
    refine ⟨2904294551145492644897609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1936196367430328429931739 2904294551145492644897609)
    ·
      refine ⟨2178220913359119483673207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2904294551145492644897609 2178220913359119483673207)
      ·
        refine ⟨3267331370038679225509811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2178220913359119483673207 3267331370038679225509811)
        ·
          refine ⟨4900997055058018838264717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3267331370038679225509811 4900997055058018838264717)
          ·
            refine ⟨1837873895646757064349269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4900997055058018838264717 1837873895646757064349269)
            ·
              refine ⟨21537584714610434347843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1837873895646757064349269 21537584714610434347843)
              ·
                rfl

theorem cell20_424686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 8].length) (baseStart_424686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424686 prefixEnd_424686 := by exact prefixLift 424686
  have htrace : WordTrace (prefixWord ++ tailWord_424686) baseStart_424686 baseEnd_424686 := by
    simpa [prefixWord, tailWord_424686, baseEnd_424686] using wordTrace_append hprefix tailTrace_424686
  have hstable : (prefixWord ++ tailWord_424686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424686).length < 2 ^ (prefixWord ++ tailWord_424686).sum := by decide
  have hdescent : baseEnd_424686 < baseStart_424686 := by decide
  rcases family_descends (prefixWord ++ tailWord_424686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424706 : List Nat := [3, 4, 1, 1, 1, 2, 4, 1, 3]
def baseStart_424706 : Nat := 118140960795 + 424706 * 2 ^ 59
def prefixEnd_424706 : Nat := 4983230072969 + 3 ^ 40 * 424706 * 2
def baseEnd_424706 : Nat := 193847390976462728463839

theorem tailTrace_424706 : CollatzResearch.WordTrace tailWord_424706 prefixEnd_424706 193847390976462728463839 := by
  unfold tailWord_424706
  simp only [CollatzResearch.WordTrace]
  refine ⟨3872575099842542713795493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10326866932913447236787981 3872575099842542713795493)
  ·
    refine ⟨726107831220476758836655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3872575099842542713795493 726107831220476758836655)
    ·
      refine ⟨1089161746830715138254983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 726107831220476758836655 1089161746830715138254983)
      ·
        refine ⟨1633742620246072707382475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1089161746830715138254983 1633742620246072707382475)
        ·
          refine ⟨2450613930369109061073713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1633742620246072707382475 2450613930369109061073713)
          ·
            refine ⟨1837960447776831795805285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2450613930369109061073713 1837960447776831795805285)
            ·
              refine ⟨344617583958155961713491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1837960447776831795805285 344617583958155961713491)
              ·
                refine ⟨516926375937233942570237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344617583958155961713491 516926375937233942570237)
                ·
                  refine ⟨193847390976462728463839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 516926375937233942570237 193847390976462728463839)
                  ·
                    rfl

theorem cell20_424706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_424706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424706 prefixEnd_424706 := by exact prefixLift 424706
  have htrace : WordTrace (prefixWord ++ tailWord_424706) baseStart_424706 baseEnd_424706 := by
    simpa [prefixWord, tailWord_424706, baseEnd_424706] using wordTrace_append hprefix tailTrace_424706
  have hstable : (prefixWord ++ tailWord_424706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424706).length < 2 ^ (prefixWord ++ tailWord_424706).sum := by decide
  have hdescent : baseEnd_424706 < baseStart_424706 := by decide
  rcases family_descends (prefixWord ++ tailWord_424706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424748 : List Nat := [2, 2, 1, 1, 1, 4, 4, 2, 3]
def baseStart_424748 : Nat := 118140960795 + 424748 * 2 ^ 59
def prefixEnd_424748 : Nat := 4983230072969 + 3 ^ 40 * 424748 * 2
def baseEnd_424748 : Nat := 193866560920897249063667

theorem tailTrace_424748 : CollatzResearch.WordTrace tailWord_424748 prefixEnd_424748 193866560920897249063667 := by
  unfold tailWord_424748
  simp only [CollatzResearch.WordTrace]
  refine ⟨7745916132609006014105449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10327888176812008018807265 7745916132609006014105449)
  ·
    refine ⟨5809437099456754510579087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7745916132609006014105449 5809437099456754510579087)
    ·
      refine ⟨8714155649185131765868631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5809437099456754510579087 8714155649185131765868631)
      ·
        refine ⟨13071233473777697648802947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8714155649185131765868631 13071233473777697648802947)
        ·
          refine ⟨19606850210666546473204421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13071233473777697648802947 19606850210666546473204421)
          ·
            refine ⟨3676284414499977463725829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19606850210666546473204421 3676284414499977463725829)
            ·
              refine ⟨689303327718745774448593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3676284414499977463725829 689303327718745774448593)
              ·
                refine ⟨516977495789059330836445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689303327718745774448593 516977495789059330836445)
                ·
                  refine ⟨193866560920897249063667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 516977495789059330836445 193866560920897249063667)
                  ·
                    rfl

theorem cell20_424748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_424748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424748 prefixEnd_424748 := by exact prefixLift 424748
  have htrace : WordTrace (prefixWord ++ tailWord_424748) baseStart_424748 baseEnd_424748 := by
    simpa [prefixWord, tailWord_424748, baseEnd_424748] using wordTrace_append hprefix tailTrace_424748
  have hstable : (prefixWord ++ tailWord_424748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424748).length < 2 ^ (prefixWord ++ tailWord_424748).sum := by decide
  have hdescent : baseEnd_424748 < baseStart_424748 := by decide
  rcases family_descends (prefixWord ++ tailWord_424748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424803 : List Nat := [1, 1, 1, 5, 3, 3, 1, 2, 3]
def baseStart_424803 : Nat := 118140960795 + 424803 * 2 ^ 59
def prefixEnd_424803 : Nat := 4983230072969 + 3 ^ 40 * 424803 * 2
def baseEnd_424803 : Nat := 193891664419561502230109

theorem tailTrace_424803 : CollatzResearch.WordTrace tailWord_424803 prefixEnd_424803 193891664419561502230109 := by
  unfold tailWord_424803
  simp only [CollatzResearch.WordTrace]
  refine ⟨15493838280018756421463063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10329225520012504280975375 15493838280018756421463063)
  ·
    refine ⟨23240757420028134632194595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15493838280018756421463063 23240757420028134632194595)
    ·
      refine ⟨34861136130042201948291893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23240757420028134632194595 34861136130042201948291893)
      ·
        refine ⟨3268231512191456432652365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34861136130042201948291893 3268231512191456432652365)
        ·
          refine ⟨1225586817071796162244637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3268231512191456432652365 1225586817071796162244637)
          ·
            refine ⟨459595056401923560841739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1225586817071796162244637 459595056401923560841739)
            ·
              refine ⟨689392584602885341262609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459595056401923560841739 689392584602885341262609)
              ·
                refine ⟨517044438452164005946957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689392584602885341262609 517044438452164005946957)
                ·
                  refine ⟨193891664419561502230109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517044438452164005946957 193891664419561502230109)
                  ·
                    rfl

theorem cell20_424803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 3].length) (baseStart_424803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424803 prefixEnd_424803 := by exact prefixLift 424803
  have htrace : WordTrace (prefixWord ++ tailWord_424803) baseStart_424803 baseEnd_424803 := by
    simpa [prefixWord, tailWord_424803, baseEnd_424803] using wordTrace_append hprefix tailTrace_424803
  have hstable : (prefixWord ++ tailWord_424803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424803).length < 2 ^ (prefixWord ++ tailWord_424803).sum := by decide
  have hdescent : baseEnd_424803 < baseStart_424803 := by decide
  rcases family_descends (prefixWord ++ tailWord_424803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424830 : List Nat := [4, 2, 3, 1, 3, 1, 2, 4]
def baseStart_424830 : Nat := 118140960795 + 424830 * 2 ^ 59
def prefixEnd_424830 : Nat := 4983230072969 + 3 ^ 40 * 424830 * 2
def baseEnd_424830 : Nat := 64634662651756469443333

theorem tailTrace_424830 : CollatzResearch.WordTrace tailWord_424830 prefixEnd_424830 64634662651756469443333 := by
  unfold tailWord_424830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1936852881365117504086993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10329882033947293355130629 1936852881365117504086993)
  ·
    refine ⟨1452639661023838128065245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1936852881365117504086993 1452639661023838128065245)
    ·
      refine ⟨544739872883939298024467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1452639661023838128065245 544739872883939298024467)
      ·
        refine ⟨817109809325908947036701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544739872883939298024467 817109809325908947036701)
        ·
          refine ⟨306416178497215855138763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 817109809325908947036701 306416178497215855138763)
          ·
            refine ⟨459624267745823782708145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306416178497215855138763 459624267745823782708145)
            ·
              refine ⟨344718200809367837031109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459624267745823782708145 344718200809367837031109)
              ·
                refine ⟨64634662651756469443333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 344718200809367837031109 64634662651756469443333)
                ·
                  rfl

theorem cell20_424830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_424830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424830 prefixEnd_424830 := by exact prefixLift 424830
  have htrace : WordTrace (prefixWord ++ tailWord_424830) baseStart_424830 baseEnd_424830 := by
    simpa [prefixWord, tailWord_424830, baseEnd_424830] using wordTrace_append hprefix tailTrace_424830
  have hstable : (prefixWord ++ tailWord_424830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424830).length < 2 ^ (prefixWord ++ tailWord_424830).sum := by decide
  have hdescent : baseEnd_424830 < baseStart_424830 := by decide
  rcases family_descends (prefixWord ++ tailWord_424830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424890 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_424890 : Nat := 118140960795 + 424890 * 2 ^ 59
def prefixEnd_424890 : Nat := 4983230072969 + 3 ^ 40 * 424890 * 2
def baseEnd_424890 : Nat := 193931373590175866329753

theorem tailTrace_424890 : CollatzResearch.WordTrace tailWord_424890 prefixEnd_424890 193931373590175866329753 := by
  unfold tailWord_424890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3874252857675892569970031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10331340953802380186586749 3874252857675892569970031)
  ·
    refine ⟨5811379286513838854955047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3874252857675892569970031 5811379286513838854955047)
    ·
      refine ⟨8717068929770758282432571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5811379286513838854955047 8717068929770758282432571)
      ·
        refine ⟨13075603394656137423648857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8717068929770758282432571 13075603394656137423648857)
        ·
          refine ⟨9806702545992103067736643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13075603394656137423648857 9806702545992103067736643)
          ·
            refine ⟨14710053818988154601604965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9806702545992103067736643 14710053818988154601604965)
            ·
              refine ⟨2758135091060278987800931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14710053818988154601604965 2758135091060278987800931)
              ·
                refine ⟨4137202636590418481701397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758135091060278987800931 4137202636590418481701397)
                ·
                  refine ⟨193931373590175866329753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4137202636590418481701397 193931373590175866329753)
                  ·
                    rfl

theorem cell20_424890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_424890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424890 prefixEnd_424890 := by exact prefixLift 424890
  have htrace : WordTrace (prefixWord ++ tailWord_424890) baseStart_424890 baseEnd_424890 := by
    simpa [prefixWord, tailWord_424890, baseEnd_424890] using wordTrace_append hprefix tailTrace_424890
  have hstable : (prefixWord ++ tailWord_424890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424890).length < 2 ^ (prefixWord ++ tailWord_424890).sum := by decide
  have hdescent : baseEnd_424890 < baseStart_424890 := by decide
  rcases family_descends (prefixWord ++ tailWord_424890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424914 : List Nat := [3, 2, 2, 3, 1, 9]
def baseStart_424914 : Nat := 118140960795 + 424914 * 2 ^ 59
def prefixEnd_424914 : Nat := 4983230072969 + 3 ^ 40 * 424914 * 2
def baseEnd_424914 : Nat := 7183049179412535167765

theorem tailTrace_424914 : CollatzResearch.WordTrace tailWord_424914 prefixEnd_424914 7183049179412535167765 := by
  unfold tailWord_424914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3874471695654155594688449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10331924521744414919169197 3874471695654155594688449)
  ·
    refine ⟨2905853771740616696016337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3874471695654155594688449 2905853771740616696016337)
    ·
      refine ⟨2179390328805462522012253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2905853771740616696016337 2179390328805462522012253)
      ·
        refine ⟨817271373302048445754595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2179390328805462522012253 817271373302048445754595)
        ·
          refine ⟨1225907059953072668631893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817271373302048445754595 1225907059953072668631893)
          ·
            refine ⟨7183049179412535167765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1225907059953072668631893 7183049179412535167765)
            ·
              rfl

theorem cell20_424914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 9].length) (baseStart_424914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424914 prefixEnd_424914 := by exact prefixLift 424914
  have htrace : WordTrace (prefixWord ++ tailWord_424914) baseStart_424914 baseEnd_424914 := by
    simpa [prefixWord, tailWord_424914, baseEnd_424914] using wordTrace_append hprefix tailTrace_424914
  have hstable : (prefixWord ++ tailWord_424914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424914).length < 2 ^ (prefixWord ++ tailWord_424914).sum := by decide
  have hdescent : baseEnd_424914 < baseStart_424914 := by decide
  rcases family_descends (prefixWord ++ tailWord_424914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424917 : List Nat := [1, 3, 2, 3, 3, 1, 2, 2, 3]
def baseStart_424917 : Nat := 118140960795 + 424917 * 2 ^ 59
def prefixEnd_424917 : Nat := 4983230072969 + 3 ^ 40 * 424917 * 2
def baseEnd_424917 : Nat := 193943697125883772429643

theorem tailTrace_424917 : CollatzResearch.WordTrace tailWord_424917 prefixEnd_424917 193943697125883772429643 := by
  unfold tailWord_424917
  simp only [CollatzResearch.WordTrace]
  refine ⟨15497996201605753891113005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10331997467737169260742003 15497996201605753891113005)
  ·
    refine ⟨5811748575602157709167377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15497996201605753891113005 5811748575602157709167377)
    ·
      refine ⟨4358811431701618281875533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5811748575602157709167377 4358811431701618281875533)
      ·
        refine ⟨1634554286888106855703325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4358811431701618281875533 1634554286888106855703325)
        ·
          refine ⟨612957857583040070888747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1634554286888106855703325 612957857583040070888747)
          ·
            refine ⟨919436786374560106333121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612957857583040070888747 919436786374560106333121)
            ·
              refine ⟨689577589780920079749841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 919436786374560106333121 689577589780920079749841)
              ·
                refine ⟨517183192335690059812381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689577589780920079749841 517183192335690059812381)
                ·
                  refine ⟨193943697125883772429643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517183192335690059812381 193943697125883772429643)
                  ·
                    rfl

theorem cell20_424917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_424917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424917 prefixEnd_424917 := by exact prefixLift 424917
  have htrace : WordTrace (prefixWord ++ tailWord_424917) baseStart_424917 baseEnd_424917 := by
    simpa [prefixWord, tailWord_424917, baseEnd_424917] using wordTrace_append hprefix tailTrace_424917
  have hstable : (prefixWord ++ tailWord_424917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424917).length < 2 ^ (prefixWord ++ tailWord_424917).sum := by decide
  have hdescent : baseEnd_424917 < baseStart_424917 := by decide
  rcases family_descends (prefixWord ++ tailWord_424917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424938 : List Nat := [3, 1, 3, 1, 2, 2, 2, 3, 3]
def baseStart_424938 : Nat := 118140960795 + 424938 * 2 ^ 59
def prefixEnd_424938 : Nat := 4983230072969 + 3 ^ 40 * 424938 * 2
def baseEnd_424938 : Nat := 193953282098101032729557

theorem tailTrace_424938 : CollatzResearch.WordTrace tailWord_424938 prefixEnd_424938 193953282098101032729557 := by
  unfold tailWord_424938
  simp only [CollatzResearch.WordTrace]
  refine ⟨3874690533632418619406867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10332508089686449651751645 3874690533632418619406867)
  ·
    refine ⟨5812035800448627929110301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3874690533632418619406867 5812035800448627929110301)
    ·
      refine ⟨2179513425168235473416363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5812035800448627929110301 2179513425168235473416363)
      ·
        refine ⟨3269270137752353210124545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2179513425168235473416363 3269270137752353210124545)
        ·
          refine ⟨2451952603314264907593409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3269270137752353210124545 2451952603314264907593409)
          ·
            refine ⟨1838964452485698680695057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2451952603314264907593409 1838964452485698680695057)
            ·
              refine ⟨1379223339364274010521293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1838964452485698680695057 1379223339364274010521293)
              ·
                refine ⟨517208752261602753945485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1379223339364274010521293 517208752261602753945485)
                ·
                  refine ⟨193953282098101032729557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517208752261602753945485 193953282098101032729557)
                  ·
                    rfl

theorem cell20_424938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_424938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424938 prefixEnd_424938 := by exact prefixLift 424938
  have htrace : WordTrace (prefixWord ++ tailWord_424938) baseStart_424938 baseEnd_424938 := by
    simpa [prefixWord, tailWord_424938, baseEnd_424938] using wordTrace_append hprefix tailTrace_424938
  have hstable : (prefixWord ++ tailWord_424938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424938).length < 2 ^ (prefixWord ++ tailWord_424938).sum := by decide
  have hdescent : baseEnd_424938 < baseStart_424938 := by decide
  rcases family_descends (prefixWord ++ tailWord_424938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424945 : List Nat := [1, 2, 2, 2, 4, 2, 1, 2, 4]
def baseStart_424945 : Nat := 118140960795 + 424945 * 2 ^ 59
def prefixEnd_424945 : Nat := 4983230072969 + 3 ^ 40 * 424945 * 2
def baseEnd_424945 : Nat := 193956477088840119496195

theorem tailTrace_424945 : CollatzResearch.WordTrace tailWord_424945 prefixEnd_424945 193956477088840119496195 := by
  unfold tailWord_424945
  simp only [CollatzResearch.WordTrace]
  refine ⟨15499017445504314673132289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10332678297002876448754859 15499017445504314673132289)
  ·
    refine ⟨11624263084128236004849217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15499017445504314673132289 11624263084128236004849217)
    ·
      refine ⟨8718197313096177003636913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11624263084128236004849217 8718197313096177003636913)
      ·
        refine ⟨6538647984822132752727685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8718197313096177003636913 6538647984822132752727685)
        ·
          refine ⟨1225996497154149891136441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6538647984822132752727685 1225996497154149891136441)
          ·
            refine ⟨919497372865612418352331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1225996497154149891136441 919497372865612418352331)
            ·
              refine ⟨1379246059298418627528497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 919497372865612418352331 1379246059298418627528497)
              ·
                refine ⟨1034434544473813970646373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1379246059298418627528497 1034434544473813970646373)
                ·
                  refine ⟨193956477088840119496195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1034434544473813970646373 193956477088840119496195)
                  ·
                    rfl

theorem cell20_424945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_424945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424945 prefixEnd_424945 := by exact prefixLift 424945
  have htrace : WordTrace (prefixWord ++ tailWord_424945) baseStart_424945 baseEnd_424945 := by
    simpa [prefixWord, tailWord_424945, baseEnd_424945] using wordTrace_append hprefix tailTrace_424945
  have hstable : (prefixWord ++ tailWord_424945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424945).length < 2 ^ (prefixWord ++ tailWord_424945).sum := by decide
  have hdescent : baseEnd_424945 < baseStart_424945 := by decide
  rcases family_descends (prefixWord ++ tailWord_424945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424958 : List Nat := [4, 2, 2, 2, 2, 1, 2, 3, 2]
def baseStart_424958 : Nat := 118140960795 + 424958 * 2 ^ 59
def prefixEnd_424958 : Nat := 4983230072969 + 3 ^ 40 * 424958 * 2
def baseEnd_424958 : Nat := 193962410643069852062809

theorem tailTrace_424958 : CollatzResearch.WordTrace tailWord_424958 prefixEnd_424958 193962410643069852062809 := by
  unfold tailWord_424958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1937436449307152236669441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10332994396304811928903685 1937436449307152236669441)
  ·
    refine ⟨1453077336980364177502081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1937436449307152236669441 1453077336980364177502081)
    ·
      refine ⟨1089808002735273133126561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1453077336980364177502081 1089808002735273133126561)
      ·
        refine ⟨817356002051454849844921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1089808002735273133126561 817356002051454849844921)
        ·
          refine ⟨613017001538591137383691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 817356002051454849844921 613017001538591137383691)
          ·
            refine ⟨919525502307886706075537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613017001538591137383691 919525502307886706075537)
            ·
              refine ⟨689644126730915029556653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 919525502307886706075537 689644126730915029556653)
              ·
                refine ⟨258616547524093136083745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 689644126730915029556653 258616547524093136083745)
                ·
                  refine ⟨193962410643069852062809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258616547524093136083745 193962410643069852062809)
                  ·
                    rfl

theorem cell20_424958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_424958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424958 prefixEnd_424958 := by exact prefixLift 424958
  have htrace : WordTrace (prefixWord ++ tailWord_424958) baseStart_424958 baseEnd_424958 := by
    simpa [prefixWord, tailWord_424958, baseEnd_424958] using wordTrace_append hprefix tailTrace_424958
  have hstable : (prefixWord ++ tailWord_424958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424958).length < 2 ^ (prefixWord ++ tailWord_424958).sum := by decide
  have hdescent : baseEnd_424958 < baseStart_424958 := by decide
  rcases family_descends (prefixWord ++ tailWord_424958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424983 : List Nat := [1, 1, 3, 5, 1, 1, 1, 3, 4]
def baseStart_424983 : Nat := 118140960795 + 424983 * 2 ^ 59
def prefixEnd_424983 : Nat := 4983230072969 + 3 ^ 40 * 424983 * 2
def baseEnd_424983 : Nat := 193973821324280876229373

theorem tailTrace_424983 : CollatzResearch.WordTrace tailWord_424983 prefixEnd_424983 193973821324280876229373 := by
  unfold tailWord_424983
  simp only [CollatzResearch.WordTrace]
  refine ⟨15500403419366647163015603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10333602279577764775343735 15500403419366647163015603)
  ·
    refine ⟨23250605129049970744523405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15500403419366647163015603 23250605129049970744523405)
    ·
      refine ⟨8718976923393739029196277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23250605129049970744523405 8718976923393739029196277)
      ·
        refine ⟨817404086568163033987151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8718976923393739029196277 817404086568163033987151)
        ·
          refine ⟨1226106129852244550980727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817404086568163033987151 1226106129852244550980727)
          ·
            refine ⟨1839159194778366826471091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226106129852244550980727 1839159194778366826471091)
            ·
              refine ⟨2758738792167550239706637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1839159194778366826471091 2758738792167550239706637)
              ·
                refine ⟨1034527047062831339889989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2758738792167550239706637 1034527047062831339889989)
                ·
                  refine ⟨193973821324280876229373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1034527047062831339889989 193973821324280876229373)
                  ·
                    rfl

theorem cell20_424983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 4].length) (baseStart_424983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424983 prefixEnd_424983 := by exact prefixLift 424983
  have htrace : WordTrace (prefixWord ++ tailWord_424983) baseStart_424983 baseEnd_424983 := by
    simpa [prefixWord, tailWord_424983, baseEnd_424983] using wordTrace_append hprefix tailTrace_424983
  have hstable : (prefixWord ++ tailWord_424983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424983).length < 2 ^ (prefixWord ++ tailWord_424983).sum := by decide
  have hdescent : baseEnd_424983 < baseStart_424983 := by decide
  rcases family_descends (prefixWord ++ tailWord_424983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424993 : List Nat := [1, 2, 3, 2, 3, 2, 3, 1, 3]
def baseStart_424993 : Nat := 118140960795 + 424993 * 2 ^ 59
def prefixEnd_424993 : Nat := 4983230072969 + 3 ^ 40 * 424993 * 2
def baseEnd_424993 : Nat := 193978385596765285895999

theorem tailTrace_424993 : CollatzResearch.WordTrace tailWord_424993 prefixEnd_424993 193978385596765285895999 := by
  unfold tailWord_424993
  simp only [CollatzResearch.WordTrace]
  refine ⟨15500768149330418870879633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10333845432886945913919755 15500768149330418870879633)
  ·
    refine ⟨11625576111997814153159725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15500768149330418870879633 11625576111997814153159725)
    ·
      refine ⟨4359591041999180307434897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11625576111997814153159725 4359591041999180307434897)
      ·
        refine ⟨3269693281499385230576173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4359591041999180307434897 3269693281499385230576173)
        ·
          refine ⟨1226134980562269461466065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3269693281499385230576173 1226134980562269461466065)
          ·
            refine ⟨919601235421702096099549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1226134980562269461466065 919601235421702096099549)
            ·
              refine ⟨344850463283138286037331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 919601235421702096099549 344850463283138286037331)
              ·
                refine ⟨517275694924707429055997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344850463283138286037331 517275694924707429055997)
                ·
                  refine ⟨193978385596765285895999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517275694924707429055997 193978385596765285895999)
                  ·
                    rfl

theorem cell20_424993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 3].length) (baseStart_424993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_424993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_424993 prefixEnd_424993 := by exact prefixLift 424993
  have htrace : WordTrace (prefixWord ++ tailWord_424993) baseStart_424993 baseEnd_424993 := by
    simpa [prefixWord, tailWord_424993, baseEnd_424993] using wordTrace_append hprefix tailTrace_424993
  have hstable : (prefixWord ++ tailWord_424993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424993).length < 2 ^ (prefixWord ++ tailWord_424993).sum := by decide
  have hdescent : baseEnd_424993 < baseStart_424993 := by decide
  rcases family_descends (prefixWord ++ tailWord_424993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425004 : List Nat := [2, 2, 1, 1, 1, 2, 3, 4, 4]
def baseStart_425004 : Nat := 118140960795 + 425004 * 2 ^ 59
def prefixEnd_425004 : Nat := 4983230072969 + 3 ^ 40 * 425004 * 2
def baseEnd_425004 : Nat := 193983406296498136529287

theorem tailTrace_425004 : CollatzResearch.WordTrace tailWord_425004 prefixEnd_425004 193983406296498136529287 := by
  unfold tailWord_425004
  simp only [CollatzResearch.WordTrace]
  refine ⟨7750584676145283874765033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10334112901527045166353377 7750584676145283874765033)
  ·
    refine ⟨5812938507108962906073775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7750584676145283874765033 5812938507108962906073775)
    ·
      refine ⟨8719407760663444359110663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5812938507108962906073775 8719407760663444359110663)
      ·
        refine ⟨13079111640995166538665995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8719407760663444359110663 13079111640995166538665995)
        ·
          refine ⟨19618667461492749807998993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13079111640995166538665995 19618667461492749807998993)
          ·
            refine ⟨14714000596119562355999245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19618667461492749807998993 14714000596119562355999245)
            ·
              refine ⟨5517750223544835883499717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14714000596119562355999245 5517750223544835883499717)
              ·
                refine ⟨1034578166914656728156197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5517750223544835883499717 1034578166914656728156197)
                ·
                  refine ⟨193983406296498136529287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1034578166914656728156197 193983406296498136529287)
                  ·
                    rfl

theorem cell20_425004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_425004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425004 prefixEnd_425004 := by exact prefixLift 425004
  have htrace : WordTrace (prefixWord ++ tailWord_425004) baseStart_425004 baseEnd_425004 := by
    simpa [prefixWord, tailWord_425004, baseEnd_425004] using wordTrace_append hprefix tailTrace_425004
  have hstable : (prefixWord ++ tailWord_425004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425004).length < 2 ^ (prefixWord ++ tailWord_425004).sum := by decide
  have hdescent : baseEnd_425004 < baseStart_425004 := by decide
  rcases family_descends (prefixWord ++ tailWord_425004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425014 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_425014 : Nat := 118140960795 + 425014 * 2 ^ 59
def prefixEnd_425014 : Nat := 4983230072969 + 3 ^ 40 * 425014 * 2
def baseEnd_425014 : Nat := 193987970568982546195913

theorem tailTrace_425014 : CollatzResearch.WordTrace tailWord_425014 prefixEnd_425014 193987970568982546195913 := by
  unfold tailWord_425014
  simp only [CollatzResearch.WordTrace]
  refine ⟨968845880140896216087131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10334356054836226304929397 968845880140896216087131)
  ·
    refine ⟨1453268820211344324130697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 968845880140896216087131 1453268820211344324130697)
    ·
      refine ⟨1089951615158508243098023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1453268820211344324130697 1089951615158508243098023)
      ·
        refine ⟨1634927422737762364647035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1089951615158508243098023 1634927422737762364647035)
        ·
          refine ⟨2452391134106643546970553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1634927422737762364647035 2452391134106643546970553)
          ·
            refine ⟨1839293350579982660227915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2452391134106643546970553 1839293350579982660227915)
            ·
              refine ⟨2758940025869973990341873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1839293350579982660227915 2758940025869973990341873)
              ·
                refine ⟨2069205019402480492756405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2758940025869973990341873 2069205019402480492756405)
                ·
                  refine ⟨193987970568982546195913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2069205019402480492756405 193987970568982546195913)
                  ·
                    rfl

theorem cell20_425014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_425014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425014 prefixEnd_425014 := by exact prefixLift 425014
  have htrace : WordTrace (prefixWord ++ tailWord_425014) baseStart_425014 baseEnd_425014 := by
    simpa [prefixWord, tailWord_425014, baseEnd_425014] using wordTrace_append hprefix tailTrace_425014
  have hstable : (prefixWord ++ tailWord_425014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425014).length < 2 ^ (prefixWord ++ tailWord_425014).sum := by decide
  have hdescent : baseEnd_425014 < baseStart_425014 := by decide
  rcases family_descends (prefixWord ++ tailWord_425014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425017 : List Nat := [1, 2, 1, 5, 2, 3, 1, 3, 2]
def baseStart_425017 : Nat := 118140960795 + 425017 * 2 ^ 59
def prefixEnd_425017 : Nat := 4983230072969 + 3 ^ 40 * 425017 * 2
def baseEnd_425017 : Nat := 193989339850727869095901

theorem tailTrace_425017 : CollatzResearch.WordTrace tailWord_425017 prefixEnd_425017 193989339850727869095901 := by
  unfold tailWord_425017
  simp only [CollatzResearch.WordTrace]
  refine ⟨15501643501243470969753305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10334429000828980646502203 15501643501243470969753305)
  ·
    refine ⟨11626232625932603227314979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15501643501243470969753305 11626232625932603227314979)
    ·
      refine ⟨17439348938898904840972469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11626232625932603227314979 17439348938898904840972469)
      ·
        refine ⟨1634938963021772328841169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17439348938898904840972469 1634938963021772328841169)
        ·
          refine ⟨1226204222266329246630877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1634938963021772328841169 1226204222266329246630877)
          ·
            refine ⟨459826583349873467486579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1226204222266329246630877 459826583349873467486579)
            ·
              refine ⟨689739875024810201229869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459826583349873467486579 689739875024810201229869)
              ·
                refine ⟨258652453134303825461201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 689739875024810201229869 258652453134303825461201)
                ·
                  refine ⟨193989339850727869095901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258652453134303825461201 193989339850727869095901)
                  ·
                    rfl

theorem cell20_425017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 2].length) (baseStart_425017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425017 prefixEnd_425017 := by exact prefixLift 425017
  have htrace : WordTrace (prefixWord ++ tailWord_425017) baseStart_425017 baseEnd_425017 := by
    simpa [prefixWord, tailWord_425017, baseEnd_425017] using wordTrace_append hprefix tailTrace_425017
  have hstable : (prefixWord ++ tailWord_425017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425017).length < 2 ^ (prefixWord ++ tailWord_425017).sum := by decide
  have hdescent : baseEnd_425017 < baseStart_425017 := by decide
  rcases family_descends (prefixWord ++ tailWord_425017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425052 : List Nat := [2, 2, 4, 1, 1, 1, 3, 3, 3]
def baseStart_425052 : Nat := 118140960795 + 425052 * 2 ^ 59
def prefixEnd_425052 : Nat := 4983230072969 + 3 ^ 40 * 425052 * 2
def baseEnd_425052 : Nat := 194005314804423302929091

theorem tailTrace_425052 : CollatzResearch.WordTrace tailWord_425052 prefixEnd_425052 194005314804423302929091 := by
  unfold tailWord_425052
  simp only [CollatzResearch.WordTrace]
  refine ⟨7751460028058335973638705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10335280037411114631518273 7751460028058335973638705)
  ·
    refine ⟨5813595021043751980229029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7751460028058335973638705 5813595021043751980229029)
    ·
      refine ⟨1090049066445703496292943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5813595021043751980229029 1090049066445703496292943)
      ·
        refine ⟨1635073599668555244439415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1090049066445703496292943 1635073599668555244439415)
        ·
          refine ⟨2452610399502832866659123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1635073599668555244439415 2452610399502832866659123)
          ·
            refine ⟨3678915599254249299988685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2452610399502832866659123 3678915599254249299988685)
            ·
              refine ⟨1379593349720343487495757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3678915599254249299988685 1379593349720343487495757)
              ·
                refine ⟨517347506145128807810909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1379593349720343487495757 517347506145128807810909)
                ·
                  refine ⟨194005314804423302929091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517347506145128807810909 194005314804423302929091)
                  ·
                    rfl

theorem cell20_425052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_425052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425052 prefixEnd_425052 := by exact prefixLift 425052
  have htrace : WordTrace (prefixWord ++ tailWord_425052) baseStart_425052 baseEnd_425052 := by
    simpa [prefixWord, tailWord_425052, baseEnd_425052] using wordTrace_append hprefix tailTrace_425052
  have hstable : (prefixWord ++ tailWord_425052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425052).length < 2 ^ (prefixWord ++ tailWord_425052).sum := by decide
  have hdescent : baseEnd_425052 < baseStart_425052 := by decide
  rcases family_descends (prefixWord ++ tailWord_425052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425066 : List Nat := [3, 1, 3, 2, 2, 1, 2, 6]
def baseStart_425066 : Nat := 118140960795 + 425066 * 2 ^ 59
def prefixEnd_425066 : Nat := 4983230072969 + 3 ^ 40 * 425066 * 2
def baseEnd_425066 : Nat := 64670568261967158820789

theorem tailTrace_425066 : CollatzResearch.WordTrace tailWord_425066 prefixEnd_425066 64670568261967158820789 := by
  unfold tailWord_425066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3875857669516488084571763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10335620452043968225524701 3875857669516488084571763)
  ·
    refine ⟨5813786504274732126857645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3875857669516488084571763 5813786504274732126857645)
    ·
      refine ⟨2180169939103024547571617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5813786504274732126857645 2180169939103024547571617)
      ·
        refine ⟨1635127454327268410678713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2180169939103024547571617 1635127454327268410678713)
        ·
          refine ⟨1226345590745451308009035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1635127454327268410678713 1226345590745451308009035)
          ·
            refine ⟨1839518386118176962013553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226345590745451308009035 1839518386118176962013553)
            ·
              refine ⟨1379638789588632721510165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1839518386118176962013553 1379638789588632721510165)
              ·
                refine ⟨64670568261967158820789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1379638789588632721510165 64670568261967158820789)
                ·
                  rfl

theorem cell20_425066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_425066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425066 prefixEnd_425066 := by exact prefixLift 425066
  have htrace : WordTrace (prefixWord ++ tailWord_425066) baseStart_425066 baseEnd_425066 := by
    simpa [prefixWord, tailWord_425066, baseEnd_425066] using wordTrace_append hprefix tailTrace_425066
  have hstable : (prefixWord ++ tailWord_425066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425066).length < 2 ^ (prefixWord ++ tailWord_425066).sum := by decide
  have hdescent : baseEnd_425066 < baseStart_425066 := by decide
  rcases family_descends (prefixWord ++ tailWord_425066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425135 : List Nat := [1, 1, 2, 1, 2, 3, 3, 5, 2]
def baseStart_425135 : Nat := 118140960795 + 425135 * 2 ^ 59
def prefixEnd_425135 : Nat := 4983230072969 + 3 ^ 40 * 425135 * 2
def baseEnd_425135 : Nat := 194043198266043903162085

theorem tailTrace_425135 : CollatzResearch.WordTrace tailWord_425135 prefixEnd_425135 194043198266043903162085 := by
  unfold tailWord_425135
  simp only [CollatzResearch.WordTrace]
  refine ⟨15505947314815977122548859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10337298209877318081699239 15505947314815977122548859)
  ·
    refine ⟨23258920972223965683823289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15505947314815977122548859 23258920972223965683823289)
    ·
      refine ⟨17444190729167974262867467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23258920972223965683823289 17444190729167974262867467)
      ·
        refine ⟨26166286093751961394301201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17444190729167974262867467 26166286093751961394301201)
        ·
          refine ⟨19624714570313971045725901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26166286093751961394301201 19624714570313971045725901)
          ·
            refine ⟨7359267963867739142147213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19624714570313971045725901 7359267963867739142147213)
            ·
              refine ⟨2759725486450402178305205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7359267963867739142147213 2759725486450402178305205)
              ·
                refine ⟨258724264354725204216113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2759725486450402178305205 258724264354725204216113)
                ·
                  refine ⟨194043198266043903162085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258724264354725204216113 194043198266043903162085)
                  ·
                    rfl

theorem cell20_425135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 2].length) (baseStart_425135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425135 prefixEnd_425135 := by exact prefixLift 425135
  have htrace : WordTrace (prefixWord ++ tailWord_425135) baseStart_425135 baseEnd_425135 := by
    simpa [prefixWord, tailWord_425135, baseEnd_425135] using wordTrace_append hprefix tailTrace_425135
  have hstable : (prefixWord ++ tailWord_425135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425135).length < 2 ^ (prefixWord ++ tailWord_425135).sum := by decide
  have hdescent : baseEnd_425135 < baseStart_425135 := by decide
  rcases family_descends (prefixWord ++ tailWord_425135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
