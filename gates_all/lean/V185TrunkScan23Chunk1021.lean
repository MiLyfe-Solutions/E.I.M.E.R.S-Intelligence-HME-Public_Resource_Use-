import V185TrunkScan23Chunk1020

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6044345 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 1, 3, 5]
def baseStart_6044345 : Nat := 118140960795 + 6044345 * 2 ^ 59
def prefixEnd_6044345 : Nat := 4983230072969 + 3 ^ 40 * 6044345 * 2
def baseEnd_6044345 : Nat := 3103654226600259206090069

theorem tailTrace_6044345 : CollatzResearch.WordTrace tailWord_6044345 prefixEnd_6044345 3103654226600259206090069 := by
  unfold tailWord_6044345
  simp only [CollatzResearch.WordTrace]
  refine ⟨220455373287377831786150489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146970248858251887857433659 220455373287377831786150489)
  ·
    refine ⟨165341529965533373839612867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220455373287377831786150489 165341529965533373839612867)
    ·
      refine ⟨248012294948300060759419301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165341529965533373839612867 248012294948300060759419301)
      ·
        refine ⟨46502305302806261392391119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248012294948300060759419301 46502305302806261392391119)
        ·
          refine ⟨69753457954209392088586679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46502305302806261392391119 69753457954209392088586679)
          ·
            refine ⟨104630186931314088132880019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69753457954209392088586679 104630186931314088132880019)
            ·
              refine ⟨156945280396971132199320029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104630186931314088132880019 156945280396971132199320029)
              ·
                refine ⟨58854480148864174574745011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156945280396971132199320029 58854480148864174574745011)
                ·
                  refine ⟨88281720223296261862117517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58854480148864174574745011 88281720223296261862117517)
                  ·
                    refine ⟨33105645083736098198294069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88281720223296261862117517 33105645083736098198294069)
                    ·
                      refine ⟨3103654226600259206090069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33105645083736098198294069 3103654226600259206090069)
                      ·
                        rfl

theorem cell23_6044345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_6044345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044345 prefixEnd_6044345 := by exact prefixLift 6044345
  have htrace : WordTrace (prefixWord ++ tailWord_6044345) baseStart_6044345 baseEnd_6044345 := by
    simpa [prefixWord, tailWord_6044345, baseEnd_6044345] using wordTrace_append hprefix tailTrace_6044345
  have hstable : (prefixWord ++ tailWord_6044345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044345).length < 2 ^ (prefixWord ++ tailWord_6044345).sum := by decide
  have hdescent : baseEnd_6044345 < baseStart_6044345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044353 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_6044353 : Nat := 118140960795 + 6044353 * 2 ^ 59
def prefixEnd_6044353 : Nat := 4983230072969 + 3 ^ 40 * 6044353 * 2
def baseEnd_6044353 : Nat := 3103658334445495174790033

theorem tailTrace_6044353 : CollatzResearch.WordTrace tailWord_6044353 prefixEnd_6044353 3103658334445495174790033 := by
  unfold tailWord_6044353
  simp only [CollatzResearch.WordTrace]
  refine ⟨220455665071348849152441713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146970443380899232768294475 220455665071348849152441713)
  ·
    refine ⟨165341748803511636864331285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220455665071348849152441713 165341748803511636864331285)
    ·
      refine ⟨7750394475164607978015529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 165341748803511636864331285 7750394475164607978015529)
      ·
        refine ⟨5812795856373455983511647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7750394475164607978015529 5812795856373455983511647)
        ·
          refine ⟨8719193784560183975267471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5812795856373455983511647 8719193784560183975267471)
          ·
            refine ⟨13078790676840275962901207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8719193784560183975267471 13078790676840275962901207)
            ·
              refine ⟨19618186015260413944351811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13078790676840275962901207 19618186015260413944351811)
              ·
                refine ⟨29427279022890620916527717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19618186015260413944351811 29427279022890620916527717)
                ·
                  refine ⟨5517614816791991421848947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29427279022890620916527717 5517614816791991421848947)
                  ·
                    refine ⟨8276422225187987132773421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5517614816791991421848947 8276422225187987132773421)
                    ·
                      refine ⟨3103658334445495174790033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8276422225187987132773421 3103658334445495174790033)
                      ·
                        rfl

theorem cell23_6044353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_6044353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044353 prefixEnd_6044353 := by exact prefixLift 6044353
  have htrace : WordTrace (prefixWord ++ tailWord_6044353) baseStart_6044353 baseEnd_6044353 := by
    simpa [prefixWord, tailWord_6044353, baseEnd_6044353] using wordTrace_append hprefix tailTrace_6044353
  have hstable : (prefixWord ++ tailWord_6044353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044353).length < 2 ^ (prefixWord ++ tailWord_6044353).sum := by decide
  have hdescent : baseEnd_6044353 < baseStart_6044353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044376 : List Nat := [2, 1, 2, 2, 3, 4, 1, 1, 1, 4, 2]
def baseStart_6044376 : Nat := 118140960795 + 6044376 * 2 ^ 59
def prefixEnd_6044376 : Nat := 4983230072969 + 3 ^ 40 * 6044376 * 2
def baseEnd_6044376 : Nat := 3103670144500548584802427

theorem tailTrace_6044376 : CollatzResearch.WordTrace tailWord_6044376 prefixEnd_6044376 3103670144500548584802427 := by
  unfold tailWord_6044376
  simp only [CollatzResearch.WordTrace]
  refine ⟨110228251975132762040264491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146971002633510349387019321 110228251975132762040264491)
  ·
    refine ⟨165342377962699143060396737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110228251975132762040264491 165342377962699143060396737)
    ·
      refine ⟨124006783472024357295297553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165342377962699143060396737 124006783472024357295297553)
      ·
        refine ⟨93005087604018267971473165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124006783472024357295297553 93005087604018267971473165)
        ·
          refine ⟨34876907851506850489302437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93005087604018267971473165 34876907851506850489302437)
          ·
            refine ⟨6539420222157534466744207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34876907851506850489302437 6539420222157534466744207)
            ·
              refine ⟨9809130333236301700116311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6539420222157534466744207 9809130333236301700116311)
              ·
                refine ⟨14713695499854452550174467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9809130333236301700116311 14713695499854452550174467)
                ·
                  refine ⟨22070543249781678825261701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14713695499854452550174467 22070543249781678825261701)
                  ·
                    refine ⟨4138226859334064779736569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22070543249781678825261701 4138226859334064779736569)
                    ·
                      refine ⟨3103670144500548584802427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4138226859334064779736569 3103670144500548584802427)
                      ·
                        rfl

theorem cell23_6044376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_6044376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044376 prefixEnd_6044376 := by exact prefixLift 6044376
  have htrace : WordTrace (prefixWord ++ tailWord_6044376) baseStart_6044376 baseEnd_6044376 := by
    simpa [prefixWord, tailWord_6044376, baseEnd_6044376] using wordTrace_append hprefix tailTrace_6044376
  have hstable : (prefixWord ++ tailWord_6044376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044376).length < 2 ^ (prefixWord ++ tailWord_6044376).sum := by decide
  have hdescent : baseEnd_6044376 < baseStart_6044376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044399 : List Nat := [1, 1, 2, 1, 5, 2, 3, 3, 5]
def baseStart_6044399 : Nat := 118140960795 + 6044399 * 2 ^ 59
def prefixEnd_6044399 : Nat := 4983230072969 + 3 ^ 40 * 6044399 * 2
def baseEnd_6044399 : Nat := 344853550506177999423869

theorem tailTrace_6044399 : CollatzResearch.WordTrace tailWord_6044399 prefixEnd_6044399 344853550506177999423869 := by
  unfold tailWord_6044399
  simp only [CollatzResearch.WordTrace]
  refine ⟨220457342829182199008616251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146971561886121466005744167 220457342829182199008616251)
  ·
    refine ⟨330686014243773298512924377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220457342829182199008616251 330686014243773298512924377)
    ·
      refine ⟨248014510682829973884693283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330686014243773298512924377 248014510682829973884693283)
      ·
        refine ⟨372021766024244960827039925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248014510682829973884693283 372021766024244960827039925)
        ·
          refine ⟨34877040564772965077534993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 372021766024244960827039925 34877040564772965077534993)
          ·
            refine ⟨26157780423579723808151245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34877040564772965077534993 26157780423579723808151245)
            ·
              refine ⟨9809167658842396428056717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26157780423579723808151245 9809167658842396428056717)
              ·
                refine ⟨3678437872065898660521269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9809167658842396428056717 3678437872065898660521269)
                ·
                  refine ⟨344853550506177999423869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3678437872065898660521269 344853550506177999423869)
                  ·
                    rfl

theorem cell23_6044399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 5].length) (baseStart_6044399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044399 prefixEnd_6044399 := by exact prefixLift 6044399
  have htrace : WordTrace (prefixWord ++ tailWord_6044399) baseStart_6044399 baseEnd_6044399 := by
    simpa [prefixWord, tailWord_6044399, baseEnd_6044399] using wordTrace_append hprefix tailTrace_6044399
  have hstable : (prefixWord ++ tailWord_6044399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044399).length < 2 ^ (prefixWord ++ tailWord_6044399).sum := by decide
  have hdescent : baseEnd_6044399 < baseStart_6044399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044412 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 4, 5]
def baseStart_6044412 : Nat := 118140960795 + 6044412 * 2 ^ 59
def prefixEnd_6044412 : Nat := 4983230072969 + 3 ^ 40 * 6044412 * 2
def baseEnd_6044412 : Nat := 1034562876601370147984087

theorem tailTrace_6044412 : CollatzResearch.WordTrace tailWord_6044412 prefixEnd_6044412 1034562876601370147984087 := by
  unfold tailWord_6044412
  simp only [CollatzResearch.WordTrace]
  refine ⟨110228908489067551114419745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146971877985423401485892993 110228908489067551114419745)
  ·
    refine ⟨82671681366800663335814809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110228908489067551114419745 82671681366800663335814809)
    ·
      refine ⟨62003761025100497501861107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82671681366800663335814809 62003761025100497501861107)
      ·
        refine ⟨93005641537650746252791661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62003761025100497501861107 93005641537650746252791661)
        ·
          refine ⟨34877115576619029844796873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93005641537650746252791661 34877115576619029844796873)
          ·
            refine ⟨26157836682464272383597655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34877115576619029844796873 26157836682464272383597655)
            ·
              refine ⟨39236755023696408575396483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26157836682464272383597655 39236755023696408575396483)
              ·
                refine ⟨58855132535544612863094725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39236755023696408575396483 58855132535544612863094725)
                ·
                  refine ⟨11035337350414614911830261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58855132535544612863094725 11035337350414614911830261)
                  ·
                    refine ⟨1034562876601370147984087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11035337350414614911830261 1034562876601370147984087)
                    ·
                      rfl

theorem cell23_6044412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_6044412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044412 prefixEnd_6044412 := by exact prefixLift 6044412
  have htrace : WordTrace (prefixWord ++ tailWord_6044412) baseStart_6044412 baseEnd_6044412 := by
    simpa [prefixWord, tailWord_6044412, baseEnd_6044412] using wordTrace_append hprefix tailTrace_6044412
  have hstable : (prefixWord ++ tailWord_6044412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044412).length < 2 ^ (prefixWord ++ tailWord_6044412).sum := by decide
  have hdescent : baseEnd_6044412 < baseStart_6044412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044449 : List Nat := [1, 2, 3, 2, 1, 2, 4, 1, 2, 1, 4]
def baseStart_6044449 : Nat := 118140960795 + 6044449 * 2 ^ 59
def prefixEnd_6044449 : Nat := 4983230072969 + 3 ^ 40 * 6044449 * 2
def baseEnd_6044449 : Nat := 3103707628588326799189591

theorem tailTrace_6044449 : CollatzResearch.WordTrace tailWord_6044449 prefixEnd_6044449 3103707628588326799189591 := by
  unfold tailWord_6044449
  simp only [CollatzResearch.WordTrace]
  refine ⟨220459166479001057547936401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146972777652667371698624267 220459166479001057547936401)
  ·
    refine ⟨165344374859250793160952301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220459166479001057547936401 165344374859250793160952301)
    ·
      refine ⟨62004140572219047435357113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165344374859250793160952301 62004140572219047435357113)
      ·
        refine ⟨46503105429164285576517835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62004140572219047435357113 46503105429164285576517835)
        ·
          refine ⟨69754658143746428364776753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46503105429164285576517835 69754658143746428364776753)
          ·
            refine ⟨52315993607809821273582565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69754658143746428364776753 52315993607809821273582565)
            ·
              refine ⟨9809248801464341488796731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52315993607809821273582565 9809248801464341488796731)
              ·
                refine ⟨14713873202196512233195097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9809248801464341488796731 14713873202196512233195097)
                ·
                  refine ⟨11035404901647384174896323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14713873202196512233195097 11035404901647384174896323)
                  ·
                    refine ⟨16553107352471076262344485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11035404901647384174896323 16553107352471076262344485)
                    ·
                      refine ⟨3103707628588326799189591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16553107352471076262344485 3103707628588326799189591)
                      ·
                        rfl

theorem cell23_6044449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_6044449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044449 prefixEnd_6044449 := by exact prefixLift 6044449
  have htrace : WordTrace (prefixWord ++ tailWord_6044449) baseStart_6044449 baseEnd_6044449 := by
    simpa [prefixWord, tailWord_6044449, baseEnd_6044449] using wordTrace_append hprefix tailTrace_6044449
  have hstable : (prefixWord ++ tailWord_6044449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044449).length < 2 ^ (prefixWord ++ tailWord_6044449).sum := by decide
  have hdescent : baseEnd_6044449 < baseStart_6044449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044493 : List Nat := [1, 6, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_6044493 : Nat := 118140960795 + 6044493 * 2 ^ 59
def prefixEnd_6044493 : Nat := 4983230072969 + 3 ^ 40 * 6044493 * 2
def baseEnd_6044493 : Nat := 1034576740579041542346463

theorem tailTrace_6044493 : CollatzResearch.WordTrace tailWord_6044493 prefixEnd_6044493 1034576740579041542346463 := by
  unfold tailWord_6044493
  simp only [CollatzResearch.WordTrace]
  refine ⟨220460771290841653062538133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146973847527227768708358755 220460771290841653062538133)
  ·
    refine ⟨10334098654258202487306475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 220460771290841653062538133 10334098654258202487306475)
    ·
      refine ⟨15501147981387303730959713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10334098654258202487306475 15501147981387303730959713)
      ·
        refine ⟨11625860986040477798219785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15501147981387303730959713 11625860986040477798219785)
        ·
          refine ⟨8719395739530358348664839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11625860986040477798219785 8719395739530358348664839)
          ·
            refine ⟨13079093609295537522997259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8719395739530358348664839 13079093609295537522997259)
            ·
              refine ⟨19618640413943306284495889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13079093609295537522997259 19618640413943306284495889)
              ·
                refine ⟨14713980310457479713371917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19618640413943306284495889 14713980310457479713371917)
                ·
                  refine ⟨5517742616421554892514469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14713980310457479713371917 5517742616421554892514469)
                  ·
                    refine ⟨1034576740579041542346463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5517742616421554892514469 1034576740579041542346463)
                    ·
                      rfl

theorem cell23_6044493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_6044493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044493 prefixEnd_6044493 := by exact prefixLift 6044493
  have htrace : WordTrace (prefixWord ++ tailWord_6044493) baseStart_6044493 baseEnd_6044493 := by
    simpa [prefixWord, tailWord_6044493, baseEnd_6044493] using wordTrace_append hprefix tailTrace_6044493
  have hstable : (prefixWord ++ tailWord_6044493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044493).length < 2 ^ (prefixWord ++ tailWord_6044493).sum := by decide
  have hdescent : baseEnd_6044493 < baseStart_6044493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044533 : List Nat := [1, 3, 4, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_6044533 : Nat := 118140960795 + 6044533 * 2 ^ 59
def prefixEnd_6044533 : Nat := 4983230072969 + 3 ^ 40 * 6044533 * 2
def baseEnd_6044533 : Nat := 3103750760963304470539205

theorem tailTrace_6044533 : CollatzResearch.WordTrace tailWord_6044533 prefixEnd_6044533 3103750760963304470539205 := by
  unfold tailWord_6044533
  simp only [CollatzResearch.WordTrace]
  refine ⟨220462230210696739893994253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146974820140464493262662835 220462230210696739893994253)
  ·
    refine ⟨82673336329011277460247845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220462230210696739893994253 82673336329011277460247845)
    ·
      refine ⟨15501250561689614523796471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82673336329011277460247845 15501250561689614523796471)
      ·
        refine ⟨23251875842534421785694707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15501250561689614523796471 23251875842534421785694707)
        ·
          refine ⟨34877813763801632678542061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23251875842534421785694707 34877813763801632678542061)
          ·
            refine ⟨13079180161425612254453273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34877813763801632678542061 13079180161425612254453273)
            ·
              refine ⟨9809385121069209190839955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13079180161425612254453273 9809385121069209190839955)
              ·
                refine ⟨14714077681603813786259933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9809385121069209190839955 14714077681603813786259933)
                ·
                  refine ⟨5517779130601430169847475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14714077681603813786259933 5517779130601430169847475)
                  ·
                    refine ⟨8276668695902145254771213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5517779130601430169847475 8276668695902145254771213)
                    ·
                      refine ⟨3103750760963304470539205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8276668695902145254771213 3103750760963304470539205)
                      ·
                        rfl

theorem cell23_6044533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_6044533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044533 prefixEnd_6044533 := by exact prefixLift 6044533
  have htrace : WordTrace (prefixWord ++ tailWord_6044533) baseStart_6044533 baseEnd_6044533 := by
    simpa [prefixWord, tailWord_6044533, baseEnd_6044533] using wordTrace_append hprefix tailTrace_6044533
  have hstable : (prefixWord ++ tailWord_6044533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044533).length < 2 ^ (prefixWord ++ tailWord_6044533).sum := by decide
  have hdescent : baseEnd_6044533 < baseStart_6044533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044549 : List Nat := [1, 3, 1, 1, 3, 3, 3, 1, 1, 6]
def baseStart_6044549 : Nat := 118140960795 + 6044549 * 2 ^ 59
def prefixEnd_6044549 : Nat := 4983230072969 + 3 ^ 40 * 6044549 * 2
def baseEnd_6044549 : Nat := 1034586325551258802646377

theorem tailTrace_6044549 : CollatzResearch.WordTrace tailWord_6044549 prefixEnd_6044549 1034586325551258802646377 := by
  unfold tailWord_6044549
  simp only [CollatzResearch.WordTrace]
  refine ⟨220462813778638774626576701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146975209185759183084384467 220462813778638774626576701)
  ·
    refine ⟨82673555166989540484966263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220462813778638774626576701 82673555166989540484966263)
    ·
      refine ⟨124010332750484310727449395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82673555166989540484966263 124010332750484310727449395)
      ·
        refine ⟨186015499125726466091174093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124010332750484310727449395 186015499125726466091174093)
        ·
          refine ⟨69755812172147424784190285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186015499125726466091174093 69755812172147424784190285)
          ·
            refine ⟨26158429564555284294071357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69755812172147424784190285 26158429564555284294071357)
            ·
              refine ⟨9809411086708231610276759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26158429564555284294071357 9809411086708231610276759)
              ·
                refine ⟨14714116630062347415415139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9809411086708231610276759 14714116630062347415415139)
                ·
                  refine ⟨22071174945093521123122709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14714116630062347415415139 22071174945093521123122709)
                  ·
                    refine ⟨1034586325551258802646377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22071174945093521123122709 1034586325551258802646377)
                    ·
                      rfl

theorem cell23_6044549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_6044549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044549 prefixEnd_6044549 := by exact prefixLift 6044549
  have htrace : WordTrace (prefixWord ++ tailWord_6044549) baseStart_6044549 baseEnd_6044549 := by
    simpa [prefixWord, tailWord_6044549, baseEnd_6044549] using wordTrace_append hprefix tailTrace_6044549
  have hstable : (prefixWord ++ tailWord_6044549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044549).length < 2 ^ (prefixWord ++ tailWord_6044549).sum := by decide
  have hdescent : baseEnd_6044549 < baseStart_6044549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044576 : List Nat := [2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 3]
def baseStart_6044576 : Nat := 118140960795 + 6044576 * 2 ^ 59
def prefixEnd_6044576 : Nat := 4983230072969 + 3 ^ 40 * 6044576 * 2
def baseEnd_6044576 : Nat := 3103772840631447802301507

theorem tailTrace_6044576 : CollatzResearch.WordTrace tailWord_6044576 prefixEnd_6044576 3103772840631447802301507 := by
  unfold tailWord_6044576
  simp only [CollatzResearch.WordTrace]
  refine ⟨110231899274770479118904791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146975865699693972158539721 110231899274770479118904791)
  ·
    refine ⟨165347848912155718678357187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110231899274770479118904791 165347848912155718678357187)
    ·
      refine ⟨248021773368233578017535781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165347848912155718678357187 248021773368233578017535781)
      ·
        refine ⟨46504082506543795878287959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248021773368233578017535781 46504082506543795878287959)
        ·
          refine ⟨69756123759815693817431939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46504082506543795878287959 69756123759815693817431939)
          ·
            refine ⟨104634185639723540726147909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69756123759815693817431939 104634185639723540726147909)
            ·
              refine ⟨19618909807448163886152733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104634185639723540726147909 19618909807448163886152733)
              ·
                refine ⟨7357091177793061457307275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19618909807448163886152733 7357091177793061457307275)
                ·
                  refine ⟨11035636766689592185960913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7357091177793061457307275 11035636766689592185960913)
                  ·
                    refine ⟨8276727575017194139470685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11035636766689592185960913 8276727575017194139470685)
                    ·
                      refine ⟨3103772840631447802301507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8276727575017194139470685 3103772840631447802301507)
                      ·
                        rfl

theorem cell23_6044576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_6044576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044576 prefixEnd_6044576 := by exact prefixLift 6044576
  have htrace : WordTrace (prefixWord ++ tailWord_6044576) baseStart_6044576 baseEnd_6044576 := by
    simpa [prefixWord, tailWord_6044576, baseEnd_6044576] using wordTrace_append hprefix tailTrace_6044576
  have hstable : (prefixWord ++ tailWord_6044576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044576).length < 2 ^ (prefixWord ++ tailWord_6044576).sum := by decide
  have hdescent : baseEnd_6044576 < baseStart_6044576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044596 : List Nat := [2, 5, 2, 1, 1, 1, 1, 10]
def baseStart_6044596 : Nat := 118140960795 + 6044596 * 2 ^ 59
def prefixEnd_6044596 : Nat := 4983230072969 + 3 ^ 40 * 6044596 * 2
def baseEnd_6044596 : Nat := 114954930009056952742645

theorem tailTrace_6044596 : CollatzResearch.WordTrace tailWord_6044596 prefixEnd_6044596 114954930009056952742645 := by
  unfold tailWord_6044596
  simp only [CollatzResearch.WordTrace]
  refine ⟨110232264004734250826768821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146976352006312334435691761 110232264004734250826768821)
  ·
    refine ⟨10334274750443836015009577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110232264004734250826768821 10334274750443836015009577)
    ·
      refine ⟨7750706062832877011257183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10334274750443836015009577 7750706062832877011257183)
      ·
        refine ⟨11626059094249315516885775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7750706062832877011257183 11626059094249315516885775)
        ·
          refine ⟨17439088641373973275328663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11626059094249315516885775 17439088641373973275328663)
          ·
            refine ⟨26158632962060959912992995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17439088641373973275328663 26158632962060959912992995)
            ·
              refine ⟨39237949443091439869489493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26158632962060959912992995 39237949443091439869489493)
              ·
                refine ⟨114954930009056952742645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39237949443091439869489493 114954930009056952742645)
                ·
                  rfl

theorem cell23_6044596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 10].length) (baseStart_6044596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044596 prefixEnd_6044596 := by exact prefixLift 6044596
  have htrace : WordTrace (prefixWord ++ tailWord_6044596) baseStart_6044596 baseEnd_6044596 := by
    simpa [prefixWord, tailWord_6044596, baseEnd_6044596] using wordTrace_append hprefix tailTrace_6044596
  have hstable : (prefixWord ++ tailWord_6044596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044596).length < 2 ^ (prefixWord ++ tailWord_6044596).sum := by decide
  have hdescent : baseEnd_6044596 < baseStart_6044596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044606 : List Nat := [4, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_6044606 : Nat := 118140960795 + 6044606 * 2 ^ 59
def prefixEnd_6044606 : Nat := 4983230072969 + 3 ^ 40 * 6044606 * 2
def baseEnd_6044606 : Nat := 3103788245051082684926369

theorem tailTrace_6044606 : CollatzResearch.WordTrace tailWord_6044606 prefixEnd_6044606 3103788245051082684926369 := by
  unfold tailWord_6044606
  simp only [CollatzResearch.WordTrace]
  refine ⟨27558111592429034170175209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146976595159621515574267781 27558111592429034170175209)
  ·
    refine ⟨20668583694321775627631407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27558111592429034170175209 20668583694321775627631407)
    ·
      refine ⟨31002875541482663441447111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20668583694321775627631407 31002875541482663441447111)
      ·
        refine ⟨46504313312223995162170667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31002875541482663441447111 46504313312223995162170667)
        ·
          refine ⟨69756469968335992743256001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46504313312223995162170667 69756469968335992743256001)
          ·
            refine ⟨52317352476251994557442001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69756469968335992743256001 52317352476251994557442001)
            ·
              refine ⟨39238014357188995918081501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52317352476251994557442001 39238014357188995918081501)
              ·
                refine ⟨14714255383945873469280563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39238014357188995918081501 14714255383945873469280563)
                ·
                  refine ⟨22071383075918810203920845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14714255383945873469280563 22071383075918810203920845)
                  ·
                    refine ⟨8276768653469553826470317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22071383075918810203920845 8276768653469553826470317)
                    ·
                      refine ⟨3103788245051082684926369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8276768653469553826470317 3103788245051082684926369)
                      ·
                        rfl

theorem cell23_6044606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_6044606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044606 prefixEnd_6044606 := by exact prefixLift 6044606
  have htrace : WordTrace (prefixWord ++ tailWord_6044606) baseStart_6044606 baseEnd_6044606 := by
    simpa [prefixWord, tailWord_6044606, baseEnd_6044606] using wordTrace_append hprefix tailTrace_6044606
  have hstable : (prefixWord ++ tailWord_6044606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044606).length < 2 ^ (prefixWord ++ tailWord_6044606).sum := by decide
  have hdescent : baseEnd_6044606 < baseStart_6044606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044696 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 2, 3, 3]
def baseStart_6044696 : Nat := 118140960795 + 6044696 * 2 ^ 59
def prefixEnd_6044696 : Nat := 4983230072969 + 3 ^ 40 * 6044696 * 2
def baseEnd_6044696 : Nat := 3103834458309987332800955

theorem tailTrace_6044696 : CollatzResearch.WordTrace tailWord_6044696 prefixEnd_6044696 3103834458309987332800955 := by
  unfold tailWord_6044696
  simp only [CollatzResearch.WordTrace]
  refine ⟨110234087654553109366088971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146978783539404145821451961 110234087654553109366088971)
  ·
    refine ⟨165351131481829664049133457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110234087654553109366088971 165351131481829664049133457)
    ·
      refine ⟨124013348611372248036850093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165351131481829664049133457 124013348611372248036850093)
      ·
        refine ⟨46505005729264593013818785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124013348611372248036850093 46505005729264593013818785)
        ·
          refine ⟨34878754296948444760364089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46505005729264593013818785 34878754296948444760364089)
          ·
            refine ⟨26159065722711333570273067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34878754296948444760364089 26159065722711333570273067)
            ·
              refine ⟨39238598584067000355409601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26159065722711333570273067 39238598584067000355409601)
              ·
                refine ⟨29428948938050250266557201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39238598584067000355409601 29428948938050250266557201)
                ·
                  refine ⟨22071711703537687699917901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29428948938050250266557201 22071711703537687699917901)
                  ·
                    refine ⟨8276891888826632887469213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22071711703537687699917901 8276891888826632887469213)
                    ·
                      refine ⟨3103834458309987332800955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8276891888826632887469213 3103834458309987332800955)
                      ·
                        rfl

theorem cell23_6044696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_6044696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044696 prefixEnd_6044696 := by exact prefixLift 6044696
  have htrace : WordTrace (prefixWord ++ tailWord_6044696) baseStart_6044696 baseEnd_6044696 := by
    simpa [prefixWord, tailWord_6044696, baseEnd_6044696] using wordTrace_append hprefix tailTrace_6044696
  have hstable : (prefixWord ++ tailWord_6044696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044696).length < 2 ^ (prefixWord ++ tailWord_6044696).sum := by decide
  have hdescent : baseEnd_6044696 < baseStart_6044696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044709 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 1, 1, 7]
def baseStart_6044709 : Nat := 118140960795 + 6044709 * 2 ^ 59
def prefixEnd_6044709 : Nat := 4983230072969 + 3 ^ 40 * 6044709 * 2
def baseEnd_6044709 : Nat := 3103841133558495781938395

theorem tailTrace_6044709 : CollatzResearch.WordTrace tailWord_6044709 prefixEnd_6044709 3103841133558495781938395 := by
  unfold tailWord_6044709
  simp only [CollatzResearch.WordTrace]
  refine ⟨220468649458059121952401181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146979099638706081301600787 220468649458059121952401181)
  ·
    refine ⟨82675743546772170732150443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220468649458059121952401181 82675743546772170732150443)
    ·
      refine ⟨124013615320158256098225665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82675743546772170732150443 124013615320158256098225665)
      ·
        refine ⟨93010211490118692073669249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124013615320158256098225665 93010211490118692073669249)
        ·
          refine ⟨69757658617589019055251937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93010211490118692073669249 69757658617589019055251937)
          ·
            refine ⟨52318243963191764291438953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69757658617589019055251937 52318243963191764291438953)
            ·
              refine ⟨39238682972393823218579215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52318243963191764291438953 39238682972393823218579215)
              ·
                refine ⟨58858024458590734827868823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39238682972393823218579215 58858024458590734827868823)
                ·
                  refine ⟨88287036687886102241803235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58858024458590734827868823 88287036687886102241803235)
                  ·
                    refine ⟨132430555031829153362704853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88287036687886102241803235 132430555031829153362704853)
                    ·
                      refine ⟨3103841133558495781938395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132430555031829153362704853 3103841133558495781938395)
                      ·
                        rfl

theorem cell23_6044709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_6044709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044709 prefixEnd_6044709 := by exact prefixLift 6044709
  have htrace : WordTrace (prefixWord ++ tailWord_6044709) baseStart_6044709 baseEnd_6044709 := by
    simpa [prefixWord, tailWord_6044709, baseEnd_6044709] using wordTrace_append hprefix tailTrace_6044709
  have hstable : (prefixWord ++ tailWord_6044709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044709).length < 2 ^ (prefixWord ++ tailWord_6044709).sum := by decide
  have hdescent : baseEnd_6044709 < baseStart_6044709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044714 : List Nat := [3, 1, 4, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_6044714 : Nat := 118140960795 + 6044714 * 2 ^ 59
def prefixEnd_6044714 : Nat := 4983230072969 + 3 ^ 40 * 6044714 * 2
def baseEnd_6044714 : Nat := 3103843700961768262375873

theorem tailTrace_6044714 : CollatzResearch.WordTrace tailWord_6044714 prefixEnd_6044714 3103843700961768262375873 := by
  unfold tailWord_6044714
  simp only [CollatzResearch.WordTrace]
  refine ⟨55117207955760251951583299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146979221215360671870888797 55117207955760251951583299)
  ·
    refine ⟨82675811933640377927374949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55117207955760251951583299 82675811933640377927374949)
    ·
      refine ⟨15501714737557570861382803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82675811933640377927374949 15501714737557570861382803)
      ·
        refine ⟨23252572106336356292074205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15501714737557570861382803 23252572106336356292074205)
        ·
          refine ⟨8719714539876133609527827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23252572106336356292074205 8719714539876133609527827)
          ·
            refine ⟨13079571809814200414291741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8719714539876133609527827 13079571809814200414291741)
            ·
              refine ⟨4904839428680325155359403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13079571809814200414291741 4904839428680325155359403)
              ·
                refine ⟨7357259143020487733039105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4904839428680325155359403 7357259143020487733039105)
                ·
                  refine ⟨5517944357265365799779329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7357259143020487733039105 5517944357265365799779329)
                  ·
                    refine ⟨4138458267949024349834497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5517944357265365799779329 4138458267949024349834497)
                    ·
                      refine ⟨3103843700961768262375873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4138458267949024349834497 3103843700961768262375873)
                      ·
                        rfl

theorem cell23_6044714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_6044714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044714 prefixEnd_6044714 := by exact prefixLift 6044714
  have htrace : WordTrace (prefixWord ++ tailWord_6044714) baseStart_6044714 baseEnd_6044714 := by
    simpa [prefixWord, tailWord_6044714, baseEnd_6044714] using wordTrace_append hprefix tailTrace_6044714
  have hstable : (prefixWord ++ tailWord_6044714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044714).length < 2 ^ (prefixWord ++ tailWord_6044714).sum := by decide
  have hdescent : baseEnd_6044714 < baseStart_6044714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044736 : List Nat := [2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 4]
def baseStart_6044736 : Nat := 118140960795 + 6044736 * 2 ^ 59
def prefixEnd_6044736 : Nat := 4983230072969 + 3 ^ 40 * 6044736 * 2
def baseEnd_6044736 : Nat := 3103854997536167176300771

theorem tailTrace_6044736 : CollatzResearch.WordTrace tailWord_6044736 prefixEnd_6044736 3103854997536167176300771 := by
  unfold tailWord_6044736
  simp only [CollatzResearch.WordTrace]
  refine ⟨110234817114480652781817031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146979756152640870375756041 110234817114480652781817031)
  ·
    refine ⟨165352225671720979172725547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110234817114480652781817031 165352225671720979172725547)
    ·
      refine ⟨248028338507581468759088321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165352225671720979172725547 248028338507581468759088321)
      ·
        refine ⟨186021253880686101569316241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248028338507581468759088321 186021253880686101569316241)
        ·
          refine ⟨139515940410514576176987181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186021253880686101569316241 139515940410514576176987181)
          ·
            refine ⟨52318477653942966066370193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139515940410514576176987181 52318477653942966066370193)
            ·
              refine ⟨39238858240457224549777645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52318477653942966066370193 39238858240457224549777645)
              ·
                refine ⟨14714571840171459206166617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39238858240457224549777645 14714571840171459206166617)
                ·
                  refine ⟨11035928880128594404624963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14714571840171459206166617 11035928880128594404624963)
                  ·
                    refine ⟨16553893320192891606937445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11035928880128594404624963 16553893320192891606937445)
                    ·
                      refine ⟨3103854997536167176300771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16553893320192891606937445 3103854997536167176300771)
                      ·
                        rfl

theorem cell23_6044736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_6044736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044736 prefixEnd_6044736 := by exact prefixLift 6044736
  have htrace : WordTrace (prefixWord ++ tailWord_6044736) baseStart_6044736 baseEnd_6044736 := by
    simpa [prefixWord, tailWord_6044736, baseEnd_6044736] using wordTrace_append hprefix tailTrace_6044736
  have hstable : (prefixWord ++ tailWord_6044736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044736).length < 2 ^ (prefixWord ++ tailWord_6044736).sum := by decide
  have hdescent : baseEnd_6044736 < baseStart_6044736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044737 : List Nat := [1, 2, 5, 1, 4, 1, 1, 3, 5]
def baseStart_6044737 : Nat := 118140960795 + 6044737 * 2 ^ 59
def prefixEnd_6044737 : Nat := 4983230072969 + 3 ^ 40 * 6044737 * 2
def baseEnd_6044737 : Nat := 344872834557424630265363

theorem tailTrace_6044737 : CollatzResearch.WordTrace tailWord_6044737 prefixEnd_6044737 344872834557424630265363 := by
  unfold tailWord_6044737
  simp only [CollatzResearch.WordTrace]
  refine ⟨220469670701957682734420465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146979780467971788489613643 220469670701957682734420465)
  ·
    refine ⟨165352253026468262050815349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220469670701957682734420465 165352253026468262050815349)
    ·
      refine ⟨15501773721231399567263939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165352253026468262050815349 15501773721231399567263939)
      ·
        refine ⟨23252660581847099350895909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15501773721231399567263939 23252660581847099350895909)
        ·
          refine ⟨4359873859096331128292983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23252660581847099350895909 4359873859096331128292983)
          ·
            refine ⟨6539810788644496692439475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4359873859096331128292983 6539810788644496692439475)
            ·
              refine ⟨9809716182966745038659213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6539810788644496692439475 9809716182966745038659213)
              ·
                refine ⟨3678643568612529389497205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9809716182966745038659213 3678643568612529389497205)
                ·
                  refine ⟨344872834557424630265363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3678643568612529389497205 344872834557424630265363)
                  ·
                    rfl

theorem cell23_6044737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 5].length) (baseStart_6044737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044737 prefixEnd_6044737 := by exact prefixLift 6044737
  have htrace : WordTrace (prefixWord ++ tailWord_6044737) baseStart_6044737 baseEnd_6044737 := by
    simpa [prefixWord, tailWord_6044737, baseEnd_6044737] using wordTrace_append hprefix tailTrace_6044737
  have hstable : (prefixWord ++ tailWord_6044737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044737).length < 2 ^ (prefixWord ++ tailWord_6044737).sum := by decide
  have hdescent : baseEnd_6044737 < baseStart_6044737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044746 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 5, 4]
def baseStart_6044746 : Nat := 118140960795 + 6044746 * 2 ^ 59
def prefixEnd_6044746 : Nat := 4983230072969 + 3 ^ 40 * 6044746 * 2
def baseEnd_6044746 : Nat := 1034620044114237379058575

theorem tailTrace_6044746 : CollatzResearch.WordTrace tailWord_6044746 prefixEnd_6044746 1034620044114237379058575 := by
  unfold tailWord_6044746
  simp only [CollatzResearch.WordTrace]
  refine ⟨55117499739731269317874523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146979999305950051514332061 55117499739731269317874523)
  ·
    refine ⟨82676249609596903976811785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55117499739731269317874523 82676249609596903976811785)
    ·
      refine ⟨62007187207197677982608839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82676249609596903976811785 62007187207197677982608839)
      ·
        refine ⟨93010780810796516973913259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62007187207197677982608839 93010780810796516973913259)
        ·
          refine ⟨139516171216194775460869889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93010780810796516973913259 139516171216194775460869889)
          ·
            refine ⟨104637128412146081595652417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139516171216194775460869889 104637128412146081595652417)
            ·
              refine ⟨78477846309109561196739313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104637128412146081595652417 78477846309109561196739313)
              ·
                refine ⟨58858384731832170897554485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78477846309109561196739313 58858384731832170897554485)
                ·
                  refine ⟨5517973568609266021645733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58858384731832170897554485 5517973568609266021645733)
                  ·
                    refine ⟨1034620044114237379058575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5517973568609266021645733 1034620044114237379058575)
                    ·
                      rfl

theorem cell23_6044746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_6044746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044746 prefixEnd_6044746 := by exact prefixLift 6044746
  have htrace : WordTrace (prefixWord ++ tailWord_6044746) baseStart_6044746 baseEnd_6044746 := by
    simpa [prefixWord, tailWord_6044746, baseEnd_6044746] using wordTrace_append hprefix tailTrace_6044746
  have hstable : (prefixWord ++ tailWord_6044746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044746).length < 2 ^ (prefixWord ++ tailWord_6044746).sum := by decide
  have hdescent : baseEnd_6044746 < baseStart_6044746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044790 : List Nat := [5, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_6044790 : Nat := 118140960795 + 6044790 * 2 ^ 59
def prefixEnd_6044790 : Nat := 4983230072969 + 3 ^ 40 * 6044790 * 2
def baseEnd_6044790 : Nat := 3103882725491509965025523

theorem tailTrace_6044790 : CollatzResearch.WordTrace tailWord_6044790 prefixEnd_6044790 3103882725491509965025523 := by
  unfold tailWord_6044790
  simp only [CollatzResearch.WordTrace]
  refine ⟨13779475235672854549131239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146981069180510448524066549 13779475235672854549131239)
  ·
    refine ⟨20669212853509281823696859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13779475235672854549131239 20669212853509281823696859)
    ·
      refine ⟨31003819280263922735545289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20669212853509281823696859 31003819280263922735545289)
      ·
        refine ⟨23252864460197942051658967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31003819280263922735545289 23252864460197942051658967)
        ·
          refine ⟨34879296690296913077488451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23252864460197942051658967 34879296690296913077488451)
          ·
            refine ⟨52318945035445369616232677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34879296690296913077488451 52318945035445369616232677)
            ·
              refine ⟨9809802194146006803043627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52318945035445369616232677 9809802194146006803043627)
              ·
                refine ⟨14714703291219010204565441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9809802194146006803043627 14714703291219010204565441)
                ·
                  refine ⟨11036027468414257653424081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14714703291219010204565441 11036027468414257653424081)
                  ·
                    refine ⟨8277020601310693240068061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11036027468414257653424081 8277020601310693240068061)
                    ·
                      refine ⟨3103882725491509965025523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8277020601310693240068061 3103882725491509965025523)
                      ·
                        rfl

theorem cell23_6044790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_6044790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044790 prefixEnd_6044790 := by exact prefixLift 6044790
  have htrace : WordTrace (prefixWord ++ tailWord_6044790) baseStart_6044790 baseEnd_6044790 := by
    simpa [prefixWord, tailWord_6044790, baseEnd_6044790] using wordTrace_append hprefix tailTrace_6044790
  have hstable : (prefixWord ++ tailWord_6044790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044790).length < 2 ^ (prefixWord ++ tailWord_6044790).sum := by decide
  have hdescent : baseEnd_6044790 < baseStart_6044790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044799 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 7]
def baseStart_6044799 : Nat := 118140960795 + 6044799 * 2 ^ 59
def prefixEnd_6044799 : Nat := 4983230072969 + 3 ^ 40 * 6044799 * 2
def baseEnd_6044799 : Nat := 3103887346817400429812981

theorem tailTrace_6044799 : CollatzResearch.WordTrace tailWord_6044799 prefixEnd_6044799 3103887346817400429812981 := by
  unfold tailWord_6044799
  simp only [CollatzResearch.WordTrace]
  refine ⟨220471932027733067323177451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146981288018488711548784967 220471932027733067323177451)
  ·
    refine ⟨330707898041599600984766177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220471932027733067323177451 330707898041599600984766177)
    ·
      refine ⟨248030923531199700738574633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330707898041599600984766177 248030923531199700738574633)
      ·
        refine ⟨186023192648399775553930975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248030923531199700738574633 186023192648399775553930975)
        ·
          refine ⟨279034788972599663330896463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186023192648399775553930975 279034788972599663330896463)
          ·
            refine ⟨418552183458899494996344695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279034788972599663330896463 418552183458899494996344695)
            ·
              refine ⟨627828275188349242494517043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418552183458899494996344695 627828275188349242494517043)
              ·
                refine ⟨941742412782523863741775565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627828275188349242494517043 941742412782523863741775565)
                ·
                  refine ⟨353153404793446448903165837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 941742412782523863741775565 353153404793446448903165837)
                  ·
                    refine ⟨132432526797542418338687189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 353153404793446448903165837 132432526797542418338687189)
                    ·
                      refine ⟨3103887346817400429812981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132432526797542418338687189 3103887346817400429812981)
                      ·
                        rfl

theorem cell23_6044799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_6044799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044799 prefixEnd_6044799 := by exact prefixLift 6044799
  have htrace : WordTrace (prefixWord ++ tailWord_6044799) baseStart_6044799 baseEnd_6044799 := by
    simpa [prefixWord, tailWord_6044799, baseEnd_6044799] using wordTrace_append hprefix tailTrace_6044799
  have hstable : (prefixWord ++ tailWord_6044799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044799).length < 2 ^ (prefixWord ++ tailWord_6044799).sum := by decide
  have hdescent : baseEnd_6044799 < baseStart_6044799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044814 : List Nat := [4, 1, 1, 3, 2, 3, 2, 2, 1, 4]
def baseStart_6044814 : Nat := 118140960795 + 6044814 * 2 ^ 59
def prefixEnd_6044814 : Nat := 4983230072969 + 3 ^ 40 * 6044814 * 2
def baseEnd_6044814 : Nat := 1034631683009072623708471

theorem tailTrace_6044814 : CollatzResearch.WordTrace tailWord_6044814 prefixEnd_6044814 1034631683009072623708471 := by
  unfold tailWord_6044814
  simp only [CollatzResearch.WordTrace]
  refine ⟨27559059890334840610621687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146981652748452483256648997 27559059890334840610621687)
  ·
    refine ⟨41338589835502260915932531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27559059890334840610621687 41338589835502260915932531)
    ·
      refine ⟨62007884753253391373898797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41338589835502260915932531 62007884753253391373898797)
      ·
        refine ⟨23252956782470021765212049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62007884753253391373898797 23252956782470021765212049)
        ·
          refine ⟨17439717586852516323909037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23252956782470021765212049 17439717586852516323909037)
          ·
            refine ⟨6539894095069693621465889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17439717586852516323909037 6539894095069693621465889)
            ·
              refine ⟨4904920571302270216099417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6539894095069693621465889 4904920571302270216099417)
              ·
                refine ⟨3678690428476702662074563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4904920571302270216099417 3678690428476702662074563)
                ·
                  refine ⟨5518035642715053993111845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3678690428476702662074563 5518035642715053993111845)
                  ·
                    refine ⟨1034631683009072623708471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5518035642715053993111845 1034631683009072623708471)
                    ·
                      rfl

theorem cell23_6044814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_6044814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044814 prefixEnd_6044814 := by exact prefixLift 6044814
  have htrace : WordTrace (prefixWord ++ tailWord_6044814) baseStart_6044814 baseEnd_6044814 := by
    simpa [prefixWord, tailWord_6044814, baseEnd_6044814] using wordTrace_append hprefix tailTrace_6044814
  have hstable : (prefixWord ++ tailWord_6044814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044814).length < 2 ^ (prefixWord ++ tailWord_6044814).sum := by decide
  have hdescent : baseEnd_6044814 < baseStart_6044814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044856 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 3, 2, 4]
def baseStart_6044856 : Nat := 118140960795 + 6044856 * 2 ^ 59
def prefixEnd_6044856 : Nat := 4983230072969 + 3 ^ 40 * 6044856 * 2
def baseEnd_6044856 : Nat := 3103916615214706706800219

theorem tailTrace_6044856 : CollatzResearch.WordTrace tailWord_6044856 prefixEnd_6044856 3103916615214706706800219 := by
  unfold tailWord_6044856
  simp only [CollatzResearch.WordTrace]
  refine ⟨110237005494263283029001211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146982673992351044038668281 110237005494263283029001211)
  ·
    refine ⟨165355508241394924543501817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110237005494263283029001211 165355508241394924543501817)
    ·
      refine ⟨124016631181046193407626363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165355508241394924543501817 124016631181046193407626363)
      ·
        refine ⟨186024946771569290111439545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124016631181046193407626363 186024946771569290111439545)
        ·
          refine ⟨139518710078676967583579659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186024946771569290111439545 139518710078676967583579659)
          ·
            refine ⟨209278065118015451375369489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139518710078676967583579659 209278065118015451375369489)
            ·
              refine ⟨156958548838511588531527117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209278065118015451375369489 156958548838511588531527117)
              ·
                refine ⟨58859455814441845699322669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156958548838511588531527117 58859455814441845699322669)
                ·
                  refine ⟨22072295930415692137246001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58859455814441845699322669 22072295930415692137246001)
                  ·
                    refine ⟨16554221947811769102934501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22072295930415692137246001 16554221947811769102934501)
                    ·
                      refine ⟨3103916615214706706800219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16554221947811769102934501 3103916615214706706800219)
                      ·
                        rfl

theorem cell23_6044856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_6044856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044856 prefixEnd_6044856 := by exact prefixLift 6044856
  have htrace : WordTrace (prefixWord ++ tailWord_6044856) baseStart_6044856 baseEnd_6044856 := by
    simpa [prefixWord, tailWord_6044856, baseEnd_6044856] using wordTrace_append hprefix tailTrace_6044856
  have hstable : (prefixWord ++ tailWord_6044856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044856).length < 2 ^ (prefixWord ++ tailWord_6044856).sum := by decide
  have hdescent : baseEnd_6044856 < baseStart_6044856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044860 : List Nat := [2, 2, 2, 3, 2, 2, 1, 3, 1, 1, 4]
def baseStart_6044860 : Nat := 118140960795 + 6044860 * 2 ^ 59
def prefixEnd_6044860 : Nat := 4983230072969 + 3 ^ 40 * 6044860 * 2
def baseEnd_6044860 : Nat := 3103918669137324691150201

theorem tailTrace_6044860 : CollatzResearch.WordTrace tailWord_6044860 prefixEnd_6044860 3103918669137324691150201 := by
  unfold tailWord_6044860
  simp only [CollatzResearch.WordTrace]
  refine ⟨110237078440256037370574017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146982771253674716494098689 110237078440256037370574017)
  ·
    refine ⟨82677808830192028027930513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110237078440256037370574017 82677808830192028027930513)
    ·
      refine ⟨62008356622644021020947885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82677808830192028027930513 62008356622644021020947885)
      ·
        refine ⟨23253133733491507882855457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62008356622644021020947885 23253133733491507882855457)
        ·
          refine ⟨17439850300118630912141593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23253133733491507882855457 17439850300118630912141593)
          ·
            refine ⟨13079887725088973184106195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17439850300118630912141593 13079887725088973184106195)
            ·
              refine ⟨19619831587633459776159293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13079887725088973184106195 19619831587633459776159293)
              ·
                refine ⟨7357436845362547416059735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19619831587633459776159293 7357436845362547416059735)
                ·
                  refine ⟨11036155268043821124089603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7357436845362547416059735 11036155268043821124089603)
                  ·
                    refine ⟨16554232902065731686134405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11036155268043821124089603 16554232902065731686134405)
                    ·
                      refine ⟨3103918669137324691150201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16554232902065731686134405 3103918669137324691150201)
                      ·
                        rfl

theorem cell23_6044860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_6044860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044860 prefixEnd_6044860 := by exact prefixLift 6044860
  have htrace : WordTrace (prefixWord ++ tailWord_6044860) baseStart_6044860 baseEnd_6044860 := by
    simpa [prefixWord, tailWord_6044860, baseEnd_6044860] using wordTrace_append hprefix tailTrace_6044860
  have hstable : (prefixWord ++ tailWord_6044860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044860).length < 2 ^ (prefixWord ++ tailWord_6044860).sum := by decide
  have hdescent : baseEnd_6044860 < baseStart_6044860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044910 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_6044910 : Nat := 118140960795 + 6044910 * 2 ^ 59
def prefixEnd_6044910 : Nat := 4983230072969 + 3 ^ 40 * 6044910 * 2
def baseEnd_6044910 : Nat := 3103944343170049495524971

theorem tailTrace_6044910 : CollatzResearch.WordTrace tailWord_6044910 prefixEnd_6044910 3103944343170049495524971 := by
  unfold tailWord_6044910
  simp only [CollatzResearch.WordTrace]
  refine ⟨27559497566291366660058523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146983987020220622186978789 27559497566291366660058523)
  ·
    refine ⟨41339246349437049990087785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27559497566291366660058523 41339246349437049990087785)
    ·
      refine ⟨31004434762077787492565839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41339246349437049990087785 31004434762077787492565839)
      ·
        refine ⟨46506652143116681238848759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31004434762077787492565839 46506652143116681238848759)
        ·
          refine ⟨69759978214675021858273139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46506652143116681238848759 69759978214675021858273139)
          ·
            refine ⟨104639967322012532787409709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69759978214675021858273139 104639967322012532787409709)
            ·
              refine ⟨39239987745754699795278641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104639967322012532787409709 39239987745754699795278641)
              ·
                refine ⟨29429990809316024846458981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39239987745754699795278641 29429990809316024846458981)
                ·
                  refine ⟨5518123276746754658711059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29429990809316024846458981 5518123276746754658711059)
                  ·
                    refine ⟨8277184915120131988066589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5518123276746754658711059 8277184915120131988066589)
                    ·
                      refine ⟨3103944343170049495524971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8277184915120131988066589 3103944343170049495524971)
                      ·
                        rfl

theorem cell23_6044910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_6044910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044910 prefixEnd_6044910 := by exact prefixLift 6044910
  have htrace : WordTrace (prefixWord ++ tailWord_6044910) baseStart_6044910 baseEnd_6044910 := by
    simpa [prefixWord, tailWord_6044910, baseEnd_6044910] using wordTrace_append hprefix tailTrace_6044910
  have hstable : (prefixWord ++ tailWord_6044910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044910).length < 2 ^ (prefixWord ++ tailWord_6044910).sum := by decide
  have hdescent : baseEnd_6044910 < baseStart_6044910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044911 : List Nat := [1, 1, 2, 1, 7, 2, 1, 3, 1, 2, 2]
def baseStart_6044911 : Nat := 118140960795 + 6044911 * 2 ^ 59
def prefixEnd_6044911 : Nat := 4983230072969 + 3 ^ 40 * 6044911 * 2
def baseEnd_6044911 : Nat := 3103944856650703991612467

theorem tailTrace_6044911 : CollatzResearch.WordTrace tailWord_6044911 prefixEnd_6044911 3103944856650703991612467 := by
  unfold tailWord_6044911
  simp only [CollatzResearch.WordTrace]
  refine ⟨220476017003327310451254587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146984011335551540300836391 220476017003327310451254587)
  ·
    refine ⟨330714025504990965676881881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220476017003327310451254587 330714025504990965676881881)
    ·
      refine ⟨248035519128743224257661411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330714025504990965676881881 248035519128743224257661411)
      ·
        refine ⟨372053278693114836386492117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248035519128743224257661411 372053278693114836386492117)
        ·
          refine ⟨8719998719369878977808409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 372053278693114836386492117 8719998719369878977808409)
          ·
            refine ⟨6539999039527409233356307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8719998719369878977808409 6539999039527409233356307)
            ·
              refine ⟨9809998559291113850034461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6539999039527409233356307 9809998559291113850034461)
              ·
                refine ⟨3678749459734167693762923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9809998559291113850034461 3678749459734167693762923)
                ·
                  refine ⟨5518124189601251540644385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3678749459734167693762923 5518124189601251540644385)
                  ·
                    refine ⟨4138593142200938655483289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5518124189601251540644385 4138593142200938655483289)
                    ·
                      refine ⟨3103944856650703991612467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4138593142200938655483289 3103944856650703991612467)
                      ·
                        rfl

theorem cell23_6044911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 1, 2, 2].length) (baseStart_6044911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044911 prefixEnd_6044911 := by exact prefixLift 6044911
  have htrace : WordTrace (prefixWord ++ tailWord_6044911) baseStart_6044911 baseEnd_6044911 := by
    simpa [prefixWord, tailWord_6044911, baseEnd_6044911] using wordTrace_append hprefix tailTrace_6044911
  have hstable : (prefixWord ++ tailWord_6044911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044911).length < 2 ^ (prefixWord ++ tailWord_6044911).sum := by decide
  have hdescent : baseEnd_6044911 < baseStart_6044911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044954 : List Nat := [3, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2]
def baseStart_6044954 : Nat := 118140960795 + 6044954 * 2 ^ 59
def prefixEnd_6044954 : Nat := 4983230072969 + 3 ^ 40 * 6044954 * 2
def baseEnd_6044954 : Nat := 3103966936318847323374769

theorem tailTrace_6044954 : CollatzResearch.WordTrace tailWord_6044954 prefixEnd_6044954 3103966936318847323374769 := by
  unfold tailWord_6044954
  simp only [CollatzResearch.WordTrace]
  refine ⟨55119396335542882198767479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146985056894781019196713277 55119396335542882198767479)
  ·
    refine ⟨82679094503314323298151219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55119396335542882198767479 82679094503314323298151219)
    ·
      refine ⟨124018641754971484947226829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82679094503314323298151219 124018641754971484947226829)
      ·
        refine ⟨46506990658114306855210061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124018641754971484947226829 46506990658114306855210061)
        ·
          refine ⟨17440121496792865070703773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46506990658114306855210061 17440121496792865070703773)
          ·
            refine ⟨6540045561297324401513915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17440121496792865070703773 6540045561297324401513915)
            ·
              refine ⟨9810068341945986602270873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6540045561297324401513915 9810068341945986602270873)
              ·
                refine ⟨7357551256459489951703155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9810068341945986602270873 7357551256459489951703155)
                ·
                  refine ⟨11036326884689234927554733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7357551256459489951703155 11036326884689234927554733)
                  ·
                    refine ⟨4138622581758463097833025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11036326884689234927554733 4138622581758463097833025)
                    ·
                      refine ⟨3103966936318847323374769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4138622581758463097833025 3103966936318847323374769)
                      ·
                        rfl

theorem cell23_6044954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_6044954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044954 prefixEnd_6044954 := by exact prefixLift 6044954
  have htrace : WordTrace (prefixWord ++ tailWord_6044954) baseStart_6044954 baseEnd_6044954 := by
    simpa [prefixWord, tailWord_6044954, baseEnd_6044954] using wordTrace_append hprefix tailTrace_6044954
  have hstable : (prefixWord ++ tailWord_6044954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044954).length < 2 ^ (prefixWord ++ tailWord_6044954).sum := by decide
  have hdescent : baseEnd_6044954 < baseStart_6044954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044970 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_6044970 : Nat := 118140960795 + 6044970 * 2 ^ 59
def prefixEnd_6044970 : Nat := 4983230072969 + 3 ^ 40 * 6044970 * 2
def baseEnd_6044970 : Nat := 3103975152009319260774695

theorem tailTrace_6044970 : CollatzResearch.WordTrace tailWord_6044970 prefixEnd_6044970 3103975152009319260774695 := by
  unfold tailWord_6044970
  simp only [CollatzResearch.WordTrace]
  refine ⟨55119542227528390881913091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146985445940075709018434909 55119542227528390881913091)
  ·
    refine ⟨82679313341292586322869637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55119542227528390881913091 82679313341292586322869637)
    ·
      refine ⟨15502371251492359935538057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82679313341292586322869637 15502371251492359935538057)
      ·
        refine ⟨11626778438619269951653543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15502371251492359935538057 11626778438619269951653543)
        ·
          refine ⟨17440167657928904927480315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11626778438619269951653543 17440167657928904927480315)
          ·
            refine ⟨26160251486893357391220473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17440167657928904927480315 26160251486893357391220473)
            ·
              refine ⟨19620188615170018043415355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26160251486893357391220473 19620188615170018043415355)
              ·
                refine ⟨29430282922755027065123033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19620188615170018043415355 29430282922755027065123033)
                ·
                  refine ⟨22072712192066270298842275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29430282922755027065123033 22072712192066270298842275)
                  ·
                    refine ⟨33109068288099405448263413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22072712192066270298842275 33109068288099405448263413)
                    ·
                      refine ⟨3103975152009319260774695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33109068288099405448263413 3103975152009319260774695)
                      ·
                        rfl

theorem cell23_6044970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_6044970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044970 prefixEnd_6044970 := by exact prefixLift 6044970
  have htrace : WordTrace (prefixWord ++ tailWord_6044970) baseStart_6044970 baseEnd_6044970 := by
    simpa [prefixWord, tailWord_6044970, baseEnd_6044970] using wordTrace_append hprefix tailTrace_6044970
  have hstable : (prefixWord ++ tailWord_6044970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044970).length < 2 ^ (prefixWord ++ tailWord_6044970).sum := by decide
  have hdescent : baseEnd_6044970 < baseStart_6044970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044980 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_6044980 : Nat := 118140960795 + 6044980 * 2 ^ 59
def prefixEnd_6044980 : Nat := 4983230072969 + 3 ^ 40 * 6044980 * 2
def baseEnd_6044980 : Nat := 3103980286815864221649649

theorem tailTrace_6044980 : CollatzResearch.WordTrace tailWord_6044980 prefixEnd_6044980 3103980286815864221649649 := by
  unfold tailWord_6044980
  simp only [CollatzResearch.WordTrace]
  refine ⟨110239266820038667617758197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146985689093384890157010929 110239266820038667617758197)
  ·
    refine ⟨10334931264378625089164831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110239266820038667617758197 10334931264378625089164831)
    ·
      refine ⟨15502396896567937633747247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10334931264378625089164831 15502396896567937633747247)
      ·
        refine ⟨23253595344851906450620871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15502396896567937633747247 23253595344851906450620871)
        ·
          refine ⟨34880393017277859675931307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23253595344851906450620871 34880393017277859675931307)
          ·
            refine ⟨52320589525916789513896961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34880393017277859675931307 52320589525916789513896961)
            ·
              refine ⟨39240442144437592135422721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52320589525916789513896961 39240442144437592135422721)
              ·
                refine ⟨29430331608328194101567041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39240442144437592135422721 29430331608328194101567041)
                ·
                  refine ⟨22072748706246145576175281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29430331608328194101567041 22072748706246145576175281)
                  ·
                    refine ⟨16554561529684609182131461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22072748706246145576175281 16554561529684609182131461)
                    ·
                      refine ⟨3103980286815864221649649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16554561529684609182131461 3103980286815864221649649)
                      ·
                        rfl

theorem cell23_6044980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_6044980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044980 prefixEnd_6044980 := by exact prefixLift 6044980
  have htrace : WordTrace (prefixWord ++ tailWord_6044980) baseStart_6044980 baseEnd_6044980 := by
    simpa [prefixWord, tailWord_6044980, baseEnd_6044980] using wordTrace_append hprefix tailTrace_6044980
  have hstable : (prefixWord ++ tailWord_6044980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044980).length < 2 ^ (prefixWord ++ tailWord_6044980).sum := by decide
  have hdescent : baseEnd_6044980 < baseStart_6044980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045010 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2]
def baseStart_6045010 : Nat := 118140960795 + 6045010 * 2 ^ 59
def prefixEnd_6045010 : Nat := 4983230072969 + 3 ^ 40 * 6045010 * 2
def baseEnd_6045010 : Nat := 3103995691235499104274511

theorem tailTrace_6045010 : CollatzResearch.WordTrace tailWord_6045010 prefixEnd_6045010 3103995691235499104274511 := by
  unfold tailWord_6045010
  simp only [CollatzResearch.WordTrace]
  refine ⟨55119906957492162589777121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146986418553312433572738989 55119906957492162589777121)
  ·
    refine ⟨41339930218119121942332841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55119906957492162589777121 41339930218119121942332841)
    ·
      refine ⟨31004947663589341456749631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41339930218119121942332841 31004947663589341456749631)
      ·
        refine ⟨46507421495384012185124447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31004947663589341456749631 46507421495384012185124447)
        ·
          refine ⟨69761132243076018277686671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46507421495384012185124447 69761132243076018277686671)
          ·
            refine ⟨104641698364614027416530007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69761132243076018277686671 104641698364614027416530007)
            ·
              refine ⟨156962547546921041124795011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104641698364614027416530007 156962547546921041124795011)
              ·
                refine ⟨235443821320381561687192517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156962547546921041124795011 235443821320381561687192517)
                ·
                  refine ⟨44145716497571542816348597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235443821320381561687192517 44145716497571542816348597)
                  ·
                    refine ⟨4138660921647332139032681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44145716497571542816348597 4138660921647332139032681)
                    ·
                      refine ⟨3103995691235499104274511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4138660921647332139032681 3103995691235499104274511)
                      ·
                        rfl

theorem cell23_6045010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_6045010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045010 prefixEnd_6045010 := by exact prefixLift 6045010
  have htrace : WordTrace (prefixWord ++ tailWord_6045010) baseStart_6045010 baseEnd_6045010 := by
    simpa [prefixWord, tailWord_6045010, baseEnd_6045010] using wordTrace_append hprefix tailTrace_6045010
  have hstable : (prefixWord ++ tailWord_6045010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045010).length < 2 ^ (prefixWord ++ tailWord_6045010).sum := by decide
  have hdescent : baseEnd_6045010 < baseStart_6045010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045040 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 4, 4, 2]
def baseStart_6045040 : Nat := 118140960795 + 6045040 * 2 ^ 59
def prefixEnd_6045040 : Nat := 4983230072969 + 3 ^ 40 * 6045040 * 2
def baseEnd_6045040 : Nat := 3104011095655133986899373

theorem tailTrace_6045040 : CollatzResearch.WordTrace tailWord_6045040 prefixEnd_6045040 3104011095655133986899373 := by
  unfold tailWord_6045040
  simp only [CollatzResearch.WordTrace]
  refine ⟨110240361009929982741350287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146987148013239976988467049 110240361009929982741350287)
  ·
    refine ⟨165360541514894974112025431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110240361009929982741350287 165360541514894974112025431)
    ·
      refine ⟨248040812272342461168038147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165360541514894974112025431 248040812272342461168038147)
      ·
        refine ⟨372061218408513691752057221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248040812272342461168038147 372061218408513691752057221)
        ·
          refine ⟨69761478451596317203510729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 372061218408513691752057221 69761478451596317203510729)
          ·
            refine ⟨52321108838697237902633047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69761478451596317203510729 52321108838697237902633047)
            ·
              refine ⟨78481663258045856853949571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52321108838697237902633047 78481663258045856853949571)
              ·
                refine ⟨117722494887068785280924357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78481663258045856853949571 117722494887068785280924357)
                ·
                  refine ⟨22072967791325397240173317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117722494887068785280924357 22072967791325397240173317)
                  ·
                    refine ⟨4138681460873511982532497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22072967791325397240173317 4138681460873511982532497)
                    ·
                      refine ⟨3104011095655133986899373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4138681460873511982532497 3104011095655133986899373)
                      ·
                        rfl

theorem cell23_6045040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 4, 4, 2].length) (baseStart_6045040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045040 prefixEnd_6045040 := by exact prefixLift 6045040
  have htrace : WordTrace (prefixWord ++ tailWord_6045040) baseStart_6045040 baseEnd_6045040 := by
    simpa [prefixWord, tailWord_6045040, baseEnd_6045040] using wordTrace_append hprefix tailTrace_6045040
  have hstable : (prefixWord ++ tailWord_6045040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045040).length < 2 ^ (prefixWord ++ tailWord_6045040).sum := by decide
  have hdescent : baseEnd_6045040 < baseStart_6045040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045043 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 3]
def baseStart_6045043 : Nat := 118140960795 + 6045043 * 2 ^ 59
def prefixEnd_6045043 : Nat := 4983230072969 + 3 ^ 40 * 6045043 * 2
def baseEnd_6045043 : Nat := 3104012636097097475161859

theorem tailTrace_6045043 : CollatzResearch.WordTrace tailWord_6045043 prefixEnd_6045043 3104012636097097475161859 := by
  unfold tailWord_6045043
  simp only [CollatzResearch.WordTrace]
  refine ⟨220480831438849096995059783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146987220959232731330039855 220480831438849096995059783)
  ·
    refine ⟨330721247158273645492589675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220480831438849096995059783 330721247158273645492589675)
    ·
      refine ⟨496081870737410468238884513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330721247158273645492589675 496081870737410468238884513)
      ·
        refine ⟨372061403053057851179163385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496081870737410468238884513 372061403053057851179163385)
        ·
          refine ⟨279046052289793388384372539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372061403053057851179163385 279046052289793388384372539)
          ·
            refine ⟨418569078434690082576558809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279046052289793388384372539 418569078434690082576558809)
            ·
              refine ⟨313926808826017561932419107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418569078434690082576558809 313926808826017561932419107)
              ·
                refine ⟨470890213239026342898628661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313926808826017561932419107 470890213239026342898628661)
                ·
                  refine ⟨44145957491158719646746437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 470890213239026342898628661 44145957491158719646746437)
                  ·
                    refine ⟨8277367029592259933764957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44145957491158719646746437 8277367029592259933764957)
                    ·
                      refine ⟨3104012636097097475161859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8277367029592259933764957 3104012636097097475161859)
                      ·
                        rfl

theorem cell23_6045043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 3].length) (baseStart_6045043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045043 prefixEnd_6045043 := by exact prefixLift 6045043
  have htrace : WordTrace (prefixWord ++ tailWord_6045043) baseStart_6045043 baseEnd_6045043 := by
    simpa [prefixWord, tailWord_6045043, baseEnd_6045043] using wordTrace_append hprefix tailTrace_6045043
  have hstable : (prefixWord ++ tailWord_6045043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045043).length < 2 ^ (prefixWord ++ tailWord_6045043).sum := by decide
  have hdescent : baseEnd_6045043 < baseStart_6045043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045053 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_6045053 : Nat := 118140960795 + 6045053 * 2 ^ 59
def prefixEnd_6045053 : Nat := 4983230072969 + 3 ^ 40 * 6045053 * 2
def baseEnd_6045053 : Nat := 3104017770903642436036813

theorem tailTrace_6045053 : CollatzResearch.WordTrace tailWord_6045053 prefixEnd_6045053 3104017770903642436036813 := by
  unfold tailWord_6045053
  simp only [CollatzResearch.WordTrace]
  refine ⟨220481196168812868702923813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146987464112541912468615875 220481196168812868702923813)
  ·
    refine ⟨41340224281652412881798215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220481196168812868702923813 41340224281652412881798215)
    ·
      refine ⟨62010336422478619322697323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41340224281652412881798215 62010336422478619322697323)
      ·
        refine ⟨93015504633717928984045985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62010336422478619322697323 93015504633717928984045985)
        ·
          refine ⟨69761628475288446738034489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93015504633717928984045985 69761628475288446738034489)
          ·
            refine ⟨52321221356466335053525867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69761628475288446738034489 52321221356466335053525867)
            ·
              refine ⟨78481832034699502580288801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52321221356466335053525867 78481832034699502580288801)
              ·
                refine ⟨58861374026024626935216601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78481832034699502580288801 58861374026024626935216601)
                ·
                  refine ⟨44146030519518470201412451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58861374026024626935216601 44146030519518470201412451)
                  ·
                    refine ⟨66219045779277705302118677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44146030519518470201412451 66219045779277705302118677)
                    ·
                      refine ⟨3104017770903642436036813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66219045779277705302118677 3104017770903642436036813)
                      ·
                        rfl

theorem cell23_6045053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_6045053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045053 prefixEnd_6045053 := by exact prefixLift 6045053
  have htrace : WordTrace (prefixWord ++ tailWord_6045053) baseStart_6045053 baseEnd_6045053 := by
    simpa [prefixWord, tailWord_6045053, baseEnd_6045053] using wordTrace_append hprefix tailTrace_6045053
  have hstable : (prefixWord ++ tailWord_6045053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045053).length < 2 ^ (prefixWord ++ tailWord_6045053).sum := by decide
  have hdescent : baseEnd_6045053 < baseStart_6045053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045060 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_6045060 : Nat := 118140960795 + 6045060 * 2 ^ 59
def prefixEnd_6045060 : Nat := 4983230072969 + 3 ^ 40 * 6045060 * 2
def baseEnd_6045060 : Nat := 3104021365268223908649281

theorem tailTrace_6045060 : CollatzResearch.WordTrace tailWord_6045060 prefixEnd_6045060 3104021365268223908649281 := by
  unfold tailWord_6045060
  simp only [CollatzResearch.WordTrace]
  refine ⟨110240725739893754449214317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146987634319858339265619089 110240725739893754449214317)
  ·
    refine ⟨41340272152460157918455369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110240725739893754449214317 41340272152460157918455369)
    ·
      refine ⟨31005204114345118438841527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41340272152460157918455369 31005204114345118438841527)
      ·
        refine ⟨46507806171517677658262291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31005204114345118438841527 46507806171517677658262291)
        ·
          refine ⟨69761709257276516487393437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46507806171517677658262291 69761709257276516487393437)
          ·
            refine ⟨26160640971478693682772539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69761709257276516487393437 26160640971478693682772539)
            ·
              refine ⟨39240961457218040524158809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26160640971478693682772539 39240961457218040524158809)
              ·
                refine ⟨29430721092913530393119107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39240961457218040524158809 29430721092913530393119107)
                ·
                  refine ⟨44146081639370295589678661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29430721092913530393119107 44146081639370295589678661)
                  ·
                    refine ⟨8277390307381930423064749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44146081639370295589678661 8277390307381930423064749)
                    ·
                      refine ⟨3104021365268223908649281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8277390307381930423064749 3104021365268223908649281)
                      ·
                        rfl

theorem cell23_6045060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_6045060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045060 prefixEnd_6045060 := by exact prefixLift 6045060
  have htrace : WordTrace (prefixWord ++ tailWord_6045060) baseStart_6045060 baseEnd_6045060 := by
    simpa [prefixWord, tailWord_6045060, baseEnd_6045060] using wordTrace_append hprefix tailTrace_6045060
  have hstable : (prefixWord ++ tailWord_6045060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045060).length < 2 ^ (prefixWord ++ tailWord_6045060).sum := by decide
  have hdescent : baseEnd_6045060 < baseStart_6045060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045117 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 4, 3, 2]
def baseStart_6045117 : Nat := 118140960795 + 6045117 * 2 ^ 59
def prefixEnd_6045117 : Nat := 4983230072969 + 3 ^ 40 * 6045117 * 2
def baseEnd_6045117 : Nat := 3104050633665530185636519

theorem tailTrace_6045117 : CollatzResearch.WordTrace tailWord_6045117 prefixEnd_6045117 3104050633665530185636519 := by
  unfold tailWord_6045117
  simp only [CollatzResearch.WordTrace]
  refine ⟨220483530440581007633253605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146989020293720671755502403 220483530440581007633253605)
  ·
    refine ⟨41340661957608938931235051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220483530440581007633253605 41340661957608938931235051)
    ·
      refine ⟨62010992936413408396852577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41340661957608938931235051 62010992936413408396852577)
      ·
        refine ⟨46508244702310056297639433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62010992936413408396852577 46508244702310056297639433)
        ·
          refine ⟨34881183526732542223229575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46508244702310056297639433 34881183526732542223229575)
          ·
            refine ⟨52321775290098813334844363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34881183526732542223229575 52321775290098813334844363)
            ·
              refine ⟨78482662935148220002266545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52321775290098813334844363 78482662935148220002266545)
              ·
                refine ⟨58861997201361165001699909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78482662935148220002266545 58861997201361165001699909)
                ·
                  refine ⟨11036624475255218437818733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58861997201361165001699909 11036624475255218437818733)
                  ·
                    refine ⟨4138734178220706914182025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11036624475255218437818733 4138734178220706914182025)
                    ·
                      refine ⟨3104050633665530185636519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4138734178220706914182025 3104050633665530185636519)
                      ·
                        rfl

theorem cell23_6045117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_6045117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045117 prefixEnd_6045117 := by exact prefixLift 6045117
  have htrace : WordTrace (prefixWord ++ tailWord_6045117) baseStart_6045117 baseEnd_6045117 := by
    simpa [prefixWord, tailWord_6045117, baseEnd_6045117] using wordTrace_append hprefix tailTrace_6045117
  have hstable : (prefixWord ++ tailWord_6045117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045117).length < 2 ^ (prefixWord ++ tailWord_6045117).sum := by decide
  have hdescent : baseEnd_6045117 < baseStart_6045117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045153 : List Nat := [1, 2, 3, 1, 2, 14]
def baseStart_6045153 : Nat := 118140960795 + 6045153 * 2 ^ 59
def prefixEnd_6045153 : Nat := 4983230072969 + 3 ^ 40 * 6045153 * 2
def baseEnd_6045153 : Nat := 12773946991642354093771

theorem tailTrace_6045153 : CollatzResearch.WordTrace tailWord_6045153 prefixEnd_6045153 12773946991642354093771 := by
  unfold tailWord_6045153
  simp only [CollatzResearch.WordTrace]
  refine ⟨220484843468450585781564113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146989895645633723854376075 220484843468450585781564113)
  ·
    refine ⟨165363632601337939336173085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220484843468450585781564113 165363632601337939336173085)
    ·
      refine ⟨62011362225501727251064907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165363632601337939336173085 62011362225501727251064907)
      ·
        refine ⟨93017043338252590876597361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62011362225501727251064907 93017043338252590876597361)
        ·
          refine ⟨69762782503689443157448021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93017043338252590876597361 69762782503689443157448021)
          ·
            refine ⟨12773946991642354093771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 69762782503689443157448021 12773946991642354093771)
            ·
              rfl

theorem cell23_6045153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 14].length) (baseStart_6045153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045153 prefixEnd_6045153 := by exact prefixLift 6045153
  have htrace : WordTrace (prefixWord ++ tailWord_6045153) baseStart_6045153 baseEnd_6045153 := by
    simpa [prefixWord, tailWord_6045153, baseEnd_6045153] using wordTrace_append hprefix tailTrace_6045153
  have hstable : (prefixWord ++ tailWord_6045153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045153).length < 2 ^ (prefixWord ++ tailWord_6045153).sum := by decide
  have hdescent : baseEnd_6045153 < baseStart_6045153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045160 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_6045160 : Nat := 118140960795 + 6045160 * 2 ^ 59
def prefixEnd_6045160 : Nat := 4983230072969 + 3 ^ 40 * 6045160 * 2
def baseEnd_6045160 : Nat := 3104072713333673517398821

theorem tailTrace_6045160 : CollatzResearch.WordTrace tailWord_6045160 prefixEnd_6045160 3104072713333673517398821 := by
  unfold tailWord_6045160
  simp only [CollatzResearch.WordTrace]
  refine ⟨110242549389712612988534467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146990065852950150651379289 110242549389712612988534467)
  ·
    refine ⟨165363824084568919482801701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110242549389712612988534467 165363824084568919482801701)
    ·
      refine ⟨31005717015856672403025319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165363824084568919482801701 31005717015856672403025319)
      ·
        refine ⟨46508575523785008604537979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31005717015856672403025319 46508575523785008604537979)
        ·
          refine ⟨69762863285677512906806969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46508575523785008604537979 69762863285677512906806969)
          ·
            refine ⟨52322147464258134680105227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69762863285677512906806969 52322147464258134680105227)
            ·
              refine ⟨78483221196387202020157841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52322147464258134680105227 78483221196387202020157841)
              ·
                refine ⟨58862415897290401515118381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78483221196387202020157841 58862415897290401515118381)
                ·
                  refine ⟨22073405961483900568169393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58862415897290401515118381 22073405961483900568169393)
                  ·
                    refine ⟨16555054471112925426127045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22073405961483900568169393 16555054471112925426127045)
                    ·
                      refine ⟨3104072713333673517398821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16555054471112925426127045 3104072713333673517398821)
                      ·
                        rfl

theorem cell23_6045160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_6045160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045160 prefixEnd_6045160 := by exact prefixLift 6045160
  have htrace : WordTrace (prefixWord ++ tailWord_6045160) baseStart_6045160 baseEnd_6045160 := by
    simpa [prefixWord, tailWord_6045160, baseEnd_6045160] using wordTrace_append hprefix tailTrace_6045160
  have hstable : (prefixWord ++ tailWord_6045160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045160).length < 2 ^ (prefixWord ++ tailWord_6045160).sum := by decide
  have hdescent : baseEnd_6045160 < baseStart_6045160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045163 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 7]
def baseStart_6045163 : Nat := 118140960795 + 6045163 * 2 ^ 59
def prefixEnd_6045163 : Nat := 4983230072969 + 3 ^ 40 * 6045163 * 2
def baseEnd_6045163 : Nat := 3104074253775637005661307

theorem tailTrace_6045163 : CollatzResearch.WordTrace tailWord_6045163 prefixEnd_6045163 3104074253775637005661307 := by
  unfold tailWord_6045163
  simp only [CollatzResearch.WordTrace]
  refine ⟨220485208198414357489428143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146990138798942904992952095 220485208198414357489428143)
  ·
    refine ⟨330727812297621536234142215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220485208198414357489428143 330727812297621536234142215)
    ·
      refine ⟨496091718446432304351213323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330727812297621536234142215 496091718446432304351213323)
      ·
        refine ⟨744137577669648456526819985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496091718446432304351213323 744137577669648456526819985)
        ·
          refine ⟨558103183252236342395114989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 744137577669648456526819985 558103183252236342395114989)
          ·
            refine ⟨209288693719588628398168121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 558103183252236342395114989 209288693719588628398168121)
            ·
              refine ⟨156966520289691471298626091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209288693719588628398168121 156966520289691471298626091)
              ·
                refine ⟨235449780434537206947939137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156966520289691471298626091 235449780434537206947939137)
                ·
                  refine ⟨176587335325902905210954353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235449780434537206947939137 176587335325902905210954353)
                  ·
                    refine ⟨132440501494427178908215765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 176587335325902905210954353 132440501494427178908215765)
                    ·
                      refine ⟨3104074253775637005661307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132440501494427178908215765 3104074253775637005661307)
                      ·
                        rfl

theorem cell23_6045163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 7].length) (baseStart_6045163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045163 prefixEnd_6045163 := by exact prefixLift 6045163
  have htrace : WordTrace (prefixWord ++ tailWord_6045163) baseStart_6045163 baseEnd_6045163 := by
    simpa [prefixWord, tailWord_6045163, baseEnd_6045163] using wordTrace_append hprefix tailTrace_6045163
  have hstable : (prefixWord ++ tailWord_6045163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045163).length < 2 ^ (prefixWord ++ tailWord_6045163).sum := by decide
  have hdescent : baseEnd_6045163 < baseStart_6045163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045174 : List Nat := [5, 1, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_6045174 : Nat := 118140960795 + 6045174 * 2 ^ 59
def prefixEnd_6045174 : Nat := 4983230072969 + 3 ^ 40 * 6045174 * 2
def baseEnd_6045174 : Nat := 1034693300687612154207919

theorem tailTrace_6045174 : CollatzResearch.WordTrace tailWord_6045174 prefixEnd_6045174 1034693300687612154207919 := by
  unfold tailWord_6045174
  simp only [CollatzResearch.WordTrace]
  refine ⟨13780350587585906648004911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146990406267583004245385717 13780350587585906648004911)
  ·
    refine ⟨20670525881378859972007367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13780350587585906648004911 20670525881378859972007367)
    ·
      refine ⟨31005788822068289958011051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20670525881378859972007367 31005788822068289958011051)
      ·
        refine ⟨46508683233102434937016577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31005788822068289958011051 46508683233102434937016577)
        ·
          refine ⟨34881512424826826202762433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46508683233102434937016577 34881512424826826202762433)
          ·
            refine ⟨26161134318620119652071825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34881512424826826202762433 26161134318620119652071825)
            ·
              refine ⟨19620850738965089739053869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26161134318620119652071825 19620850738965089739053869)
              ·
                refine ⟨7357819027111908652145201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19620850738965089739053869 7357819027111908652145201)
                ·
                  refine ⟨5518364270333931489108901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7357819027111908652145201 5518364270333931489108901)
                  ·
                    refine ⟨1034693300687612154207919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5518364270333931489108901 1034693300687612154207919)
                    ·
                      rfl

theorem cell23_6045174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_6045174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045174 prefixEnd_6045174 := by exact prefixLift 6045174
  have htrace : WordTrace (prefixWord ++ tailWord_6045174) baseStart_6045174 baseEnd_6045174 := by
    simpa [prefixWord, tailWord_6045174, baseEnd_6045174] using wordTrace_append hprefix tailTrace_6045174
  have hstable : (prefixWord ++ tailWord_6045174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045174).length < 2 ^ (prefixWord ++ tailWord_6045174).sum := by decide
  have hdescent : baseEnd_6045174 < baseStart_6045174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045198 : List Nat := [4, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4]
def baseStart_6045198 : Nat := 118140960795 + 6045198 * 2 ^ 59
def prefixEnd_6045198 : Nat := 4983230072969 + 3 ^ 40 * 6045198 * 2
def baseEnd_6045198 : Nat := 3104092225598544368723647

theorem tailTrace_6045198 : CollatzResearch.WordTrace tailWord_6045198 prefixEnd_6045198 3104092225598544368723647 := by
  unfold tailWord_6045198
  simp only [CollatzResearch.WordTrace]
  refine ⟨27560810594160944808369031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146990989835525038977968165 27560810594160944808369031)
  ·
    refine ⟨41341215891241417212553547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27560810594160944808369031 41341215891241417212553547)
    ·
      refine ⟨62011823836862125818830321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41341215891241417212553547 62011823836862125818830321)
      ·
        refine ⟨46508867877646594364122741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62011823836862125818830321 46508867877646594364122741)
        ·
          refine ⟨4360206363529368221636507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46508867877646594364122741 4360206363529368221636507)
          ·
            refine ⟨6540309545294052332454761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4360206363529368221636507 6540309545294052332454761)
            ·
              refine ⟨4905232158970539249341071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6540309545294052332454761 4905232158970539249341071)
              ·
                refine ⟨7357848238455808874011607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4905232158970539249341071 7357848238455808874011607)
                ·
                  refine ⟨11036772357683713311017411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7357848238455808874011607 11036772357683713311017411)
                  ·
                    refine ⟨16555158536525569966526117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11036772357683713311017411 16555158536525569966526117)
                    ·
                      refine ⟨3104092225598544368723647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16555158536525569966526117 3104092225598544368723647)
                      ·
                        rfl

theorem cell23_6045198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_6045198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045198 prefixEnd_6045198 := by exact prefixLift 6045198
  have htrace : WordTrace (prefixWord ++ tailWord_6045198) baseStart_6045198 baseEnd_6045198 := by
    simpa [prefixWord, tailWord_6045198, baseEnd_6045198] using wordTrace_append hprefix tailTrace_6045198
  have hstable : (prefixWord ++ tailWord_6045198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045198).length < 2 ^ (prefixWord ++ tailWord_6045198).sum := by decide
  have hdescent : baseEnd_6045198 < baseStart_6045198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045241 : List Nat := [1, 2, 1, 5, 1, 3, 2, 2, 1, 3, 2]
def baseStart_6045241 : Nat := 118140960795 + 6045241 * 2 ^ 59
def prefixEnd_6045241 : Nat := 4983230072969 + 3 ^ 40 * 6045241 * 2
def baseEnd_6045241 : Nat := 3104114305266687700485949

theorem tailTrace_6045241 : CollatzResearch.WordTrace tailWord_6045241 prefixEnd_6045241 3104114305266687700485949 := by
  unfold tailWord_6045241
  simp only [CollatzResearch.WordTrace]
  refine ⟨220488053092131776810767577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146992035394754517873845051 220488053092131776810767577)
  ·
    refine ⟨165366039819098832608075683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220488053092131776810767577 165366039819098832608075683)
    ·
      refine ⟨248049059728648248912113525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165366039819098832608075683 248049059728648248912113525)
      ·
        refine ⟨23254599349560773335510643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 248049059728648248912113525 23254599349560773335510643)
        ·
          refine ⟨34881899024341160003265965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23254599349560773335510643 34881899024341160003265965)
          ·
            refine ⟨13080712134127935001224737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34881899024341160003265965 13080712134127935001224737)
            ·
              refine ⟨9810534100595951250918553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13080712134127935001224737 9810534100595951250918553)
              ·
                refine ⟨7357900575446963438188915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9810534100595951250918553 7357900575446963438188915)
                ·
                  refine ⟨11036850863170445157283373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7357900575446963438188915 11036850863170445157283373)
                  ·
                    refine ⟨4138819073688916933981265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11036850863170445157283373 4138819073688916933981265)
                    ·
                      refine ⟨3104114305266687700485949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4138819073688916933981265 3104114305266687700485949)
                      ·
                        rfl

theorem cell23_6045241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_6045241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045241 prefixEnd_6045241 := by exact prefixLift 6045241
  have htrace : WordTrace (prefixWord ++ tailWord_6045241) baseStart_6045241 baseEnd_6045241 := by
    simpa [prefixWord, tailWord_6045241, baseEnd_6045241] using wordTrace_append hprefix tailTrace_6045241
  have hstable : (prefixWord ++ tailWord_6045241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045241).length < 2 ^ (prefixWord ++ tailWord_6045241).sum := by decide
  have hdescent : baseEnd_6045241 < baseStart_6045241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045287 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_6045287 : Nat := 118140960795 + 6045287 * 2 ^ 59
def prefixEnd_6045287 : Nat := 4983230072969 + 3 ^ 40 * 6045287 * 2
def baseEnd_6045287 : Nat := 3104137925376794520510737

theorem tailTrace_6045287 : CollatzResearch.WordTrace tailWord_6045287 prefixEnd_6045287 3104137925376794520510737 := by
  unfold tailWord_6045287
  simp only [CollatzResearch.WordTrace]
  refine ⟨220489730849965126666942115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146993153899976751111294743 220489730849965126666942115)
  ·
    refine ⟨330734596274947690000413173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220489730849965126666942115 330734596274947690000413173)
    ·
      refine ⟨31006368400776345937538735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 330734596274947690000413173 31006368400776345937538735)
      ·
        refine ⟨46509552601164518906308103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31006368400776345937538735 46509552601164518906308103)
        ·
          refine ⟨69764328901746778359462155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46509552601164518906308103 69764328901746778359462155)
          ·
            refine ⟨104646493352620167539193233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69764328901746778359462155 104646493352620167539193233)
            ·
              refine ⟨78484870014465125654394925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104646493352620167539193233 78484870014465125654394925)
              ·
                refine ⟨29431826255424422120398097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78484870014465125654394925 29431826255424422120398097)
                ·
                  refine ⟨22073869691568316590298573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29431826255424422120398097 22073869691568316590298573)
                  ·
                    refine ⟨8277701134338118721361965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22073869691568316590298573 8277701134338118721361965)
                    ·
                      refine ⟨3104137925376794520510737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8277701134338118721361965 3104137925376794520510737)
                      ·
                        rfl

theorem cell23_6045287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_6045287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045287 prefixEnd_6045287 := by exact prefixLift 6045287
  have htrace : WordTrace (prefixWord ++ tailWord_6045287) baseStart_6045287 baseEnd_6045287 := by
    simpa [prefixWord, tailWord_6045287, baseEnd_6045287] using wordTrace_append hprefix tailTrace_6045287
  have hstable : (prefixWord ++ tailWord_6045287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045287).length < 2 ^ (prefixWord ++ tailWord_6045287).sum := by decide
  have hdescent : baseEnd_6045287 < baseStart_6045287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045288 : List Nat := [2, 1, 4, 3, 1, 2, 1, 3, 2, 2, 2]
def baseStart_6045288 : Nat := 118140960795 + 6045288 * 2 ^ 59
def prefixEnd_6045288 : Nat := 4983230072969 + 3 ^ 40 * 6045288 * 2
def baseEnd_6045288 : Nat := 3104138438857449016598233

theorem tailTrace_6045288 : CollatzResearch.WordTrace tailWord_6045288 prefixEnd_6045288 3104138438857449016598233 := by
  unfold tailWord_6045288
  simp only [CollatzResearch.WordTrace]
  refine ⟨110244883661480751918864259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146993178215307669225152345 110244883661480751918864259)
  ·
    refine ⟨165367325492221127878296389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110244883661480751918864259 165367325492221127878296389)
    ·
      refine ⟨31006373529791461477180573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165367325492221127878296389 31006373529791461477180573)
      ·
        refine ⟨11627390073671798053942715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31006373529791461477180573 11627390073671798053942715)
        ·
          refine ⟨17441085110507697080914073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11627390073671798053942715 17441085110507697080914073)
          ·
            refine ⟨13080813832880772810685555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17441085110507697080914073 13080813832880772810685555)
            ·
              refine ⟨19621220749321159216028333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13080813832880772810685555 19621220749321159216028333)
              ·
                refine ⟨7357957780995434706010625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19621220749321159216028333 7357957780995434706010625)
                ·
                  refine ⟨5518468335746576029507969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7357957780995434706010625 5518468335746576029507969)
                  ·
                    refine ⟨4138851251809932022130977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5518468335746576029507969 4138851251809932022130977)
                    ·
                      refine ⟨3104138438857449016598233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4138851251809932022130977 3104138438857449016598233)
                      ·
                        rfl

theorem cell23_6045288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_6045288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045288 prefixEnd_6045288 := by exact prefixLift 6045288
  have htrace : WordTrace (prefixWord ++ tailWord_6045288) baseStart_6045288 baseEnd_6045288 := by
    simpa [prefixWord, tailWord_6045288, baseEnd_6045288] using wordTrace_append hprefix tailTrace_6045288
  have hstable : (prefixWord ++ tailWord_6045288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045288).length < 2 ^ (prefixWord ++ tailWord_6045288).sum := by decide
  have hdescent : baseEnd_6045288 < baseStart_6045288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045307 : List Nat := [1, 1, 1, 1, 1, 4, 6, 1, 2, 5]
def baseStart_6045307 : Nat := 118140960795 + 6045307 * 2 ^ 59
def prefixEnd_6045307 : Nat := 4983230072969 + 3 ^ 40 * 6045307 * 2
def baseEnd_6045307 : Nat := 1034716064996628147420215

theorem tailTrace_6045307 : CollatzResearch.WordTrace tailWord_6045307 prefixEnd_6045307 1034716064996628147420215 := by
  unfold tailWord_6045307
  simp only [CollatzResearch.WordTrace]
  refine ⟨220490460309892670082670175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146993640206595113388446783 220490460309892670082670175)
  ·
    refine ⟨330735690464839005124005263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220490460309892670082670175 330735690464839005124005263)
    ·
      refine ⟨496103535697258507686007895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330735690464839005124005263 496103535697258507686007895)
      ·
        refine ⟨744155303545887761529011843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496103535697258507686007895 744155303545887761529011843)
        ·
          refine ⟨1116232955318831642293517765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744155303545887761529011843 1116232955318831642293517765)
          ·
            refine ⟨209293679122280932930034581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1116232955318831642293517765 209293679122280932930034581)
            ·
              refine ⟨9810641208856918731095371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 209293679122280932930034581 9810641208856918731095371)
              ·
                refine ⟨14715961813285378096643057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9810641208856918731095371 14715961813285378096643057)
                ·
                  refine ⟨11036971359964033572482293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14715961813285378096643057 11036971359964033572482293)
                  ·
                    refine ⟨1034716064996628147420215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11036971359964033572482293 1034716064996628147420215)
                    ·
                      rfl

theorem cell23_6045307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 5].length) (baseStart_6045307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045307 prefixEnd_6045307 := by exact prefixLift 6045307
  have htrace : WordTrace (prefixWord ++ tailWord_6045307) baseStart_6045307 baseEnd_6045307 := by
    simpa [prefixWord, tailWord_6045307, baseEnd_6045307] using wordTrace_append hprefix tailTrace_6045307
  have hstable : (prefixWord ++ tailWord_6045307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045307).length < 2 ^ (prefixWord ++ tailWord_6045307).sum := by decide
  have hdescent : baseEnd_6045307 < baseStart_6045307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045344 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 1, 6, 2]
def baseStart_6045344 : Nat := 118140960795 + 6045344 * 2 ^ 59
def prefixEnd_6045344 : Nat := 4983230072969 + 3 ^ 40 * 6045344 * 2
def baseEnd_6045344 : Nat := 3104167193774100797497975

theorem tailTrace_6045344 : CollatzResearch.WordTrace tailWord_6045344 prefixEnd_6045344 3104167193774100797497975 := by
  unfold tailWord_6045344
  simp only [CollatzResearch.WordTrace]
  refine ⟨110245904905379312700883543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146994539873839083601178057 110245904905379312700883543)
  ·
    refine ⟨165368857358068969051325315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110245904905379312700883543 165368857358068969051325315)
    ·
      refine ⟨248053286037103453576987973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165368857358068969051325315 248053286037103453576987973)
      ·
        refine ⟨46509991131956897545685245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248053286037103453576987973 46509991131956897545685245)
        ·
          refine ⟨17441246674483836579631967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46509991131956897545685245 17441246674483836579631967)
          ·
            refine ⟨26161870011725754869447951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17441246674483836579631967 26161870011725754869447951)
            ·
              refine ⟨39242805017588632304171927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26161870011725754869447951 39242805017588632304171927)
              ·
                refine ⟨58864207526382948456257891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39242805017588632304171927 58864207526382948456257891)
                ·
                  refine ⟨88296311289574422684386837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58864207526382948456257891 88296311289574422684386837)
                  ·
                    refine ⟨4138889591698801063330633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88296311289574422684386837 4138889591698801063330633)
                    ·
                      refine ⟨3104167193774100797497975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4138889591698801063330633 3104167193774100797497975)
                      ·
                        rfl

theorem cell23_6045344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_6045344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045344 prefixEnd_6045344 := by exact prefixLift 6045344
  have htrace : WordTrace (prefixWord ++ tailWord_6045344) baseStart_6045344 baseEnd_6045344 := by
    simpa [prefixWord, tailWord_6045344, baseEnd_6045344] using wordTrace_append hprefix tailTrace_6045344
  have hstable : (prefixWord ++ tailWord_6045344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045344).length < 2 ^ (prefixWord ++ tailWord_6045344).sum := by decide
  have hdescent : baseEnd_6045344 < baseStart_6045344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045347 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 3]
def baseStart_6045347 : Nat := 118140960795 + 6045347 * 2 ^ 59
def prefixEnd_6045347 : Nat := 4983230072969 + 3 ^ 40 * 6045347 * 2
def baseEnd_6045347 : Nat := 3104168734216064285760461

theorem tailTrace_6045347 : CollatzResearch.WordTrace tailWord_6045347 prefixEnd_6045347 3104168734216064285760461 := by
  unfold tailWord_6045347
  simp only [CollatzResearch.WordTrace]
  refine ⟨220491919229747756914126295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146994612819831837942750863 220491919229747756914126295)
  ·
    refine ⟨330737878844621635371189443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220491919229747756914126295 330737878844621635371189443)
    ·
      refine ⟨496106818266932453056784165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330737878844621635371189443 496106818266932453056784165)
      ·
        refine ⟨93020028425049834948147031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 496106818266932453056784165 93020028425049834948147031)
        ·
          refine ⟨139530042637574752422220547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93020028425049834948147031 139530042637574752422220547)
          ·
            refine ⟨209295063956362128633330821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139530042637574752422220547 209295063956362128633330821)
            ·
              refine ⟨39242824491817899118749529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209295063956362128633330821 39242824491817899118749529)
              ·
                refine ⟨29432118368863424339062147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39242824491817899118749529 29432118368863424339062147)
                ·
                  refine ⟨44148177553295136508593221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29432118368863424339062147 44148177553295136508593221)
                  ·
                    refine ⟨8277783291242838095361229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44148177553295136508593221 8277783291242838095361229)
                    ·
                      refine ⟨3104168734216064285760461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8277783291242838095361229 3104168734216064285760461)
                      ·
                        rfl

theorem cell23_6045347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_6045347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045347 prefixEnd_6045347 := by exact prefixLift 6045347
  have htrace : WordTrace (prefixWord ++ tailWord_6045347) baseStart_6045347 baseEnd_6045347 := by
    simpa [prefixWord, tailWord_6045347, baseEnd_6045347] using wordTrace_append hprefix tailTrace_6045347
  have hstable : (prefixWord ++ tailWord_6045347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045347).length < 2 ^ (prefixWord ++ tailWord_6045347).sum := by decide
  have hdescent : baseEnd_6045347 < baseStart_6045347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045358 : List Nat := [4, 1, 4, 1, 2, 2, 1, 1, 2, 5]
def baseStart_6045358 : Nat := 118140960795 + 6045358 * 2 ^ 59
def prefixEnd_6045358 : Nat := 4983230072969 + 3 ^ 40 * 6045358 * 2
def baseEnd_6045358 : Nat := 1034724794167754580907637

theorem tailTrace_6045358 : CollatzResearch.WordTrace tailWord_6045358 prefixEnd_6045358 1034724794167754580907637 := by
  unfold tailWord_6045358
  simp only [CollatzResearch.WordTrace]
  refine ⟨27561540054088488224097091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146994880288471937195184485 27561540054088488224097091)
  ·
    refine ⟨41342310081132732336145637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27561540054088488224097091 41342310081132732336145637)
    ·
      refine ⟨7751683140212387313027307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41342310081132732336145637 7751683140212387313027307)
      ·
        refine ⟨11627524710318580969540961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7751683140212387313027307 11627524710318580969540961)
        ·
          refine ⟨8720643532738935727155721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11627524710318580969540961 8720643532738935727155721)
          ·
            refine ⟨6540482649554201795366791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8720643532738935727155721 6540482649554201795366791)
            ·
              refine ⟨9810723974331302693050187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6540482649554201795366791 9810723974331302693050187)
              ·
                refine ⟨14716085961496954039575281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9810723974331302693050187 14716085961496954039575281)
                ·
                  refine ⟨11037064471122715529681461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14716085961496954039575281 11037064471122715529681461)
                  ·
                    refine ⟨1034724794167754580907637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11037064471122715529681461 1034724794167754580907637)
                    ·
                      rfl

theorem cell23_6045358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_6045358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045358 prefixEnd_6045358 := by exact prefixLift 6045358
  have htrace : WordTrace (prefixWord ++ tailWord_6045358) baseStart_6045358 baseEnd_6045358 := by
    simpa [prefixWord, tailWord_6045358, baseEnd_6045358] using wordTrace_append hprefix tailTrace_6045358
  have hstable : (prefixWord ++ tailWord_6045358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045358).length < 2 ^ (prefixWord ++ tailWord_6045358).sum := by decide
  have hdescent : baseEnd_6045358 < baseStart_6045358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045421 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 1, 5, 2]
def baseStart_6045421 : Nat := 118140960795 + 6045421 * 2 ^ 59
def prefixEnd_6045421 : Nat := 4983230072969 + 3 ^ 40 * 6045421 * 2
def baseEnd_6045421 : Nat := 3104206731784496996235121

theorem tailTrace_6045421 : CollatzResearch.WordTrace tailWord_6045421 prefixEnd_6045421 3104206731784496996235121 := by
  unfold tailWord_6045421
  simp only [CollatzResearch.WordTrace]
  refine ⟨220494618231479667552320117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146996412154319778368213411 220494618231479667552320117)
  ·
    refine ⟨20671370459201218833030011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220494618231479667552320117 20671370459201218833030011)
    ·
      refine ⟨31007055688801828249545017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20671370459201218833030011 31007055688801828249545017)
      ·
        refine ⟨23255291766601371187158763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31007055688801828249545017 23255291766601371187158763)
        ·
          refine ⟨34882937649902056780738145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23255291766601371187158763 34882937649902056780738145)
          ·
            refine ⟨26162203237426542585553609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34882937649902056780738145 26162203237426542585553609)
            ·
              refine ⟨19621652428069906939165207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26162203237426542585553609 19621652428069906939165207)
              ·
                refine ⟨29432478642104860408747811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19621652428069906939165207 29432478642104860408747811)
                ·
                  refine ⟨44148717963157290613121717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29432478642104860408747811 44148717963157290613121717)
                  ·
                    refine ⟨4138942309045995994980161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44148717963157290613121717 4138942309045995994980161)
                    ·
                      refine ⟨3104206731784496996235121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4138942309045995994980161 3104206731784496996235121)
                      ·
                        rfl

theorem cell23_6045421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_6045421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045421 prefixEnd_6045421 := by exact prefixLift 6045421
  have htrace : WordTrace (prefixWord ++ tailWord_6045421) baseStart_6045421 baseEnd_6045421 := by
    simpa [prefixWord, tailWord_6045421, baseEnd_6045421] using wordTrace_append hprefix tailTrace_6045421
  have hstable : (prefixWord ++ tailWord_6045421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045421).length < 2 ^ (prefixWord ++ tailWord_6045421).sum := by decide
  have hdescent : baseEnd_6045421 < baseStart_6045421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045427 : List Nat := [1, 1, 1, 2, 2, 3, 2, 4, 1, 6]
def baseStart_6045427 : Nat := 118140960795 + 6045427 * 2 ^ 59
def prefixEnd_6045427 : Nat := 4983230072969 + 3 ^ 40 * 6045427 * 2
def baseEnd_6045427 : Nat := 1034736604222807990920031

theorem tailTrace_6045427 : CollatzResearch.WordTrace tailWord_6045427 prefixEnd_6045427 1034736604222807990920031 := by
  unfold tailWord_6045427
  simp only [CollatzResearch.WordTrace]
  refine ⟨220494837069457930577038535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146996558046305287051359023 220494837069457930577038535)
  ·
    refine ⟨330742255604186895865557803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220494837069457930577038535 330742255604186895865557803)
    ·
      refine ⟨496113383406280343798336705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330742255604186895865557803 496113383406280343798336705)
      ·
        refine ⟨372085037554710257848752529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496113383406280343798336705 372085037554710257848752529)
        ·
          refine ⟨279063778166032693386564397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372085037554710257848752529 279063778166032693386564397)
          ·
            refine ⟨104648916812262260019961649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279063778166032693386564397 104648916812262260019961649)
            ·
              refine ⟨78486687609196695014971237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104648916812262260019961649 78486687609196695014971237)
              ·
                refine ⟨14716253926724380315307107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78486687609196695014971237 14716253926724380315307107)
                ·
                  refine ⟨22074380890086570472960661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14716253926724380315307107 22074380890086570472960661)
                  ·
                    refine ⟨1034736604222807990920031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22074380890086570472960661 1034736604222807990920031)
                    ·
                      rfl

theorem cell23_6045427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 6].length) (baseStart_6045427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045427 prefixEnd_6045427 := by exact prefixLift 6045427
  have htrace : WordTrace (prefixWord ++ tailWord_6045427) baseStart_6045427 baseEnd_6045427 := by
    simpa [prefixWord, tailWord_6045427, baseEnd_6045427] using wordTrace_append hprefix tailTrace_6045427
  have hstable : (prefixWord ++ tailWord_6045427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045427).length < 2 ^ (prefixWord ++ tailWord_6045427).sum := by decide
  have hdescent : baseEnd_6045427 < baseStart_6045427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045454 : List Nat := [4, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_6045454 : Nat := 118140960795 + 6045454 * 2 ^ 59
def prefixEnd_6045454 : Nat := 4983230072969 + 3 ^ 40 * 6045454 * 2
def baseEnd_6045454 : Nat := 3104223676646095367122469

theorem tailTrace_6045454 : CollatzResearch.WordTrace tailWord_6045454 prefixEnd_6045454 3104223676646095367122469 := by
  unfold tailWord_6045454
  simp only [CollatzResearch.WordTrace]
  refine ⟨27561977730045014273533927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146997214560240076125514277 27561977730045014273533927)
  ·
    refine ⟨41342966595067521410300891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27561977730045014273533927 41342966595067521410300891)
    ·
      refine ⟨62014449892601282115451337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41342966595067521410300891 62014449892601282115451337)
      ·
        refine ⟨46510837419450961586588503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62014449892601282115451337 46510837419450961586588503)
        ·
          refine ⟨69766256129176442379882755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46510837419450961586588503 69766256129176442379882755)
          ·
            refine ⟨104649384193764663569824133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69766256129176442379882755 104649384193764663569824133)
            ·
              refine ⟨19621759536330874419342025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104649384193764663569824133 19621759536330874419342025)
              ·
                refine ⟨14716319652248155814506519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19621759536330874419342025 14716319652248155814506519)
                ·
                  refine ⟨22074479478372233721759779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14716319652248155814506519 22074479478372233721759779)
                  ·
                    refine ⟨33111719217558350582639669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22074479478372233721759779 33111719217558350582639669)
                    ·
                      refine ⟨3104223676646095367122469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33111719217558350582639669 3104223676646095367122469)
                      ·
                        rfl

theorem cell23_6045454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_6045454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045454 prefixEnd_6045454 := by exact prefixLift 6045454
  have htrace : WordTrace (prefixWord ++ tailWord_6045454) baseStart_6045454 baseEnd_6045454 := by
    simpa [prefixWord, tailWord_6045454, baseEnd_6045454] using wordTrace_append hprefix tailTrace_6045454
  have hstable : (prefixWord ++ tailWord_6045454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045454).length < 2 ^ (prefixWord ++ tailWord_6045454).sum := by decide
  have hdescent : baseEnd_6045454 < baseStart_6045454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045461 : List Nat := [1, 3, 2, 1, 2, 4, 1, 3, 2, 4]
def baseStart_6045461 : Nat := 118140960795 + 6045461 * 2 ^ 59
def prefixEnd_6045461 : Nat := 4983230072969 + 3 ^ 40 * 6045461 * 2
def baseEnd_6045461 : Nat := 1034742423670225613244979

theorem tailTrace_6045461 : CollatzResearch.WordTrace tailWord_6045461 prefixEnd_6045461 1034742423670225613244979 := by
  unfold tailWord_6045461
  simp only [CollatzResearch.WordTrace]
  refine ⟨220496077151334754383776237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146997384767556502922517491 220496077151334754383776237)
  ·
    refine ⟨82686028931750532893916089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220496077151334754383776237 82686028931750532893916089)
    ·
      refine ⟨62014521698812899670437067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82686028931750532893916089 62014521698812899670437067)
      ·
        refine ⟨93021782548219349505655601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62014521698812899670437067 93021782548219349505655601)
        ·
          refine ⟨69766336911164512129241701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93021782548219349505655601 69766336911164512129241701)
          ·
            refine ⟨13081188170843346024232819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69766336911164512129241701 13081188170843346024232819)
            ·
              refine ⟨19621782256265019036349229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13081188170843346024232819 19621782256265019036349229)
              ·
                refine ⟨7358168346099382138630961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19621782256265019036349229 7358168346099382138630961)
                ·
                  refine ⟨5518626259574536603973221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7358168346099382138630961 5518626259574536603973221)
                  ·
                    refine ⟨1034742423670225613244979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5518626259574536603973221 1034742423670225613244979)
                    ·
                      rfl

theorem cell23_6045461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_6045461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045461 prefixEnd_6045461 := by exact prefixLift 6045461
  have htrace : WordTrace (prefixWord ++ tailWord_6045461) baseStart_6045461 baseEnd_6045461 := by
    simpa [prefixWord, tailWord_6045461, baseEnd_6045461] using wordTrace_append hprefix tailTrace_6045461
  have hstable : (prefixWord ++ tailWord_6045461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045461).length < 2 ^ (prefixWord ++ tailWord_6045461).sum := by decide
  have hdescent : baseEnd_6045461 < baseStart_6045461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045484 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 3]
def baseStart_6045484 : Nat := 118140960795 + 6045484 * 2 ^ 59
def prefixEnd_6045484 : Nat := 4983230072969 + 3 ^ 40 * 6045484 * 2
def baseEnd_6045484 : Nat := 3104239081065730249747331

theorem tailTrace_6045484 : CollatzResearch.WordTrace tailWord_6045484 prefixEnd_6045484 3104239081065730249747331 := by
  unfold tailWord_6045484
  simp only [CollatzResearch.WordTrace]
  refine ⟨110248458015125714655931753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146997944020167619541242337 110248458015125714655931753)
  ·
    refine ⟨82686343511344285991948815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110248458015125714655931753 82686343511344285991948815)
    ·
      refine ⟨124029515267016428987923223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82686343511344285991948815 124029515267016428987923223)
      ·
        refine ⟨186044272900524643481884835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124029515267016428987923223 186044272900524643481884835)
        ·
          refine ⟨279066409350786965222827253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186044272900524643481884835 279066409350786965222827253)
          ·
            refine ⟨26162475876636277989640055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 279066409350786965222827253 26162475876636277989640055)
            ·
              refine ⟨39243713814954416984460083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26162475876636277989640055 39243713814954416984460083)
              ·
                refine ⟨58865570722431625476690125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39243713814954416984460083 58865570722431625476690125)
                ·
                  refine ⟨22074589020911859553758797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58865570722431625476690125 22074589020911859553758797)
                  ·
                    refine ⟨8277970882841947332659549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22074589020911859553758797 8277970882841947332659549)
                    ·
                      refine ⟨3104239081065730249747331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8277970882841947332659549 3104239081065730249747331)
                      ·
                        rfl

theorem cell23_6045484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_6045484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045484 prefixEnd_6045484 := by exact prefixLift 6045484
  have htrace : WordTrace (prefixWord ++ tailWord_6045484) baseStart_6045484 baseEnd_6045484 := by
    simpa [prefixWord, tailWord_6045484, baseEnd_6045484] using wordTrace_append hprefix tailTrace_6045484
  have hstable : (prefixWord ++ tailWord_6045484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045484).length < 2 ^ (prefixWord ++ tailWord_6045484).sum := by decide
  have hdescent : baseEnd_6045484 < baseStart_6045484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045502 : List Nat := [4, 2, 1, 2, 2, 2, 1, 4, 1, 2, 2]
def baseStart_6045502 : Nat := 118140960795 + 6045502 * 2 ^ 59
def prefixEnd_6045502 : Nat := 4983230072969 + 3 ^ 40 * 6045502 * 2
def baseEnd_6045502 : Nat := 3104248323717511179322249

theorem tailTrace_6045502 : CollatzResearch.WordTrace tailWord_6045502 prefixEnd_6045502 3104248323717511179322249 := by
  unfold tailWord_6045502
  simp only [CollatzResearch.WordTrace]
  refine ⟨27562196568023277298252345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146998381696124145590679173 27562196568023277298252345)
  ·
    refine ⟨20671647426017457973689259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27562196568023277298252345 20671647426017457973689259)
    ·
      refine ⟨31007471139026186960533889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20671647426017457973689259 31007471139026186960533889)
      ·
        refine ⟨23255603354269640220400417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31007471139026186960533889 23255603354269640220400417)
        ·
          refine ⟨17441702515702230165300313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23255603354269640220400417 17441702515702230165300313)
          ·
            refine ⟨13081276886776672623975235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17441702515702230165300313 13081276886776672623975235)
            ·
              refine ⟨19621915330165008935962853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13081276886776672623975235 19621915330165008935962853)
              ·
                refine ⟨3679109124405939175493035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19621915330165008935962853 3679109124405939175493035)
                ·
                  refine ⟨5518663686608908763239553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3679109124405939175493035 5518663686608908763239553)
                  ·
                    refine ⟨4138997764956681572429665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5518663686608908763239553 4138997764956681572429665)
                    ·
                      refine ⟨3104248323717511179322249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4138997764956681572429665 3104248323717511179322249)
                      ·
                        rfl

theorem cell23_6045502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_6045502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045502 prefixEnd_6045502 := by exact prefixLift 6045502
  have htrace : WordTrace (prefixWord ++ tailWord_6045502) baseStart_6045502 baseEnd_6045502 := by
    simpa [prefixWord, tailWord_6045502, baseEnd_6045502] using wordTrace_append hprefix tailTrace_6045502
  have hstable : (prefixWord ++ tailWord_6045502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045502).length < 2 ^ (prefixWord ++ tailWord_6045502).sum := by decide
  have hdescent : baseEnd_6045502 < baseStart_6045502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045511 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 3, 3, 2]
def baseStart_6045511 : Nat := 118140960795 + 6045511 * 2 ^ 59
def prefixEnd_6045511 : Nat := 4983230072969 + 3 ^ 40 * 6045511 * 2
def baseEnd_6045511 : Nat := 3104252945043401644109707

theorem tailTrace_6045511 : CollatzResearch.WordTrace tailWord_6045511 prefixEnd_6045511 3104252945043401644109707 := by
  unfold tailWord_6045511
  simp only [CollatzResearch.WordTrace]
  refine ⟨220497900801153612923096387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146998600534102408615397591 220497900801153612923096387)
  ·
    refine ⟨330746851201730419384644581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220497900801153612923096387 330746851201730419384644581)
    ·
      refine ⟨62015034600324453634620859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 330746851201730419384644581 62015034600324453634620859)
      ·
        refine ⟨93022551900486680451931289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62015034600324453634620859 93022551900486680451931289)
        ·
          refine ⟨69766913925365010338948467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93022551900486680451931289 69766913925365010338948467)
          ·
            refine ⟨104650370888047515508422701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69766913925365010338948467 104650370888047515508422701)
            ·
              refine ⟨39243889083017818315658513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104650370888047515508422701 39243889083017818315658513)
              ·
                refine ⟨29432916812263363736743885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39243889083017818315658513 29432916812263363736743885)
                ·
                  refine ⟨11037343804598761401278957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29432916812263363736743885 11037343804598761401278957)
                  ·
                    refine ⟨4139003926724535525479609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11037343804598761401278957 4139003926724535525479609)
                    ·
                      refine ⟨3104252945043401644109707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4139003926724535525479609 3104252945043401644109707)
                      ·
                        rfl

theorem cell23_6045511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_6045511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045511 prefixEnd_6045511 := by exact prefixLift 6045511
  have htrace : WordTrace (prefixWord ++ tailWord_6045511) baseStart_6045511 baseEnd_6045511 := by
    simpa [prefixWord, tailWord_6045511, baseEnd_6045511] using wordTrace_append hprefix tailTrace_6045511
  have hstable : (prefixWord ++ tailWord_6045511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045511).length < 2 ^ (prefixWord ++ tailWord_6045511).sum := by decide
  have hdescent : baseEnd_6045511 < baseStart_6045511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045544 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_6045544 : Nat := 118140960795 + 6045544 * 2 ^ 59
def prefixEnd_6045544 : Nat := 4983230072969 + 3 ^ 40 * 6045544 * 2
def baseEnd_6045544 : Nat := 3104269889905000014997055

theorem tailTrace_6045544 : CollatzResearch.WordTrace tailWord_6045544 prefixEnd_6045544 3104269889905000014997055 := by
  unfold tailWord_6045544
  simp only [CollatzResearch.WordTrace]
  refine ⟨110249552205017029779523843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146999402940022706372698457 110249552205017029779523843)
  ·
    refine ⟨165374328307525544669285765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110249552205017029779523843 165374328307525544669285765)
    ·
      refine ⟨31007686557661039625491081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165374328307525544669285765 31007686557661039625491081)
      ·
        refine ⟨23255764918245779719118311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31007686557661039625491081 23255764918245779719118311)
        ·
          refine ⟨34883647377368669578677467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23255764918245779719118311 34883647377368669578677467)
          ·
            refine ⟨52325471066053004368016201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34883647377368669578677467 52325471066053004368016201)
            ·
              refine ⟨39244103299539753276012151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52325471066053004368016201 39244103299539753276012151)
              ·
                refine ⟨58866154949309629914018227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39244103299539753276012151 58866154949309629914018227)
                ·
                  refine ⟨88299232423964444871027341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58866154949309629914018227 88299232423964444871027341)
                  ·
                    refine ⟨33112212158986666826635253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88299232423964444871027341 33112212158986666826635253)
                    ·
                      refine ⟨3104269889905000014997055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33112212158986666826635253 3104269889905000014997055)
                      ·
                        rfl

theorem cell23_6045544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_6045544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045544 prefixEnd_6045544 := by exact prefixLift 6045544
  have htrace : WordTrace (prefixWord ++ tailWord_6045544) baseStart_6045544 baseEnd_6045544 := by
    simpa [prefixWord, tailWord_6045544, baseEnd_6045544] using wordTrace_append hprefix tailTrace_6045544
  have hstable : (prefixWord ++ tailWord_6045544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045544).length < 2 ^ (prefixWord ++ tailWord_6045544).sum := by decide
  have hdescent : baseEnd_6045544 < baseStart_6045544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045547 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 11]
def baseStart_6045547 : Nat := 118140960795 + 6045547 * 2 ^ 59
def prefixEnd_6045547 : Nat := 4983230072969 + 3 ^ 40 * 6045547 * 2
def baseEnd_6045547 : Nat := 344919047816329278139949

theorem tailTrace_6045547 : CollatzResearch.WordTrace tailWord_6045547 prefixEnd_6045547 344919047816329278139949 := by
  unfold tailWord_6045547
  simp only [CollatzResearch.WordTrace]
  refine ⟨220499213829023191071406895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146999475886015460714271263 220499213829023191071406895)
  ·
    refine ⟨330748820743534786607110343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220499213829023191071406895 330748820743534786607110343)
    ·
      refine ⟨496123231115302179910665515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330748820743534786607110343 496123231115302179910665515)
      ·
        refine ⟨744184846672953269865998273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496123231115302179910665515 744184846672953269865998273)
        ·
          refine ⟨558138635004714952399498705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 744184846672953269865998273 558138635004714952399498705)
          ·
            refine ⟨418603976253536214299624029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 558138635004714952399498705 418603976253536214299624029)
            ·
              refine ⟨156976491095076080362359011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 418603976253536214299624029 156976491095076080362359011)
              ·
                refine ⟨235464736642614120543538517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156976491095076080362359011 235464736642614120543538517)
                ·
                  refine ⟨344919047816329278139949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 235464736642614120543538517 344919047816329278139949)
                  ·
                    rfl

theorem cell23_6045547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 11].length) (baseStart_6045547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045547 prefixEnd_6045547 := by exact prefixLift 6045547
  have htrace : WordTrace (prefixWord ++ tailWord_6045547) baseStart_6045547 baseEnd_6045547 := by
    simpa [prefixWord, tailWord_6045547, baseEnd_6045547] using wordTrace_append hprefix tailTrace_6045547
  have hstable : (prefixWord ++ tailWord_6045547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045547).length < 2 ^ (prefixWord ++ tailWord_6045547).sum := by decide
  have hdescent : baseEnd_6045547 < baseStart_6045547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045575 : List Nat := [1, 1, 4, 2, 4, 2, 1, 1, 1, 4, 2]
def baseStart_6045575 : Nat := 118140960795 + 6045575 * 2 ^ 59
def prefixEnd_6045575 : Nat := 4983230072969 + 3 ^ 40 * 6045575 * 2
def baseEnd_6045575 : Nat := 3104285807805289393709413

theorem tailTrace_6045575 : CollatzResearch.WordTrace tailWord_6045575 prefixEnd_6045575 3104285807805289393709413 := by
  unfold tailWord_6045575
  simp only [CollatzResearch.WordTrace]
  refine ⟨220500235072921751853426179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147000156715281167902284119 220500235072921751853426179)
  ·
    refine ⟨330750352609382627780139269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220500235072921751853426179 330750352609382627780139269)
    ·
      refine ⟨62015691114259242708776113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 330750352609382627780139269 62015691114259242708776113)
      ·
        refine ⟨46511768335694432031582085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62015691114259242708776113 46511768335694432031582085)
        ·
          refine ⟨8720956562942706005921641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46511768335694432031582085 8720956562942706005921641)
          ·
            refine ⟨6540717422207029504441231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8720956562942706005921641 6540717422207029504441231)
            ·
              refine ⟨9811076133310544256661847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6540717422207029504441231 9811076133310544256661847)
              ·
                refine ⟨14716614199965816384992771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9811076133310544256661847 14716614199965816384992771)
                ·
                  refine ⟨22074921299948724577489157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14716614199965816384992771 22074921299948724577489157)
                  ·
                    refine ⟨4139047743740385858279217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22074921299948724577489157 4139047743740385858279217)
                    ·
                      refine ⟨3104285807805289393709413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4139047743740385858279217 3104285807805289393709413)
                      ·
                        rfl

theorem cell23_6045575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_6045575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045575 prefixEnd_6045575 := by exact prefixLift 6045575
  have htrace : WordTrace (prefixWord ++ tailWord_6045575) baseStart_6045575 baseEnd_6045575 := by
    simpa [prefixWord, tailWord_6045575, baseEnd_6045575] using wordTrace_append hprefix tailTrace_6045575
  have hstable : (prefixWord ++ tailWord_6045575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045575).length < 2 ^ (prefixWord ++ tailWord_6045575).sum := by decide
  have hdescent : baseEnd_6045575 < baseStart_6045575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045621 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_6045621 : Nat := 118140960795 + 6045621 * 2 ^ 59
def prefixEnd_6045621 : Nat := 4983230072969 + 3 ^ 40 * 6045621 * 2
def baseEnd_6045621 : Nat := 3104309427915396213734201

theorem tailTrace_6045621 : CollatzResearch.WordTrace tailWord_6045621 prefixEnd_6045621 3104309427915396213734201 := by
  unfold tailWord_6045621
  simp only [CollatzResearch.WordTrace]
  refine ⟨220501912830755101709600717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147001275220503401139733811 220501912830755101709600717)
  ·
    refine ⟨82688217311533163141100269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220501912830755101709600717 82688217311533163141100269)
    ·
      refine ⟨31008081491824936177912601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82688217311533163141100269 31008081491824936177912601)
      ·
        refine ⟨23256061118868702133434451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31008081491824936177912601 23256061118868702133434451)
        ·
          refine ⟨34884091678303053200151677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23256061118868702133434451 34884091678303053200151677)
          ·
            refine ⟨13081534379363644950056879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34884091678303053200151677 13081534379363644950056879)
            ·
              refine ⟨19622301569045467425085319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13081534379363644950056879 19622301569045467425085319)
              ·
                refine ⟨29433452353568201137627979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19622301569045467425085319 29433452353568201137627979)
                ·
                  refine ⟨44150178530352301706441969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29433452353568201137627979 44150178530352301706441969)
                  ·
                    refine ⟨33112633897764226279831477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44150178530352301706441969 33112633897764226279831477)
                    ·
                      refine ⟨3104309427915396213734201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33112633897764226279831477 3104309427915396213734201)
                      ·
                        rfl

theorem cell23_6045621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_6045621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045621 prefixEnd_6045621 := by exact prefixLift 6045621
  have htrace : WordTrace (prefixWord ++ tailWord_6045621) baseStart_6045621 baseEnd_6045621 := by
    simpa [prefixWord, tailWord_6045621, baseEnd_6045621] using wordTrace_append hprefix tailTrace_6045621
  have hstable : (prefixWord ++ tailWord_6045621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045621).length < 2 ^ (prefixWord ++ tailWord_6045621).sum := by decide
  have hdescent : baseEnd_6045621 < baseStart_6045621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045631 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 1, 6, 2]
def baseStart_6045631 : Nat := 118140960795 + 6045631 * 2 ^ 59
def prefixEnd_6045631 : Nat := 4983230072969 + 3 ^ 40 * 6045631 * 2
def baseEnd_6045631 : Nat := 3104314562721941174609155

theorem tailTrace_6045631 : CollatzResearch.WordTrace tailWord_6045631 prefixEnd_6045631 3104314562721941174609155 := by
  unfold tailWord_6045631
  simp only [CollatzResearch.WordTrace]
  refine ⟨220502277560718873417464747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147001518373812582278309831 220502277560718873417464747)
  ·
    refine ⟨330753416341078310126197121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220502277560718873417464747 330753416341078310126197121)
    ·
      refine ⟨248065062255808732594647841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330753416341078310126197121 248065062255808732594647841)
      ·
        refine ⟨186048796691856549445985881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248065062255808732594647841 186048796691856549445985881)
        ·
          refine ⟨139536597518892412084489411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186048796691856549445985881 139536597518892412084489411)
          ·
            refine ⟨209304896278338618126734117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139536597518892412084489411 209304896278338618126734117)
            ·
              refine ⟨39244668052188490898762647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209304896278338618126734117 39244668052188490898762647)
              ·
                refine ⟨58867002078282736348143971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39244668052188490898762647 58867002078282736348143971)
                ·
                  refine ⟨88300503117424104522215957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58867002078282736348143971 88300503117424104522215957)
                  ·
                    refine ⟨4139086083629254899478873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88300503117424104522215957 4139086083629254899478873)
                    ·
                      refine ⟨3104314562721941174609155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4139086083629254899478873 3104314562721941174609155)
                      ·
                        rfl

theorem cell23_6045631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 6, 2].length) (baseStart_6045631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045631 prefixEnd_6045631 := by exact prefixLift 6045631
  have htrace : WordTrace (prefixWord ++ tailWord_6045631) baseStart_6045631 baseEnd_6045631 := by
    simpa [prefixWord, tailWord_6045631, baseEnd_6045631] using wordTrace_append hprefix tailTrace_6045631
  have hstable : (prefixWord ++ tailWord_6045631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045631).length < 2 ^ (prefixWord ++ tailWord_6045631).sum := by decide
  have hdescent : baseEnd_6045631 < baseStart_6045631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045701 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 3, 5]
def baseStart_6045701 : Nat := 118140960795 + 6045701 * 2 ^ 59
def prefixEnd_6045701 : Nat := 4983230072969 + 3 ^ 40 * 6045701 * 2
def baseEnd_6045701 : Nat := 1034783502122585300244611

theorem tailTrace_6045701 : CollatzResearch.WordTrace tailWord_6045701 prefixEnd_6045701 1034783502122585300244611 := by
  unfold tailWord_6045701
  simp only [CollatzResearch.WordTrace]
  refine ⟨220504830670465275372512957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147003220446976850248341971 220504830670465275372512957)
  ·
    refine ⟨82689311501424478264692359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220504830670465275372512957 82689311501424478264692359)
    ·
      refine ⟨124033967252136717397038539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82689311501424478264692359 124033967252136717397038539)
      ·
        refine ⟨186050950878205076095557809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124033967252136717397038539 186050950878205076095557809)
        ·
          refine ⟨139538213158653807071668357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186050950878205076095557809 139538213158653807071668357)
          ·
            refine ⟨26163414967247588825937817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139538213158653807071668357 26163414967247588825937817)
            ·
              refine ⟨19622561225435691619453363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26163414967247588825937817 19622561225435691619453363)
              ·
                refine ⟨29433841838153537429180045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19622561225435691619453363 29433841838153537429180045)
                ·
                  refine ⟨11037690689307576535942517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29433841838153537429180045 11037690689307576535942517)
                  ·
                    refine ⟨1034783502122585300244611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11037690689307576535942517 1034783502122585300244611)
                    ·
                      rfl

theorem cell23_6045701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_6045701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045701 prefixEnd_6045701 := by exact prefixLift 6045701
  have htrace : WordTrace (prefixWord ++ tailWord_6045701) baseStart_6045701 baseEnd_6045701 := by
    simpa [prefixWord, tailWord_6045701, baseEnd_6045701] using wordTrace_append hprefix tailTrace_6045701
  have hstable : (prefixWord ++ tailWord_6045701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045701).length < 2 ^ (prefixWord ++ tailWord_6045701).sum := by decide
  have hdescent : baseEnd_6045701 < baseStart_6045701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045708 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 1, 5, 2]
def baseStart_6045708 : Nat := 118140960795 + 6045708 * 2 ^ 59
def prefixEnd_6045708 : Nat := 4983230072969 + 3 ^ 40 * 6045708 * 2
def baseEnd_6045708 : Nat := 3104354100732337373346301

theorem tailTrace_6045708 : CollatzResearch.WordTrace tailWord_6045708 prefixEnd_6045708 3104354100732337373346301 := by
  unfold tailWord_6045708
  simp only [CollatzResearch.WordTrace]
  refine ⟨110252542990719957784008889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147003390654293277045345185 110252542990719957784008889)
  ·
    refine ⟨82689407243039968338006667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110252542990719957784008889 82689407243039968338006667)
    ·
      refine ⟨124034110864559952507010001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82689407243039968338006667 124034110864559952507010001)
      ·
        refine ⟨93025583148419964380257501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124034110864559952507010001 93025583148419964380257501)
        ·
          refine ⟨34884593680657486642596563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93025583148419964380257501 34884593680657486642596563)
          ·
            refine ⟨52326890520986229963894845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34884593680657486642596563 52326890520986229963894845)
            ·
              refine ⟨19622583945369836236460567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52326890520986229963894845 19622583945369836236460567)
              ·
                refine ⟨29433875918054754354690851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19622583945369836236460567 29433875918054754354690851)
                ·
                  refine ⟨44150813877082131532036277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29433875918054754354690851 44150813877082131532036277)
                  ·
                    refine ⟨4139138800976449831128401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44150813877082131532036277 4139138800976449831128401)
                    ·
                      refine ⟨3104354100732337373346301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4139138800976449831128401 3104354100732337373346301)
                      ·
                        rfl

theorem cell23_6045708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_6045708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045708 prefixEnd_6045708 := by exact prefixLift 6045708
  have htrace : WordTrace (prefixWord ++ tailWord_6045708) baseStart_6045708 baseEnd_6045708 := by
    simpa [prefixWord, tailWord_6045708, baseEnd_6045708] using wordTrace_append hprefix tailTrace_6045708
  have hstable : (prefixWord ++ tailWord_6045708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045708).length < 2 ^ (prefixWord ++ tailWord_6045708).sum := by decide
  have hdescent : baseEnd_6045708 < baseStart_6045708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045715 : List Nat := [1, 1, 1, 2, 1, 4, 3, 5, 1, 1, 3]
def baseStart_6045715 : Nat := 118140960795 + 6045715 * 2 ^ 59
def prefixEnd_6045715 : Nat := 4983230072969 + 3 ^ 40 * 6045715 * 2
def baseEnd_6045715 : Nat := 3104357695096918845958769

theorem tailTrace_6045715 : CollatzResearch.WordTrace tailWord_6045715 prefixEnd_6045715 3104357695096918845958769 := by
  unfold tailWord_6045715
  simp only [CollatzResearch.WordTrace]
  refine ⟨220505341292414555763522599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147003560861609703842348399 220505341292414555763522599)
  ·
    refine ⟨330758011938621833645283899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220505341292414555763522599 330758011938621833645283899)
    ·
      refine ⟨496137017907932750467925849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330758011938621833645283899 496137017907932750467925849)
      ·
        refine ⟨372102763430949562850944387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496137017907932750467925849 372102763430949562850944387)
        ·
          refine ⟨558154145146424344276416581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372102763430949562850944387 558154145146424344276416581)
          ·
            refine ⟨104653902214954564551828109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 558154145146424344276416581 104653902214954564551828109)
            ·
              refine ⟨39245213330607961706935541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104653902214954564551828109 39245213330607961706935541)
              ·
                refine ⟨3679238749744496410025207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39245213330607961706935541 3679238749744496410025207)
                ·
                  refine ⟨5518858124616744615037811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3679238749744496410025207 5518858124616744615037811)
                  ·
                    refine ⟨8278287186925116922556717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5518858124616744615037811 8278287186925116922556717)
                    ·
                      refine ⟨3104357695096918845958769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8278287186925116922556717 3104357695096918845958769)
                      ·
                        rfl

theorem cell23_6045715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 1, 1, 3].length) (baseStart_6045715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045715 prefixEnd_6045715 := by exact prefixLift 6045715
  have htrace : WordTrace (prefixWord ++ tailWord_6045715) baseStart_6045715 baseEnd_6045715 := by
    simpa [prefixWord, tailWord_6045715, baseEnd_6045715] using wordTrace_append hprefix tailTrace_6045715
  have hstable : (prefixWord ++ tailWord_6045715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045715).length < 2 ^ (prefixWord ++ tailWord_6045715).sum := by decide
  have hdescent : baseEnd_6045715 < baseStart_6045715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045732 : List Nat := [2, 3, 1, 4, 2, 1, 2, 1, 3, 1, 3]
def baseStart_6045732 : Nat := 118140960795 + 6045732 * 2 ^ 59
def prefixEnd_6045732 : Nat := 4983230072969 + 3 ^ 40 * 6045732 * 2
def baseEnd_6045732 : Nat := 3104366424268045279446191

theorem tailTrace_6045732 : CollatzResearch.WordTrace tailWord_6045732 prefixEnd_6045732 3104366424268045279446191 := by
  unfold tailWord_6045732
  simp only [CollatzResearch.WordTrace]
  refine ⟨110252980666676483833445725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147003974222235311777927633 110252980666676483833445725)
  ·
    refine ⟨41344867750003681437542147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110252980666676483833445725 41344867750003681437542147)
    ·
      refine ⟨62017301625005522156313221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41344867750003681437542147 62017301625005522156313221)
      ·
        refine ⟨11628244054688535404308729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62017301625005522156313221 11628244054688535404308729)
        ·
          refine ⟨8721183041016401553231547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11628244054688535404308729 8721183041016401553231547)
          ·
            refine ⟨13081774561524602329847321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8721183041016401553231547 13081774561524602329847321)
            ·
              refine ⟨9811330921143451747385491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13081774561524602329847321 9811330921143451747385491)
              ·
                refine ⟨14716996381715177621078237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9811330921143451747385491 14716996381715177621078237)
                ·
                  refine ⟨5518873643143191607904339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14716996381715177621078237 5518873643143191607904339)
                  ·
                    refine ⟨8278310464714787411856509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5518873643143191607904339 8278310464714787411856509)
                    ·
                      refine ⟨3104366424268045279446191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8278310464714787411856509 3104366424268045279446191)
                      ·
                        rfl

theorem cell23_6045732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_6045732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045732 prefixEnd_6045732 := by exact prefixLift 6045732
  have htrace : WordTrace (prefixWord ++ tailWord_6045732) baseStart_6045732 baseEnd_6045732 := by
    simpa [prefixWord, tailWord_6045732, baseEnd_6045732] using wordTrace_append hprefix tailTrace_6045732
  have hstable : (prefixWord ++ tailWord_6045732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045732).length < 2 ^ (prefixWord ++ tailWord_6045732).sum := by decide
  have hdescent : baseEnd_6045732 < baseStart_6045732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045778 : List Nat := [3, 2, 2, 1, 4, 2, 9]
def baseStart_6045778 : Nat := 118140960795 + 6045778 * 2 ^ 59
def prefixEnd_6045778 : Nat := 4983230072969 + 3 ^ 40 * 6045778 * 2
def baseEnd_6045778 : Nat := 38325803017014223450259

theorem tailTrace_6045778 : CollatzResearch.WordTrace tailWord_6045778 prefixEnd_6045778 38325803017014223450259 := by
  unfold tailWord_6045778
  simp only [CollatzResearch.WordTrace]
  refine ⟨55126909772796579380766497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147005092727457545015377325 55126909772796579380766497)
  ·
    refine ⟨41345182329597434535574873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55126909772796579380766497 41345182329597434535574873)
    ·
      refine ⟨31008886747198075901681155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41345182329597434535574873 31008886747198075901681155)
      ·
        refine ⟨46513330120797113852521733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31008886747198075901681155 46513330120797113852521733)
        ·
          refine ⟨8721249397649458847347825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46513330120797113852521733 8721249397649458847347825)
          ·
            refine ⟨6540937048237094135510869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8721249397649458847347825 6540937048237094135510869)
            ·
              refine ⟨38325803017014223450259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6540937048237094135510869 38325803017014223450259)
              ·
                rfl

theorem cell23_6045778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 9].length) (baseStart_6045778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045778 prefixEnd_6045778 := by exact prefixLift 6045778
  have htrace : WordTrace (prefixWord ++ tailWord_6045778) baseStart_6045778 baseEnd_6045778 := by
    simpa [prefixWord, tailWord_6045778, baseEnd_6045778] using wordTrace_append hprefix tailTrace_6045778
  have hstable : (prefixWord ++ tailWord_6045778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045778).length < 2 ^ (prefixWord ++ tailWord_6045778).sum := by decide
  have hdescent : baseEnd_6045778 < baseStart_6045778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045782 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_6045782 : Nat := 118140960795 + 6045782 * 2 ^ 59
def prefixEnd_6045782 : Nat := 4983230072969 + 3 ^ 40 * 6045782 * 2
def baseEnd_6045782 : Nat := 1034797366100256694606987

theorem tailTrace_6045782 : CollatzResearch.WordTrace tailWord_6045782 prefixEnd_6045782 1034797366100256694606987 := by
  unfold tailWord_6045782
  simp only [CollatzResearch.WordTrace]
  refine ⟨13781736561448239137888225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147005189988781217470807733 13781736561448239137888225)
  ·
    refine ⟨10336302421086179353416169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13781736561448239137888225 10336302421086179353416169)
    ·
      refine ⟨7752226815814634515062127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10336302421086179353416169 7752226815814634515062127)
      ·
        refine ⟨11628340223721951772593191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7752226815814634515062127 11628340223721951772593191)
        ·
          refine ⟨17442510335582927658889787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11628340223721951772593191 17442510335582927658889787)
          ·
            refine ⟨26163765503374391488334681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17442510335582927658889787 26163765503374391488334681)
            ·
              refine ⟨19622824127530793616251011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26163765503374391488334681 19622824127530793616251011)
              ·
                refine ⟨29434236191296190424376517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19622824127530793616251011 29434236191296190424376517)
                ·
                  refine ⟨5518919285868035704570597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29434236191296190424376517 5518919285868035704570597)
                  ·
                    refine ⟨1034797366100256694606987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5518919285868035704570597 1034797366100256694606987)
                    ·
                      rfl

theorem cell23_6045782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_6045782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045782 prefixEnd_6045782 := by exact prefixLift 6045782
  have htrace : WordTrace (prefixWord ++ tailWord_6045782) baseStart_6045782 baseEnd_6045782 := by
    simpa [prefixWord, tailWord_6045782, baseEnd_6045782] using wordTrace_append hprefix tailTrace_6045782
  have hstable : (prefixWord ++ tailWord_6045782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045782).length < 2 ^ (prefixWord ++ tailWord_6045782).sum := by decide
  have hdescent : baseEnd_6045782 < baseStart_6045782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045789 : List Nat := [1, 4, 4, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_6045789 : Nat := 118140960795 + 6045789 * 2 ^ 59
def prefixEnd_6045789 : Nat := 4983230072969 + 3 ^ 40 * 6045789 * 2
def baseEnd_6045789 : Nat := 3104395692665351556433429

theorem tailTrace_6045789 : CollatzResearch.WordTrace tailWord_6045789 prefixEnd_6045789 3104395692665351556433429 := by
  unfold tailWord_6045789
  simp only [CollatzResearch.WordTrace]
  refine ⟨220508040294146466401716421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147005360196097644267810947 220508040294146466401716421)
  ·
    refine ⟨41345257555152462450321829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220508040294146466401716421 41345257555152462450321829)
    ·
      refine ⟨7752235791591086709435343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41345257555152462450321829 7752235791591086709435343)
      ·
        refine ⟨11628353687386630064153015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7752235791591086709435343 11628353687386630064153015)
        ·
          refine ⟨17442530531079945096229523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11628353687386630064153015 17442530531079945096229523)
          ·
            refine ⟨26163795796619917644344285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17442530531079945096229523 26163795796619917644344285)
            ·
              refine ⟨9811423423732469116629107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26163795796619917644344285 9811423423732469116629107)
              ·
                refine ⟨14717135135598703674943661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9811423423732469116629107 14717135135598703674943661)
                ·
                  refine ⟨5518925675849513878103873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14717135135598703674943661 5518925675849513878103873)
                  ·
                    refine ⟨4139194256887135408577905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5518925675849513878103873 4139194256887135408577905)
                    ·
                      refine ⟨3104395692665351556433429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4139194256887135408577905 3104395692665351556433429)
                      ·
                        rfl

theorem cell23_6045789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_6045789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045789 prefixEnd_6045789 := by exact prefixLift 6045789
  have htrace : WordTrace (prefixWord ++ tailWord_6045789) baseStart_6045789 baseEnd_6045789 := by
    simpa [prefixWord, tailWord_6045789, baseEnd_6045789] using wordTrace_append hprefix tailTrace_6045789
  have hstable : (prefixWord ++ tailWord_6045789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045789).length < 2 ^ (prefixWord ++ tailWord_6045789).sum := by decide
  have hdescent : baseEnd_6045789 < baseStart_6045789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045815 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 3, 3, 2]
def baseStart_6045815 : Nat := 118140960795 + 6045815 * 2 ^ 59
def prefixEnd_6045815 : Nat := 4983230072969 + 3 ^ 40 * 6045815 * 2
def baseEnd_6045815 : Nat := 3104409043162368454708309

theorem tailTrace_6045815 : CollatzResearch.WordTrace tailWord_6045815 prefixEnd_6045815 3104409043162368454708309 := by
  unfold tailWord_6045815
  simp only [CollatzResearch.WordTrace]
  refine ⟨220508988592052272842162899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147005992394701515228108599 220508988592052272842162899)
  ·
    refine ⟨330763482888078409263244349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220508988592052272842162899 330763482888078409263244349)
    ·
      refine ⟨124036306083029403473716631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330763482888078409263244349 124036306083029403473716631)
      ·
        refine ⟨186054459124544105210574947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124036306083029403473716631 186054459124544105210574947)
        ·
          refine ⟨279081688686816157815862421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186054459124544105210574947 279081688686816157815862421)
          ·
            refine ⟨13081954157194507397618551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 279081688686816157815862421 13081954157194507397618551)
            ·
              refine ⟨19622931235791761096427827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13081954157194507397618551 19622931235791761096427827)
              ·
                refine ⟨29434396853687641644641741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19622931235791761096427827 29434396853687641644641741)
                ·
                  refine ⟨11037898820132865616740653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29434396853687641644641741 11037898820132865616740653)
                  ·
                    refine ⟨4139212057549824606277745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11037898820132865616740653 4139212057549824606277745)
                    ·
                      refine ⟨3104409043162368454708309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4139212057549824606277745 3104409043162368454708309)
                      ·
                        rfl

theorem cell23_6045815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 3, 2].length) (baseStart_6045815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045815 prefixEnd_6045815 := by exact prefixLift 6045815
  have htrace : WordTrace (prefixWord ++ tailWord_6045815) baseStart_6045815 baseEnd_6045815 := by
    simpa [prefixWord, tailWord_6045815, baseEnd_6045815] using wordTrace_append hprefix tailTrace_6045815
  have hstable : (prefixWord ++ tailWord_6045815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045815).length < 2 ^ (prefixWord ++ tailWord_6045815).sum := by decide
  have hdescent : baseEnd_6045815 < baseStart_6045815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045841 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 4]
def baseStart_6045841 : Nat := 118140960795 + 6045841 * 2 ^ 59
def prefixEnd_6045841 : Nat := 4983230072969 + 3 ^ 40 * 6045841 * 2
def baseEnd_6045841 : Nat := 3104422393659385352983189

theorem tailTrace_6045841 : CollatzResearch.WordTrace tailWord_6045841 prefixEnd_6045841 3104422393659385352983189 := by
  unfold tailWord_6045841
  simp only [CollatzResearch.WordTrace]
  refine ⟨220509936889958079282609377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147006624593305386188406251 220509936889958079282609377)
  ·
    refine ⟨165382452667468559461957033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220509936889958079282609377 165382452667468559461957033)
    ·
      refine ⟨124036839500601419596467775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165382452667468559461957033 124036839500601419596467775)
      ·
        refine ⟨186055259250902129394701663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124036839500601419596467775 186055259250902129394701663)
        ·
          refine ⟨279082888876353194092052495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186055259250902129394701663 279082888876353194092052495)
          ·
            refine ⟨418624333314529791138078743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279082888876353194092052495 418624333314529791138078743)
            ·
              refine ⟨627936499971794686707118115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418624333314529791138078743 627936499971794686707118115)
              ·
                refine ⟨941904749957692030060677173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627936499971794686707118115 941904749957692030060677173)
                ·
                  refine ⟨88303570308533627818188485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 941904749957692030060677173 88303570308533627818188485)
                  ·
                    refine ⟨16556919432850055215910341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88303570308533627818188485 16556919432850055215910341)
                    ·
                      refine ⟨3104422393659385352983189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16556919432850055215910341 3104422393659385352983189)
                      ·
                        rfl

theorem cell23_6045841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_6045841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045841 prefixEnd_6045841 := by exact prefixLift 6045841
  have htrace : WordTrace (prefixWord ++ tailWord_6045841) baseStart_6045841 baseEnd_6045841 := by
    simpa [prefixWord, tailWord_6045841, baseEnd_6045841] using wordTrace_append hprefix tailTrace_6045841
  have hstable : (prefixWord ++ tailWord_6045841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045841).length < 2 ^ (prefixWord ++ tailWord_6045841).sum := by decide
  have hdescent : baseEnd_6045841 < baseStart_6045841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045846 : List Nat := [5, 3, 2, 1, 1, 2, 1, 8]
def baseStart_6045846 : Nat := 118140960795 + 6045846 * 2 ^ 59
def prefixEnd_6045846 : Nat := 4983230072969 + 3 ^ 40 * 6045846 * 2
def baseEnd_6045846 : Nat := 114978702261579919756321

theorem tailTrace_6045846 : CollatzResearch.WordTrace tailWord_6045846 prefixEnd_6045846 114978702261579919756321 := by
  unfold tailWord_6045846
  simp only [CollatzResearch.WordTrace]
  refine ⟨13781882453433747821033837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147006746169959976757694261 13781882453433747821033837)
  ·
    refine ⟨5168205920037655432887689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13781882453433747821033837 5168205920037655432887689)
    ·
      refine ⟨3876154440028241574665767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5168205920037655432887689 3876154440028241574665767)
      ·
        refine ⟨5814231660042362361998651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3876154440028241574665767 5814231660042362361998651)
        ·
          refine ⟨8721347490063543542997977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5814231660042362361998651 8721347490063543542997977)
          ·
            refine ⟨6541010617547657657248483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8721347490063543542997977 6541010617547657657248483)
            ·
              refine ⟨9811515926321486485872725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6541010617547657657248483 9811515926321486485872725)
              ·
                refine ⟨114978702261579919756321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9811515926321486485872725 114978702261579919756321)
                ·
                  rfl

theorem cell23_6045846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_6045846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045846 prefixEnd_6045846 := by exact prefixLift 6045846
  have htrace : WordTrace (prefixWord ++ tailWord_6045846) baseStart_6045846 baseEnd_6045846 := by
    simpa [prefixWord, tailWord_6045846, baseEnd_6045846] using wordTrace_append hprefix tailTrace_6045846
  have hstable : (prefixWord ++ tailWord_6045846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045846).length < 2 ^ (prefixWord ++ tailWord_6045846).sum := by decide
  have hdescent : baseEnd_6045846 < baseStart_6045846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045898 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 4, 5]
def baseStart_6045898 : Nat := 118140960795 + 6045898 * 2 ^ 59
def prefixEnd_6045898 : Nat := 4983230072969 + 3 ^ 40 * 6045898 * 2
def baseEnd_6045898 : Nat := 1034817220685563876656809

theorem tailTrace_6045898 : CollatzResearch.WordTrace tailWord_6045898 prefixEnd_6045898 1034817220685563876656809 := by
  unfold tailWord_6045898
  simp only [CollatzResearch.WordTrace]
  refine ⟨55128003962687894504358587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147008010567167718678289565 55128003962687894504358587)
  ·
    refine ⟨82692005944031841756537881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55128003962687894504358587 82692005944031841756537881)
    ·
      refine ⟨62019004458023881317403411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82692005944031841756537881 62019004458023881317403411)
      ·
        refine ⟨93028506687035821976105117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62019004458023881317403411 93028506687035821976105117)
        ·
          refine ⟨34885690007638433241039419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93028506687035821976105117 34885690007638433241039419)
          ·
            refine ⟨52328535011457649861559129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34885690007638433241039419 52328535011457649861559129)
            ·
              refine ⟨39246401258593237396169347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52328535011457649861559129 39246401258593237396169347)
              ·
                refine ⟨58869601887889856094254021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39246401258593237396169347 58869601887889856094254021)
                ·
                  refine ⟨11038050353979348017672629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58869601887889856094254021 11038050353979348017672629)
                  ·
                    refine ⟨1034817220685563876656809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11038050353979348017672629 1034817220685563876656809)
                    ·
                      rfl

theorem cell23_6045898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_6045898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045898 prefixEnd_6045898 := by exact prefixLift 6045898
  have htrace : WordTrace (prefixWord ++ tailWord_6045898) baseStart_6045898 baseEnd_6045898 := by
    simpa [prefixWord, tailWord_6045898, baseEnd_6045898] using wordTrace_append hprefix tailTrace_6045898
  have hstable : (prefixWord ++ tailWord_6045898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045898).length < 2 ^ (prefixWord ++ tailWord_6045898).sum := by decide
  have hdescent : baseEnd_6045898 < baseStart_6045898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045955 : List Nat := [1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 3]
def baseStart_6045955 : Nat := 118140960795 + 6045955 * 2 ^ 59
def prefixEnd_6045955 : Nat := 4983230072969 + 3 ^ 40 * 6045955 * 2
def baseEnd_6045955 : Nat := 3104480930453997906957665

theorem tailTrace_6045955 : CollatzResearch.WordTrace tailWord_6045955 prefixEnd_6045955 3104480930453997906957665 := by
  unfold tailWord_6045955
  simp only [CollatzResearch.WordTrace]
  refine ⟨220514094811545076752259319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147009396541030051168172879 220514094811545076752259319)
  ·
    refine ⟨330771142217317615128388979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220514094811545076752259319 330771142217317615128388979)
    ·
      refine ⟨496156713325976422692583469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330771142217317615128388979 496156713325976422692583469)
      ·
        refine ⟨186058767497241158509718801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 496156713325976422692583469 186058767497241158509718801)
        ·
          refine ⟨139544075622930868882289101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186058767497241158509718801 139544075622930868882289101)
          ·
            refine ⟨52329028358599075830858413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139544075622930868882289101 52329028358599075830858413)
            ·
              refine ⟨19623385634474653436571905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52329028358599075830858413 19623385634474653436571905)
              ·
                refine ⟨14717539225855990077428929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19623385634474653436571905 14717539225855990077428929)
                ·
                  refine ⟨11038154419391992558071697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14717539225855990077428929 11038154419391992558071697)
                  ·
                    refine ⟨8278615814543994418553773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11038154419391992558071697 8278615814543994418553773)
                    ·
                      refine ⟨3104480930453997906957665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8278615814543994418553773 3104480930453997906957665)
                      ·
                        rfl

theorem cell23_6045955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_6045955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045955 prefixEnd_6045955 := by exact prefixLift 6045955
  have htrace : WordTrace (prefixWord ++ tailWord_6045955) baseStart_6045955 baseEnd_6045955 := by
    simpa [prefixWord, tailWord_6045955, baseEnd_6045955] using wordTrace_append hprefix tailTrace_6045955
  have hstable : (prefixWord ++ tailWord_6045955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045955).length < 2 ^ (prefixWord ++ tailWord_6045955).sum := by decide
  have hdescent : baseEnd_6045955 < baseStart_6045955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045962 : List Nat := [3, 1, 2, 2, 1, 1, 2, 6, 1, 4]
def baseStart_6045962 : Nat := 118140960795 + 6045962 * 2 ^ 59
def prefixEnd_6045962 : Nat := 4983230072969 + 3 ^ 40 * 6045962 * 2
def baseEnd_6045962 : Nat := 1034828174939526459856711

theorem tailTrace_6045962 : CollatzResearch.WordTrace tailWord_6045962 prefixEnd_6045962 1034828174939526459856711 := by
  unfold tailWord_6045962
  simp only [CollatzResearch.WordTrace]
  refine ⟨55128587530629929236941035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147009566748346477965176093 55128587530629929236941035)
  ·
    refine ⟨82692881295944893855411553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55128587530629929236941035 82692881295944893855411553)
    ·
      refine ⟨62019660971958670391558665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82692881295944893855411553 62019660971958670391558665)
      ·
        refine ⟨46514745728969002793668999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62019660971958670391558665 46514745728969002793668999)
        ·
          refine ⟨69772118593453504190503499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46514745728969002793668999 69772118593453504190503499)
          ·
            refine ⟨104658177890180256285755249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69772118593453504190503499 104658177890180256285755249)
            ·
              refine ⟨78493633417635192214316437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104658177890180256285755249 78493633417635192214316437)
              ·
                refine ⟨3679389066451649635046083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78493633417635192214316437 3679389066451649635046083)
                ·
                  refine ⟨5519083599677474452569125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3679389066451649635046083 5519083599677474452569125)
                  ·
                    refine ⟨1034828174939526459856711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5519083599677474452569125 1034828174939526459856711)
                    ·
                      rfl

theorem cell23_6045962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_6045962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045962 prefixEnd_6045962 := by exact prefixLift 6045962
  have htrace : WordTrace (prefixWord ++ tailWord_6045962) baseStart_6045962 baseEnd_6045962 := by
    simpa [prefixWord, tailWord_6045962, baseEnd_6045962] using wordTrace_append hprefix tailTrace_6045962
  have hstable : (prefixWord ++ tailWord_6045962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045962).length < 2 ^ (prefixWord ++ tailWord_6045962).sum := by decide
  have hdescent : baseEnd_6045962 < baseStart_6045962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6045975 : List Nat := [1, 1, 3, 4, 1, 3, 1, 3, 6]
def baseStart_6045975 : Nat := 118140960795 + 6045975 * 2 ^ 59
def prefixEnd_6045975 : Nat := 4983230072969 + 3 ^ 40 * 6045975 * 2
def baseEnd_6045975 : Nat := 344943466674120869856397

theorem tailTrace_6045975 : CollatzResearch.WordTrace tailWord_6045975 prefixEnd_6045975 344943466674120869856397 := by
  unfold tailWord_6045975
  simp only [CollatzResearch.WordTrace]
  refine ⟨220514824271472620167987379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147009882847648413445324919 220514824271472620167987379)
  ·
    refine ⟨330772236407208930251981069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220514824271472620167987379 330772236407208930251981069)
    ·
      refine ⟨124039588652703348844492901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330772236407208930251981069 124039588652703348844492901)
      ·
        refine ⟨23257422872381877908342419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124039588652703348844492901 23257422872381877908342419)
        ·
          refine ⟨34886134308572816862513629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23257422872381877908342419 34886134308572816862513629)
          ·
            refine ⟨13082300365714806323442611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34886134308572816862513629 13082300365714806323442611)
            ·
              refine ⟨19623450548572209485163917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13082300365714806323442611 19623450548572209485163917)
              ·
                refine ⟨7358793955714578556936469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19623450548572209485163917 7358793955714578556936469)
                ·
                  refine ⟨344943466674120869856397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7358793955714578556936469 344943466674120869856397)
                  ·
                    rfl

theorem cell23_6045975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 6].length) (baseStart_6045975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6045975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6045975 prefixEnd_6045975 := by exact prefixLift 6045975
  have htrace : WordTrace (prefixWord ++ tailWord_6045975) baseStart_6045975 baseEnd_6045975 := by
    simpa [prefixWord, tailWord_6045975, baseEnd_6045975] using wordTrace_append hprefix tailTrace_6045975
  have hstable : (prefixWord ++ tailWord_6045975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6045975).length < 2 ^ (prefixWord ++ tailWord_6045975).sum := by decide
  have hdescent : baseEnd_6045975 < baseStart_6045975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6045975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046012 : List Nat := [2, 2, 2, 2, 1, 2, 1, 4, 2, 3, 2]
def baseStart_6046012 : Nat := 118140960795 + 6046012 * 2 ^ 59
def prefixEnd_6046012 : Nat := 4983230072969 + 3 ^ 40 * 6046012 * 2
def baseEnd_6046012 : Nat := 3104510198851304183944903

theorem tailTrace_6046012 : CollatzResearch.WordTrace tailWord_6046012 prefixEnd_6046012 3104510198851304183944903 := by
  unfold tailWord_6046012
  simp only [CollatzResearch.WordTrace]
  refine ⟨110258086886169287743542145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147010782514892383658056193 110258086886169287743542145)
  ·
    refine ⟨82693565164626965807656609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110258086886169287743542145 82693565164626965807656609)
    ·
      refine ⟨62020173873470224355742457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82693565164626965807656609 62020173873470224355742457)
      ·
        refine ⟨46515130405102668266806843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62020173873470224355742457 46515130405102668266806843)
        ·
          refine ⟨69772695607654002400210265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46515130405102668266806843 69772695607654002400210265)
          ·
            refine ⟨52329521705740501800157699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69772695607654002400210265 52329521705740501800157699)
            ·
              refine ⟨78494282558610752700236549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52329521705740501800157699 78494282558610752700236549)
              ·
                refine ⟨14717677979739516131294353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78494282558610752700236549 14717677979739516131294353)
                ·
                  refine ⟨11038258484804637098470765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14717677979739516131294353 11038258484804637098470765)
                  ·
                    refine ⟨4139346931801738911926537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11038258484804637098470765 4139346931801738911926537)
                    ·
                      refine ⟨3104510198851304183944903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4139346931801738911926537 3104510198851304183944903)
                      ·
                        rfl

theorem cell23_6046012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_6046012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046012 prefixEnd_6046012 := by exact prefixLift 6046012
  have htrace : WordTrace (prefixWord ++ tailWord_6046012) baseStart_6046012 baseEnd_6046012 := by
    simpa [prefixWord, tailWord_6046012, baseEnd_6046012] using wordTrace_append hprefix tailTrace_6046012
  have hstable : (prefixWord ++ tailWord_6046012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046012).length < 2 ^ (prefixWord ++ tailWord_6046012).sum := by decide
  have hdescent : baseEnd_6046012 < baseStart_6046012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046025 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 2, 6, 2]
def baseStart_6046025 : Nat := 118140960795 + 6046025 * 2 ^ 59
def prefixEnd_6046025 : Nat := 4983230072969 + 3 ^ 40 * 6046025 * 2
def baseEnd_6046025 : Nat := 3104516874099812633082343

theorem tailTrace_6046025 : CollatzResearch.WordTrace tailWord_6046025 prefixEnd_6046025 3104516874099812633082343 := by
  unfold tailWord_6046025
  simp only [CollatzResearch.WordTrace]
  refine ⟨220516647921291478707307529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147011098614194319138205019 220516647921291478707307529)
  ·
    refine ⟨165387485940968609030480647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220516647921291478707307529 165387485940968609030480647)
    ·
      refine ⟨248081228911452913545720971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165387485940968609030480647 248081228911452913545720971)
      ·
        refine ⟨372121843367179370318581457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248081228911452913545720971 372121843367179370318581457)
        ·
          refine ⟨279091382525384527738936093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372121843367179370318581457 279091382525384527738936093)
          ·
            refine ⟨104659268447019197902101035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279091382525384527738936093 104659268447019197902101035)
            ·
              refine ⟨156988902670528796853151553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104659268447019197902101035 156988902670528796853151553)
              ·
                refine ⟨117741677002896597639863665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156988902670528796853151553 117741677002896597639863665)
                ·
                  refine ⟨88306257752172448229897749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117741677002896597639863665 88306257752172448229897749)
                  ·
                    refine ⟨4139355832133083510776457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88306257752172448229897749 4139355832133083510776457)
                    ·
                      refine ⟨3104516874099812633082343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4139355832133083510776457 3104516874099812633082343)
                      ·
                        rfl

theorem cell23_6046025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 6, 2].length) (baseStart_6046025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046025 prefixEnd_6046025 := by exact prefixLift 6046025
  have htrace : WordTrace (prefixWord ++ tailWord_6046025) baseStart_6046025 baseEnd_6046025 := by
    simpa [prefixWord, tailWord_6046025, baseEnd_6046025] using wordTrace_append hprefix tailTrace_6046025
  have hstable : (prefixWord ++ tailWord_6046025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046025).length < 2 ^ (prefixWord ++ tailWord_6046025).sum := by decide
  have hdescent : baseEnd_6046025 < baseStart_6046025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046069 : List Nat := [1, 3, 4, 1, 2, 1, 3, 2, 2, 4]
def baseStart_6046069 : Nat := 118140960795 + 6046069 * 2 ^ 59
def prefixEnd_6046069 : Nat := 4983230072969 + 3 ^ 40 * 6046069 * 2
def baseEnd_6046069 : Nat := 1034846489082870153644047

theorem tailTrace_6046069 : CollatzResearch.WordTrace tailWord_6046069 prefixEnd_6046069 1034846489082870153644047 := by
  unfold tailWord_6046069
  simp only [CollatzResearch.WordTrace]
  refine ⟨220518252733132074221909261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147012168488754716147939507 220518252733132074221909261)
  ·
    refine ⟨82694344774924527833215973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220518252733132074221909261 82694344774924527833215973)
    ·
      refine ⟨15505189645298348968727995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82694344774924527833215973 15505189645298348968727995)
      ·
        refine ⟨23257784467947523453091993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15505189645298348968727995 23257784467947523453091993)
        ·
          refine ⟨17443338350960642589818995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23257784467947523453091993 17443338350960642589818995)
          ·
            refine ⟨26165007526440963884728493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17443338350960642589818995 26165007526440963884728493)
            ·
              refine ⟨9811877822415361456773185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26165007526440963884728493 9811877822415361456773185)
              ·
                refine ⟨7358908366811521092579889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9811877822415361456773185 7358908366811521092579889)
                ·
                  refine ⟨5519181275108640819434917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7358908366811521092579889 5519181275108640819434917)
                  ·
                    refine ⟨1034846489082870153644047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5519181275108640819434917 1034846489082870153644047)
                    ·
                      rfl

theorem cell23_6046069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_6046069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046069 prefixEnd_6046069 := by exact prefixLift 6046069
  have htrace : WordTrace (prefixWord ++ tailWord_6046069) baseStart_6046069 baseEnd_6046069 := by
    simpa [prefixWord, tailWord_6046069, baseEnd_6046069] using wordTrace_append hprefix tailTrace_6046069
  have hstable : (prefixWord ++ tailWord_6046069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046069).length < 2 ^ (prefixWord ++ tailWord_6046069).sum := by decide
  have hdescent : baseEnd_6046069 < baseStart_6046069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046092 : List Nat := [2, 2, 1, 2, 1, 4, 3, 1, 1, 3, 3]
def baseStart_6046092 : Nat := 118140960795 + 6046092 * 2 ^ 59
def prefixEnd_6046092 : Nat := 4983230072969 + 3 ^ 40 * 6046092 * 2
def baseEnd_6046092 : Nat := 3104551277303663870944535

theorem tailTrace_6046092 : CollatzResearch.WordTrace tailWord_6046092 prefixEnd_6046092 3104551277303663870944535 := by
  unfold tailWord_6046092
  simp only [CollatzResearch.WordTrace]
  refine ⟨110259545806024374574998265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147012727741365832766664353 110259545806024374574998265)
  ·
    refine ⟨82694659354518280931248699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110259545806024374574998265 82694659354518280931248699)
    ·
      refine ⟨124041989031777421396873049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82694659354518280931248699 124041989031777421396873049)
      ·
        refine ⟨93031491773833066047654787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124041989031777421396873049 93031491773833066047654787)
        ·
          refine ⟨139547237660749599071482181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93031491773833066047654787 139547237660749599071482181)
          ·
            refine ⟨26165107061390549825902909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139547237660749599071482181 26165107061390549825902909)
            ·
              refine ⟨9811915148021456184713591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26165107061390549825902909 9811915148021456184713591)
              ·
                refine ⟨14717872722032184277070387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9811915148021456184713591 14717872722032184277070387)
                ·
                  refine ⟨22076809083048276415605581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14717872722032184277070387 22076809083048276415605581)
                  ·
                    refine ⟨8278803406143103655852093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22076809083048276415605581 8278803406143103655852093)
                    ·
                      refine ⟨3104551277303663870944535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8278803406143103655852093 3104551277303663870944535)
                      ·
                        rfl

theorem cell23_6046092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_6046092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046092 prefixEnd_6046092 := by exact prefixLift 6046092
  have htrace : WordTrace (prefixWord ++ tailWord_6046092) baseStart_6046092 baseEnd_6046092 := by
    simpa [prefixWord, tailWord_6046092, baseEnd_6046092] using wordTrace_append hprefix tailTrace_6046092
  have hstable : (prefixWord ++ tailWord_6046092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046092).length < 2 ^ (prefixWord ++ tailWord_6046092).sum := by decide
  have hdescent : baseEnd_6046092 < baseStart_6046092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046110 : List Nat := [4, 3, 1, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_6046110 : Nat := 118140960795 + 6046110 * 2 ^ 59
def prefixEnd_6046110 : Nat := 4983230072969 + 3 ^ 40 * 6046110 * 2
def baseEnd_6046110 : Nat := 3104560519955444800519453

theorem tailTrace_6046110 : CollatzResearch.WordTrace tailWord_6046110 prefixEnd_6046110 3104560519955444800519453 := by
  unfold tailWord_6046110
  simp only [CollatzResearch.WordTrace]
  refine ⟨27564968515747942278018973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147013165417322358816101189 27564968515747942278018973)
  ·
    refine ⟨10336863193405478354257115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27564968515747942278018973 10336863193405478354257115)
    ·
      refine ⟨15505294790108217531385673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10336863193405478354257115 15505294790108217531385673)
      ·
        refine ⟨11628971092581163148539255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15505294790108217531385673 11628971092581163148539255)
        ·
          refine ⟨17443456638871744722808883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11628971092581163148539255 17443456638871744722808883)
          ·
            refine ⟨26165184958307617084213325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17443456638871744722808883 26165184958307617084213325)
            ·
              refine ⟨9811944359365356406579997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26165184958307617084213325 9811944359365356406579997)
              ·
                refine ⟨3679479134762008652467499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9811944359365356406579997 3679479134762008652467499)
                ·
                  refine ⟨5519218702143012978701249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3679479134762008652467499 5519218702143012978701249)
                  ·
                    refine ⟨4139414026607259734025937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5519218702143012978701249 4139414026607259734025937)
                    ·
                      refine ⟨3104560519955444800519453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4139414026607259734025937 3104560519955444800519453)
                      ·
                        rfl

theorem cell23_6046110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_6046110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046110 prefixEnd_6046110 := by exact prefixLift 6046110
  have htrace : WordTrace (prefixWord ++ tailWord_6046110) baseStart_6046110 baseEnd_6046110 := by
    simpa [prefixWord, tailWord_6046110, baseEnd_6046110] using wordTrace_append hprefix tailTrace_6046110
  have hstable : (prefixWord ++ tailWord_6046110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046110).length < 2 ^ (prefixWord ++ tailWord_6046110).sum := by decide
  have hdescent : baseEnd_6046110 < baseStart_6046110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046166 : List Nat := [5, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_6046166 : Nat := 118140960795 + 6046166 * 2 ^ 59
def prefixEnd_6046166 : Nat := 4983230072969 + 3 ^ 40 * 6046166 * 2
def baseEnd_6046166 : Nat := 3104589274872096581419195

theorem tailTrace_6046166 : CollatzResearch.WordTrace tailWord_6046166 prefixEnd_6046166 3104589274872096581419195 := by
  unfold tailWord_6046166
  simp only [CollatzResearch.WordTrace]
  refine ⟨13782611913361291236761897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147014527075853773192126901 13782611913361291236761897)
  ·
    refine ⟨10336958935020968427571423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13782611913361291236761897 10336958935020968427571423)
    ·
      refine ⟨15505438402531452641357135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10336958935020968427571423 15505438402531452641357135)
      ·
        refine ⟨23258157603797178962035703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15505438402531452641357135 23258157603797178962035703)
        ·
          refine ⟨34887236405695768443053555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23258157603797178962035703 34887236405695768443053555)
          ·
            refine ⟨52330854608543652664580333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34887236405695768443053555 52330854608543652664580333)
            ·
              refine ⟨19624070478203869749217625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52330854608543652664580333 19624070478203869749217625)
              ·
                refine ⟨14718052858652902311913219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19624070478203869749217625 14718052858652902311913219)
                ·
                  refine ⟨22077079287979353467869829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14718052858652902311913219 22077079287979353467869829)
                  ·
                    refine ⟨4139452366496128775225593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22077079287979353467869829 4139452366496128775225593)
                    ·
                      refine ⟨3104589274872096581419195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4139452366496128775225593 3104589274872096581419195)
                      ·
                        rfl

theorem cell23_6046166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_6046166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046166 prefixEnd_6046166 := by exact prefixLift 6046166
  have htrace : WordTrace (prefixWord ++ tailWord_6046166) baseStart_6046166 baseEnd_6046166 := by
    simpa [prefixWord, tailWord_6046166, baseEnd_6046166] using wordTrace_append hprefix tailTrace_6046166
  have hstable : (prefixWord ++ tailWord_6046166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046166).length < 2 ^ (prefixWord ++ tailWord_6046166).sum := by decide
  have hdescent : baseEnd_6046166 < baseStart_6046166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046185 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 4, 5]
def baseStart_6046185 : Nat := 118140960795 + 6046185 * 2 ^ 59
def prefixEnd_6046185 : Nat := 4983230072969 + 3 ^ 40 * 6046185 * 2
def baseEnd_6046185 : Nat := 1034866343668177335693869

theorem tailTrace_6046185 : CollatzResearch.WordTrace tailWord_6046185 prefixEnd_6046185 1034866343668177335693869 := by
  unfold tailWord_6046185
  simp only [CollatzResearch.WordTrace]
  refine ⟨220522483600711826033132009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147014989067141217355421339 220522483600711826033132009)
  ·
    refine ⟨165391862700533869524849007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220522483600711826033132009 165391862700533869524849007)
    ·
      refine ⟨248087794050800804287273511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165391862700533869524849007 248087794050800804287273511)
      ·
        refine ⟨372131691076201206430910267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248087794050800804287273511 372131691076201206430910267)
        ·
          refine ⟨558197536614301809646365401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372131691076201206430910267 558197536614301809646365401)
          ·
            refine ⟨418648152460726357234774051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 558197536614301809646365401 418648152460726357234774051)
            ·
              refine ⟨627972228691089535852161077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418648152460726357234774051 627972228691089535852161077)
              ·
                refine ⟨58872396439789643986140101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 627972228691089535852161077 58872396439789643986140101)
                ·
                  refine ⟨11038574332460558247401269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58872396439789643986140101 11038574332460558247401269)
                  ·
                    refine ⟨1034866343668177335693869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11038574332460558247401269 1034866343668177335693869)
                    ·
                      rfl

theorem cell23_6046185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 5].length) (baseStart_6046185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046185 prefixEnd_6046185 := by exact prefixLift 6046185
  have htrace : WordTrace (prefixWord ++ tailWord_6046185) baseStart_6046185 baseEnd_6046185 := by
    simpa [prefixWord, tailWord_6046185, baseEnd_6046185] using wordTrace_append hprefix tailTrace_6046185
  have hstable : (prefixWord ++ tailWord_6046185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046185).length < 2 ^ (prefixWord ++ tailWord_6046185).sum := by decide
  have hdescent : baseEnd_6046185 < baseStart_6046185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046192 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 1, 7, 2]
def baseStart_6046192 : Nat := 118140960795 + 6046192 * 2 ^ 59
def prefixEnd_6046192 : Nat := 4983230072969 + 3 ^ 40 * 6046192 * 2
def baseEnd_6046192 : Nat := 3104602625369113479694075

theorem tailTrace_6046192 : CollatzResearch.WordTrace tailWord_6046192 prefixEnd_6046192 3104602625369113479694075 := by
  unfold tailWord_6046192
  simp only [CollatzResearch.WordTrace]
  refine ⟨110261369455843233114318415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147015159274457644152424553 110261369455843233114318415)
  ·
    refine ⟨165392054183764849671477623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110261369455843233114318415 165392054183764849671477623)
    ·
      refine ⟨248088081275647274507216435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165392054183764849671477623 248088081275647274507216435)
      ·
        refine ⟨372132121913470911760824653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248088081275647274507216435 372132121913470911760824653)
        ·
          refine ⟨139549545717551591910309245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 372132121913470911760824653 139549545717551591910309245)
          ·
            refine ⟨52331079644081846966365967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139549545717551591910309245 52331079644081846966365967)
            ·
              refine ⟨78496619466122770449548951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52331079644081846966365967 78496619466122770449548951)
              ·
                refine ⟨117744929199184155674323427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78496619466122770449548951 117744929199184155674323427)
                ·
                  refine ⟨176617393798776233511485141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117744929199184155674323427 176617393798776233511485141)
                  ·
                    refine ⟨4139470167158817972925433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 176617393798776233511485141 4139470167158817972925433)
                    ·
                      refine ⟨3104602625369113479694075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4139470167158817972925433 3104602625369113479694075)
                      ·
                        rfl

theorem cell23_6046192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 7, 2].length) (baseStart_6046192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046192 prefixEnd_6046192 := by exact prefixLift 6046192
  have htrace : WordTrace (prefixWord ++ tailWord_6046192) baseStart_6046192 baseEnd_6046192 := by
    simpa [prefixWord, tailWord_6046192, baseEnd_6046192] using wordTrace_append hprefix tailTrace_6046192
  have hstable : (prefixWord ++ tailWord_6046192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046192).length < 2 ^ (prefixWord ++ tailWord_6046192).sum := by decide
  have hdescent : baseEnd_6046192 < baseStart_6046192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046195 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 5]
def baseStart_6046195 : Nat := 118140960795 + 6046195 * 2 ^ 59
def prefixEnd_6046195 : Nat := 4983230072969 + 3 ^ 40 * 6046195 * 2
def baseEnd_6046195 : Nat := 3104604165811076967956561

theorem tailTrace_6046195 : CollatzResearch.WordTrace tailWord_6046195 prefixEnd_6046195 3104604165811076967956561 := by
  unfold tailWord_6046195
  simp only [CollatzResearch.WordTrace]
  refine ⟨220522848330675597740996039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147015232220450398493997359 220522848330675597740996039)
  ·
    refine ⟨330784272496013396611494059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220522848330675597740996039 330784272496013396611494059)
    ·
      refine ⟨496176408744020094917241089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330784272496013396611494059 496176408744020094917241089)
      ·
        refine ⟨372132306558015071187930817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496176408744020094917241089 372132306558015071187930817)
        ·
          refine ⟨279099229918511303390948113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372132306558015071187930817 279099229918511303390948113)
          ·
            refine ⟨209324422438883477543211085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279099229918511303390948113 209324422438883477543211085)
            ·
              refine ⟨78496658414581304078704157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209324422438883477543211085 78496658414581304078704157)
              ·
                refine ⟨29436246905467989029514059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78496658414581304078704157 29436246905467989029514059)
                ·
                  refine ⟨44154370358201983544271089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29436246905467989029514059 44154370358201983544271089)
                  ·
                    refine ⟨33115777768651487658203317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44154370358201983544271089 33115777768651487658203317)
                    ·
                      refine ⟨3104604165811076967956561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33115777768651487658203317 3104604165811076967956561)
                      ·
                        rfl

theorem cell23_6046195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_6046195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046195 prefixEnd_6046195 := by exact prefixLift 6046195
  have htrace : WordTrace (prefixWord ++ tailWord_6046195) baseStart_6046195 baseEnd_6046195 := by
    simpa [prefixWord, tailWord_6046195, baseEnd_6046195] using wordTrace_append hprefix tailTrace_6046195
  have hstable : (prefixWord ++ tailWord_6046195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046195).length < 2 ^ (prefixWord ++ tailWord_6046195).sum := by decide
  have hdescent : baseEnd_6046195 < baseStart_6046195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046219 : List Nat := [1, 1, 1, 1, 7, 3, 1, 1, 2, 5]
def baseStart_6046219 : Nat := 118140960795 + 6046219 * 2 ^ 59
def prefixEnd_6046219 : Nat := 4983230072969 + 3 ^ 40 * 6046219 * 2
def baseEnd_6046219 : Nat := 1034872163115594958018817

theorem tailTrace_6046219 : CollatzResearch.WordTrace tailWord_6046219 prefixEnd_6046219 1034872163115594958018817 := by
  unfold tailWord_6046219
  simp only [CollatzResearch.WordTrace]
  refine ⟨220523723682588649839869711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147015815788392433226579807 220523723682588649839869711)
  ·
    refine ⟨330785585523882974759804567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220523723682588649839869711 330785585523882974759804567)
    ·
      refine ⟨496178378285824462139706851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330785585523882974759804567 496178378285824462139706851)
      ·
        refine ⟨744267567428736693209560277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496178378285824462139706851 744267567428736693209560277)
        ·
          refine ⟨17443771111611016247099069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 744267567428736693209560277 17443771111611016247099069)
          ·
            refine ⟨6541414166854131092662151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17443771111611016247099069 6541414166854131092662151)
            ·
              refine ⟨9812121250281196638993227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6541414166854131092662151 9812121250281196638993227)
              ·
                refine ⟨14718181875421794958489841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9812121250281196638993227 14718181875421794958489841)
                ·
                  refine ⟨11038636406566346218867381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14718181875421794958489841 11038636406566346218867381)
                  ·
                    refine ⟨1034872163115594958018817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11038636406566346218867381 1034872163115594958018817)
                    ·
                      rfl

theorem cell23_6046219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 5].length) (baseStart_6046219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046219 prefixEnd_6046219 := by exact prefixLift 6046219
  have htrace : WordTrace (prefixWord ++ tailWord_6046219) baseStart_6046219 baseEnd_6046219 := by
    simpa [prefixWord, tailWord_6046219, baseEnd_6046219] using wordTrace_append hprefix tailTrace_6046219
  have hstable : (prefixWord ++ tailWord_6046219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046219).length < 2 ^ (prefixWord ++ tailWord_6046219).sum := by decide
  have hdescent : baseEnd_6046219 < baseStart_6046219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046225 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 5]
def baseStart_6046225 : Nat := 118140960795 + 6046225 * 2 ^ 59
def prefixEnd_6046225 : Nat := 4983230072969 + 3 ^ 40 * 6046225 * 2
def baseEnd_6046225 : Nat := 3104619570230711850581423

theorem tailTrace_6046225 : CollatzResearch.WordTrace tailWord_6046225 prefixEnd_6046225 3104619570230711850581423 := by
  unfold tailWord_6046225
  simp only [CollatzResearch.WordTrace]
  refine ⟨220523942520566912864588129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147015961680377941909725419 220523942520566912864588129)
  ·
    refine ⟨165392956890425184648441097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220523942520566912864588129 165392956890425184648441097)
    ·
      refine ⟨124044717667818888486330823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165392956890425184648441097 124044717667818888486330823)
      ·
        refine ⟨186067076501728332729496235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124044717667818888486330823 186067076501728332729496235)
        ·
          refine ⟨279100614752592499094244353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186067076501728332729496235 279100614752592499094244353)
          ·
            refine ⟨209325461064444374320683265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279100614752592499094244353 209325461064444374320683265)
            ·
              refine ⟨156994095798333280740512449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209325461064444374320683265 156994095798333280740512449)
              ·
                refine ⟨117745571848749960555384337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156994095798333280740512449 117745571848749960555384337)
                ·
                  refine ⟨88309178886562470416538253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117745571848749960555384337 88309178886562470416538253)
                  ·
                    refine ⟨33115942082460926406201845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88309178886562470416538253 33115942082460926406201845)
                    ·
                      refine ⟨3104619570230711850581423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33115942082460926406201845 3104619570230711850581423)
                      ·
                        rfl

theorem cell23_6046225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_6046225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046225 prefixEnd_6046225 := by exact prefixLift 6046225
  have htrace : WordTrace (prefixWord ++ tailWord_6046225) baseStart_6046225 baseEnd_6046225 := by
    simpa [prefixWord, tailWord_6046225, baseEnd_6046225] using wordTrace_append hprefix tailTrace_6046225
  have hstable : (prefixWord ++ tailWord_6046225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046225).length < 2 ^ (prefixWord ++ tailWord_6046225).sum := by decide
  have hdescent : baseEnd_6046225 < baseStart_6046225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046235 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 4]
def baseStart_6046235 : Nat := 118140960795 + 6046235 * 2 ^ 59
def prefixEnd_6046235 : Nat := 4983230072969 + 3 ^ 40 * 6046235 * 2
def baseEnd_6046235 : Nat := 3104624705037256811456377

theorem tailTrace_6046235 : CollatzResearch.WordTrace tailWord_6046235 prefixEnd_6046235 3104624705037256811456377 := by
  unfold tailWord_6046235
  simp only [CollatzResearch.WordTrace]
  refine ⟨220524307250530684572452159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147016204833687123048301439 220524307250530684572452159)
  ·
    refine ⟨330786460875796026858678239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220524307250530684572452159 330786460875796026858678239)
    ·
      refine ⟨496179691313694040288017359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330786460875796026858678239 496179691313694040288017359)
      ·
        refine ⟨744269536970541060432026039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496179691313694040288017359 744269536970541060432026039)
        ·
          refine ⟨1116404305455811590648039059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744269536970541060432026039 1116404305455811590648039059)
          ·
            refine ⟨1674606458183717385972058589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116404305455811590648039059 1674606458183717385972058589)
            ·
              refine ⟨627977421818894019739521971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1674606458183717385972058589 627977421818894019739521971)
              ·
                refine ⟨941966132728341029609282957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627977421818894019739521971 941966132728341029609282957)
                ·
                  refine ⟨353237299773127886103481109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 941966132728341029609282957 353237299773127886103481109)
                  ·
                    refine ⟨16557998426865369661100677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 353237299773127886103481109 16557998426865369661100677)
                    ·
                      refine ⟨3104624705037256811456377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16557998426865369661100677 3104624705037256811456377)
                      ·
                        rfl

theorem cell23_6046235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 4].length) (baseStart_6046235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046235 prefixEnd_6046235 := by exact prefixLift 6046235
  have htrace : WordTrace (prefixWord ++ tailWord_6046235) baseStart_6046235 baseEnd_6046235 := by
    simpa [prefixWord, tailWord_6046235, baseEnd_6046235] using wordTrace_append hprefix tailTrace_6046235
  have hstable : (prefixWord ++ tailWord_6046235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046235).length < 2 ^ (prefixWord ++ tailWord_6046235).sum := by decide
  have hdescent : baseEnd_6046235 < baseStart_6046235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046275 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 2, 9]
def baseStart_6046275 : Nat := 118140960795 + 6046275 * 2 ^ 59
def prefixEnd_6046275 : Nat := 4983230072969 + 3 ^ 40 * 6046275 * 2
def baseEnd_6046275 : Nat := 1034881748087812218318731

theorem tailTrace_6046275 : CollatzResearch.WordTrace tailWord_6046275 prefixEnd_6046275 1034881748087812218318731 := by
  unfold tailWord_6046275
  simp only [CollatzResearch.WordTrace]
  refine ⟨220525766170385771403908279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147017177446923847602605519 220525766170385771403908279)
  ·
    refine ⟨330788649255578657105862419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220525766170385771403908279 330788649255578657105862419)
    ·
      refine ⟨496182973883367985658793629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330788649255578657105862419 496182973883367985658793629)
      ·
        refine ⟨186068615206262994622047611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 496182973883367985658793629 186068615206262994622047611)
        ·
          refine ⟨279102922809394491933071417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186068615206262994622047611 279102922809394491933071417)
          ·
            refine ⟨209327192107045868949803563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279102922809394491933071417 209327192107045868949803563)
            ·
              refine ⟨313990788160568803424705345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209327192107045868949803563 313990788160568803424705345)
              ·
                refine ⟨235493091120426602568529009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313990788160568803424705345 235493091120426602568529009)
                ·
                  refine ⟨176619818340319951926396757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235493091120426602568529009 176619818340319951926396757)
                  ·
                    refine ⟨1034881748087812218318731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 176619818340319951926396757 1034881748087812218318731)
                    ·
                      rfl

theorem cell23_6046275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 9].length) (baseStart_6046275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046275 prefixEnd_6046275 := by exact prefixLift 6046275
  have htrace : WordTrace (prefixWord ++ tailWord_6046275) baseStart_6046275 baseEnd_6046275 := by
    simpa [prefixWord, tailWord_6046275, baseEnd_6046275] using wordTrace_append hprefix tailTrace_6046275
  have hstable : (prefixWord ++ tailWord_6046275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046275).length < 2 ^ (prefixWord ++ tailWord_6046275).sum := by decide
  have hdescent : baseEnd_6046275 < baseStart_6046275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046300 : List Nat := [2, 2, 4, 1, 3, 1, 3, 2, 1, 4]
def baseStart_6046300 : Nat := 118140960795 + 6046300 * 2 ^ 59
def prefixEnd_6046300 : Nat := 4983230072969 + 3 ^ 40 * 6046300 * 2
def baseEnd_6046300 : Nat := 1034886027093266352381193

theorem tailTrace_6046300 : CollatzResearch.WordTrace tailWord_6046300 prefixEnd_6046300 1034886027093266352381193 := by
  unfold tailWord_6046300
  simp only [CollatzResearch.WordTrace]
  refine ⟨110263338997647600336784177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147017785330196800449045569 110263338997647600336784177)
  ·
    refine ⟨82697504248235700252588133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110263338997647600336784177 82697504248235700252588133)
    ·
      refine ⟨15505782046544193797360275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82697504248235700252588133 15505782046544193797360275)
      ·
        refine ⟨23258673069816290696040413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15505782046544193797360275 23258673069816290696040413)
        ·
          refine ⟨8722002401181109011015155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23258673069816290696040413 8722002401181109011015155)
          ·
            refine ⟨13083003601771663516522733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8722002401181109011015155 13083003601771663516522733)
            ·
              refine ⟨4906126350664373818696025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13083003601771663516522733 4906126350664373818696025)
              ·
                refine ⟨3679594762998280364022019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4906126350664373818696025 3679594762998280364022019)
                ·
                  refine ⟨5519392144497420546033029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3679594762998280364022019 5519392144497420546033029)
                  ·
                    refine ⟨1034886027093266352381193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5519392144497420546033029 1034886027093266352381193)
                    ·
                      rfl

theorem cell23_6046300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_6046300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046300 prefixEnd_6046300 := by exact prefixLift 6046300
  have htrace : WordTrace (prefixWord ++ tailWord_6046300) baseStart_6046300 baseEnd_6046300 := by
    simpa [prefixWord, tailWord_6046300, baseEnd_6046300] using wordTrace_append hprefix tailTrace_6046300
  have hstable : (prefixWord ++ tailWord_6046300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046300).length < 2 ^ (prefixWord ++ tailWord_6046300).sum := by decide
  have hdescent : baseEnd_6046300 < baseStart_6046300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046326 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_6046326 : Nat := 118140960795 + 6046326 * 2 ^ 59
def prefixEnd_6046326 : Nat := 4983230072969 + 3 ^ 40 * 6046326 * 2
def baseEnd_6046326 : Nat := 1034890477258938651806153

theorem tailTrace_6046326 : CollatzResearch.WordTrace tailWord_6046326 prefixEnd_6046326 1034890477258938651806153 := by
  unfold tailWord_6046326
  simp only [CollatzResearch.WordTrace]
  refine ⟨13782976643325062944625927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147018417528800671409343221 13782976643325062944625927)
  ·
    refine ⟨20674464964987594416938891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13782976643325062944625927 20674464964987594416938891)
    ·
      refine ⟨31011697447481391625408337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20674464964987594416938891 31011697447481391625408337)
      ·
        refine ⟨23258773085611043719056253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31011697447481391625408337 23258773085611043719056253)
        ·
          refine ⟨8722039907104141394646095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23258773085611043719056253 8722039907104141394646095)
          ·
            refine ⟨13083059860656212091969143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8722039907104141394646095 13083059860656212091969143)
            ·
              refine ⟨19624589790984318137953715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13083059860656212091969143 19624589790984318137953715)
              ·
                refine ⟨29436884686476477206930573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19624589790984318137953715 29436884686476477206930573)
                ·
                  refine ⟨11038831757428678952598965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29436884686476477206930573 11038831757428678952598965)
                  ·
                    refine ⟨1034890477258938651806153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11038831757428678952598965 1034890477258938651806153)
                    ·
                      rfl

theorem cell23_6046326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_6046326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046326 prefixEnd_6046326 := by exact prefixLift 6046326
  have htrace : WordTrace (prefixWord ++ tailWord_6046326) baseStart_6046326 baseEnd_6046326 := by
    simpa [prefixWord, tailWord_6046326, baseEnd_6046326] using wordTrace_append hprefix tailTrace_6046326
  have hstable : (prefixWord ++ tailWord_6046326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046326).length < 2 ^ (prefixWord ++ tailWord_6046326).sum := by decide
  have hdescent : baseEnd_6046326 < baseStart_6046326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046329 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 3, 1, 4]
def baseStart_6046329 : Nat := 118140960795 + 6046329 * 2 ^ 59
def prefixEnd_6046329 : Nat := 4983230072969 + 3 ^ 40 * 6046329 * 2
def baseEnd_6046329 : Nat := 3104672972218779443680945

theorem tailTrace_6046329 : CollatzResearch.WordTrace tailWord_6046329 prefixEnd_6046329 3104672972218779443680945 := by
  unfold tailWord_6046329
  simp only [CollatzResearch.WordTrace]
  refine ⟨220527735712190138626374041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147018490474793425750916027 220527735712190138626374041)
  ·
    refine ⟨165395801784142603969780531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220527735712190138626374041 165395801784142603969780531)
    ·
      refine ⟨248093702676213905954670797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165395801784142603969780531 248093702676213905954670797)
      ·
        refine ⟨93035138503580214733001549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248093702676213905954670797 93035138503580214733001549)
        ·
          refine ⟨34888176938842580524875581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93035138503580214733001549 34888176938842580524875581)
          ·
            refine ⟨13083066352065967696828343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34888176938842580524875581 13083066352065967696828343)
            ·
              refine ⟨19624599528098951545242515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13083066352065967696828343 19624599528098951545242515)
              ·
                refine ⟨29436899292148427317863773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19624599528098951545242515 29436899292148427317863773)
                ·
                  refine ⟨11038837234555660244198915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29436899292148427317863773 11038837234555660244198915)
                  ·
                    refine ⟨16558255851833490366298373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11038837234555660244198915 16558255851833490366298373)
                    ·
                      refine ⟨3104672972218779443680945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16558255851833490366298373 3104672972218779443680945)
                      ·
                        rfl

theorem cell23_6046329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_6046329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046329 prefixEnd_6046329 := by exact prefixLift 6046329
  have htrace : WordTrace (prefixWord ++ tailWord_6046329) baseStart_6046329 baseEnd_6046329 := by
    simpa [prefixWord, tailWord_6046329, baseEnd_6046329] using wordTrace_append hprefix tailTrace_6046329
  have hstable : (prefixWord ++ tailWord_6046329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046329).length < 2 ^ (prefixWord ++ tailWord_6046329).sum := by decide
  have hdescent : baseEnd_6046329 < baseStart_6046329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046332 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_6046332 : Nat := 118140960795 + 6046332 * 2 ^ 59
def prefixEnd_6046332 : Nat := 4983230072969 + 3 ^ 40 * 6046332 * 2
def baseEnd_6046332 : Nat := 3104674512660742931943431

theorem tailTrace_6046332 : CollatzResearch.WordTrace tailWord_6046332 prefixEnd_6046332 3104674512660742931943431 := by
  unfold tailWord_6046332
  simp only [CollatzResearch.WordTrace]
  refine ⟨110263922565589635069366625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147018563420786180092488833 110263922565589635069366625)
  ·
    refine ⟨82697941924192226302024969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110263922565589635069366625 82697941924192226302024969)
    ·
      refine ⟨62023456443144169726518727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82697941924192226302024969 62023456443144169726518727)
      ·
        refine ⟨93035184664716254589778091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62023456443144169726518727 93035184664716254589778091)
        ·
          refine ⟨139552776997074381884667137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93035184664716254589778091 139552776997074381884667137)
          ·
            refine ⟨104664582747805786413500353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139552776997074381884667137 104664582747805786413500353)
            ·
              refine ⟨78498437060854339810125265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104664582747805786413500353 78498437060854339810125265)
              ·
                refine ⟨58873827795640754857593949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78498437060854339810125265 58873827795640754857593949)
                ·
                  refine ⟨22077685423365283071597731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58873827795640754857593949 22077685423365283071597731)
                  ·
                    refine ⟨33116528135047924607396597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22077685423365283071597731 33116528135047924607396597)
                    ·
                      refine ⟨3104674512660742931943431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33116528135047924607396597 3104674512660742931943431)
                      ·
                        rfl

theorem cell23_6046332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_6046332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046332 prefixEnd_6046332 := by exact prefixLift 6046332
  have htrace : WordTrace (prefixWord ++ tailWord_6046332) baseStart_6046332 baseEnd_6046332 := by
    simpa [prefixWord, tailWord_6046332, baseEnd_6046332] using wordTrace_append hprefix tailTrace_6046332
  have hstable : (prefixWord ++ tailWord_6046332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046332).length < 2 ^ (prefixWord ++ tailWord_6046332).sum := by decide
  have hdescent : baseEnd_6046332 < baseStart_6046332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046333 : List Nat := [1, 4, 1, 1, 5, 1, 2, 1, 2, 3, 2]
def baseStart_6046333 : Nat := 118140960795 + 6046333 * 2 ^ 59
def prefixEnd_6046333 : Nat := 4983230072969 + 3 ^ 40 * 6046333 * 2
def baseEnd_6046333 : Nat := 3104675026141397428030927

theorem tailTrace_6046333 : CollatzResearch.WordTrace tailWord_6046333 prefixEnd_6046333 3104675026141397428030927 := by
  unfold tailWord_6046333
  simp only [CollatzResearch.WordTrace]
  refine ⟨220527881604175647309519653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147018587736117098206346435 220527881604175647309519653)
  ·
    refine ⟨41348977800782933870534935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220527881604175647309519653 41348977800782933870534935)
    ·
      refine ⟨62023466701174400805802403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41348977800782933870534935 62023466701174400805802403)
      ·
        refine ⟨93035200051761601208703605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62023466701174400805802403 93035200051761601208703605)
        ·
          refine ⟨8722050004852650113315963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93035200051761601208703605 8722050004852650113315963)
          ·
            refine ⟨13083075007278975169973945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8722050004852650113315963 13083075007278975169973945)
            ·
              refine ⟨9812306255459231377480459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13083075007278975169973945 9812306255459231377480459)
              ·
                refine ⟨14718459383188847066220689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9812306255459231377480459 14718459383188847066220689)
                ·
                  refine ⟨11038844537391635299665517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14718459383188847066220689 11038844537391635299665517)
                  ·
                    refine ⟨4139566701521863237374569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11038844537391635299665517 4139566701521863237374569)
                    ·
                      refine ⟨3104675026141397428030927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4139566701521863237374569 3104675026141397428030927)
                      ·
                        rfl

theorem cell23_6046333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_6046333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046333 prefixEnd_6046333 := by exact prefixLift 6046333
  have htrace : WordTrace (prefixWord ++ tailWord_6046333) baseStart_6046333 baseEnd_6046333 := by
    simpa [prefixWord, tailWord_6046333, baseEnd_6046333] using wordTrace_append hprefix tailTrace_6046333
  have hstable : (prefixWord ++ tailWord_6046333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046333).length < 2 ^ (prefixWord ++ tailWord_6046333).sum := by decide
  have hdescent : baseEnd_6046333 < baseStart_6046333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046366 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_6046366 : Nat := 118140960795 + 6046366 * 2 ^ 59
def prefixEnd_6046366 : Nat := 4983230072969 + 3 ^ 40 * 6046366 * 2
def baseEnd_6046366 : Nat := 3104691971002995798918275

theorem tailTrace_6046366 : CollatzResearch.WordTrace tailWord_6046366 prefixEnd_6046366 3104691971002995798918275 := by
  unfold tailWord_6046366
  simp only [CollatzResearch.WordTrace]
  refine ⟨27566135651632011743183869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147019390142037395963647301 27566135651632011743183869)
  ·
    refine ⟨10337300869362004403693951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27566135651632011743183869 10337300869362004403693951)
    ·
      refine ⟨15505951304043006605540927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10337300869362004403693951 15505951304043006605540927)
      ·
        refine ⟨23258926956064509908311391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15505951304043006605540927 23258926956064509908311391)
        ·
          refine ⟨34888390434096764862467087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23258926956064509908311391 34888390434096764862467087)
          ·
            refine ⟨52332585651145147293700631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34888390434096764862467087 52332585651145147293700631)
            ·
              refine ⟨78498878476717720940550947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52332585651145147293700631 78498878476717720940550947)
              ·
                refine ⟨117748317715076581410826421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78498878476717720940550947 117748317715076581410826421)
                ·
                  refine ⟨11038904785788429507264977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117748317715076581410826421 11038904785788429507264977)
                  ·
                    refine ⟨8279178589341322130448733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11038904785788429507264977 8279178589341322130448733)
                    ·
                      refine ⟨3104691971002995798918275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8279178589341322130448733 3104691971002995798918275)
                      ·
                        rfl

theorem cell23_6046366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_6046366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046366 prefixEnd_6046366 := by exact prefixLift 6046366
  have htrace : WordTrace (prefixWord ++ tailWord_6046366) baseStart_6046366 baseEnd_6046366 := by
    simpa [prefixWord, tailWord_6046366, baseEnd_6046366] using wordTrace_append hprefix tailTrace_6046366
  have hstable : (prefixWord ++ tailWord_6046366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046366).length < 2 ^ (prefixWord ++ tailWord_6046366).sum := by decide
  have hdescent : baseEnd_6046366 < baseStart_6046366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046396 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 4, 1, 3]
def baseStart_6046396 : Nat := 118140960795 + 6046396 * 2 ^ 59
def prefixEnd_6046396 : Nat := 4983230072969 + 3 ^ 40 * 6046396 * 2
def baseEnd_6046396 : Nat := 3104707375422630681543137

theorem tailTrace_6046396 : CollatzResearch.WordTrace tailWord_6046396 prefixEnd_6046396 3104707375422630681543137 := by
  unfold tailWord_6046396
  simp only [CollatzResearch.WordTrace]
  refine ⟨110265089701473704534531521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147020119601964939379375361 110265089701473704534531521)
  ·
    refine ⟨82698817276105278400898641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110265089701473704534531521 82698817276105278400898641)
    ·
      refine ⟨62024112957078958800673981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82698817276105278400898641 62024112957078958800673981)
      ·
        refine ⟨23259042358904609550252743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62024112957078958800673981 23259042358904609550252743)
        ·
          refine ⟨34888563538356914325379115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23259042358904609550252743 34888563538356914325379115)
          ·
            refine ⟨52332845307535371488068673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34888563538356914325379115 52332845307535371488068673)
            ·
              refine ⟨39249633980651528616051505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52332845307535371488068673 39249633980651528616051505)
              ·
                refine ⟨29437225485488646462038629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39249633980651528616051505 29437225485488646462038629)
                ·
                  refine ⟨5519479778529121211632243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29437225485488646462038629 5519479778529121211632243)
                  ·
                    refine ⟨8279219667793681817448365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5519479778529121211632243 8279219667793681817448365)
                    ·
                      refine ⟨3104707375422630681543137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8279219667793681817448365 3104707375422630681543137)
                      ·
                        rfl

theorem cell23_6046396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_6046396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046396 prefixEnd_6046396 := by exact prefixLift 6046396
  have htrace : WordTrace (prefixWord ++ tailWord_6046396) baseStart_6046396 baseEnd_6046396 := by
    simpa [prefixWord, tailWord_6046396, baseEnd_6046396] using wordTrace_append hprefix tailTrace_6046396
  have hstable : (prefixWord ++ tailWord_6046396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046396).length < 2 ^ (prefixWord ++ tailWord_6046396).sum := by decide
  have hdescent : baseEnd_6046396 < baseStart_6046396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046440 : List Nat := [2, 1, 4, 1, 4, 1, 2, 2, 1, 3, 2]
def baseStart_6046440 : Nat := 118140960795 + 6046440 * 2 ^ 59
def prefixEnd_6046440 : Nat := 4983230072969 + 3 ^ 40 * 6046440 * 2
def baseEnd_6046440 : Nat := 3104729968571428509392935

theorem tailTrace_6046440 : CollatzResearch.WordTrace tailWord_6046440 prefixEnd_6046440 3104729968571428509392935 := by
  unfold tailWord_6046440
  simp only [CollatzResearch.WordTrace]
  refine ⟨110265892107394002291832387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147021189476525336389109849 110265892107394002291832387)
  ·
    refine ⟨165398838161091003437748581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110265892107394002291832387 165398838161091003437748581)
    ·
      refine ⟨31012282155204563144577859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165398838161091003437748581 31012282155204563144577859)
      ·
        refine ⟨46518423232806844716866789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31012282155204563144577859 46518423232806844716866789)
        ·
          refine ⟨8722204356151283384412523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46518423232806844716866789 8722204356151283384412523)
          ·
            refine ⟨13083306534226925076618785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8722204356151283384412523 13083306534226925076618785)
            ·
              refine ⟨9812479900670193807464089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13083306534226925076618785 9812479900670193807464089)
              ·
                refine ⟨7359359925502645355598067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9812479900670193807464089 7359359925502645355598067)
                ·
                  refine ⟨11039039888253968033397101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7359359925502645355598067 11039039888253968033397101)
                  ·
                    refine ⟨4139639958095238012523913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11039039888253968033397101 4139639958095238012523913)
                    ·
                      refine ⟨3104729968571428509392935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4139639958095238012523913 3104729968571428509392935)
                      ·
                        rfl

theorem cell23_6046440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_6046440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046440 prefixEnd_6046440 := by exact prefixLift 6046440
  have htrace : WordTrace (prefixWord ++ tailWord_6046440) baseStart_6046440 baseEnd_6046440 := by
    simpa [prefixWord, tailWord_6046440, baseEnd_6046440] using wordTrace_append hprefix tailTrace_6046440
  have hstable : (prefixWord ++ tailWord_6046440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046440).length < 2 ^ (prefixWord ++ tailWord_6046440).sum := by decide
  have hdescent : baseEnd_6046440 < baseStart_6046440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046469 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 4, 3, 3]
def baseStart_6046469 : Nat := 118140960795 + 6046469 * 2 ^ 59
def prefixEnd_6046469 : Nat := 4983230072969 + 3 ^ 40 * 6046469 * 2
def baseEnd_6046469 : Nat := 3104744859510408895930301

theorem tailTrace_6046469 : CollatzResearch.WordTrace tailWord_6046469 prefixEnd_6046469 3104744859510408895930301 := by
  unfold tailWord_6046469
  simp only [CollatzResearch.WordTrace]
  refine ⟨220532841931682942536470461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147021894621121961690980307 220532841931682942536470461)
  ·
    refine ⟨82699815724381103451176423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220532841931682942536470461 82699815724381103451176423)
    ·
      refine ⟨124049723586571655176764635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82699815724381103451176423 124049723586571655176764635)
      ·
        refine ⟨186074585379857482765146953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124049723586571655176764635 186074585379857482765146953)
        ·
          refine ⟨139555939034893112073860215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186074585379857482765146953 139555939034893112073860215)
          ·
            refine ⟨209333908552339668110790323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139555939034893112073860215 209333908552339668110790323)
            ·
              refine ⟨314000862828509502166185485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209333908552339668110790323 314000862828509502166185485)
              ·
                refine ⟨117750323560691063312319557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314000862828509502166185485 117750323560691063312319557)
                ·
                  refine ⟨22078185667629574371059917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117750323560691063312319557 22078185667629574371059917)
                  ·
                    refine ⟨8279319625361090389147469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22078185667629574371059917 8279319625361090389147469)
                    ·
                      refine ⟨3104744859510408895930301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8279319625361090389147469 3104744859510408895930301)
                      ·
                        rfl

theorem cell23_6046469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_6046469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046469 prefixEnd_6046469 := by exact prefixLift 6046469
  have htrace : WordTrace (prefixWord ++ tailWord_6046469) baseStart_6046469 baseEnd_6046469 := by
    simpa [prefixWord, tailWord_6046469, baseEnd_6046469] using wordTrace_append hprefix tailTrace_6046469
  have hstable : (prefixWord ++ tailWord_6046469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046469).length < 2 ^ (prefixWord ++ tailWord_6046469).sum := by decide
  have hdescent : baseEnd_6046469 < baseStart_6046469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046536 : List Nat := [2, 1, 3, 1, 1, 3, 2, 3, 3, 4]
def baseStart_6046536 : Nat := 118140960795 + 6046536 * 2 ^ 59
def prefixEnd_6046536 : Nat := 4983230072969 + 3 ^ 40 * 6046536 * 2
def baseEnd_6046536 : Nat := 1034926420904753377930831

theorem tailTrace_6046536 : CollatzResearch.WordTrace tailWord_6046536 prefixEnd_6046536 1034926420904753377930831 := by
  unfold tailWord_6046536
  simp only [CollatzResearch.WordTrace]
  refine ⟨110267642811220106489579731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147023523748293475319439641 110267642811220106489579731)
  ·
    refine ⟨165401464216830159734369597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110267642811220106489579731 165401464216830159734369597)
    ·
      refine ⟨62025549081311309900388599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165401464216830159734369597 62025549081311309900388599)
      ·
        refine ⟨93038323621966964850582899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62025549081311309900388599 93038323621966964850582899)
        ·
          refine ⟨139557485432950447275874349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93038323621966964850582899 139557485432950447275874349)
          ·
            refine ⟨52334057037356417728452881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139557485432950447275874349 52334057037356417728452881)
            ·
              refine ⟨39250542778017313296339661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52334057037356417728452881 39250542778017313296339661)
              ·
                refine ⟨14718953541756492486127373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39250542778017313296339661 14718953541756492486127373)
                ·
                  refine ⟨5519607578158684682297765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14718953541756492486127373 5519607578158684682297765)
                  ·
                    refine ⟨1034926420904753377930831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5519607578158684682297765 1034926420904753377930831)
                    ·
                      rfl

theorem cell23_6046536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_6046536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046536 prefixEnd_6046536 := by exact prefixLift 6046536
  have htrace : WordTrace (prefixWord ++ tailWord_6046536) baseStart_6046536 baseEnd_6046536 := by
    simpa [prefixWord, tailWord_6046536, baseEnd_6046536] using wordTrace_append hprefix tailTrace_6046536
  have hstable : (prefixWord ++ tailWord_6046536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046536).length < 2 ^ (prefixWord ++ tailWord_6046536).sum := by decide
  have hdescent : baseEnd_6046536 < baseStart_6046536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046546 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_6046546 : Nat := 118140960795 + 6046546 * 2 ^ 59
def prefixEnd_6046546 : Nat := 4983230072969 + 3 ^ 40 * 6046546 * 2
def baseEnd_6046546 : Nat := 3104784397520805094667447

theorem tailTrace_6046546 : CollatzResearch.WordTrace tailWord_6046546 prefixEnd_6046546 3104784397520805094667447 := by
  unfold tailWord_6046546
  simp only [CollatzResearch.WordTrace]
  refine ⟨55133912588100996171755873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147023766901602656458015661 55133912588100996171755873)
  ·
    refine ⟨41350434441075747128816905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55133912588100996171755873 41350434441075747128816905)
    ·
      refine ⟨31012825830806810346612679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41350434441075747128816905 31012825830806810346612679)
      ·
        refine ⟨46519238746210215519919019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31012825830806810346612679 46519238746210215519919019)
        ·
          refine ⟨69778858119315323279878529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46519238746210215519919019 69778858119315323279878529)
          ·
            refine ⟨52334143589486492459908897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69778858119315323279878529 52334143589486492459908897)
            ·
              refine ⟨39250607692114869344931673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52334143589486492459908897 39250607692114869344931673)
              ·
                refine ⟨29437955769086152008698755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39250607692114869344931673 29437955769086152008698755)
                ·
                  refine ⟨44156933653629228013048133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29437955769086152008698755 44156933653629228013048133)
                  ·
                    refine ⟨8279425060055480252446525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44156933653629228013048133 8279425060055480252446525)
                    ·
                      refine ⟨3104784397520805094667447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8279425060055480252446525 3104784397520805094667447)
                      ·
                        rfl

theorem cell23_6046546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_6046546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046546 prefixEnd_6046546 := by exact prefixLift 6046546
  have htrace : WordTrace (prefixWord ++ tailWord_6046546) baseStart_6046546 baseEnd_6046546 := by
    simpa [prefixWord, tailWord_6046546, baseEnd_6046546] using wordTrace_append hprefix tailTrace_6046546
  have hstable : (prefixWord ++ tailWord_6046546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046546).length < 2 ^ (prefixWord ++ tailWord_6046546).sum := by decide
  have hdescent : baseEnd_6046546 < baseStart_6046546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046563 : List Nat := [1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 3]
def baseStart_6046563 : Nat := 118140960795 + 6046563 * 2 ^ 59
def prefixEnd_6046563 : Nat := 4983230072969 + 3 ^ 40 * 6046563 * 2
def baseEnd_6046563 : Nat := 3104793126691931528154869

theorem tailTrace_6046563 : CollatzResearch.WordTrace tailWord_6046563 prefixEnd_6046563 3104793126691931528154869 := by
  unfold tailWord_6046563
  simp only [CollatzResearch.WordTrace]
  refine ⟨220536270393342396590392343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147024180262228264393594895 220536270393342396590392343)
  ·
    refine ⟨330804405590013594885588515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220536270393342396590392343 330804405590013594885588515)
    ·
      refine ⟨496206608385020392328382773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330804405590013594885588515 496206608385020392328382773)
      ·
        refine ⟨46519369536095661780785885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 496206608385020392328382773 46519369536095661780785885)
        ·
          refine ⟨17444763576035873167794707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46519369536095661780785885 17444763576035873167794707)
          ·
            refine ⟨26167145364053809751692061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17444763576035873167794707 26167145364053809751692061)
            ·
              refine ⟨9812679511520178656884523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26167145364053809751692061 9812679511520178656884523)
              ·
                refine ⟨14719019267280267985326785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9812679511520178656884523 14719019267280267985326785)
                ·
                  refine ⟨11039264450460200988995089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14719019267280267985326785 11039264450460200988995089)
                  ·
                    refine ⟨8279448337845150741746317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11039264450460200988995089 8279448337845150741746317)
                    ·
                      refine ⟨3104793126691931528154869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8279448337845150741746317 3104793126691931528154869)
                      ·
                        rfl

theorem cell23_6046563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_6046563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046563 prefixEnd_6046563 := by exact prefixLift 6046563
  have htrace : WordTrace (prefixWord ++ tailWord_6046563) baseStart_6046563 baseEnd_6046563 := by
    simpa [prefixWord, tailWord_6046563, baseEnd_6046563] using wordTrace_append hprefix tailTrace_6046563
  have hstable : (prefixWord ++ tailWord_6046563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046563).length < 2 ^ (prefixWord ++ tailWord_6046563).sum := by decide
  have hdescent : baseEnd_6046563 < baseStart_6046563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046613 : List Nat := [1, 3, 2, 1, 1, 5, 2, 2, 1, 5]
def baseStart_6046613 : Nat := 118140960795 + 6046613 * 2 ^ 59
def prefixEnd_6046613 : Nat := 4983230072969 + 3 ^ 40 * 6046613 * 2
def baseEnd_6046613 : Nat := 1034939600241552110843213

theorem tailTrace_6046613 : CollatzResearch.WordTrace tailWord_6046613 prefixEnd_6046613 1034939600241552110843213 := by
  unfold tailWord_6046613
  simp only [CollatzResearch.WordTrace]
  refine ⟨220538094043161255129712493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147025396028774170086474995 220538094043161255129712493)
  ·
    refine ⟨82701785266185470673642185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220538094043161255129712493 82701785266185470673642185)
    ·
      refine ⟨62026338949639103005231639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82701785266185470673642185 62026338949639103005231639)
      ·
        refine ⟨93039508424458654507847459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62026338949639103005231639 93039508424458654507847459)
        ·
          refine ⟨139559262636687981761771189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93039508424458654507847459 139559262636687981761771189)
          ·
            refine ⟨13083680872189498290166049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139559262636687981761771189 13083680872189498290166049)
            ·
              refine ⟨9812760654142123717624537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13083680872189498290166049 9812760654142123717624537)
              ·
                refine ⟨7359570490606592788218403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9812760654142123717624537 7359570490606592788218403)
                ·
                  refine ⟨11039355735909889182327605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7359570490606592788218403 11039355735909889182327605)
                  ·
                    refine ⟨1034939600241552110843213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11039355735909889182327605 1034939600241552110843213)
                    ·
                      rfl

theorem cell23_6046613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_6046613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046613 prefixEnd_6046613 := by exact prefixLift 6046613
  have htrace : WordTrace (prefixWord ++ tailWord_6046613) baseStart_6046613 baseEnd_6046613 := by
    simpa [prefixWord, tailWord_6046613, baseEnd_6046613] using wordTrace_append hprefix tailTrace_6046613
  have hstable : (prefixWord ++ tailWord_6046613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046613).length < 2 ^ (prefixWord ++ tailWord_6046613).sum := by decide
  have hdescent : baseEnd_6046613 < baseStart_6046613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046644 : List Nat := [2, 5, 2, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_6046644 : Nat := 118140960795 + 6046644 * 2 ^ 59
def prefixEnd_6046644 : Nat := 4983230072969 + 3 ^ 40 * 6046644 * 2
def baseEnd_6046644 : Nat := 3104834718624945711241997

theorem tailTrace_6046644 : CollatzResearch.WordTrace tailWord_6046644 prefixEnd_6046644 3104834718624945711241997 := by
  unfold tailWord_6046644
  simp only [CollatzResearch.WordTrace]
  refine ⟨110269612353024473712045493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147026149804032631616060657 110269612353024473712045493)
  ·
    refine ⟨10337776158096044410504265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110269612353024473712045493 10337776158096044410504265)
    ·
      refine ⟨7753332118572033307878199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10337776158096044410504265 7753332118572033307878199)
      ·
        refine ⟨11629998177858049961817299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7753332118572033307878199 11629998177858049961817299)
        ·
          refine ⟨17444997266787074942725949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11629998177858049961817299 17444997266787074942725949)
          ·
            refine ⟨6541873975045153103522231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17444997266787074942725949 6541873975045153103522231)
            ·
              refine ⟨9812810962567729655283347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6541873975045153103522231 9812810962567729655283347)
              ·
                refine ⟨14719216443851594482925021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9812810962567729655283347 14719216443851594482925021)
                ·
                  refine ⟨5519706166444347931096883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14719216443851594482925021 5519706166444347931096883)
                  ·
                    refine ⟨8279559249666521896645325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5519706166444347931096883 8279559249666521896645325)
                    ·
                      refine ⟨3104834718624945711241997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8279559249666521896645325 3104834718624945711241997)
                      ·
                        rfl

theorem cell23_6046644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_6046644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046644 prefixEnd_6046644 := by exact prefixLift 6046644
  have htrace : WordTrace (prefixWord ++ tailWord_6046644) baseStart_6046644 baseEnd_6046644 := by
    simpa [prefixWord, tailWord_6046644, baseEnd_6046644] using wordTrace_append hprefix tailTrace_6046644
  have hstable : (prefixWord ++ tailWord_6046644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046644).length < 2 ^ (prefixWord ++ tailWord_6046644).sum := by decide
  have hdescent : baseEnd_6046644 < baseStart_6046644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046656 : List Nat := [2, 1, 1, 2, 3, 4, 2, 8]
def baseStart_6046656 : Nat := 118140960795 + 6046656 * 2 ^ 59
def prefixEnd_6046656 : Nat := 4983230072969 + 3 ^ 40 * 6046656 * 2
def baseEnd_6046656 : Nat := 114994106681214802381183

theorem tailTrace_6046656 : CollatzResearch.WordTrace tailWord_6046656 prefixEnd_6046656 114994106681214802381183 := by
  unfold tailWord_6046656
  simp only [CollatzResearch.WordTrace]
  refine ⟨110269831191002736736763911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147026441588003648982351881 110269831191002736736763911)
  ·
    refine ⟨165404746786504105105145867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110269831191002736736763911 165404746786504105105145867)
    ·
      refine ⟨248107120179756157657718801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165404746786504105105145867 248107120179756157657718801)
      ·
        refine ⟨186080340134817118243289101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248107120179756157657718801 186080340134817118243289101)
        ·
          refine ⟨69780127550556419341233413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186080340134817118243289101 69780127550556419341233413)
          ·
            refine ⟨13083773915729328626481265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69780127550556419341233413 13083773915729328626481265)
            ·
              refine ⟨9812830436796996469860949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13083773915729328626481265 9812830436796996469860949)
              ·
                refine ⟨114994106681214802381183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9812830436796996469860949 114994106681214802381183)
                ·
                  rfl

theorem cell23_6046656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 8].length) (baseStart_6046656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046656 prefixEnd_6046656 := by exact prefixLift 6046656
  have htrace : WordTrace (prefixWord ++ tailWord_6046656) baseStart_6046656 baseEnd_6046656 := by
    simpa [prefixWord, tailWord_6046656, baseEnd_6046656] using wordTrace_append hprefix tailTrace_6046656
  have hstable : (prefixWord ++ tailWord_6046656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046656).length < 2 ^ (prefixWord ++ tailWord_6046656).sum := by decide
  have hdescent : baseEnd_6046656 < baseStart_6046656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046670 : List Nat := [4, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3]
def baseStart_6046670 : Nat := 118140960795 + 6046670 * 2 ^ 59
def prefixEnd_6046670 : Nat := 4983230072969 + 3 ^ 40 * 6046670 * 2
def baseEnd_6046670 : Nat := 3104848069121962609516877

theorem tailTrace_6046670 : CollatzResearch.WordTrace tailWord_6046670 prefixEnd_6046670 3104848069121962609516877 := by
  unfold tailWord_6046670
  simp only [CollatzResearch.WordTrace]
  refine ⟨27567521625494344233067183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147026782002636502576358309 27567521625494344233067183)
  ·
    refine ⟨41351282438241516349600775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27567521625494344233067183 41351282438241516349600775)
    ·
      refine ⟨62026923657362274524401163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41351282438241516349600775 62026923657362274524401163)
      ·
        refine ⟨93040385486043411786601745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62026923657362274524401163 93040385486043411786601745)
        ·
          refine ⟨69780289114532558839951309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93040385486043411786601745 69780289114532558839951309)
          ·
            refine ⟨26167608417949709564981741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69780289114532558839951309 26167608417949709564981741)
            ·
              refine ⟨9812853156731141086868153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26167608417949709564981741 9812853156731141086868153)
              ·
                refine ⟨7359639867548355815151115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9812853156731141086868153 7359639867548355815151115)
                ·
                  refine ⟨11039459801322533722726673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7359639867548355815151115 11039459801322533722726673)
                  ·
                    refine ⟨8279594850991900292045005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11039459801322533722726673 8279594850991900292045005)
                    ·
                      refine ⟨3104848069121962609516877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8279594850991900292045005 3104848069121962609516877)
                      ·
                        rfl

theorem cell23_6046670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_6046670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046670 prefixEnd_6046670 := by exact prefixLift 6046670
  have htrace : WordTrace (prefixWord ++ tailWord_6046670) baseStart_6046670 baseEnd_6046670 := by
    simpa [prefixWord, tailWord_6046670, baseEnd_6046670] using wordTrace_append hprefix tailTrace_6046670
  have hstable : (prefixWord ++ tailWord_6046670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046670).length < 2 ^ (prefixWord ++ tailWord_6046670).sum := by decide
  have hdescent : baseEnd_6046670 < baseStart_6046670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046687 : List Nat := [1, 1, 2, 3, 5, 1, 3, 1, 1, 2, 3]
def baseStart_6046687 : Nat := 118140960795 + 6046687 * 2 ^ 59
def prefixEnd_6046687 : Nat := 4983230072969 + 3 ^ 40 * 6046687 * 2
def baseEnd_6046687 : Nat := 3104856798293089043004299

theorem tailTrace_6046687 : CollatzResearch.WordTrace tailWord_6046687 prefixEnd_6046687 3104856798293089043004299 := by
  unfold tailWord_6046687
  simp only [CollatzResearch.WordTrace]
  refine ⟨220540793044893165767906315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147027195363262110511937543 220540793044893165767906315)
  ·
    refine ⟨330811189567339748651859473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220540793044893165767906315 330811189567339748651859473)
    ·
      refine ⟨248108392175504811488894605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330811189567339748651859473 248108392175504811488894605)
      ·
        refine ⟨93040647065814304308335477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248108392175504811488894605 93040647065814304308335477)
        ·
          refine ⟨8722560662420091028906451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93040647065814304308335477 8722560662420091028906451)
          ·
            refine ⟨13083840993630136543359677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8722560662420091028906451 13083840993630136543359677)
            ·
              refine ⟨4906440372611301203759879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13083840993630136543359677 4906440372611301203759879)
              ·
                refine ⟨7359660558916951805639819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4906440372611301203759879 7359660558916951805639819)
                ·
                  refine ⟨11039490838375427708459729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7359660558916951805639819 11039490838375427708459729)
                  ·
                    refine ⟨8279618128781570781344797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11039490838375427708459729 8279618128781570781344797)
                    ·
                      refine ⟨3104856798293089043004299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8279618128781570781344797 3104856798293089043004299)
                      ·
                        rfl

theorem cell23_6046687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_6046687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046687 prefixEnd_6046687 := by exact prefixLift 6046687
  have htrace : WordTrace (prefixWord ++ tailWord_6046687) baseStart_6046687 baseEnd_6046687 := by
    simpa [prefixWord, tailWord_6046687, baseEnd_6046687] using wordTrace_append hprefix tailTrace_6046687
  have hstable : (prefixWord ++ tailWord_6046687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046687).length < 2 ^ (prefixWord ++ tailWord_6046687).sum := by decide
  have hdescent : baseEnd_6046687 < baseStart_6046687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046696 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_6046696 : Nat := 118140960795 + 6046696 * 2 ^ 59
def prefixEnd_6046696 : Nat := 4983230072969 + 3 ^ 40 * 6046696 * 2
def baseEnd_6046696 : Nat := 3104861419618979507791757

theorem tailTrace_6046696 : CollatzResearch.WordTrace tailWord_6046696 prefixEnd_6046696 3104861419618979507791757 := by
  unfold tailWord_6046696
  simp only [CollatzResearch.WordTrace]
  refine ⟨110270560650930280152491971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147027414201240373536655961 110270560650930280152491971)
  ·
    refine ⟨165405840976395420228737957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110270560650930280152491971 165405840976395420228737957)
    ·
      refine ⟨31013595183074141292888367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165405840976395420228737957 31013595183074141292888367)
      ·
        refine ⟨46520392774611211939332551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31013595183074141292888367 46520392774611211939332551)
        ·
          refine ⟨69780589161916817908998827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46520392774611211939332551 69780589161916817908998827)
          ·
            refine ⟨104670883742875226863498241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69780589161916817908998827 104670883742875226863498241)
            ·
              refine ⟨78503162807156420147623681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104670883742875226863498241 78503162807156420147623681)
              ·
                refine ⟨58877372105367315110717761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78503162807156420147623681 58877372105367315110717761)
                ·
                  refine ⟨44158029079025486333038321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58877372105367315110717761 44158029079025486333038321)
                  ·
                    refine ⟨33118521809269114749778741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44158029079025486333038321 33118521809269114749778741)
                    ·
                      refine ⟨3104861419618979507791757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33118521809269114749778741 3104861419618979507791757)
                      ·
                        rfl

theorem cell23_6046696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_6046696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046696 prefixEnd_6046696 := by exact prefixLift 6046696
  have htrace : WordTrace (prefixWord ++ tailWord_6046696) baseStart_6046696 baseEnd_6046696 := by
    simpa [prefixWord, tailWord_6046696, baseEnd_6046696] using wordTrace_append hprefix tailTrace_6046696
  have hstable : (prefixWord ++ tailWord_6046696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046696).length < 2 ^ (prefixWord ++ tailWord_6046696).sum := by decide
  have hdescent : baseEnd_6046696 < baseStart_6046696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046716 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 1, 8]
def baseStart_6046716 : Nat := 118140960795 + 6046716 * 2 ^ 59
def prefixEnd_6046716 : Nat := 4983230072969 + 3 ^ 40 * 6046716 * 2
def baseEnd_6046716 : Nat := 1034957229744023143180555

theorem tailTrace_6046716 : CollatzResearch.WordTrace tailWord_6046716 prefixEnd_6046716 1034957229744023143180555 := by
  unfold tailWord_6046716
  simp only [CollatzResearch.WordTrace]
  refine ⟨110270925380894051860356001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147027900507858735813808001 110270925380894051860356001)
  ·
    refine ⟨82703194035670538895267001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110270925380894051860356001 82703194035670538895267001)
    ·
      refine ⟨62027395526752904171450251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82703194035670538895267001 62027395526752904171450251)
      ·
        refine ⟨93041093290129356257175377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62027395526752904171450251 93041093290129356257175377)
        ·
          refine ⟨69780819967597017192881533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93041093290129356257175377 69780819967597017192881533)
          ·
            refine ⟨26167807487848881447330575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69780819967597017192881533 26167807487848881447330575)
            ·
              refine ⟨39251711231773322170995863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26167807487848881447330575 39251711231773322170995863)
              ·
                refine ⟨58877566847659983256493795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39251711231773322170995863 58877566847659983256493795)
                ·
                  refine ⟨88316350271489974884740693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58877566847659983256493795 88316350271489974884740693)
                  ·
                    refine ⟨1034957229744023143180555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88316350271489974884740693 1034957229744023143180555)
                    ·
                      rfl

theorem cell23_6046716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_6046716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046716 prefixEnd_6046716 := by exact prefixLift 6046716
  have htrace : WordTrace (prefixWord ++ tailWord_6046716) baseStart_6046716 baseEnd_6046716 := by
    simpa [prefixWord, tailWord_6046716, baseEnd_6046716] using wordTrace_append hprefix tailTrace_6046716
  have hstable : (prefixWord ++ tailWord_6046716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046716).length < 2 ^ (prefixWord ++ tailWord_6046716).sum := by decide
  have hdescent : baseEnd_6046716 < baseStart_6046716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046736 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 4]
def baseStart_6046736 : Nat := 118140960795 + 6046736 * 2 ^ 59
def prefixEnd_6046736 : Nat := 4983230072969 + 3 ^ 40 * 6046736 * 2
def baseEnd_6046736 : Nat := 3104881958845159351291573

theorem tailTrace_6046736 : CollatzResearch.WordTrace tailWord_6046736 prefixEnd_6046736 3104881958845159351291573 := by
  unfold tailWord_6046736
  simp only [CollatzResearch.WordTrace]
  refine ⟨110271290110857823568220031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147028386814477098090960041 110271290110857823568220031)
  ·
    refine ⟨165406935166286735352330047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110271290110857823568220031 165406935166286735352330047)
    ·
      refine ⟨248110402749430103028495071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165406935166286735352330047 248110402749430103028495071)
      ·
        refine ⟨372165604124145154542742607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248110402749430103028495071 372165604124145154542742607)
        ·
          refine ⟨558248406186217731814113911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372165604124145154542742607 558248406186217731814113911)
          ·
            refine ⟨837372609279326597721170867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558248406186217731814113911 837372609279326597721170867)
            ·
              refine ⟨1256058913918989896581756301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837372609279326597721170867 1256058913918989896581756301)
              ·
                refine ⟨471022092719621211218158613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1256058913918989896581756301 471022092719621211218158613)
                ·
                  refine ⟨22079160596232244275851185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 471022092719621211218158613 22079160596232244275851185)
                  ·
                    refine ⟨16559370447174183206888389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22079160596232244275851185 16559370447174183206888389)
                    ·
                      refine ⟨3104881958845159351291573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16559370447174183206888389 3104881958845159351291573)
                      ·
                        rfl

theorem cell23_6046736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_6046736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046736 prefixEnd_6046736 := by exact prefixLift 6046736
  have htrace : WordTrace (prefixWord ++ tailWord_6046736) baseStart_6046736 baseEnd_6046736 := by
    simpa [prefixWord, tailWord_6046736, baseEnd_6046736] using wordTrace_append hprefix tailTrace_6046736
  have hstable : (prefixWord ++ tailWord_6046736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046736).length < 2 ^ (prefixWord ++ tailWord_6046736).sum := by decide
  have hdescent : baseEnd_6046736 < baseStart_6046736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046738 : List Nat := [3, 2, 5, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_6046738 : Nat := 118140960795 + 6046738 * 2 ^ 59
def prefixEnd_6046738 : Nat := 4983230072969 + 3 ^ 40 * 6046738 * 2
def baseEnd_6046738 : Nat := 3104882985806468343466565

theorem tailTrace_6046738 : CollatzResearch.WordTrace tailWord_6046738 prefixEnd_6046738 3104882985806468343466565 := by
  unfold tailWord_6046738
  simp only [CollatzResearch.WordTrace]
  refine ⟨55135663291927100369503217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147028435445138934318675245 55135663291927100369503217)
  ·
    refine ⟨41351747468945325277127413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55135663291927100369503217 41351747468945325277127413)
    ·
      refine ⟨3876726325213624244730695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41351747468945325277127413 3876726325213624244730695)
      ·
        refine ⟨5815089487820436367096043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3876726325213624244730695 5815089487820436367096043)
        ·
          refine ⟨8722634231730654550644065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5815089487820436367096043 8722634231730654550644065)
          ·
            refine ⟨6541975673797990912983049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8722634231730654550644065 6541975673797990912983049)
            ·
              refine ⟨4906481755348493184737287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6541975673797990912983049 4906481755348493184737287)
              ·
                refine ⟨7359722633022739777105931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4906481755348493184737287 7359722633022739777105931)
                ·
                  refine ⟨11039583949534109665658897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7359722633022739777105931 11039583949534109665658897)
                  ·
                    refine ⟨8279687962150582249244173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11039583949534109665658897 8279687962150582249244173)
                    ·
                      refine ⟨3104882985806468343466565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8279687962150582249244173 3104882985806468343466565)
                      ·
                        rfl

theorem cell23_6046738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_6046738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046738 prefixEnd_6046738 := by exact prefixLift 6046738
  have htrace : WordTrace (prefixWord ++ tailWord_6046738) baseStart_6046738 baseEnd_6046738 := by
    simpa [prefixWord, tailWord_6046738, baseEnd_6046738] using wordTrace_append hprefix tailTrace_6046738
  have hstable : (prefixWord ++ tailWord_6046738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046738).length < 2 ^ (prefixWord ++ tailWord_6046738).sum := by decide
  have hdescent : baseEnd_6046738 < baseStart_6046738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046744 : List Nat := [2, 1, 2, 3, 2, 4, 2, 1, 1, 3, 2]
def baseStart_6046744 : Nat := 118140960795 + 6046744 * 2 ^ 59
def prefixEnd_6046744 : Nat := 4983230072969 + 3 ^ 40 * 6046744 * 2
def baseEnd_6046744 : Nat := 3104886066690395319991537

theorem tailTrace_6046744 : CollatzResearch.WordTrace tailWord_6046744 prefixEnd_6046744 3104886066690395319991537 := by
  unfold tailWord_6046744
  simp only [CollatzResearch.WordTrace]
  refine ⟨110271436002843332251365643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147028581337124443001820857 110271436002843332251365643)
  ·
    refine ⟨165407154004264998377048465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110271436002843332251365643 165407154004264998377048465)
    ·
      refine ⟨124055365503198748782786349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165407154004264998377048465 124055365503198748782786349)
      ·
        refine ⟨46520762063699530793544881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124055365503198748782786349 46520762063699530793544881)
        ·
          refine ⟨34890571547774648095158661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46520762063699530793544881 34890571547774648095158661)
          ·
            refine ⟨6541982165207746517842249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34890571547774648095158661 6541982165207746517842249)
            ·
              refine ⟨4906486623905809888381687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6541982165207746517842249 4906486623905809888381687)
              ·
                refine ⟨7359729935858714832572531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4906486623905809888381687 7359729935858714832572531)
                ·
                  refine ⟨11039594903788072248858797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7359729935858714832572531 11039594903788072248858797)
                  ·
                    refine ⟨4139848088920527093322049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11039594903788072248858797 4139848088920527093322049)
                    ·
                      refine ⟨3104886066690395319991537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4139848088920527093322049 3104886066690395319991537)
                      ·
                        rfl

theorem cell23_6046744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_6046744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046744 prefixEnd_6046744 := by exact prefixLift 6046744
  have htrace : WordTrace (prefixWord ++ tailWord_6046744) baseStart_6046744 baseEnd_6046744 := by
    simpa [prefixWord, tailWord_6046744, baseEnd_6046744] using wordTrace_append hprefix tailTrace_6046744
  have hstable : (prefixWord ++ tailWord_6046744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046744).length < 2 ^ (prefixWord ++ tailWord_6046744).sum := by decide
  have hdescent : baseEnd_6046744 < baseStart_6046744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046746 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 9]
def baseStart_6046746 : Nat := 118140960795 + 6046746 * 2 ^ 59
def prefixEnd_6046746 : Nat := 4983230072969 + 3 ^ 40 * 6046746 * 2
def baseEnd_6046746 : Nat := 344987454850189368018503

theorem tailTrace_6046746 : CollatzResearch.WordTrace tailWord_6046746 prefixEnd_6046746 344987454850189368018503 := by
  unfold tailWord_6046746
  simp only [CollatzResearch.WordTrace]
  refine ⟨55135736237919854711076023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147028629967786279229536061 55135736237919854711076023)
  ·
    refine ⟨82703604356879782066614035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55135736237919854711076023 82703604356879782066614035)
    ·
      refine ⟨124055406535319673099921053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82703604356879782066614035 124055406535319673099921053)
      ·
        refine ⟨46520777450744877412470395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124055406535319673099921053 46520777450744877412470395)
        ·
          refine ⟨69781166176117316118705593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46520777450744877412470395 69781166176117316118705593)
          ·
            refine ⟨52335874632087987089029195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69781166176117316118705593 52335874632087987089029195)
            ·
              refine ⟨78503811948131980633543793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52335874632087987089029195 78503811948131980633543793)
              ·
                refine ⟨58877858961098985475157845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78503811948131980633543793 58877858961098985475157845)
                ·
                  refine ⟨344987454850189368018503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58877858961098985475157845 344987454850189368018503)
                  ·
                    rfl

theorem cell23_6046746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 9].length) (baseStart_6046746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046746 prefixEnd_6046746 := by exact prefixLift 6046746
  have htrace : WordTrace (prefixWord ++ tailWord_6046746) baseStart_6046746 baseEnd_6046746 := by
    simpa [prefixWord, tailWord_6046746, baseEnd_6046746] using wordTrace_append hprefix tailTrace_6046746
  have hstable : (prefixWord ++ tailWord_6046746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046746).length < 2 ^ (prefixWord ++ tailWord_6046746).sum := by decide
  have hdescent : baseEnd_6046746 < baseStart_6046746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046753 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_6046753 : Nat := 118140960795 + 6046753 * 2 ^ 59
def prefixEnd_6046753 : Nat := 4983230072969 + 3 ^ 40 * 6046753 * 2
def baseEnd_6046753 : Nat := 3104890688016285784778995

theorem tailTrace_6046753 : CollatzResearch.WordTrace tailWord_6046753 prefixEnd_6046753 3104890688016285784778995 := by
  unfold tailWord_6046753
  simp only [CollatzResearch.WordTrace]
  refine ⟨220543200262654059039808913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147028800175102706026539275 220543200262654059039808913)
  ·
    refine ⟨165407400196990544279856685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220543200262654059039808913 165407400196990544279856685)
    ·
      refine ⟨62027775073871454104946257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165407400196990544279856685 62027775073871454104946257)
      ·
        refine ⟨46520831305403590578709693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62027775073871454104946257 46520831305403590578709693)
        ·
          refine ⟨17445311739526346467016135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46520831305403590578709693 17445311739526346467016135)
          ·
            refine ⟨26167967609289519700524203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17445311739526346467016135 26167967609289519700524203)
            ·
              refine ⟨39251951413934279550786305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26167967609289519700524203 39251951413934279550786305)
              ·
                refine ⟨29438963560450709663089729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39251951413934279550786305 29438963560450709663089729)
                ·
                  refine ⟨22079222670338032247317297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29438963560450709663089729 22079222670338032247317297)
                  ·
                    refine ⟨16559417002753524185487973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22079222670338032247317297 16559417002753524185487973)
                    ·
                      refine ⟨3104890688016285784778995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16559417002753524185487973 3104890688016285784778995)
                      ·
                        rfl

theorem cell23_6046753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_6046753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046753 prefixEnd_6046753 := by exact prefixLift 6046753
  have htrace : WordTrace (prefixWord ++ tailWord_6046753) baseStart_6046753 baseEnd_6046753 := by
    simpa [prefixWord, tailWord_6046753, baseEnd_6046753] using wordTrace_append hprefix tailTrace_6046753
  have hstable : (prefixWord ++ tailWord_6046753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046753).length < 2 ^ (prefixWord ++ tailWord_6046753).sum := by decide
  have hdescent : baseEnd_6046753 < baseStart_6046753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046763 : List Nat := [1, 1, 1, 1, 2, 1, 5, 6, 5]
def baseStart_6046763 : Nat := 118140960795 + 6046763 * 2 ^ 59
def prefixEnd_6046763 : Nat := 4983230072969 + 3 ^ 40 * 6046763 * 2
def baseEnd_6046763 : Nat := 344988424758092305072661

theorem tailTrace_6046763 : CollatzResearch.WordTrace tailWord_6046763 prefixEnd_6046763 344988424758092305072661 := by
  unfold tailWord_6046763
  simp only [CollatzResearch.WordTrace]
  refine ⟨220543564992617830747672943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147029043328411887165115295 220543564992617830747672943)
  ·
    refine ⟨330815347488926746121509415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220543564992617830747672943 330815347488926746121509415)
    ·
      refine ⟨496223021233390119182264123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330815347488926746121509415 496223021233390119182264123)
      ·
        refine ⟨744334531850085178773396185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496223021233390119182264123 744334531850085178773396185)
        ·
          refine ⟨558250898887563884080047139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 744334531850085178773396185 558250898887563884080047139)
          ·
            refine ⟨837376348331345826120070709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558250898887563884080047139 837376348331345826120070709)
            ·
              refine ⟨78504032656063671198756629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 837376348331345826120070709 78504032656063671198756629)
              ·
                refine ⟨3679876530752984587441717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78504032656063671198756629 3679876530752984587441717)
                ·
                  refine ⟨344988424758092305072661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3679876530752984587441717 344988424758092305072661)
                  ·
                    rfl

theorem cell23_6046763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 5].length) (baseStart_6046763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046763 prefixEnd_6046763 := by exact prefixLift 6046763
  have htrace : WordTrace (prefixWord ++ tailWord_6046763) baseStart_6046763 baseEnd_6046763 := by
    simpa [prefixWord, tailWord_6046763, baseEnd_6046763] using wordTrace_append hprefix tailTrace_6046763
  have hstable : (prefixWord ++ tailWord_6046763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046763).length < 2 ^ (prefixWord ++ tailWord_6046763).sum := by decide
  have hdescent : baseEnd_6046763 < baseStart_6046763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046774 : List Nat := [5, 1, 2, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_6046774 : Nat := 118140960795 + 6046774 * 2 ^ 59
def prefixEnd_6046774 : Nat := 4983230072969 + 3 ^ 40 * 6046774 * 2
def baseEnd_6046774 : Nat := 3104901471110030202616399

theorem tailTrace_6046774 : CollatzResearch.WordTrace tailWord_6046774 prefixEnd_6046774 3104901471110030202616399 := by
  unfold tailWord_6046774
  simp only [CollatzResearch.WordTrace]
  refine ⟨13783997887223623726645211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147029310797051986417548917 13783997887223623726645211)
  ·
    refine ⟨20675996830835435589967817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13783997887223623726645211 20675996830835435589967817)
    ·
      refine ⟨15506997623126576692475863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20675996830835435589967817 15506997623126576692475863)
      ·
        refine ⟨23260496434689865038713795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15506997623126576692475863 23260496434689865038713795)
        ·
          refine ⟨34890744652034797558070693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23260496434689865038713795 34890744652034797558070693)
          ·
            refine ⟨6542014622256524542138255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34890744652034797558070693 6542014622256524542138255)
            ·
              refine ⟨9813021933384786813207383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6542014622256524542138255 9813021933384786813207383)
              ·
                refine ⟨14719532900077180219811075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9813021933384786813207383 14719532900077180219811075)
                ·
                  refine ⟨22079299350115770329716613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14719532900077180219811075 22079299350115770329716613)
                  ·
                    refine ⟨4139868628146706936821865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22079299350115770329716613 4139868628146706936821865)
                    ·
                      refine ⟨3104901471110030202616399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4139868628146706936821865 3104901471110030202616399)
                      ·
                        rfl

theorem cell23_6046774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_6046774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046774 prefixEnd_6046774 := by exact prefixLift 6046774
  have htrace : WordTrace (prefixWord ++ tailWord_6046774) baseStart_6046774 baseEnd_6046774 := by
    simpa [prefixWord, tailWord_6046774, baseEnd_6046774] using wordTrace_append hprefix tailTrace_6046774
  have hstable : (prefixWord ++ tailWord_6046774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046774).length < 2 ^ (prefixWord ++ tailWord_6046774).sum := by decide
  have hdescent : baseEnd_6046774 < baseStart_6046774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046797 : List Nat := [1, 6, 1, 1, 1, 2, 3, 3, 5]
def baseStart_6046797 : Nat := 118140960795 + 6046797 * 2 ^ 59
def prefixEnd_6046797 : Nat := 4983230072969 + 3 ^ 40 * 6046797 * 2
def baseEnd_6046797 : Nat := 344990364573898179180977

theorem tailTrace_6046797 : CollatzResearch.WordTrace tailWord_6046797 prefixEnd_6046797 344990364573898179180977 := by
  unfold tailWord_6046797
  simp only [CollatzResearch.WordTrace]
  refine ⟨220544805074494654554410645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147029870049663103036273763 220544805074494654554410645)
  ·
    refine ⟨10338037737866936932237999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 220544805074494654554410645 10338037737866936932237999)
    ·
      refine ⟨15507056606800405398356999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10338037737866936932237999 15507056606800405398356999)
      ·
        refine ⟨23260584910200608097535499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15507056606800405398356999 23260584910200608097535499)
        ·
          refine ⟨34890877365300912146303249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23260584910200608097535499 34890877365300912146303249)
          ·
            refine ⟨26168158023975684109727437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34890877365300912146303249 26168158023975684109727437)
            ·
              refine ⟨9813059258990881541147789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26168158023975684109727437 9813059258990881541147789)
              ·
                refine ⟨3679897222121580577930421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9813059258990881541147789 3679897222121580577930421)
                ·
                  refine ⟨344990364573898179180977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3679897222121580577930421 344990364573898179180977)
                  ·
                    rfl

theorem cell23_6046797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_6046797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046797 prefixEnd_6046797 := by exact prefixLift 6046797
  have htrace : WordTrace (prefixWord ++ tailWord_6046797) baseStart_6046797 baseEnd_6046797 := by
    simpa [prefixWord, tailWord_6046797, baseEnd_6046797] using wordTrace_append hprefix tailTrace_6046797
  have hstable : (prefixWord ++ tailWord_6046797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046797).length < 2 ^ (prefixWord ++ tailWord_6046797).sum := by decide
  have hdescent : baseEnd_6046797 < baseStart_6046797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046814 : List Nat := [4, 4, 1, 1, 1, 3, 1, 1, 7]
def baseStart_6046814 : Nat := 118140960795 + 6046814 * 2 ^ 59
def prefixEnd_6046814 : Nat := 4983230072969 + 3 ^ 40 * 6046814 * 2
def baseEnd_6046814 : Nat := 344991334481801116235135

theorem tailTrace_6046814 : CollatzResearch.WordTrace tailWord_6046814 prefixEnd_6046814 344991334481801116235135 := by
  unfold tailWord_6046814
  simp only [CollatzResearch.WordTrace]
  refine ⟨27568178139429133307222437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147030283410288710971852997 27568178139429133307222437)
  ·
    refine ⟨5169033401142962495104207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27568178139429133307222437 5169033401142962495104207)
    ·
      refine ⟨7753550101714443742656311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5169033401142962495104207 7753550101714443742656311)
      ·
        refine ⟨11630325152571665613984467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7753550101714443742656311 11630325152571665613984467)
        ·
          refine ⟨17445487728857498420976701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11630325152571665613984467 17445487728857498420976701)
          ·
            refine ⟨6542057898321561907866263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17445487728857498420976701 6542057898321561907866263)
            ·
              refine ⟨9813086847482342861799395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6542057898321561907866263 9813086847482342861799395)
              ·
                refine ⟨14719630271223514292699093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9813086847482342861799395 14719630271223514292699093)
                ·
                  refine ⟨344991334481801116235135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14719630271223514292699093 344991334481801116235135)
                  ·
                    rfl

theorem cell23_6046814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_6046814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046814 prefixEnd_6046814 := by exact prefixLift 6046814
  have htrace : WordTrace (prefixWord ++ tailWord_6046814) baseStart_6046814 baseEnd_6046814 := by
    simpa [prefixWord, tailWord_6046814, baseEnd_6046814] using wordTrace_append hprefix tailTrace_6046814
  have hstable : (prefixWord ++ tailWord_6046814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046814).length < 2 ^ (prefixWord ++ tailWord_6046814).sum := by decide
  have hdescent : baseEnd_6046814 < baseStart_6046814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046833 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 1, 4, 3]
def baseStart_6046833 : Nat := 118140960795 + 6046833 * 2 ^ 59
def prefixEnd_6046833 : Nat := 4983230072969 + 3 ^ 40 * 6046833 * 2
def baseEnd_6046833 : Nat := 3104931766468645471778627

theorem tailTrace_6046833 : CollatzResearch.WordTrace tailWord_6046833 prefixEnd_6046833 3104931766468645471778627 := by
  unfold tailWord_6046833
  simp only [CollatzResearch.WordTrace]
  refine ⟨220546118102364232702721153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147030745401576155135147435 220546118102364232702721153)
  ·
    refine ⟨165409588576773174527040865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220546118102364232702721153 165409588576773174527040865)
    ·
      refine ⟨124057191432579880895280649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165409588576773174527040865 124057191432579880895280649)
      ·
        refine ⟨93042893574434910671460487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124057191432579880895280649 93042893574434910671460487)
        ·
          refine ⟨139564340361652366007190731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93042893574434910671460487 139564340361652366007190731)
          ·
            refine ⟨209346510542478549010786097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139564340361652366007190731 209346510542478549010786097)
            ·
              refine ⟨157009882906858911758089573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209346510542478549010786097 157009882906858911758089573)
              ·
                refine ⟨29439353045036045954641795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157009882906858911758089573 29439353045036045954641795)
                ·
                  refine ⟨44159029567554068931962693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29439353045036045954641795 44159029567554068931962693)
                  ·
                    refine ⟨8279818043916387924743005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44159029567554068931962693 8279818043916387924743005)
                    ·
                      refine ⟨3104931766468645471778627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8279818043916387924743005 3104931766468645471778627)
                      ·
                        rfl

theorem cell23_6046833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_6046833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046833 prefixEnd_6046833 := by exact prefixLift 6046833
  have htrace : WordTrace (prefixWord ++ tailWord_6046833) baseStart_6046833 baseEnd_6046833 := by
    simpa [prefixWord, tailWord_6046833, baseEnd_6046833] using wordTrace_append hprefix tailTrace_6046833
  have hstable : (prefixWord ++ tailWord_6046833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046833).length < 2 ^ (prefixWord ++ tailWord_6046833).sum := by decide
  have hdescent : baseEnd_6046833 < baseStart_6046833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046874 : List Nat := [3, 1, 1, 5, 1, 2, 1, 4, 1, 4]
def baseStart_6046874 : Nat := 118140960795 + 6046874 * 2 ^ 59
def prefixEnd_6046874 : Nat := 4983230072969 + 3 ^ 40 * 6046874 * 2
def baseEnd_6046874 : Nat := 1034984273058493270455313

theorem tailTrace_6046874 : CollatzResearch.WordTrace tailWord_6046874 prefixEnd_6046874 1034984273058493270455313 := by
  unfold tailWord_6046874
  simp only [CollatzResearch.WordTrace]
  refine ⟨55136903373803924176240919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147031742330143797803309117 55136903373803924176240919)
  ·
    refine ⟨82705355060705886264361379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55136903373803924176240919 82705355060705886264361379)
    ·
      refine ⟨124058032591058829396542069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82705355060705886264361379 124058032591058829396542069)
      ·
        refine ⟨11630440555411765255925819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124058032591058829396542069 11630440555411765255925819)
        ·
          refine ⟨17445660833117647883888729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11630440555411765255925819 17445660833117647883888729)
          ·
            refine ⟨13084245624838235912916547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17445660833117647883888729 13084245624838235912916547)
            ·
              refine ⟨19626368437257353869374821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13084245624838235912916547 19626368437257353869374821)
              ·
                refine ⟨3679944081985753850507779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19626368437257353869374821 3679944081985753850507779)
                ·
                  refine ⟨5519916122978630775761669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3679944081985753850507779 5519916122978630775761669)
                  ·
                    refine ⟨1034984273058493270455313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5519916122978630775761669 1034984273058493270455313)
                    ·
                      rfl

theorem cell23_6046874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 1, 4].length) (baseStart_6046874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046874 prefixEnd_6046874 := by exact prefixLift 6046874
  have htrace : WordTrace (prefixWord ++ tailWord_6046874) baseStart_6046874 baseEnd_6046874 := by
    simpa [prefixWord, tailWord_6046874, baseEnd_6046874] using wordTrace_append hprefix tailTrace_6046874
  have hstable : (prefixWord ++ tailWord_6046874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046874).length < 2 ^ (prefixWord ++ tailWord_6046874).sum := by decide
  have hdescent : baseEnd_6046874 < baseStart_6046874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046897 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 5, 1, 3]
def baseStart_6046897 : Nat := 118140960795 + 6046897 * 2 ^ 59
def prefixEnd_6046897 : Nat := 4983230072969 + 3 ^ 40 * 6046897 * 2
def baseEnd_6046897 : Nat := 3104964629230533221378333

theorem tailTrace_6046897 : CollatzResearch.WordTrace tailWord_6046897 prefixEnd_6046897 3104964629230533221378333 := by
  unfold tailWord_6046897
  simp only [CollatzResearch.WordTrace]
  refine ⟨220548452374132371633050945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147032301582754914422033963 220548452374132371633050945)
  ·
    refine ⟨165411339280599278724788209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220548452374132371633050945 165411339280599278724788209)
    ·
      refine ⟨124058504460449459043591157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165411339280599278724788209 124058504460449459043591157)
      ·
        refine ⟨11630484793167136785336671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124058504460449459043591157 11630484793167136785336671)
        ·
          refine ⟨17445727189750705178005007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11630484793167136785336671 17445727189750705178005007)
          ·
            refine ⟨26168590784626057767007511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17445727189750705178005007 26168590784626057767007511)
            ·
              refine ⟨39252886176939086650511267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26168590784626057767007511 39252886176939086650511267)
              ·
                refine ⟨58879329265408629975766901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39252886176939086650511267 58879329265408629975766901)
                ·
                  refine ⟨5519937118632059060228147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58879329265408629975766901 5519937118632059060228147)
                  ·
                    refine ⟨8279905677948088590342221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5519937118632059060228147 8279905677948088590342221)
                    ·
                      refine ⟨3104964629230533221378333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8279905677948088590342221 3104964629230533221378333)
                      ·
                        rfl

theorem cell23_6046897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_6046897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046897 prefixEnd_6046897 := by exact prefixLift 6046897
  have htrace : WordTrace (prefixWord ++ tailWord_6046897) baseStart_6046897 baseEnd_6046897 := by
    simpa [prefixWord, tailWord_6046897, baseEnd_6046897] using wordTrace_append hprefix tailTrace_6046897
  have hstable : (prefixWord ++ tailWord_6046897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046897).length < 2 ^ (prefixWord ++ tailWord_6046897).sum := by decide
  have hdescent : baseEnd_6046897 < baseStart_6046897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046954 : List Nat := [3, 1, 3, 1, 1, 3, 2, 2, 3, 2, 2]
def baseStart_6046954 : Nat := 118140960795 + 6046954 * 2 ^ 59
def prefixEnd_6046954 : Nat := 4983230072969 + 3 ^ 40 * 6046954 * 2
def baseEnd_6046954 : Nat := 3104993897627839498365571

theorem tailTrace_6046954 : CollatzResearch.WordTrace tailWord_6046954 prefixEnd_6046954 3104993897627839498365571 := by
  unfold tailWord_6046954
  simp only [CollatzResearch.WordTrace]
  refine ⟨55137632833731467591968979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147033687556617246911917277 55137632833731467591968979)
  ·
    refine ⟨82706449250597201387953469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55137632833731467591968979 82706449250597201387953469)
    ·
      refine ⟨31014918468973950520482551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82706449250597201387953469 31014918468973950520482551)
      ·
        refine ⟨46522377703460925780723827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31014918468973950520482551 46522377703460925780723827)
        ·
          refine ⟨69783566555191388671085741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46522377703460925780723827 69783566555191388671085741)
          ·
            refine ⟨26168837458196770751657153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69783566555191388671085741 26168837458196770751657153)
            ·
              refine ⟨19626628093647578063742865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26168837458196770751657153 19626628093647578063742865)
              ·
                refine ⟨14719971070235683547807149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19626628093647578063742865 14719971070235683547807149)
                ·
                  refine ⟨5519989151338381330427681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14719971070235683547807149 5519989151338381330427681)
                  ·
                    refine ⟨4139991863503785997820761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5519989151338381330427681 4139991863503785997820761)
                    ·
                      refine ⟨3104993897627839498365571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4139991863503785997820761 3104993897627839498365571)
                      ·
                        rfl

theorem cell23_6046954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_6046954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046954 prefixEnd_6046954 := by exact prefixLift 6046954
  have htrace : WordTrace (prefixWord ++ tailWord_6046954) baseStart_6046954 baseEnd_6046954 := by
    simpa [prefixWord, tailWord_6046954, baseEnd_6046954] using wordTrace_append hprefix tailTrace_6046954
  have hstable : (prefixWord ++ tailWord_6046954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046954).length < 2 ^ (prefixWord ++ tailWord_6046954).sum := by decide
  have hdescent : baseEnd_6046954 < baseStart_6046954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046970 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3]
def baseStart_6046970 : Nat := 118140960795 + 6046970 * 2 ^ 59
def prefixEnd_6046970 : Nat := 4983230072969 + 3 ^ 40 * 6046970 * 2
def baseEnd_6046970 : Nat := 3105002113318311435765497

theorem tailTrace_6046970 : CollatzResearch.WordTrace tailWord_6046970 prefixEnd_6046970 3105002113318311435765497 := by
  unfold tailWord_6046970
  simp only [CollatzResearch.WordTrace]
  refine ⟨55137778725716976275114591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147034076601911936733638909 55137778725716976275114591)
  ·
    refine ⟨82706668088575464412671887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55137778725716976275114591 82706668088575464412671887)
    ·
      refine ⟨124060002132863196619007831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82706668088575464412671887 124060002132863196619007831)
      ·
        refine ⟨186090003199294794928511747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124060002132863196619007831 186090003199294794928511747)
        ·
          refine ⟨279135004798942192392767621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186090003199294794928511747 279135004798942192392767621)
          ·
            refine ⟨52337813399801661073643929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 279135004798942192392767621 52337813399801661073643929)
            ·
              refine ⟨39253360049851245805232947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52337813399801661073643929 39253360049851245805232947)
              ·
                refine ⟨58880040074776868707849421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39253360049851245805232947 58880040074776868707849421)
                ·
                  refine ⟨22080015028041325765443533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58880040074776868707849421 22080015028041325765443533)
                  ·
                    refine ⟨8280005635515497162041325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22080015028041325765443533 8280005635515497162041325)
                    ·
                      refine ⟨3105002113318311435765497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8280005635515497162041325 3105002113318311435765497)
                      ·
                        rfl

theorem cell23_6046970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_6046970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046970 prefixEnd_6046970 := by exact prefixLift 6046970
  have htrace : WordTrace (prefixWord ++ tailWord_6046970) baseStart_6046970 baseEnd_6046970 := by
    simpa [prefixWord, tailWord_6046970, baseEnd_6046970] using wordTrace_append hprefix tailTrace_6046970
  have hstable : (prefixWord ++ tailWord_6046970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046970).length < 2 ^ (prefixWord ++ tailWord_6046970).sum := by decide
  have hdescent : baseEnd_6046970 < baseStart_6046970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046973 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 3, 9]
def baseStart_6046973 : Nat := 118140960795 + 6046973 * 2 ^ 59
def prefixEnd_6046973 : Nat := 4983230072969 + 3 ^ 40 * 6046973 * 2
def baseEnd_6046973 : Nat := 1035001217920091641342661

theorem tailTrace_6046973 : CollatzResearch.WordTrace tailWord_6046973 prefixEnd_6046973 1035001217920091641342661 := by
  unfold tailWord_6046973
  simp only [CollatzResearch.WordTrace]
  refine ⟨220551224321857036612817573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147034149547904691075211715 220551224321857036612817573)
  ·
    refine ⟨41353354560348194364903295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220551224321857036612817573 41353354560348194364903295)
    ·
      refine ⟨62030031840522291547354943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41353354560348194364903295 62030031840522291547354943)
      ·
        refine ⟨93045047760783437321032415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62030031840522291547354943 93045047760783437321032415)
        ·
          refine ⟨139567571641175155981548623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93045047760783437321032415 139567571641175155981548623)
          ·
            refine ⟨209351357461762733972322935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139567571641175155981548623 209351357461762733972322935)
            ·
              refine ⟨314027036192644100958484403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209351357461762733972322935 314027036192644100958484403)
              ·
                refine ⟨471040554288966151437726605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314027036192644100958484403 471040554288966151437726605)
                ·
                  refine ⟨176640207858362306789147477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 471040554288966151437726605 176640207858362306789147477)
                  ·
                    refine ⟨1035001217920091641342661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 176640207858362306789147477 1035001217920091641342661)
                    ·
                      rfl

theorem cell23_6046973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_6046973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046973 prefixEnd_6046973 := by exact prefixLift 6046973
  have htrace : WordTrace (prefixWord ++ tailWord_6046973) baseStart_6046973 baseEnd_6046973 := by
    simpa [prefixWord, tailWord_6046973, baseEnd_6046973] using wordTrace_append hprefix tailTrace_6046973
  have hstable : (prefixWord ++ tailWord_6046973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046973).length < 2 ^ (prefixWord ++ tailWord_6046973).sum := by decide
  have hdescent : baseEnd_6046973 < baseStart_6046973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046974 : List Nat := [4, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_6046974 : Nat := 118140960795 + 6046974 * 2 ^ 59
def prefixEnd_6046974 : Nat := 4983230072969 + 3 ^ 40 * 6046974 * 2
def baseEnd_6046974 : Nat := 3105004167240929420115479

theorem tailTrace_6046974 : CollatzResearch.WordTrace tailWord_6046974 prefixEnd_6046974 3105004167240929420115479 := by
  unfold tailWord_6046974
  simp only [CollatzResearch.WordTrace]
  refine ⟨27568907599356676722950497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147034173863235609189069317 27568907599356676722950497)
  ·
    refine ⟨20676680699517507542212873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27568907599356676722950497 20676680699517507542212873)
    ·
      refine ⟨15507510524638130656659655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20676680699517507542212873 15507510524638130656659655)
      ·
        refine ⟨23261265786957195984989483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15507510524638130656659655 23261265786957195984989483)
        ·
          refine ⟨34891898680435793977484225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23261265786957195984989483 34891898680435793977484225)
          ·
            refine ⟨26168924010326845483113169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34891898680435793977484225 26168924010326845483113169)
            ·
              refine ⟨19626693007745134112334877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26168924010326845483113169 19626693007745134112334877)
              ·
                refine ⟨7360009877904425292125579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19626693007745134112334877 7360009877904425292125579)
                ·
                  refine ⟨11040014816856637938188369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7360009877904425292125579 11040014816856637938188369)
                  ·
                    refine ⟨8280011112642478453641277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11040014816856637938188369 8280011112642478453641277)
                    ·
                      refine ⟨3105004167240929420115479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8280011112642478453641277 3105004167240929420115479)
                      ·
                        rfl

theorem cell23_6046974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_6046974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046974 prefixEnd_6046974 := by exact prefixLift 6046974
  have htrace : WordTrace (prefixWord ++ tailWord_6046974) baseStart_6046974 baseEnd_6046974 := by
    simpa [prefixWord, tailWord_6046974, baseEnd_6046974] using wordTrace_append hprefix tailTrace_6046974
  have hstable : (prefixWord ++ tailWord_6046974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046974).length < 2 ^ (prefixWord ++ tailWord_6046974).sum := by decide
  have hdescent : baseEnd_6046974 < baseStart_6046974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046987 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 4, 1, 3]
def baseStart_6046987 : Nat := 118140960795 + 6046987 * 2 ^ 59
def prefixEnd_6046987 : Nat := 4983230072969 + 3 ^ 40 * 6046987 * 2
def baseEnd_6046987 : Nat := 3105010842489437869252919

theorem tailTrace_6046987 : CollatzResearch.WordTrace tailWord_6046987 prefixEnd_6046987 3105010842489437869252919 := by
  unfold tailWord_6046987
  simp only [CollatzResearch.WordTrace]
  refine ⟨220551734943806317003827215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147034489962537544669218143 220551734943806317003827215)
  ·
    refine ⟨330827602415709475505740823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220551734943806317003827215 330827602415709475505740823)
    ·
      refine ⟨496241403623564213258611235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330827602415709475505740823 496241403623564213258611235)
      ·
        refine ⟨744362105435346319887916853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496241403623564213258611235 744362105435346319887916853)
        ·
          refine ⟨69783947384563717489492205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 744362105435346319887916853 69783947384563717489492205)
          ·
            refine ⟨26168980269211394058559577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69783947384563717489492205 26168980269211394058559577)
            ·
              refine ⟨19626735201908545543919683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26168980269211394058559577 19626735201908545543919683)
              ·
                refine ⟨29440102802862818315879525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19626735201908545543919683 29440102802862818315879525)
                ·
                  refine ⟨5520019275536778434227411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29440102802862818315879525 5520019275536778434227411)
                  ·
                    refine ⟨8280028913305167651341117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5520019275536778434227411 8280028913305167651341117)
                    ·
                      refine ⟨3105010842489437869252919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8280028913305167651341117 3105010842489437869252919)
                      ·
                        rfl

theorem cell23_6046987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 1, 3].length) (baseStart_6046987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046987 prefixEnd_6046987 := by exact prefixLift 6046987
  have htrace : WordTrace (prefixWord ++ tailWord_6046987) baseStart_6046987 baseEnd_6046987 := by
    simpa [prefixWord, tailWord_6046987, baseEnd_6046987] using wordTrace_append hprefix tailTrace_6046987
  have hstable : (prefixWord ++ tailWord_6046987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046987).length < 2 ^ (prefixWord ++ tailWord_6046987).sum := by decide
  have hdescent : baseEnd_6046987 < baseStart_6046987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046988 : List Nat := [2, 2, 1, 2, 2, 4, 3, 2, 1, 2, 2]
def baseStart_6046988 : Nat := 118140960795 + 6046988 * 2 ^ 59
def prefixEnd_6046988 : Nat := 4983230072969 + 3 ^ 40 * 6046988 * 2
def baseEnd_6046988 : Nat := 3105011355970092365340415

theorem tailTrace_6046988 : CollatzResearch.WordTrace tailWord_6046988 prefixEnd_6046988 3105011355970092365340415 := by
  unfold tailWord_6046988
  simp only [CollatzResearch.WordTrace]
  refine ⟨110275885708401347087306809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147034514277868462783075745 110275885708401347087306809)
  ·
    refine ⟨82706914281301010315480107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110275885708401347087306809 82706914281301010315480107)
    ·
      refine ⟨124060371421951515473220161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82706914281301010315480107 124060371421951515473220161)
      ·
        refine ⟨93045278566463636604915121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124060371421951515473220161 93045278566463636604915121)
        ·
          refine ⟨69783958924847727453686341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93045278566463636604915121 69783958924847727453686341)
          ·
            refine ⟨13084492298408948897566189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69783958924847727453686341 13084492298408948897566189)
            ·
              refine ⟨4906684611903355836587321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13084492298408948897566189 4906684611903355836587321)
              ·
                refine ⟨3680013458927516877440491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4906684611903355836587321 3680013458927516877440491)
                ·
                  refine ⟨5520020188391275316160737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3680013458927516877440491 5520020188391275316160737)
                  ·
                    refine ⟨4140015141293456487120553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5520020188391275316160737 4140015141293456487120553)
                    ·
                      refine ⟨3105011355970092365340415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4140015141293456487120553 3105011355970092365340415)
                      ·
                        rfl

theorem cell23_6046988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 1, 2, 2].length) (baseStart_6046988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046988 prefixEnd_6046988 := by exact prefixLift 6046988
  have htrace : WordTrace (prefixWord ++ tailWord_6046988) baseStart_6046988 baseEnd_6046988 := by
    simpa [prefixWord, tailWord_6046988, baseEnd_6046988] using wordTrace_append hprefix tailTrace_6046988
  have hstable : (prefixWord ++ tailWord_6046988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046988).length < 2 ^ (prefixWord ++ tailWord_6046988).sum := by decide
  have hdescent : baseEnd_6046988 < baseStart_6046988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046994 : List Nat := [3, 2, 4, 2, 1, 1, 2, 8]
def baseStart_6046994 : Nat := 118140960795 + 6046994 * 2 ^ 59
def prefixEnd_6046994 : Nat := 4983230072969 + 3 ^ 40 * 6046994 * 2
def baseEnd_6046994 : Nat := 115000534698297012661681

theorem tailTrace_6046994 : CollatzResearch.WordTrace tailWord_6046994 prefixEnd_6046994 115000534698297012661681 := by
  unfold tailWord_6046994
  simp only [CollatzResearch.WordTrace]
  refine ⟨55137997563695239299833009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147034660169853971466221357 55137997563695239299833009)
  ·
    refine ⟨41353498172771429474874757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55137997563695239299833009 41353498172771429474874757)
    ·
      refine ⟨7753780907394643026539017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41353498172771429474874757 7753780907394643026539017)
      ·
        refine ⟨5815335680545982269904263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7753780907394643026539017 5815335680545982269904263)
        ·
          refine ⟨8723003520818973404856395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5815335680545982269904263 8723003520818973404856395)
          ·
            refine ⟨13084505281228460107284593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8723003520818973404856395 13084505281228460107284593)
            ·
              refine ⟨9813378960921345080463445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13084505281228460107284593 9813378960921345080463445)
              ·
                refine ⟨115000534698297012661681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9813378960921345080463445 115000534698297012661681)
                ·
                  rfl

theorem cell23_6046994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 8].length) (baseStart_6046994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046994 prefixEnd_6046994 := by exact prefixLift 6046994
  have htrace : WordTrace (prefixWord ++ tailWord_6046994) baseStart_6046994 baseEnd_6046994 := by
    simpa [prefixWord, tailWord_6046994, baseEnd_6046994] using wordTrace_append hprefix tailTrace_6046994
  have hstable : (prefixWord ++ tailWord_6046994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046994).length < 2 ^ (prefixWord ++ tailWord_6046994).sum := by decide
  have hdescent : baseEnd_6046994 < baseStart_6046994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6046997 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 3, 3, 2]
def baseStart_6046997 : Nat := 118140960795 + 6046997 * 2 ^ 59
def prefixEnd_6046997 : Nat := 4983230072969 + 3 ^ 40 * 6046997 * 2
def baseEnd_6046997 : Nat := 3105015977295982830127873

theorem tailTrace_6046997 : CollatzResearch.WordTrace tailWord_6046997 prefixEnd_6046997 3105015977295982830127873 := by
  unfold tailWord_6046997
  simp only [CollatzResearch.WordTrace]
  refine ⟨220552099673770088711691245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147034733115846725807794163 220552099673770088711691245)
  ·
    refine ⟨82707037377663783266884217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220552099673770088711691245 82707037377663783266884217)
    ·
      refine ⟨62030278033247837450163163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82707037377663783266884217 62030278033247837450163163)
      ·
        refine ⟨93045417049871756175244745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62030278033247837450163163 93045417049871756175244745)
        ·
          refine ⟨69784062787403817131433559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93045417049871756175244745 69784062787403817131433559)
          ·
            refine ⟨104676094181105725697150339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69784062787403817131433559 104676094181105725697150339)
            ·
              refine ⟨157014141271658588545725509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104676094181105725697150339 157014141271658588545725509)
              ·
                refine ⟨29440151488435985352323533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157014141271658588545725509 29440151488435985352323533)
                ·
                  refine ⟨11040056808163494507121325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29440151488435985352323533 11040056808163494507121325)
                  ·
                    refine ⟨4140021303061310440170497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11040056808163494507121325 4140021303061310440170497)
                    ·
                      refine ⟨3105015977295982830127873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4140021303061310440170497 3105015977295982830127873)
                      ·
                        rfl

theorem cell23_6046997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_6046997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6046997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6046997 prefixEnd_6046997 := by exact prefixLift 6046997
  have htrace : WordTrace (prefixWord ++ tailWord_6046997) baseStart_6046997 baseEnd_6046997 := by
    simpa [prefixWord, tailWord_6046997, baseEnd_6046997] using wordTrace_append hprefix tailTrace_6046997
  have hstable : (prefixWord ++ tailWord_6046997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6046997).length < 2 ^ (prefixWord ++ tailWord_6046997).sum := by decide
  have hdescent : baseEnd_6046997 < baseStart_6046997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6046997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047003 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 1, 8]
def baseStart_6047003 : Nat := 118140960795 + 6047003 * 2 ^ 59
def prefixEnd_6047003 : Nat := 4983230072969 + 3 ^ 40 * 6047003 * 2
def baseEnd_6047003 : Nat := 1035006352726636602217615

theorem tailTrace_6047003 : CollatzResearch.WordTrace tailWord_6047003 prefixEnd_6047003 1035006352726636602217615 := by
  unfold tailWord_6047003
  simp only [CollatzResearch.WordTrace]
  refine ⟨220552318511748351736409663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147034879007832234490939775 220552318511748351736409663)
  ·
    refine ⟨330828477767622527604614495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220552318511748351736409663 330828477767622527604614495)
    ·
      refine ⟨496242716651433791406921743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330828477767622527604614495 496242716651433791406921743)
      ·
        refine ⟨744364074977150687110382615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496242716651433791406921743 744364074977150687110382615)
        ·
          refine ⟨1116546112465726030665573923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744364074977150687110382615 1116546112465726030665573923)
          ·
            refine ⟨1674819168698589045998360885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116546112465726030665573923 1674819168698589045998360885)
            ·
              refine ⟨157014297065492723062346333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1674819168698589045998360885 157014297065492723062346333)
              ·
                refine ⟨58880361399559771148379875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157014297065492723062346333 58880361399559771148379875)
                ·
                  refine ⟨88320542099339656722569813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58880361399559771148379875 88320542099339656722569813)
                  ·
                    refine ⟨1035006352726636602217615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88320542099339656722569813 1035006352726636602217615)
                    ·
                      rfl

theorem cell23_6047003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 8].length) (baseStart_6047003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047003 prefixEnd_6047003 := by exact prefixLift 6047003
  have htrace : WordTrace (prefixWord ++ tailWord_6047003) baseStart_6047003 baseEnd_6047003 := by
    simpa [prefixWord, tailWord_6047003, baseEnd_6047003] using wordTrace_append hprefix tailTrace_6047003
  have hstable : (prefixWord ++ tailWord_6047003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047003).length < 2 ^ (prefixWord ++ tailWord_6047003).sum := by decide
  have hdescent : baseEnd_6047003 < baseStart_6047003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047027 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 3, 4, 2]
def baseStart_6047027 : Nat := 118140960795 + 6047027 * 2 ^ 59
def prefixEnd_6047027 : Nat := 4983230072969 + 3 ^ 40 * 6047027 * 2
def baseEnd_6047027 : Nat := 3105031381715617712752735

theorem tailTrace_6047027 : CollatzResearch.WordTrace tailWord_6047027 prefixEnd_6047027 3105031381715617712752735 := by
  unfold tailWord_6047027
  simp only [CollatzResearch.WordTrace]
  refine ⟨220553193863661403835283335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147035462575774269223522223 220553193863661403835283335)
  ·
    refine ⟨330829790795492105752925003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220553193863661403835283335 330829790795492105752925003)
    ·
      refine ⟨496244686193238158629387505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330829790795492105752925003 496244686193238158629387505)
      ·
        refine ⟨372183514644928618972040629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496244686193238158629387505 372183514644928618972040629)
        ·
          refine ⟨34892204497962058028628809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 372183514644928618972040629 34892204497962058028628809)
          ·
            refine ⟨26169153373471543521471607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34892204497962058028628809 26169153373471543521471607)
            ·
              refine ⟨39253730060207315282207411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26169153373471543521471607 39253730060207315282207411)
              ·
                refine ⟨58880595090310972923311117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39253730060207315282207411 58880595090310972923311117)
                ·
                  refine ⟨22080223158866614846241669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58880595090310972923311117 22080223158866614846241669)
                  ·
                    refine ⟨4140041842287490283670313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22080223158866614846241669 4140041842287490283670313)
                    ·
                      refine ⟨3105031381715617712752735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4140041842287490283670313 3105031381715617712752735)
                      ·
                        rfl

theorem cell23_6047027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 4, 2].length) (baseStart_6047027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047027 prefixEnd_6047027 := by exact prefixLift 6047027
  have htrace : WordTrace (prefixWord ++ tailWord_6047027) baseStart_6047027 baseEnd_6047027 := by
    simpa [prefixWord, tailWord_6047027, baseEnd_6047027] using wordTrace_append hprefix tailTrace_6047027
  have hstable : (prefixWord ++ tailWord_6047027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047027).length < 2 ^ (prefixWord ++ tailWord_6047027).sum := by decide
  have hdescent : baseEnd_6047027 < baseStart_6047027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047040 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 4]
def baseStart_6047040 : Nat := 118140960795 + 6047040 * 2 ^ 59
def prefixEnd_6047040 : Nat := 4983230072969 + 3 ^ 40 * 6047040 * 2
def baseEnd_6047040 : Nat := 3105038056964126161890175

theorem tailTrace_6047040 : CollatzResearch.WordTrace tailWord_6047040 prefixEnd_6047040 3105038056964126161890175 := by
  unfold tailWord_6047040
  simp only [CollatzResearch.WordTrace]
  refine ⟨110276834006307153527753287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147035778675076204703671049 110276834006307153527753287)
  ·
    refine ⟨165415251009460730291629931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110276834006307153527753287 165415251009460730291629931)
    ·
      refine ⟨248122876514191095437444897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165415251009460730291629931 248122876514191095437444897)
      ·
        refine ⟨186092157385643321578083673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248122876514191095437444897 186092157385643321578083673)
        ·
          refine ⟨139569118039232491183562755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186092157385643321578083673 139569118039232491183562755)
          ·
            refine ⟨209353677058848736775344133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139569118039232491183562755 209353677058848736775344133)
            ·
              refine ⟨39253814448534138145377025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209353677058848736775344133 39253814448534138145377025)
              ·
                refine ⟨29440360836400603609032769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39253814448534138145377025 29440360836400603609032769)
                ·
                  refine ⟨22080270627300452706774577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29440360836400603609032769 22080270627300452706774577)
                  ·
                    refine ⟨16560202970475339530080933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22080270627300452706774577 16560202970475339530080933)
                    ·
                      refine ⟨3105038056964126161890175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16560202970475339530080933 3105038056964126161890175)
                      ·
                        rfl

theorem cell23_6047040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_6047040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047040 prefixEnd_6047040 := by exact prefixLift 6047040
  have htrace : WordTrace (prefixWord ++ tailWord_6047040) baseStart_6047040 baseEnd_6047040 := by
    simpa [prefixWord, tailWord_6047040, baseEnd_6047040] using wordTrace_append hprefix tailTrace_6047040
  have hstable : (prefixWord ++ tailWord_6047040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047040).length < 2 ^ (prefixWord ++ tailWord_6047040).sum := by decide
  have hdescent : baseEnd_6047040 < baseStart_6047040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047061 : List Nat := [1, 3, 2, 2, 3, 1, 2, 3, 2, 2, 2]
def baseStart_6047061 : Nat := 118140960795 + 6047061 * 2 ^ 59
def prefixEnd_6047061 : Nat := 4983230072969 + 3 ^ 40 * 6047061 * 2
def baseEnd_6047061 : Nat := 3105048840057870579727579

theorem tailTrace_6047061 : CollatzResearch.WordTrace tailWord_6047061 prefixEnd_6047061 3105048840057870579727579 := by
  unfold tailWord_6047061
  simp only [CollatzResearch.WordTrace]
  refine ⟨220554433945538227642021037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147036289297025485094680691 220554433945538227642021037)
  ·
    refine ⟨82707912729576835365757889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220554433945538227642021037 82707912729576835365757889)
    ·
      refine ⟨62030934547182626524318417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82707912729576835365757889 62030934547182626524318417)
      ·
        refine ⟨46523200910386969893238813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62030934547182626524318417 46523200910386969893238813)
        ·
          refine ⟨17446200341395113709964555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46523200910386969893238813 17446200341395113709964555)
          ·
            refine ⟨26169300512092670564946833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17446200341395113709964555 26169300512092670564946833)
            ·
              refine ⟨19626975384069502923710125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26169300512092670564946833 19626975384069502923710125)
              ·
                refine ⟨7360115769026063596391297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19626975384069502923710125 7360115769026063596391297)
                ·
                  refine ⟨5520086826769547697293473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7360115769026063596391297 5520086826769547697293473)
                  ·
                    refine ⟨4140065120077160772970105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5520086826769547697293473 4140065120077160772970105)
                    ·
                      refine ⟨3105048840057870579727579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4140065120077160772970105 3105048840057870579727579)
                      ·
                        rfl

theorem cell23_6047061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_6047061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047061 prefixEnd_6047061 := by exact prefixLift 6047061
  have htrace : WordTrace (prefixWord ++ tailWord_6047061) baseStart_6047061 baseEnd_6047061 := by
    simpa [prefixWord, tailWord_6047061, baseEnd_6047061] using wordTrace_append hprefix tailTrace_6047061
  have hstable : (prefixWord ++ tailWord_6047061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047061).length < 2 ^ (prefixWord ++ tailWord_6047061).sum := by decide
  have hdescent : baseEnd_6047061 < baseStart_6047061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047084 : List Nat := [2, 2, 1, 1, 5, 2, 2, 3, 5]
def baseStart_6047084 : Nat := 118140960795 + 6047084 * 2 ^ 59
def prefixEnd_6047084 : Nat := 4983230072969 + 3 ^ 40 * 6047084 * 2
def baseEnd_6047084 : Nat := 345006738901435998859997

theorem tailTrace_6047084 : CollatzResearch.WordTrace tailWord_6047084 prefixEnd_6047084 345006738901435998859997 := by
  unfold tailWord_6047084
  simp only [CollatzResearch.WordTrace]
  refine ⟨110277636412227451285054153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147036848549636601713405537 110277636412227451285054153)
  ·
    refine ⟨82708227309170588463790615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110277636412227451285054153 82708227309170588463790615)
    ·
      refine ⟨124062340963755882695685923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82708227309170588463790615 124062340963755882695685923)
      ·
        refine ⟨186093511445633824043528885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124062340963755882695685923 186093511445633824043528885)
        ·
          refine ⟨17446266698028171004080833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 186093511445633824043528885 17446266698028171004080833)
          ·
            refine ⟨13084700023521128253060625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17446266698028171004080833 13084700023521128253060625)
            ·
              refine ⟨9813525017640846189795469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13084700023521128253060625 9813525017640846189795469)
              ·
                refine ⟨3680071881615317321173301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9813525017640846189795469 3680071881615317321173301)
                ·
                  refine ⟨345006738901435998859997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3680071881615317321173301 345006738901435998859997)
                  ·
                    rfl

theorem cell23_6047084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 5].length) (baseStart_6047084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047084 prefixEnd_6047084 := by exact prefixLift 6047084
  have htrace : WordTrace (prefixWord ++ tailWord_6047084) baseStart_6047084 baseEnd_6047084 := by
    simpa [prefixWord, tailWord_6047084, baseEnd_6047084] using wordTrace_append hprefix tailTrace_6047084
  have hstable : (prefixWord ++ tailWord_6047084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047084).length < 2 ^ (prefixWord ++ tailWord_6047084).sum := by decide
  have hdescent : baseEnd_6047084 < baseStart_6047084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047157 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 8]
def baseStart_6047157 : Nat := 118140960795 + 6047157 * 2 ^ 59
def prefixEnd_6047157 : Nat := 4983230072969 + 3 ^ 40 * 6047157 * 2
def baseEnd_6047157 : Nat := 345010903800078022680793

theorem tailTrace_6047157 : CollatzResearch.WordTrace tailWord_6047157 prefixEnd_6047157 345010903800078022680793 := by
  unfold tailWord_6047157
  simp only [CollatzResearch.WordTrace]
  refine ⟨220557935353190436037515725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147038623568793624025010483 220557935353190436037515725)
  ·
    refine ⟨82709225757446413514068397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220557935353190436037515725 82709225757446413514068397)
    ·
      refine ⟨31015959659042405067775649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82709225757446413514068397 31015959659042405067775649)
      ·
        refine ⟨23261969744281803800831737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31015959659042405067775649 23261969744281803800831737)
        ·
          refine ⟨17446477308211352850623803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23261969744281803800831737 17446477308211352850623803)
          ·
            refine ⟨26169715962317029275935705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17446477308211352850623803 26169715962317029275935705)
            ·
              refine ⟨19627286971737771956951779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26169715962317029275935705 19627286971737771956951779)
              ·
                refine ⟨29440930457606657935427669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19627286971737771956951779 29440930457606657935427669)
                ·
                  refine ⟨345010903800078022680793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29440930457606657935427669 345010903800078022680793)
                  ·
                    rfl

theorem cell23_6047157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 8].length) (baseStart_6047157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047157 prefixEnd_6047157 := by exact prefixLift 6047157
  have htrace : WordTrace (prefixWord ++ tailWord_6047157) baseStart_6047157 baseEnd_6047157 := by
    simpa [prefixWord, tailWord_6047157, baseEnd_6047157] using wordTrace_append hprefix tailTrace_6047157
  have hstable : (prefixWord ++ tailWord_6047157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047157).length < 2 ^ (prefixWord ++ tailWord_6047157).sum := by decide
  have hdescent : baseEnd_6047157 < baseStart_6047157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047160 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 1, 1, 8]
def baseStart_6047160 : Nat := 118140960795 + 6047160 * 2 ^ 59
def prefixEnd_6047160 : Nat := 4983230072969 + 3 ^ 40 * 6047160 * 2
def baseEnd_6047160 : Nat := 3105099674642665692389623

theorem tailTrace_6047160 : CollatzResearch.WordTrace tailWord_6047160 prefixEnd_6047160 3105099674642665692389623 := by
  unfold tailWord_6047160
  simp only [CollatzResearch.WordTrace]
  refine ⟨110279022386089783774937467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147038696514786378366583289 110279022386089783774937467)
  ·
    refine ⟨165418533579134675662406201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110279022386089783774937467 165418533579134675662406201)
    ·
      refine ⟨124063900184351006746804651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165418533579134675662406201 124063900184351006746804651)
      ·
        refine ⟨186095850276526510120206977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124063900184351006746804651 186095850276526510120206977)
        ·
          refine ⟨139571887707394882590155233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186095850276526510120206977 139571887707394882590155233)
          ·
            refine ⟨104678915780546161942616425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139571887707394882590155233 104678915780546161942616425)
            ·
              refine ⟨78509186835409621456962319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104678915780546161942616425 78509186835409621456962319)
              ·
                refine ⟨117763780253114432185443479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78509186835409621456962319 117763780253114432185443479)
                ·
                  refine ⟨176645670379671648278165219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117763780253114432185443479 176645670379671648278165219)
                  ·
                    refine ⟨264968505569507472417247829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 176645670379671648278165219 264968505569507472417247829)
                    ·
                      refine ⟨3105099674642665692389623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 264968505569507472417247829 3105099674642665692389623)
                      ·
                        rfl

theorem cell23_6047160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_6047160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047160 prefixEnd_6047160 := by exact prefixLift 6047160
  have htrace : WordTrace (prefixWord ++ tailWord_6047160) baseStart_6047160 baseEnd_6047160 := by
    simpa [prefixWord, tailWord_6047160, baseEnd_6047160] using wordTrace_append hprefix tailTrace_6047160
  have hstable : (prefixWord ++ tailWord_6047160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047160).length < 2 ^ (prefixWord ++ tailWord_6047160).sum := by decide
  have hdescent : baseEnd_6047160 < baseStart_6047160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047161 : List Nat := [1, 2, 1, 4, 4, 2, 1, 1, 3, 4]
def baseStart_6047161 : Nat := 118140960795 + 6047161 * 2 ^ 59
def prefixEnd_6047161 : Nat := 4983230072969 + 3 ^ 40 * 6047161 * 2
def baseEnd_6047161 : Nat := 1035033396041106729492373

theorem tailTrace_6047161 : CollatzResearch.WordTrace tailWord_6047161 prefixEnd_6047161 1035033396041106729492373 := by
  unfold tailWord_6047161
  simp only [CollatzResearch.WordTrace]
  refine ⟨220558081245175944720661337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147038720830117296480440891 220558081245175944720661337)
  ·
    refine ⟨165418560933881958540496003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220558081245175944720661337 165418560933881958540496003)
    ·
      refine ⟨248127841400822937810744005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165418560933881958540496003 248127841400822937810744005)
      ·
        refine ⟨46523970262654300839514501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248127841400822937810744005 46523970262654300839514501)
        ·
          refine ⟨8723244424247681407408969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46523970262654300839514501 8723244424247681407408969)
          ·
            refine ⟨6542433318185761055556727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8723244424247681407408969 6542433318185761055556727)
            ·
              refine ⟨9813649977278641583335091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6542433318185761055556727 9813649977278641583335091)
              ·
                refine ⟨14720474965917962375002637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9813649977278641583335091 14720474965917962375002637)
                ·
                  refine ⟨5520178112219235890625989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14720474965917962375002637 5520178112219235890625989)
                  ·
                    refine ⟨1035033396041106729492373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5520178112219235890625989 1035033396041106729492373)
                    ·
                      rfl

theorem cell23_6047161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 4].length) (baseStart_6047161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047161 prefixEnd_6047161 := by exact prefixLift 6047161
  have htrace : WordTrace (prefixWord ++ tailWord_6047161) baseStart_6047161 baseEnd_6047161 := by
    simpa [prefixWord, tailWord_6047161, baseEnd_6047161] using wordTrace_append hprefix tailTrace_6047161
  have hstable : (prefixWord ++ tailWord_6047161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047161).length < 2 ^ (prefixWord ++ tailWord_6047161).sum := by decide
  have hdescent : baseEnd_6047161 < baseStart_6047161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047241 : List Nat := [1, 2, 1, 1, 3, 1, 5, 2, 3, 2, 2]
def baseStart_6047241 : Nat := 118140960795 + 6047241 * 2 ^ 59
def prefixEnd_6047241 : Nat := 4983230072969 + 3 ^ 40 * 6047241 * 2
def baseEnd_6047241 : Nat := 3105141266575679875476751

theorem tailTrace_6047241 : CollatzResearch.WordTrace tailWord_6047241 prefixEnd_6047241 3105141266575679875476751 := by
  unfold tailWord_6047241
  simp only [CollatzResearch.WordTrace]
  refine ⟨220560999084886118383573577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147040666056590745589049051 220560999084886118383573577)
  ·
    refine ⟨165420749313664588787680183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220560999084886118383573577 165420749313664588787680183)
    ·
      refine ⟨248131123970496883181520275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165420749313664588787680183 248131123970496883181520275)
      ·
        refine ⟨372196685955745324772280413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248131123970496883181520275 372196685955745324772280413)
        ·
          refine ⟨139573757233404496789605155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 372196685955745324772280413 139573757233404496789605155)
          ·
            refine ⟨209360635850106745184407733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139573757233404496789605155 209360635850106745184407733)
            ·
              refine ⟨19627559610947507361038225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 209360635850106745184407733 19627559610947507361038225)
              ·
                refine ⟨14720669708210630520778669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19627559610947507361038225 14720669708210630520778669)
                ·
                  refine ⟨5520251140578986445292001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14720669708210630520778669 5520251140578986445292001)
                  ·
                    refine ⟨4140188355434239833969001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5520251140578986445292001 4140188355434239833969001)
                    ·
                      refine ⟨3105141266575679875476751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4140188355434239833969001 3105141266575679875476751)
                      ·
                        rfl

theorem cell23_6047241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 2, 2].length) (baseStart_6047241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047241 prefixEnd_6047241 := by exact prefixLift 6047241
  have htrace : WordTrace (prefixWord ++ tailWord_6047241) baseStart_6047241 baseEnd_6047241 := by
    simpa [prefixWord, tailWord_6047241, baseEnd_6047241] using wordTrace_append hprefix tailTrace_6047241
  have hstable : (prefixWord ++ tailWord_6047241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047241).length < 2 ^ (prefixWord ++ tailWord_6047241).sum := by decide
  have hdescent : baseEnd_6047241 < baseStart_6047241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047245 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_6047245 : Nat := 118140960795 + 6047245 * 2 ^ 59
def prefixEnd_6047245 : Nat := 4983230072969 + 3 ^ 40 * 6047245 * 2
def baseEnd_6047245 : Nat := 3105143320498297859826733

theorem tailTrace_6047245 : CollatzResearch.WordTrace tailWord_6047245 prefixEnd_6047245 3105143320498297859826733 := by
  unfold tailWord_6047245
  simp only [CollatzResearch.WordTrace]
  refine ⟨220561144976871627066719189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147040763317914418044479459 220561144976871627066719189)
  ·
    refine ⟨5169401835395428759376231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 220561144976871627066719189 5169401835395428759376231)
    ·
      refine ⟨7754102753093143139064347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5169401835395428759376231 7754102753093143139064347)
      ·
        refine ⟨11631154129639714708596521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7754102753093143139064347 11631154129639714708596521)
        ·
          refine ⟨8723365597229786031447391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11631154129639714708596521 8723365597229786031447391)
          ·
            refine ⟨13085048395844679047171087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8723365597229786031447391 13085048395844679047171087)
            ·
              refine ⟨19627572593767018570756631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13085048395844679047171087 19627572593767018570756631)
              ·
                refine ⟨29441358890650527856134947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19627572593767018570756631 29441358890650527856134947)
                ·
                  refine ⟨44162038335975791784202421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29441358890650527856134947 44162038335975791784202421)
                  ·
                    refine ⟨4140191093997730479768977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44162038335975791784202421 4140191093997730479768977)
                    ·
                      refine ⟨3105143320498297859826733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4140191093997730479768977 3105143320498297859826733)
                      ·
                        rfl

theorem cell23_6047245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_6047245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047245 prefixEnd_6047245 := by exact prefixLift 6047245
  have htrace : WordTrace (prefixWord ++ tailWord_6047245) baseStart_6047245 baseEnd_6047245 := by
    simpa [prefixWord, tailWord_6047245, baseEnd_6047245] using wordTrace_append hprefix tailTrace_6047245
  have hstable : (prefixWord ++ tailWord_6047245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047245).length < 2 ^ (prefixWord ++ tailWord_6047245).sum := by decide
  have hdescent : baseEnd_6047245 < baseStart_6047245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047252 : List Nat := [2, 4, 3, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_6047252 : Nat := 118140960795 + 6047252 * 2 ^ 59
def prefixEnd_6047252 : Nat := 4983230072969 + 3 ^ 40 * 6047252 * 2
def baseEnd_6047252 : Nat := 3105146914862879332439201

theorem tailTrace_6047252 : CollatzResearch.WordTrace tailWord_6047252 prefixEnd_6047252 3105146914862879332439201 := by
  unfold tailWord_6047252
  simp only [CollatzResearch.WordTrace]
  refine ⟨110280700143923133631112005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147040933525230844841482673 110280700143923133631112005)
  ·
    refine ⟨20677631276985587555833501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110280700143923133631112005 20677631276985587555833501)
    ·
      refine ⟨7754111728869595333437563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20677631276985587555833501 7754111728869595333437563)
      ·
        refine ⟨11631167593304393000156345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7754111728869595333437563 11631167593304393000156345)
        ·
          refine ⟨8723375694978294750117259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11631167593304393000156345 8723375694978294750117259)
          ·
            refine ⟨13085063542467442125175889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8723375694978294750117259 13085063542467442125175889)
            ·
              refine ⟨9813797656850581593881917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13085063542467442125175889 9813797656850581593881917)
              ·
                refine ⟨3680174121318968097705719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9813797656850581593881917 3680174121318968097705719)
                ·
                  refine ⟨5520261181978452146558579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3680174121318968097705719 5520261181978452146558579)
                  ·
                    refine ⟨8280391772967678219837869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5520261181978452146558579 8280391772967678219837869)
                    ·
                      refine ⟨3105146914862879332439201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8280391772967678219837869 3105146914862879332439201)
                      ·
                        rfl

theorem cell23_6047252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_6047252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047252 prefixEnd_6047252 := by exact prefixLift 6047252
  have htrace : WordTrace (prefixWord ++ tailWord_6047252) baseStart_6047252 baseEnd_6047252 := by
    simpa [prefixWord, tailWord_6047252, baseEnd_6047252] using wordTrace_append hprefix tailTrace_6047252
  have hstable : (prefixWord ++ tailWord_6047252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047252).length < 2 ^ (prefixWord ++ tailWord_6047252).sum := by decide
  have hdescent : baseEnd_6047252 < baseStart_6047252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047261 : List Nat := [1, 4, 2, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_6047261 : Nat := 118140960795 + 6047261 * 2 ^ 59
def prefixEnd_6047261 : Nat := 4983230072969 + 3 ^ 40 * 6047261 * 2
def baseEnd_6047261 : Nat := 3105151536188769797226659

theorem tailTrace_6047261 : CollatzResearch.WordTrace tailWord_6047261 prefixEnd_6047261 3105151536188769797226659 := by
  unfold tailWord_6047261
  simp only [CollatzResearch.WordTrace]
  refine ⟨220561728544813661799301637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147041152363209107866201091 220561728544813661799301637)
  ·
    refine ⟨41355324102152561587369057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220561728544813661799301637 41355324102152561587369057)
    ·
      refine ⟨31016493076614421190526793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41355324102152561587369057 31016493076614421190526793)
      ·
        refine ⟨23262369807460815892895095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31016493076614421190526793 23262369807460815892895095)
        ·
          refine ⟨34893554711191223839342643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23262369807460815892895095 34893554711191223839342643)
          ·
            refine ⟨52340332066786835759013965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34893554711191223839342643 52340332066786835759013965)
            ·
              refine ⟨19627624525045063409630237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52340332066786835759013965 19627624525045063409630237)
              ·
                refine ⟨7360359196891898778611339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19627624525045063409630237 7360359196891898778611339)
                ·
                  refine ⟨11040538795337848167917009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7360359196891898778611339 11040538795337848167917009)
                  ·
                    refine ⟨8280404096503386125937757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11040538795337848167917009 8280404096503386125937757)
                    ·
                      refine ⟨3105151536188769797226659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8280404096503386125937757 3105151536188769797226659)
                      ·
                        rfl

theorem cell23_6047261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_6047261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047261 prefixEnd_6047261 := by exact prefixLift 6047261
  have htrace : WordTrace (prefixWord ++ tailWord_6047261) baseStart_6047261 baseEnd_6047261 := by
    simpa [prefixWord, tailWord_6047261, baseEnd_6047261] using wordTrace_append hprefix tailTrace_6047261
  have hstable : (prefixWord ++ tailWord_6047261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047261).length < 2 ^ (prefixWord ++ tailWord_6047261).sum := by decide
  have hdescent : baseEnd_6047261 < baseStart_6047261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047309 : List Nat := [1, 6, 1, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_6047309 : Nat := 118140960795 + 6047309 * 2 ^ 59
def prefixEnd_6047309 : Nat := 4983230072969 + 3 ^ 40 * 6047309 * 2
def baseEnd_6047309 : Nat := 3105176183260185609426439

theorem tailTrace_6047309 : CollatzResearch.WordTrace tailWord_6047309 prefixEnd_6047309 3105176183260185609426439 := by
  unfold tailWord_6047309
  simp only [CollatzResearch.WordTrace]
  refine ⟨220563479248639765997048981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147042319499093177331365987 220563479248639765997048981)
  ·
    refine ⟨10338913089779989031111671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 220563479248639765997048981 10338913089779989031111671)
    ·
      refine ⟨15508369634669983546667507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10338913089779989031111671 15508369634669983546667507)
      ·
        refine ⟨23262554452004975320001261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15508369634669983546667507 23262554452004975320001261)
        ·
          refine ⟨8723457919501865745000473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23262554452004975320001261 8723457919501865745000473)
          ·
            refine ⟨6542593439626399308750355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8723457919501865745000473 6542593439626399308750355)
            ·
              refine ⟨9813890159439598963125533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6542593439626399308750355 9813890159439598963125533)
              ·
                refine ⟨3680208809789849611172075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9813890159439598963125533 3680208809789849611172075)
                ·
                  refine ⟨5520313214684774416758113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3680208809789849611172075 5520313214684774416758113)
                  ·
                    refine ⟨4140234911013580812568585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5520313214684774416758113 4140234911013580812568585)
                    ·
                      refine ⟨3105176183260185609426439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4140234911013580812568585 3105176183260185609426439)
                      ·
                        rfl

theorem cell23_6047309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_6047309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047309 prefixEnd_6047309 := by exact prefixLift 6047309
  have htrace : WordTrace (prefixWord ++ tailWord_6047309) baseStart_6047309 baseEnd_6047309 := by
    simpa [prefixWord, tailWord_6047309, baseEnd_6047309] using wordTrace_append hprefix tailTrace_6047309
  have hstable : (prefixWord ++ tailWord_6047309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047309).length < 2 ^ (prefixWord ++ tailWord_6047309).sum := by decide
  have hdescent : baseEnd_6047309 < baseStart_6047309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047342 : List Nat := [4, 1, 2, 2, 3, 2, 2, 1, 2, 1, 3]
def baseStart_6047342 : Nat := 118140960795 + 6047342 * 2 ^ 59
def prefixEnd_6047342 : Nat := 4983230072969 + 3 ^ 40 * 6047342 * 2
def baseEnd_6047342 : Nat := 3105193128121783980313787

theorem tailTrace_6047342 : CollatzResearch.WordTrace tailWord_6047342 prefixEnd_6047342 3105193128121783980313787 := by
  unfold tailWord_6047342
  simp only [CollatzResearch.WordTrace]
  refine ⟨27570585357190026579125035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147043121905013475088666853 27570585357190026579125035)
  ·
    refine ⟨41355878035785039868687553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27570585357190026579125035 41355878035785039868687553)
    ·
      refine ⟨31016908526838779901515665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41355878035785039868687553 31016908526838779901515665)
      ·
        refine ⟨23262681395129084926136749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31016908526838779901515665 23262681395129084926136749)
        ·
          refine ⟨8723505523173406847301281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23262681395129084926136749 8723505523173406847301281)
          ·
            refine ⟨6542629142380055135475961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8723505523173406847301281 6542629142380055135475961)
            ·
              refine ⟨4906971856785041351606971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6542629142380055135475961 4906971856785041351606971)
              ·
                refine ⟨7360457785177562027410457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4906971856785041351606971 7360457785177562027410457)
                ·
                  refine ⟨5520343338883171520557843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7360457785177562027410457 5520343338883171520557843)
                  ·
                    refine ⟨8280515008324757280836765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5520343338883171520557843 8280515008324757280836765)
                    ·
                      refine ⟨3105193128121783980313787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8280515008324757280836765 3105193128121783980313787)
                      ·
                        rfl

theorem cell23_6047342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_6047342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047342 prefixEnd_6047342 := by exact prefixLift 6047342
  have htrace : WordTrace (prefixWord ++ tailWord_6047342) baseStart_6047342 baseEnd_6047342 := by
    simpa [prefixWord, tailWord_6047342, baseEnd_6047342] using wordTrace_append hprefix tailTrace_6047342
  have hstable : (prefixWord ++ tailWord_6047342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047342).length < 2 ^ (prefixWord ++ tailWord_6047342).sum := by decide
  have hdescent : baseEnd_6047342 < baseStart_6047342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047388 : List Nat := [2, 2, 3, 2, 3, 1, 1, 4, 5]
def baseStart_6047388 : Nat := 118140960795 + 6047388 * 2 ^ 59
def prefixEnd_6047388 : Nat := 4983230072969 + 3 ^ 40 * 6047388 * 2
def baseEnd_6047388 : Nat := 345024083136876755593175

theorem tailTrace_6047388 : CollatzResearch.WordTrace tailWord_6047388 prefixEnd_6047388 345024083136876755593175 := by
  unfold tailWord_6047388
  simp only [CollatzResearch.WordTrace]
  refine ⟨110283180307676781244587409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147044240410235708326116545 110283180307676781244587409)
  ·
    refine ⟨82712385230757585933440557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110283180307676781244587409 82712385230757585933440557)
    ·
      refine ⟨31017144461534094725040209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82712385230757585933440557 31017144461534094725040209)
      ·
        refine ⟨23262858346150571043780157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31017144461534094725040209 23262858346150571043780157)
        ·
          refine ⟨8723571879806464141417559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23262858346150571043780157 8723571879806464141417559)
          ·
            refine ⟨13085357819709696212126339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8723571879806464141417559 13085357819709696212126339)
            ·
              refine ⟨19628036729564544318189509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13085357819709696212126339 19628036729564544318189509)
              ·
                refine ⟨3680256886793352059660533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19628036729564544318189509 3680256886793352059660533)
                ·
                  refine ⟨345024083136876755593175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3680256886793352059660533 345024083136876755593175)
                  ·
                    rfl

theorem cell23_6047388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 5].length) (baseStart_6047388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047388 prefixEnd_6047388 := by exact prefixLift 6047388
  have htrace : WordTrace (prefixWord ++ tailWord_6047388) baseStart_6047388 baseEnd_6047388 := by
    simpa [prefixWord, tailWord_6047388, baseEnd_6047388] using wordTrace_append hprefix tailTrace_6047388
  have hstable : (prefixWord ++ tailWord_6047388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047388).length < 2 ^ (prefixWord ++ tailWord_6047388).sum := by decide
  have hdescent : baseEnd_6047388 < baseStart_6047388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047421 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 1, 6, 2]
def baseStart_6047421 : Nat := 118140960795 + 6047421 * 2 ^ 59
def prefixEnd_6047421 : Nat := 4983230072969 + 3 ^ 40 * 6047421 * 2
def baseEnd_6047421 : Nat := 3105233693093489171225923

theorem tailTrace_6047421 : CollatzResearch.WordTrace tailWord_6047421 prefixEnd_6047421 3105233693093489171225923 := by
  unfold tailWord_6047421
  simp only [CollatzResearch.WordTrace]
  refine ⟨220567564224234009125126117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147045042816156006083417411 220567564224234009125126117)
  ·
    refine ⟨41356418292043876710961147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220567564224234009125126117 41356418292043876710961147)
    ·
      refine ⟨62034627438065815066441721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41356418292043876710961147 62034627438065815066441721)
      ·
        refine ⟨46525970578549361299831291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62034627438065815066441721 46525970578549361299831291)
        ·
          refine ⟨69788955867824041949746937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46525970578549361299831291 69788955867824041949746937)
          ·
            refine ⟨52341716900868031462310203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69788955867824041949746937 52341716900868031462310203)
            ·
              refine ⟨78512575351302047193465305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52341716900868031462310203 78512575351302047193465305)
              ·
                refine ⟨58884431513476535395098979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78512575351302047193465305 58884431513476535395098979)
                ·
                  refine ⟨88326647270214803092648469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58884431513476535395098979 88326647270214803092648469)
                  ·
                    refine ⟨4140311590791318894967897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88326647270214803092648469 4140311590791318894967897)
                    ·
                      refine ⟨3105233693093489171225923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4140311590791318894967897 3105233693093489171225923)
                      ·
                        rfl

theorem cell23_6047421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_6047421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047421 prefixEnd_6047421 := by exact prefixLift 6047421
  have htrace : WordTrace (prefixWord ++ tailWord_6047421) baseStart_6047421 baseEnd_6047421 := by
    simpa [prefixWord, tailWord_6047421, baseEnd_6047421] using wordTrace_append hprefix tailTrace_6047421
  have hstable : (prefixWord ++ tailWord_6047421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047421).length < 2 ^ (prefixWord ++ tailWord_6047421).sum := by decide
  have hdescent : baseEnd_6047421 < baseStart_6047421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047448 : List Nat := [2, 1, 2, 2, 3, 1, 1, 6, 1, 4]
def baseStart_6047448 : Nat := 118140960795 + 6047448 * 2 ^ 59
def prefixEnd_6047448 : Nat := 4983230072969 + 3 ^ 40 * 6047448 * 2
def baseEnd_6047448 : Nat := 1035082519023720188529433

theorem tailTrace_6047448 : CollatzResearch.WordTrace tailWord_6047448 prefixEnd_6047448 1035082519023720188529433 := by
  unfold tailWord_6047448
  simp only [CollatzResearch.WordTrace]
  refine ⟨110284274497568096368179499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147045699330090795157572665 110284274497568096368179499)
  ·
    refine ⟨165426411746352144552269249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110284274497568096368179499 165426411746352144552269249)
    ·
      refine ⟨124069808809764108414201937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165426411746352144552269249 124069808809764108414201937)
      ·
        refine ⟨93052356607323081310651453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124069808809764108414201937 93052356607323081310651453)
        ·
          refine ⟨34894633727746155491494295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93052356607323081310651453 34894633727746155491494295)
          ·
            refine ⟨52341950591619233237241443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34894633727746155491494295 52341950591619233237241443)
            ·
              refine ⟨78512925887428849855862165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52341950591619233237241443 78512925887428849855862165)
              ·
                refine ⟨3680293400973227336993539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78512925887428849855862165 3680293400973227336993539)
                ·
                  refine ⟨5520440101459841005490309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3680293400973227336993539 5520440101459841005490309)
                  ·
                    refine ⟨1035082519023720188529433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5520440101459841005490309 1035082519023720188529433)
                    ·
                      rfl

theorem cell23_6047448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 1, 4].length) (baseStart_6047448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047448 prefixEnd_6047448 := by exact prefixLift 6047448
  have htrace : WordTrace (prefixWord ++ tailWord_6047448) baseStart_6047448 baseEnd_6047448 := by
    simpa [prefixWord, tailWord_6047448, baseEnd_6047448] using wordTrace_append hprefix tailTrace_6047448
  have hstable : (prefixWord ++ tailWord_6047448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047448).length < 2 ^ (prefixWord ++ tailWord_6047448).sum := by decide
  have hdescent : baseEnd_6047448 < baseStart_6047448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047491 : List Nat := [1, 1, 1, 3, 2, 2, 4, 3, 1, 5]
def baseStart_6047491 : Nat := 118140960795 + 6047491 * 2 ^ 59
def prefixEnd_6047491 : Nat := 4983230072969 + 3 ^ 40 * 6047491 * 2
def baseEnd_6047491 : Nat := 1035089878913101299116867

theorem tailTrace_6047491 : CollatzResearch.WordTrace tailWord_6047491 prefixEnd_6047491 1035089878913101299116867 := by
  unfold tailWord_6047491
  simp only [CollatzResearch.WordTrace]
  refine ⟨220570117333980411080174327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147046744889320274053449551 220570117333980411080174327)
  ·
    refine ⟨330855176000970616620261491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220570117333980411080174327 330855176000970616620261491)
    ·
      refine ⟨496282764001455924930392237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330855176000970616620261491 496282764001455924930392237)
      ·
        refine ⟨186106036500545971848897089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 496282764001455924930392237 186106036500545971848897089)
        ·
          refine ⟨139579527375409478886672817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186106036500545971848897089 139579527375409478886672817)
          ·
            refine ⟨104684645531557109165004613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139579527375409478886672817 104684645531557109165004613)
            ·
              refine ⟨19628371037166957968438365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104684645531557109165004613 19628371037166957968438365)
              ·
                refine ⟨7360639138937609238164387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19628371037166957968438365 7360639138937609238164387)
                ·
                  refine ⟨11040958708406413857246581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7360639138937609238164387 11040958708406413857246581)
                  ·
                    refine ⟨1035089878913101299116867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11040958708406413857246581 1035089878913101299116867)
                    ·
                      rfl

theorem cell23_6047491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 5].length) (baseStart_6047491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047491 prefixEnd_6047491 := by exact prefixLift 6047491
  have htrace : WordTrace (prefixWord ++ tailWord_6047491) baseStart_6047491 baseEnd_6047491 := by
    simpa [prefixWord, tailWord_6047491, baseEnd_6047491] using wordTrace_append hprefix tailTrace_6047491
  have hstable : (prefixWord ++ tailWord_6047491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047491).length < 2 ^ (prefixWord ++ tailWord_6047491).sum := by decide
  have hdescent : baseEnd_6047491 < baseStart_6047491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047498 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 4, 3, 2]
def baseStart_6047498 : Nat := 118140960795 + 6047498 * 2 ^ 59
def prefixEnd_6047498 : Nat := 4983230072969 + 3 ^ 40 * 6047498 * 2
def baseEnd_6047498 : Nat := 3105273231103885369963069

theorem tailTrace_6047498 : CollatzResearch.WordTrace tailWord_6047498 prefixEnd_6047498 3105273231103885369963069 := by
  unfold tailWord_6047498
  simp only [CollatzResearch.WordTrace]
  refine ⟨55142593161238762818919787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147046915096636700850452765 55142593161238762818919787)
  ·
    refine ⟨82713889741858144228379681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55142593161238762818919787 82713889741858144228379681)
    ·
      refine ⟨62035417306393608171284761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82713889741858144228379681 62035417306393608171284761)
      ·
        refine ⟨46526562979795206128463571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62035417306393608171284761 46526562979795206128463571)
        ·
          refine ⟨69789844469692809192695357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46526562979795206128463571 69789844469692809192695357)
          ·
            refine ⟨26171191676134803447260759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69789844469692809192695357 26171191676134803447260759)
            ·
              refine ⟨39256787514202205170891139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26171191676134803447260759 39256787514202205170891139)
              ·
                refine ⟨58885181271303307756336709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39256787514202205170891139 58885181271303307756336709)
                ·
                  refine ⟨11040971488369370204313133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58885181271303307756336709 11040971488369370204313133)
                  ·
                    refine ⟨4140364308138513826617425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11040971488369370204313133 4140364308138513826617425)
                    ·
                      refine ⟨3105273231103885369963069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4140364308138513826617425 3105273231103885369963069)
                      ·
                        rfl

theorem cell23_6047498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_6047498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047498 prefixEnd_6047498 := by exact prefixLift 6047498
  have htrace : WordTrace (prefixWord ++ tailWord_6047498) baseStart_6047498 baseEnd_6047498 := by
    simpa [prefixWord, tailWord_6047498, baseEnd_6047498] using wordTrace_append hprefix tailTrace_6047498
  have hstable : (prefixWord ++ tailWord_6047498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047498).length < 2 ^ (prefixWord ++ tailWord_6047498).sum := by decide
  have hdescent : baseEnd_6047498 < baseStart_6047498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047528 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_6047528 : Nat := 118140960795 + 6047528 * 2 ^ 59
def prefixEnd_6047528 : Nat := 4983230072969 + 3 ^ 40 * 6047528 * 2
def baseEnd_6047528 : Nat := 3105288635523520252587931

theorem tailTrace_6047528 : CollatzResearch.WordTrace tailWord_6047528 prefixEnd_6047528 3105288635523520252587931 := by
  unfold tailWord_6047528
  simp only [CollatzResearch.WordTrace]
  refine ⟨110285733417423183199635619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147047644556564244266180825 110285733417423183199635619)
  ·
    refine ⟨165428600126134774799453429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110285733417423183199635619 165428600126134774799453429)
    ·
      refine ⟨15508931261825135137448759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165428600126134774799453429 15508931261825135137448759)
      ·
        refine ⟨23263396892737702706173139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15508931261825135137448759 23263396892737702706173139)
        ·
          refine ⟨34895095339106554059259709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23263396892737702706173139 34895095339106554059259709)
          ·
            refine ⟨13085660752164957772222391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34895095339106554059259709 13085660752164957772222391)
            ·
              refine ⟨19628491128247436658333587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13085660752164957772222391 19628491128247436658333587)
              ·
                refine ⟨29442736692371154987500381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19628491128247436658333587 29442736692371154987500381)
                ·
                  refine ⟨11041026259639183120312643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29442736692371154987500381 11041026259639183120312643)
                  ·
                    refine ⟨16561539389458774680468965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11041026259639183120312643 16561539389458774680468965)
                    ·
                      refine ⟨3105288635523520252587931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16561539389458774680468965 3105288635523520252587931)
                      ·
                        rfl

theorem cell23_6047528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_6047528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047528 prefixEnd_6047528 := by exact prefixLift 6047528
  have htrace : WordTrace (prefixWord ++ tailWord_6047528) baseStart_6047528 baseEnd_6047528 := by
    simpa [prefixWord, tailWord_6047528, baseEnd_6047528] using wordTrace_append hprefix tailTrace_6047528
  have hstable : (prefixWord ++ tailWord_6047528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047528).length < 2 ^ (prefixWord ++ tailWord_6047528).sum := by decide
  have hdescent : baseEnd_6047528 < baseStart_6047528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047542 : List Nat := [5, 1, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_6047542 : Nat := 118140960795 + 6047542 * 2 ^ 59
def prefixEnd_6047542 : Nat := 4983230072969 + 3 ^ 40 * 6047542 * 2
def baseEnd_6047542 : Nat := 1035098608084227732604289

theorem tailTrace_6047542 : CollatzResearch.WordTrace tailWord_6047542 prefixEnd_6047542 1035098608084227732604289 := by
  unfold tailWord_6047542
  simp only [CollatzResearch.WordTrace]
  refine ⟨13785748591049727924392555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147047984971197097860187253 13785748591049727924392555)
  ·
    refine ⟨20678622886574591886588833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13785748591049727924392555 20678622886574591886588833)
    ·
      refine ⟨15508967164930943914941625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20678622886574591886588833 15508967164930943914941625)
      ·
        refine ⟨11631725373698207936206219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15508967164930943914941625 11631725373698207936206219)
        ·
          refine ⟨17447588060547311904309329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11631725373698207936206219 17447588060547311904309329)
          ·
            refine ⟨13085691045410483928231997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17447588060547311904309329 13085691045410483928231997)
            ·
              refine ⟨4907134142028931473086999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13085691045410483928231997 4907134142028931473086999)
              ·
                refine ⟨7360701213043397209630499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4907134142028931473086999 7360701213043397209630499)
                ·
                  refine ⟨11041051819565095814445749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7360701213043397209630499 11041051819565095814445749)
                  ·
                    refine ⟨1035098608084227732604289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11041051819565095814445749 1035098608084227732604289)
                    ·
                      rfl

theorem cell23_6047542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_6047542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047542 prefixEnd_6047542 := by exact prefixLift 6047542
  have htrace : WordTrace (prefixWord ++ tailWord_6047542) baseStart_6047542 baseEnd_6047542 := by
    simpa [prefixWord, tailWord_6047542, baseEnd_6047542] using wordTrace_append hprefix tailTrace_6047542
  have hstable : (prefixWord ++ tailWord_6047542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047542).length < 2 ^ (prefixWord ++ tailWord_6047542).sum := by decide
  have hdescent : baseEnd_6047542 < baseStart_6047542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047548 : List Nat := [2, 2, 2, 2, 1, 1, 2, 5, 1, 2, 3]
def baseStart_6047548 : Nat := 118140960795 + 6047548 * 2 ^ 59
def prefixEnd_6047548 : Nat := 4983230072969 + 3 ^ 40 * 6047548 * 2
def baseEnd_6047548 : Nat := 3105298905136610174337839

theorem tailTrace_6047548 : CollatzResearch.WordTrace tailWord_6047548 prefixEnd_6047548 3105298905136610174337839 := by
  unfold tailWord_6047548
  simp only [CollatzResearch.WordTrace]
  refine ⟨110286098147386954907499649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147048130863182606543332865 110286098147386954907499649)
  ·
    refine ⟨82714573610540216180624737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110286098147386954907499649 82714573610540216180624737)
    ·
      refine ⟨62035930207905162135468553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82714573610540216180624737 62035930207905162135468553)
      ·
        refine ⟨46526947655928871601601415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62035930207905162135468553 46526947655928871601601415)
        ·
          refine ⟨69790421483893307402402123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46526947655928871601601415 69790421483893307402402123)
          ·
            refine ⟨104685632225839961103603185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69790421483893307402402123 104685632225839961103603185)
            ·
              refine ⟨78514224169379970827702389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104685632225839961103603185 78514224169379970827702389)
              ·
                refine ⟨7360708515879372265097099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78514224169379970827702389 7360708515879372265097099)
                ·
                  refine ⟨11041062773819058397645649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7360708515879372265097099 11041062773819058397645649)
                  ·
                    refine ⟨8280797080364293798234237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11041062773819058397645649 8280797080364293798234237)
                    ·
                      refine ⟨3105298905136610174337839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8280797080364293798234237 3105298905136610174337839)
                      ·
                        rfl

theorem cell23_6047548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_6047548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047548 prefixEnd_6047548 := by exact prefixLift 6047548
  have htrace : WordTrace (prefixWord ++ tailWord_6047548) baseStart_6047548 baseEnd_6047548 := by
    simpa [prefixWord, tailWord_6047548, baseEnd_6047548] using wordTrace_append hprefix tailTrace_6047548
  have hstable : (prefixWord ++ tailWord_6047548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047548).length < 2 ^ (prefixWord ++ tailWord_6047548).sum := by decide
  have hdescent : baseEnd_6047548 < baseStart_6047548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047551 : List Nat := [1, 1, 2, 2, 7, 10]
def baseStart_6047551 : Nat := 118140960795 + 6047551 * 2 ^ 59
def prefixEnd_6047551 : Nat := 4983230072969 + 3 ^ 40 * 6047551 * 2
def baseEnd_6047551 : Nat := 12779014179335694084775

theorem tailTrace_6047551 : CollatzResearch.WordTrace tailWord_6047551 prefixEnd_6047551 12779014179335694084775 := by
  unfold tailWord_6047551
  simp only [CollatzResearch.WordTrace]
  refine ⟨220572305713763041327358507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147048203809175360884905671 220572305713763041327358507)
  ·
    refine ⟨330858458570644561991037761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220572305713763041327358507 330858458570644561991037761)
    ·
      refine ⟨248143843927983421493278321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330858458570644561991037761 248143843927983421493278321)
      ·
        refine ⟨186107882945987566119958741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248143843927983421493278321 186107882945987566119958741)
        ·
          refine ⟨4361903506546583580936533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 186107882945987566119958741 4361903506546583580936533)
          ·
            refine ⟨12779014179335694084775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4361903506546583580936533 12779014179335694084775)
            ·
              rfl

theorem cell23_6047551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 10].length) (baseStart_6047551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047551 prefixEnd_6047551 := by exact prefixLift 6047551
  have htrace : WordTrace (prefixWord ++ tailWord_6047551) baseStart_6047551 baseEnd_6047551 := by
    simpa [prefixWord, tailWord_6047551, baseEnd_6047551] using wordTrace_append hprefix tailTrace_6047551
  have hstable : (prefixWord ++ tailWord_6047551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047551).length < 2 ^ (prefixWord ++ tailWord_6047551).sum := by decide
  have hdescent : baseEnd_6047551 < baseStart_6047551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047561 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 3, 3, 3]
def baseStart_6047561 : Nat := 118140960795 + 6047561 * 2 ^ 59
def prefixEnd_6047561 : Nat := 4983230072969 + 3 ^ 40 * 6047561 * 2
def baseEnd_6047561 : Nat := 3105305580385118623475279

theorem tailTrace_6047561 : CollatzResearch.WordTrace tailWord_6047561 prefixEnd_6047561 3105305580385118623475279 := by
  unfold tailWord_6047561
  simp only [CollatzResearch.WordTrace]
  refine ⟨220572670443726813035222537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147048446962484542023481691 220572670443726813035222537)
  ·
    refine ⟨165429502832795109776416903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220572670443726813035222537 165429502832795109776416903)
    ·
      refine ⟨248144254249192664664625355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165429502832795109776416903 248144254249192664664625355)
      ·
        refine ⟨372216381373788996996938033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248144254249192664664625355 372216381373788996996938033)
        ·
          refine ⟨279162286030341747747703525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372216381373788996996938033 279162286030341747747703525)
          ·
            refine ⟨52342928630689077702694411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 279162286030341747747703525 52342928630689077702694411)
            ·
              refine ⟨78514392946033616554041617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52342928630689077702694411 78514392946033616554041617)
              ·
                refine ⟨58885794709525212415531213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78514392946033616554041617 58885794709525212415531213)
                ·
                  refine ⟨22082173016071954655824205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58885794709525212415531213 22082173016071954655824205)
                  ·
                    refine ⟨8280814881026982995934077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22082173016071954655824205 8280814881026982995934077)
                    ·
                      refine ⟨3105305580385118623475279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8280814881026982995934077 3105305580385118623475279)
                      ·
                        rfl

theorem cell23_6047561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 3, 3].length) (baseStart_6047561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047561 prefixEnd_6047561 := by exact prefixLift 6047561
  have htrace : WordTrace (prefixWord ++ tailWord_6047561) baseStart_6047561 baseEnd_6047561 := by
    simpa [prefixWord, tailWord_6047561, baseEnd_6047561] using wordTrace_append hprefix tailTrace_6047561
  have hstable : (prefixWord ++ tailWord_6047561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047561).length < 2 ^ (prefixWord ++ tailWord_6047561).sum := by decide
  have hdescent : baseEnd_6047561 < baseStart_6047561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047562 : List Nat := [3, 1, 2, 1, 1, 1, 5, 4, 1, 2, 2]
def baseStart_6047562 : Nat := 118140960795 + 6047562 * 2 ^ 59
def prefixEnd_6047562 : Nat := 4983230072969 + 3 ^ 40 * 6047562 * 2
def baseEnd_6047562 : Nat := 3105306093865773119562775

theorem tailTrace_6047562 : CollatzResearch.WordTrace tailWord_6047562 prefixEnd_6047562 3105306093865773119562775 := by
  unfold tailWord_6047562
  simp only [CollatzResearch.WordTrace]
  refine ⟨55143176729180797551502235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147048471277815460137339293 55143176729180797551502235)
  ·
    refine ⟨82714765093771196327253353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55143176729180797551502235 82714765093771196327253353)
    ·
      refine ⟨62036073820328397245440015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82714765093771196327253353 62036073820328397245440015)
      ·
        refine ⟨93054110730492595868160023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62036073820328397245440015 93054110730492595868160023)
        ·
          refine ⟨139581166095738893802240035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93054110730492595868160023 139581166095738893802240035)
          ·
            refine ⟨209371749143608340703360053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139581166095738893802240035 209371749143608340703360053)
            ·
              refine ⟨19628601482213281940940005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 209371749143608340703360053 19628601482213281940940005)
              ·
                refine ⟨3680362777914990363926251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19628601482213281940940005 3680362777914990363926251)
                ·
                  refine ⟨5520544166872485545889377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3680362777914990363926251 5520544166872485545889377)
                  ·
                    refine ⟨4140408125154364159417033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5520544166872485545889377 4140408125154364159417033)
                    ·
                      refine ⟨3105306093865773119562775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4140408125154364159417033 3105306093865773119562775)
                      ·
                        rfl

theorem cell23_6047562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 1, 2, 2].length) (baseStart_6047562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047562 prefixEnd_6047562 := by exact prefixLift 6047562
  have htrace : WordTrace (prefixWord ++ tailWord_6047562) baseStart_6047562 baseEnd_6047562 := by
    simpa [prefixWord, tailWord_6047562, baseEnd_6047562] using wordTrace_append hprefix tailTrace_6047562
  have hstable : (prefixWord ++ tailWord_6047562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047562).length < 2 ^ (prefixWord ++ tailWord_6047562).sum := by decide
  have hdescent : baseEnd_6047562 < baseStart_6047562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047565 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_6047565 : Nat := 118140960795 + 6047565 * 2 ^ 59
def prefixEnd_6047565 : Nat := 4983230072969 + 3 ^ 40 * 6047565 * 2
def baseEnd_6047565 : Nat := 3105307634307736607825261

theorem tailTrace_6047565 : CollatzResearch.WordTrace tailWord_6047565 prefixEnd_6047565 3105307634307736607825261 := by
  unfold tailWord_6047565
  simp only [CollatzResearch.WordTrace]
  refine ⟨220572816335712321718368149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147048544223808214478912099 220572816335712321718368149)
  ·
    refine ⟨10339350765736515080548507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 220572816335712321718368149 10339350765736515080548507)
    ·
      refine ⟨15509026148604772620822761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10339350765736515080548507 15509026148604772620822761)
      ·
        refine ⟨11631769611453579465617071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15509026148604772620822761 11631769611453579465617071)
        ·
          refine ⟨17447654417180369198425607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11631769611453579465617071 17447654417180369198425607)
          ·
            refine ⟨26171481625770553797638411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17447654417180369198425607 26171481625770553797638411)
            ·
              refine ⟨39257222438655830696457617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26171481625770553797638411 39257222438655830696457617)
              ·
                refine ⟨29442916828991873022343213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39257222438655830696457617 29442916828991873022343213)
                ·
                  refine ⟨11041093810871952383378705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29442916828991873022343213 11041093810871952383378705)
                  ·
                    refine ⟨8280820358153964287534029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11041093810871952383378705 8280820358153964287534029)
                    ·
                      refine ⟨3105307634307736607825261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8280820358153964287534029 3105307634307736607825261)
                      ·
                        rfl

theorem cell23_6047565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_6047565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047565 prefixEnd_6047565 := by exact prefixLift 6047565
  have htrace : WordTrace (prefixWord ++ tailWord_6047565) baseStart_6047565 baseEnd_6047565 := by
    simpa [prefixWord, tailWord_6047565, baseEnd_6047565] using wordTrace_append hprefix tailTrace_6047565
  have hstable : (prefixWord ++ tailWord_6047565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047565).length < 2 ^ (prefixWord ++ tailWord_6047565).sum := by decide
  have hdescent : baseEnd_6047565 < baseStart_6047565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047578 : List Nat := [3, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3]
def baseStart_6047578 : Nat := 118140960795 + 6047578 * 2 ^ 59
def prefixEnd_6047578 : Nat := 4983230072969 + 3 ^ 40 * 6047578 * 2
def baseEnd_6047578 : Nat := 3105314309556245056962701

theorem tailTrace_6047578 : CollatzResearch.WordTrace tailWord_6047578 prefixEnd_6047578 3105314309556245056962701 := by
  unfold tailWord_6047578
  simp only [CollatzResearch.WordTrace]
  refine ⟨55143322621166306234647847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147048860323110149959060925 55143322621166306234647847)
  ·
    refine ⟨82714983931749459351971771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55143322621166306234647847 82714983931749459351971771)
    ·
      refine ⟨124072475897624189027957657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82714983931749459351971771 124072475897624189027957657)
      ·
        refine ⟨93054356923218141770968243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124072475897624189027957657 93054356923218141770968243)
        ·
          refine ⟨139581535384827212656452365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93054356923218141770968243 139581535384827212656452365)
          ·
            refine ⟨52343075769310204746169637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139581535384827212656452365 52343075769310204746169637)
            ·
              refine ⟨9814326706745663389906807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52343075769310204746169637 9814326706745663389906807)
              ·
                refine ⟨14721490060118495084860211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9814326706745663389906807 14721490060118495084860211)
                ·
                  refine ⟨22082235090177742627290317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14721490060118495084860211 22082235090177742627290317)
                  ·
                    refine ⟨8280838158816653485233869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22082235090177742627290317 8280838158816653485233869)
                    ·
                      refine ⟨3105314309556245056962701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8280838158816653485233869 3105314309556245056962701)
                      ·
                        rfl

theorem cell23_6047578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_6047578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047578 prefixEnd_6047578 := by exact prefixLift 6047578
  have htrace : WordTrace (prefixWord ++ tailWord_6047578) baseStart_6047578 baseEnd_6047578 := by
    simpa [prefixWord, tailWord_6047578, baseEnd_6047578] using wordTrace_append hprefix tailTrace_6047578
  have hstable : (prefixWord ++ tailWord_6047578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047578).length < 2 ^ (prefixWord ++ tailWord_6047578).sum := by decide
  have hdescent : baseEnd_6047578 < baseStart_6047578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047591 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_6047591 : Nat := 118140960795 + 6047591 * 2 ^ 59
def prefixEnd_6047591 : Nat := 4983230072969 + 3 ^ 40 * 6047591 * 2
def baseEnd_6047591 : Nat := 3105320984804753506100141

theorem tailTrace_6047591 : CollatzResearch.WordTrace tailWord_6047591 prefixEnd_6047591 3105320984804753506100141 := by
  unfold tailWord_6047591
  simp only [CollatzResearch.WordTrace]
  refine ⟨220573764633618128158814627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147049176422412085439209751 220573764633618128158814627)
  ·
    refine ⟨330860646950427192238221941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220573764633618128158814627 330860646950427192238221941)
    ·
      refine ⟨31018185651602549272333307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 330860646950427192238221941 31018185651602549272333307)
      ·
        refine ⟨46527278477403823908499961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31018185651602549272333307 46527278477403823908499961)
        ·
          refine ⟨34895458858052867931374971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46527278477403823908499961 34895458858052867931374971)
          ·
            refine ⟨52343188287079301897062457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34895458858052867931374971 52343188287079301897062457)
            ·
              refine ⟨39257391215309476422796843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52343188287079301897062457 39257391215309476422796843)
              ·
                refine ⟨58886086822964214634195265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39257391215309476422796843 58886086822964214634195265)
                ·
                  refine ⟨44164565117223160975646449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58886086822964214634195265 44164565117223160975646449)
                  ·
                    refine ⟨33123423837917370731734837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44164565117223160975646449 33123423837917370731734837)
                    ·
                      refine ⟨3105320984804753506100141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33123423837917370731734837 3105320984804753506100141)
                      ·
                        rfl

theorem cell23_6047591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_6047591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047591 prefixEnd_6047591 := by exact prefixLift 6047591
  have htrace : WordTrace (prefixWord ++ tailWord_6047591) baseStart_6047591 baseEnd_6047591 := by
    simpa [prefixWord, tailWord_6047591, baseEnd_6047591] using wordTrace_append hprefix tailTrace_6047591
  have hstable : (prefixWord ++ tailWord_6047591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047591).length < 2 ^ (prefixWord ++ tailWord_6047591).sum := by decide
  have hdescent : baseEnd_6047591 < baseStart_6047591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047641 : List Nat := [1, 2, 1, 2, 1, 3, 4, 2, 7]
def baseStart_6047641 : Nat := 118140960795 + 6047641 * 2 ^ 59
def prefixEnd_6047641 : Nat := 4983230072969 + 3 ^ 40 * 6047641 * 2
def baseEnd_6047641 : Nat := 345038517648608701163879

theorem tailTrace_6047641 : CollatzResearch.WordTrace tailWord_6047641 prefixEnd_6047641 345038517648608701163879 := by
  unfold tailWord_6047641
  simp only [CollatzResearch.WordTrace]
  refine ⟨220575588283436986698134777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147050392188957991132089851 220575588283436986698134777)
  ·
    refine ⟨165431691212577740023601083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220575588283436986698134777 165431691212577740023601083)
    ·
      refine ⟨248147536818866610035401625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165431691212577740023601083 248147536818866610035401625)
      ·
        refine ⟨186110652614149957526551219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248147536818866610035401625 186110652614149957526551219)
        ·
          refine ⟨279165978921224936289826829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186110652614149957526551219 279165978921224936289826829)
          ·
            refine ⟨104687242095459351108685061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279165978921224936289826829 104687242095459351108685061)
            ·
              refine ⟨19628857892898628332878449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104687242095459351108685061 19628857892898628332878449)
              ·
                refine ⟨14721643419673971249658837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19628857892898628332878449 14721643419673971249658837)
                ·
                  refine ⟨345038517648608701163879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14721643419673971249658837 345038517648608701163879)
                  ·
                    rfl

theorem cell23_6047641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 7].length) (baseStart_6047641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047641 prefixEnd_6047641 := by exact prefixLift 6047641
  have htrace : WordTrace (prefixWord ++ tailWord_6047641) baseStart_6047641 baseEnd_6047641 := by
    simpa [prefixWord, tailWord_6047641, baseEnd_6047641] using wordTrace_append hprefix tailTrace_6047641
  have hstable : (prefixWord ++ tailWord_6047641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047641).length < 2 ^ (prefixWord ++ tailWord_6047641).sum := by decide
  have hdescent : baseEnd_6047641 < baseStart_6047641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047705 : List Nat := [1, 2, 1, 2, 6, 1, 2, 1, 2, 5]
def baseStart_6047705 : Nat := 118140960795 + 6047705 * 2 ^ 59
def prefixEnd_6047705 : Nat := 4983230072969 + 3 ^ 40 * 6047705 * 2
def baseEnd_6047705 : Nat := 1035126507199788686691539

theorem tailTrace_6047705 : CollatzResearch.WordTrace tailWord_6047705 prefixEnd_6047705 1035126507199788686691539 := by
  unfold tailWord_6047705
  simp only [CollatzResearch.WordTrace]
  refine ⟨220577922555205125628464569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147051948370136750418976379 220577922555205125628464569)
  ·
    refine ⟨165433441916403844221348427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220577922555205125628464569 165433441916403844221348427)
    ·
      refine ⟨248150162874605766332022641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165433441916403844221348427 248150162874605766332022641)
      ·
        refine ⟨186112622155954324749016981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248150162874605766332022641 186112622155954324749016981)
        ·
          refine ⟨8724029163560358972610171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 186112622155954324749016981 8724029163560358972610171)
          ·
            refine ⟨13086043745340538458915257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8724029163560358972610171 13086043745340538458915257)
            ·
              refine ⟨9814532809005403844186443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13086043745340538458915257 9814532809005403844186443)
              ·
                refine ⟨14721799213508105766279665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9814532809005403844186443 14721799213508105766279665)
                ·
                  refine ⟨11041349410131079324709749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14721799213508105766279665 11041349410131079324709749)
                  ·
                    refine ⟨1035126507199788686691539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11041349410131079324709749 1035126507199788686691539)
                    ·
                      rfl

theorem cell23_6047705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 5].length) (baseStart_6047705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047705 prefixEnd_6047705 := by exact prefixLift 6047705
  have htrace : WordTrace (prefixWord ++ tailWord_6047705) baseStart_6047705 baseEnd_6047705 := by
    simpa [prefixWord, tailWord_6047705, baseEnd_6047705] using wordTrace_append hprefix tailTrace_6047705
  have hstable : (prefixWord ++ tailWord_6047705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047705).length < 2 ^ (prefixWord ++ tailWord_6047705).sum := by decide
  have hdescent : baseEnd_6047705 < baseStart_6047705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047731 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 8]
def baseStart_6047731 : Nat := 118140960795 + 6047731 * 2 ^ 59
def prefixEnd_6047731 : Nat := 4983230072969 + 3 ^ 40 * 6047731 * 2
def baseEnd_6047731 : Nat := 345043652455153662038833

theorem tailTrace_6047731 : CollatzResearch.WordTrace tailWord_6047731 prefixEnd_6047731 345043652455153662038833 := by
  unfold tailWord_6047731
  simp only [CollatzResearch.WordTrace]
  refine ⟨220578870853110932068911047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147052580568740621379274031 220578870853110932068911047)
  ·
    refine ⟨330868306279666398103366571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220578870853110932068911047 330868306279666398103366571)
    ·
      refine ⟨496302459419499597155049857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330868306279666398103366571 496302459419499597155049857)
      ·
        refine ⟨372226844564624697866287393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496302459419499597155049857 372226844564624697866287393)
        ·
          refine ⟨279170133423468523399715545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372226844564624697866287393 279170133423468523399715545)
          ·
            refine ⟨209377600067601392549786659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279170133423468523399715545 209377600067601392549786659)
            ·
              refine ⟨314066400101402088824679989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209377600067601392549786659 314066400101402088824679989)
              ·
                refine ⟨29443725009506445827313749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 314066400101402088824679989 29443725009506445827313749)
                ·
                  refine ⟨345043652455153662038833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29443725009506445827313749 345043652455153662038833)
                  ·
                    rfl

theorem cell23_6047731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 8].length) (baseStart_6047731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047731 prefixEnd_6047731 := by exact prefixLift 6047731
  have htrace : WordTrace (prefixWord ++ tailWord_6047731) baseStart_6047731 baseEnd_6047731 := by
    simpa [prefixWord, tailWord_6047731, baseEnd_6047731] using wordTrace_append hprefix tailTrace_6047731
  have hstable : (prefixWord ++ tailWord_6047731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047731).length < 2 ^ (prefixWord ++ tailWord_6047731).sum := by decide
  have hdescent : baseEnd_6047731 < baseStart_6047731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047742 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_6047742 : Nat := 118140960795 + 6047742 * 2 ^ 59
def prefixEnd_6047742 : Nat := 4983230072969 + 3 ^ 40 * 6047742 * 2
def baseEnd_6047742 : Nat := 3105398520383582415311947

theorem tailTrace_6047742 : CollatzResearch.WordTrace tailWord_6047742 prefixEnd_6047742 3105398520383582415311947 := by
  unfold tailWord_6047742
  simp only [CollatzResearch.WordTrace]
  refine ⟨27572409007008885118445185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147052848037380720631707653 27572409007008885118445185)
  ·
    refine ⟨20679306755256663838833889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27572409007008885118445185 20679306755256663838833889)
    ·
      refine ⟨15509480066442497879125417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20679306755256663838833889 15509480066442497879125417)
      ·
        refine ⟨11632110049831873409344063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15509480066442497879125417 11632110049831873409344063)
        ·
          refine ⟨17448165074747810114016095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11632110049831873409344063 17448165074747810114016095)
          ·
            refine ⟨26172247612121715171024143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17448165074747810114016095 26172247612121715171024143)
            ·
              refine ⟨39258371418182572756536215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26172247612121715171024143 39258371418182572756536215)
              ·
                refine ⟨58887557127273859134804323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39258371418182572756536215 58887557127273859134804323)
                ·
                  refine ⟨88331335690910788702206485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58887557127273859134804323 88331335690910788702206485)
                  ·
                    refine ⟨4140531360511443220415929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88331335690910788702206485 4140531360511443220415929)
                    ·
                      refine ⟨3105398520383582415311947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4140531360511443220415929 3105398520383582415311947)
                      ·
                        rfl

theorem cell23_6047742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_6047742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047742 prefixEnd_6047742 := by exact prefixLift 6047742
  have htrace : WordTrace (prefixWord ++ tailWord_6047742) baseStart_6047742 baseEnd_6047742 := by
    simpa [prefixWord, tailWord_6047742, baseEnd_6047742] using wordTrace_append hprefix tailTrace_6047742
  have hstable : (prefixWord ++ tailWord_6047742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047742).length < 2 ^ (prefixWord ++ tailWord_6047742).sum := by decide
  have hdescent : baseEnd_6047742 < baseStart_6047742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047775 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 5, 1, 3]
def baseStart_6047775 : Nat := 118140960795 + 6047775 * 2 ^ 59
def prefixEnd_6047775 : Nat := 4983230072969 + 3 ^ 40 * 6047775 * 2
def baseEnd_6047775 : Nat := 3105415465245180786199295

theorem tailTrace_6047775 : CollatzResearch.WordTrace tailWord_6047775 prefixEnd_6047775 3105415465245180786199295 := by
  unfold tailWord_6047775
  simp only [CollatzResearch.WordTrace]
  refine ⟨220580475664951527583512779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147053650443301018389008519 220580475664951527583512779)
  ·
    refine ⟨330870713497427291375269169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220580475664951527583512779 330870713497427291375269169)
    ·
      refine ⟨248153035123070468531451877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330870713497427291375269169 248153035123070468531451877)
      ·
        refine ⟨46528694085575712849647227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248153035123070468531451877 46528694085575712849647227)
        ·
          refine ⟨69793041128363569274470841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46528694085575712849647227 69793041128363569274470841)
          ·
            refine ⟨52344780846272676955853131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69793041128363569274470841 52344780846272676955853131)
            ·
              refine ⟨78517171269409015433779697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52344780846272676955853131 78517171269409015433779697)
              ·
                refine ⟨58887878452056761575334773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78517171269409015433779697 58887878452056761575334773)
                ·
                  refine ⟨5520738604880321397687635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58887878452056761575334773 5520738604880321397687635)
                  ·
                    refine ⟨8281107907320482096531453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5520738604880321397687635 8281107907320482096531453)
                    ·
                      refine ⟨3105415465245180786199295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8281107907320482096531453 3105415465245180786199295)
                      ·
                        rfl

theorem cell23_6047775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_6047775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047775 prefixEnd_6047775 := by exact prefixLift 6047775
  have htrace : WordTrace (prefixWord ++ tailWord_6047775) baseStart_6047775 baseEnd_6047775 := by
    simpa [prefixWord, tailWord_6047775, baseEnd_6047775] using wordTrace_append hprefix tailTrace_6047775
  have hstable : (prefixWord ++ tailWord_6047775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047775).length < 2 ^ (prefixWord ++ tailWord_6047775).sum := by decide
  have hdescent : baseEnd_6047775 < baseStart_6047775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047792 : List Nat := [2, 1, 1, 1, 2, 6, 2, 1, 3, 1, 3]
def baseStart_6047792 : Nat := 118140960795 + 6047792 * 2 ^ 59
def prefixEnd_6047792 : Nat := 4983230072969 + 3 ^ 40 * 6047792 * 2
def baseEnd_6047792 : Nat := 3105424194416307219686717

theorem tailTrace_6047792 : CollatzResearch.WordTrace tailWord_6047792 prefixEnd_6047792 3105424194416307219686717 := by
  unfold tailWord_6047792
  simp only [CollatzResearch.WordTrace]
  refine ⟨110290547852944969743440815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147054063803926626324587753 110290547852944969743440815)
  ·
    refine ⟨165435821779417454615161223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110290547852944969743440815 165435821779417454615161223)
    ·
      refine ⟨248153732669126181922741835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165435821779417454615161223 248153732669126181922741835)
      ·
        refine ⟨372230599003689272884112753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248153732669126181922741835 372230599003689272884112753)
        ·
          refine ⟨279172949252766954663084565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372230599003689272884112753 279172949252766954663084565)
          ·
            refine ⟨13086231996223450999832089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 279172949252766954663084565 13086231996223450999832089)
            ·
              refine ⟨9814673997167588249874067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13086231996223450999832089 9814673997167588249874067)
              ·
                refine ⟨14722010995751382374811101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9814673997167588249874067 14722010995751382374811101)
                ·
                  refine ⟨5520754123406768390554163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14722010995751382374811101 5520754123406768390554163)
                  ·
                    refine ⟨8281131185110152585831245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5520754123406768390554163 8281131185110152585831245)
                    ·
                      refine ⟨3105424194416307219686717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8281131185110152585831245 3105424194416307219686717)
                      ·
                        rfl

theorem cell23_6047792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 3, 1, 3].length) (baseStart_6047792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047792 prefixEnd_6047792 := by exact prefixLift 6047792
  have htrace : WordTrace (prefixWord ++ tailWord_6047792) baseStart_6047792 baseEnd_6047792 := by
    simpa [prefixWord, tailWord_6047792, baseEnd_6047792] using wordTrace_append hprefix tailTrace_6047792
  have hstable : (prefixWord ++ tailWord_6047792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047792).length < 2 ^ (prefixWord ++ tailWord_6047792).sum := by decide
  have hdescent : baseEnd_6047792 < baseStart_6047792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047815 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 2, 6, 2]
def baseStart_6047815 : Nat := 118140960795 + 6047815 * 2 ^ 59
def prefixEnd_6047815 : Nat := 4983230072969 + 3 ^ 40 * 6047815 * 2
def baseEnd_6047815 : Nat := 3105436004471360629699111

theorem tailTrace_6047815 : CollatzResearch.WordTrace tailWord_6047815 prefixEnd_6047815 3105436004471360629699111 := by
  unfold tailWord_6047815
  simp only [CollatzResearch.WordTrace]
  refine ⟨220581934584806614414968899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147054623056537742943312599 220581934584806614414968899)
  ·
    refine ⟨330872901877209921622453349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220581934584806614414968899 330872901877209921622453349)
    ·
      refine ⟨62038669101976860304210003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 330872901877209921622453349 62038669101976860304210003)
      ·
        refine ⟨93058003652965290456315005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62038669101976860304210003 93058003652965290456315005)
        ·
          refine ⟨34896751369861983921118127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93058003652965290456315005 34896751369861983921118127)
          ·
            refine ⟨52345127054792975881677191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34896751369861983921118127 52345127054792975881677191)
            ·
              refine ⟨78517690582189463822515787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52345127054792975881677191 78517690582189463822515787)
              ·
                refine ⟨117776535873284195733773681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78517690582189463822515787 117776535873284195733773681)
                ·
                  refine ⟨88332401904963146800330261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117776535873284195733773681 88332401904963146800330261)
                  ·
                    refine ⟨4140581339295147506265481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88332401904963146800330261 4140581339295147506265481)
                    ·
                      refine ⟨3105436004471360629699111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4140581339295147506265481 3105436004471360629699111)
                      ·
                        rfl

theorem cell23_6047815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_6047815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047815 prefixEnd_6047815 := by exact prefixLift 6047815
  have htrace : WordTrace (prefixWord ++ tailWord_6047815) baseStart_6047815 baseEnd_6047815 := by
    simpa [prefixWord, tailWord_6047815, baseEnd_6047815] using wordTrace_append hprefix tailTrace_6047815
  have hstable : (prefixWord ++ tailWord_6047815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047815).length < 2 ^ (prefixWord ++ tailWord_6047815).sum := by decide
  have hdescent : baseEnd_6047815 < baseStart_6047815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047818 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_6047818 : Nat := 118140960795 + 6047818 * 2 ^ 59
def prefixEnd_6047818 : Nat := 4983230072969 + 3 ^ 40 * 6047818 * 2
def baseEnd_6047818 : Nat := 3105437544913324117961597

theorem tailTrace_6047818 : CollatzResearch.WordTrace tailWord_6047818 prefixEnd_6047818 3105437544913324117961597 := by
  unfold tailWord_6047818
  simp only [CollatzResearch.WordTrace]
  refine ⟨55145511000948936481832027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147054696002530497284885405 55145511000948936481832027)
  ·
    refine ⟨82718266501423404722748041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55145511000948936481832027 82718266501423404722748041)
    ·
      refine ⟨62038699876067553542061031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82718266501423404722748041 62038699876067553542061031)
      ·
        refine ⟨93058049814101330313091547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62038699876067553542061031 93058049814101330313091547)
        ·
          refine ⟨139587074721151995469637321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93058049814101330313091547 139587074721151995469637321)
          ·
            refine ⟨104690306040863996602227991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139587074721151995469637321 104690306040863996602227991)
            ·
              refine ⟨157035459061295994903341987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104690306040863996602227991 157035459061295994903341987)
              ·
                refine ⟨235553188591943992355012981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157035459061295994903341987 235553188591943992355012981)
                ·
                  refine ⟨22083111430494749283282467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 235553188591943992355012981 22083111430494749283282467)
                  ·
                    refine ⟨33124667145742123924923701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22083111430494749283282467 33124667145742123924923701)
                    ·
                      refine ⟨3105437544913324117961597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33124667145742123924923701 3105437544913324117961597)
                      ·
                        rfl

theorem cell23_6047818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_6047818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047818 prefixEnd_6047818 := by exact prefixLift 6047818
  have htrace : WordTrace (prefixWord ++ tailWord_6047818) baseStart_6047818 baseEnd_6047818 := by
    simpa [prefixWord, tailWord_6047818, baseEnd_6047818] using wordTrace_append hprefix tailTrace_6047818
  have hstable : (prefixWord ++ tailWord_6047818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047818).length < 2 ^ (prefixWord ++ tailWord_6047818).sum := by decide
  have hdescent : baseEnd_6047818 < baseStart_6047818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047869 : List Nat := [1, 4, 1, 1, 3, 4, 1, 2, 1, 2, 3]
def baseStart_6047869 : Nat := 118140960795 + 6047869 * 2 ^ 59
def prefixEnd_6047869 : Nat := 4983230072969 + 3 ^ 40 * 6047869 * 2
def baseEnd_6047869 : Nat := 3105463732426703418423863

theorem tailTrace_6047869 : CollatzResearch.WordTrace tailWord_6047869 prefixEnd_6047869 3105463732426703418423863 := by
  unfold tailWord_6047869
  simp only [CollatzResearch.WordTrace]
  refine ⟨220583904126610981637434661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147055936084407321091623107 220583904126610981637434661)
  ·
    refine ⟨41359482023739559057018999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220583904126610981637434661 41359482023739559057018999)
    ·
      refine ⟨62039223035609338585528499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41359482023739559057018999 62039223035609338585528499)
      ·
        refine ⟨93058834553414007878292749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62039223035609338585528499 93058834553414007878292749)
        ·
          refine ⟨34897062957530252954359781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93058834553414007878292749 34897062957530252954359781)
          ·
            refine ⟨6543199304536922428942459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34897062957530252954359781 6543199304536922428942459)
            ·
              refine ⟨9814798956805383643413689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6543199304536922428942459 9814798956805383643413689)
              ·
                refine ⟨7361099217604037732560267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9814798956805383643413689 7361099217604037732560267)
                ·
                  refine ⟨11041648826406056598840401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7361099217604037732560267 11041648826406056598840401)
                  ·
                    refine ⟨8281236619804542449130301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11041648826406056598840401 8281236619804542449130301)
                    ·
                      refine ⟨3105463732426703418423863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8281236619804542449130301 3105463732426703418423863)
                      ·
                        rfl

theorem cell23_6047869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_6047869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047869 prefixEnd_6047869 := by exact prefixLift 6047869
  have htrace : WordTrace (prefixWord ++ tailWord_6047869) baseStart_6047869 baseEnd_6047869 := by
    simpa [prefixWord, tailWord_6047869, baseEnd_6047869] using wordTrace_append hprefix tailTrace_6047869
  have hstable : (prefixWord ++ tailWord_6047869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047869).length < 2 ^ (prefixWord ++ tailWord_6047869).sum := by decide
  have hdescent : baseEnd_6047869 < baseStart_6047869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047882 : List Nat := [3, 1, 2, 3, 1, 3, 1, 2, 1, 3, 3]
def baseStart_6047882 : Nat := 118140960795 + 6047882 * 2 ^ 59
def prefixEnd_6047882 : Nat := 4983230072969 + 3 ^ 40 * 6047882 * 2
def baseEnd_6047882 : Nat := 3105470407675211867561303

theorem tailTrace_6047882 : CollatzResearch.WordTrace tailWord_6047882 prefixEnd_6047882 3105470407675211867561303 := by
  unfold tailWord_6047882
  simp only [CollatzResearch.WordTrace]
  refine ⟨55146094568890971214414475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147056252183709256571771933 55146094568890971214414475)
  ·
    refine ⟨82719141853336456821621713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55146094568890971214414475 82719141853336456821621713)
    ·
      refine ⟨62039356390002342616216285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82719141853336456821621713 62039356390002342616216285)
      ·
        refine ⟨23264758646250878481081107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62039356390002342616216285 23264758646250878481081107)
        ·
          refine ⟨34897137969376317721621661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23264758646250878481081107 34897137969376317721621661)
          ·
            refine ⟨13086426738516119145608123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34897137969376317721621661 13086426738516119145608123)
            ·
              refine ⟨19629640107774178718412185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13086426738516119145608123 19629640107774178718412185)
              ·
                refine ⟨14722230080830634038809139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19629640107774178718412185 14722230080830634038809139)
                ·
                  refine ⟨22083345121245951058213709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14722230080830634038809139 22083345121245951058213709)
                  ·
                    refine ⟨8281254420467231646830141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22083345121245951058213709 8281254420467231646830141)
                    ·
                      refine ⟨3105470407675211867561303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8281254420467231646830141 3105470407675211867561303)
                      ·
                        rfl

theorem cell23_6047882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_6047882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047882 prefixEnd_6047882 := by exact prefixLift 6047882
  have htrace : WordTrace (prefixWord ++ tailWord_6047882) baseStart_6047882 baseEnd_6047882 := by
    simpa [prefixWord, tailWord_6047882, baseEnd_6047882] using wordTrace_append hprefix tailTrace_6047882
  have hstable : (prefixWord ++ tailWord_6047882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047882).length < 2 ^ (prefixWord ++ tailWord_6047882).sum := by decide
  have hdescent : baseEnd_6047882 < baseStart_6047882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047886 : List Nat := [4, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3]
def baseStart_6047886 : Nat := 118140960795 + 6047886 * 2 ^ 59
def prefixEnd_6047886 : Nat := 4983230072969 + 3 ^ 40 * 6047886 * 2
def baseEnd_6047886 : Nat := 3105472461597829851911285

theorem tailTrace_6047886 : CollatzResearch.WordTrace tailWord_6047886 prefixEnd_6047886 3105472461597829851911285 := by
  unfold tailWord_6047886
  simp only [CollatzResearch.WordTrace]
  refine ⟨27573065520943674192600439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147056349445032929027202341 27573065520943674192600439)
  ·
    refine ⟨41359598281415511288900659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27573065520943674192600439 41359598281415511288900659)
    ·
      refine ⟨62039397422123266933350989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41359598281415511288900659 62039397422123266933350989)
      ·
        refine ⟨23264774033296225100006621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62039397422123266933350989 23264774033296225100006621)
        ·
          refine ⟨8724290262486084412502483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23264774033296225100006621 8724290262486084412502483)
          ·
            refine ⟨13086435393729126618753725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8724290262486084412502483 13086435393729126618753725)
            ·
              refine ⟨4907413272648422482032647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13086435393729126618753725 4907413272648422482032647)
              ·
                refine ⟨7361119908972633723048971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4907413272648422482032647 7361119908972633723048971)
                ·
                  refine ⟨11041679863458950584573457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7361119908972633723048971 11041679863458950584573457)
                  ·
                    refine ⟨8281259897594212938430093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11041679863458950584573457 8281259897594212938430093)
                    ·
                      refine ⟨3105472461597829851911285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8281259897594212938430093 3105472461597829851911285)
                      ·
                        rfl

theorem cell23_6047886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_6047886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047886 prefixEnd_6047886 := by exact prefixLift 6047886
  have htrace : WordTrace (prefixWord ++ tailWord_6047886) baseStart_6047886 baseEnd_6047886 := by
    simpa [prefixWord, tailWord_6047886, baseEnd_6047886] using wordTrace_append hprefix tailTrace_6047886
  have hstable : (prefixWord ++ tailWord_6047886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047886).length < 2 ^ (prefixWord ++ tailWord_6047886).sum := by decide
  have hdescent : baseEnd_6047886 < baseStart_6047886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047905 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_6047905 : Nat := 118140960795 + 6047905 * 2 ^ 59
def prefixEnd_6047905 : Nat := 4983230072969 + 3 ^ 40 * 6047905 * 2
def baseEnd_6047905 : Nat := 3105482217730265277573697

theorem tailTrace_6047905 : CollatzResearch.WordTrace tailWord_6047905 prefixEnd_6047905 3105482217730265277573697 := by
  unfold tailWord_6047905
  simp only [CollatzResearch.WordTrace]
  refine ⟨220585217154480559785745169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147056811436320373190496779 220585217154480559785745169)
  ·
    refine ⟨165438912865860419839308877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220585217154480559785745169 165438912865860419839308877)
    ·
      refine ⟨62039592324697657439740829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165438912865860419839308877 62039592324697657439740829)
      ·
        refine ⟨23264847121761621539902811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62039592324697657439740829 23264847121761621539902811)
        ·
          refine ⟨34897270682642432309854217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23264847121761621539902811 34897270682642432309854217)
          ·
            refine ⟨26172953011981824232390663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34897270682642432309854217 26172953011981824232390663)
            ·
              refine ⟨39259429517972736348585995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26172953011981824232390663 39259429517972736348585995)
              ·
                refine ⟨58889144276959104522878993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39259429517972736348585995 58889144276959104522878993)
                ·
                  refine ⟨44166858207719328392159245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58889144276959104522878993 44166858207719328392159245)
                  ·
                    refine ⟨16562571827894748147059717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44166858207719328392159245 16562571827894748147059717)
                    ·
                      refine ⟨3105482217730265277573697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16562571827894748147059717 3105482217730265277573697)
                      ·
                        rfl

theorem cell23_6047905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_6047905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047905 prefixEnd_6047905 := by exact prefixLift 6047905
  have htrace : WordTrace (prefixWord ++ tailWord_6047905) baseStart_6047905 baseEnd_6047905 := by
    simpa [prefixWord, tailWord_6047905, baseEnd_6047905] using wordTrace_append hprefix tailTrace_6047905
  have hstable : (prefixWord ++ tailWord_6047905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047905).length < 2 ^ (prefixWord ++ tailWord_6047905).sum := by decide
  have hdescent : baseEnd_6047905 < baseStart_6047905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047962 : List Nat := [3, 1, 1, 2, 2, 1, 4, 4, 5]
def baseStart_6047962 : Nat := 118140960795 + 6047962 * 2 ^ 59
def prefixEnd_6047962 : Nat := 4983230072969 + 3 ^ 40 * 6047962 * 2
def baseEnd_6047962 : Nat := 345056831791952394951215

theorem tailTrace_6047962 : CollatzResearch.WordTrace tailWord_6047962 prefixEnd_6047962 345056831791952394951215 := by
  unfold tailWord_6047962
  simp only [CollatzResearch.WordTrace]
  refine ⟨55146824028818514630142535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147058197410182705680380093 55146824028818514630142535)
  ·
    refine ⟨82720236043227771945213803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55146824028818514630142535 82720236043227771945213803)
    ·
      refine ⟨124080354064841657917820705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82720236043227771945213803 124080354064841657917820705)
      ·
        refine ⟨93060265548631243438365529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124080354064841657917820705 93060265548631243438365529)
        ·
          refine ⟨69795199161473432578774147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93060265548631243438365529 69795199161473432578774147)
          ·
            refine ⟨104692798742210148868161221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69795199161473432578774147 104692798742210148868161221)
            ·
              refine ⟨19629899764164402912780229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104692798742210148868161221 19629899764164402912780229)
              ·
                refine ⟨3680606205780825546146293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19629899764164402912780229 3680606205780825546146293)
                ·
                  refine ⟨345056831791952394951215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3680606205780825546146293 345056831791952394951215)
                  ·
                    rfl

theorem cell23_6047962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 5].length) (baseStart_6047962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047962 prefixEnd_6047962 := by exact prefixLift 6047962
  have htrace : WordTrace (prefixWord ++ tailWord_6047962) baseStart_6047962 baseEnd_6047962 := by
    simpa [prefixWord, tailWord_6047962, baseEnd_6047962] using wordTrace_append hprefix tailTrace_6047962
  have hstable : (prefixWord ++ tailWord_6047962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047962).length < 2 ^ (prefixWord ++ tailWord_6047962).sum := by decide
  have hdescent : baseEnd_6047962 < baseStart_6047962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047973 : List Nat := [1, 3, 1, 4, 2, 2, 3, 1, 2, 2, 2]
def baseStart_6047973 : Nat := 118140960795 + 6047973 * 2 ^ 59
def prefixEnd_6047973 : Nat := 4983230072969 + 3 ^ 40 * 6047973 * 2
def baseEnd_6047973 : Nat := 3105517134414771011523385

theorem tailTrace_6047973 : CollatzResearch.WordTrace tailWord_6047973 prefixEnd_6047973 3105517134414771011523385 := by
  unfold tailWord_6047973
  simp only [CollatzResearch.WordTrace]
  refine ⟨220587697318234207399220573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147058464878822804932813715 220587697318234207399220573)
  ·
    refine ⟨82720386494337827774707715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220587697318234207399220573 82720386494337827774707715)
    ·
      refine ⟨124080579741506741662061573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82720386494337827774707715 124080579741506741662061573)
      ·
        refine ⟨23265108701532514061636545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124080579741506741662061573 23265108701532514061636545)
        ·
          refine ⟨17448831526149385546227409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23265108701532514061636545 17448831526149385546227409)
          ·
            refine ⟨13086623644612039159670557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17448831526149385546227409 13086623644612039159670557)
            ·
              refine ⟨4907483866729514684876459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13086623644612039159670557 4907483866729514684876459)
              ·
                refine ⟨7361225800094272027314689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4907483866729514684876459 7361225800094272027314689)
                ·
                  refine ⟨5520919350070704020486017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7361225800094272027314689 5520919350070704020486017)
                  ·
                    refine ⟨4140689512553028015364513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5520919350070704020486017 4140689512553028015364513)
                    ·
                      refine ⟨3105517134414771011523385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4140689512553028015364513 3105517134414771011523385)
                      ·
                        rfl

theorem cell23_6047973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_6047973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047973 prefixEnd_6047973 := by exact prefixLift 6047973
  have htrace : WordTrace (prefixWord ++ tailWord_6047973) baseStart_6047973 baseEnd_6047973 := by
    simpa [prefixWord, tailWord_6047973, baseEnd_6047973] using wordTrace_append hprefix tailTrace_6047973
  have hstable : (prefixWord ++ tailWord_6047973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047973).length < 2 ^ (prefixWord ++ tailWord_6047973).sum := by decide
  have hdescent : baseEnd_6047973 < baseStart_6047973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6047995 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 4]
def baseStart_6047995 : Nat := 118140960795 + 6047995 * 2 ^ 59
def prefixEnd_6047995 : Nat := 4983230072969 + 3 ^ 40 * 6047995 * 2
def baseEnd_6047995 : Nat := 3105528430989169925448283

theorem tailTrace_6047995 : CollatzResearch.WordTrace tailWord_6047995 prefixEnd_6047995 3105528430989169925448283 := by
  unfold tailWord_6047995
  simp only [CollatzResearch.WordTrace]
  refine ⟨220588499724154505156521439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147058999816103003437680959 220588499724154505156521439)
  ·
    refine ⟨330882749586231757734782159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220588499724154505156521439 330882749586231757734782159)
    ·
      refine ⟨496324124379347636602173239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330882749586231757734782159 496324124379347636602173239)
      ·
        refine ⟨744486186569021454903259859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496324124379347636602173239 744486186569021454903259859)
        ·
          refine ⟨1116729279853532182354889789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744486186569021454903259859 1116729279853532182354889789)
          ·
            refine ⟨418773479945074568383083671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1116729279853532182354889789 418773479945074568383083671)
            ·
              refine ⟨628160219917611852574625507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418773479945074568383083671 628160219917611852574625507)
              ·
                refine ⟨942240329876417778861938261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628160219917611852574625507 942240329876417778861938261)
                ·
                  refine ⟨11041878865739270846038339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 942240329876417778861938261 11041878865739270846038339)
                  ·
                    refine ⟨16562818298608906269057509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11041878865739270846038339 16562818298608906269057509)
                    ·
                      refine ⟨3105528430989169925448283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16562818298608906269057509 3105528430989169925448283)
                      ·
                        rfl

theorem cell23_6047995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 4].length) (baseStart_6047995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6047995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6047995 prefixEnd_6047995 := by exact prefixLift 6047995
  have htrace : WordTrace (prefixWord ++ tailWord_6047995) baseStart_6047995 baseEnd_6047995 := by
    simpa [prefixWord, tailWord_6047995, baseEnd_6047995] using wordTrace_append hprefix tailTrace_6047995
  have hstable : (prefixWord ++ tailWord_6047995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6047995).length < 2 ^ (prefixWord ++ tailWord_6047995).sum := by decide
  have hdescent : baseEnd_6047995 < baseStart_6047995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6047995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048012 : List Nat := [2, 2, 1, 2, 2, 2, 3, 2, 2, 1, 4]
def baseStart_6048012 : Nat := 118140960795 + 6048012 * 2 ^ 59
def prefixEnd_6048012 : Nat := 4983230072969 + 3 ^ 40 * 6048012 * 2
def baseEnd_6048012 : Nat := 3105537160160296358935705

theorem tailTrace_6048012 : CollatzResearch.WordTrace tailWord_6048012 prefixEnd_6048012 3105537160160296358935705 := by
  unfold tailWord_6048012
  simp only [CollatzResearch.WordTrace]
  refine ⟨110294559882546458529945145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147059413176728611373260193 110294559882546458529945145)
  ·
    refine ⟨82720919911909843897458859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110294559882546458529945145 82720919911909843897458859)
    ·
      refine ⟨124081379867864765846188289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82720919911909843897458859 124081379867864765846188289)
      ·
        refine ⟨93061034900898574384641217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124081379867864765846188289 93061034900898574384641217)
        ·
          refine ⟨69795776175673930788480913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93061034900898574384641217 69795776175673930788480913)
          ·
            refine ⟨52346832131755448091360685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69795776175673930788480913 52346832131755448091360685)
            ·
              refine ⟨19630062049408293034260257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52346832131755448091360685 19630062049408293034260257)
              ·
                refine ⟨14722546537056219775695193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19630062049408293034260257 14722546537056219775695193)
                ·
                  refine ⟨11041909902792164831771395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14722546537056219775695193 11041909902792164831771395)
                  ·
                    refine ⟨16562864854188247247657093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11041909902792164831771395 16562864854188247247657093)
                    ·
                      refine ⟨3105537160160296358935705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16562864854188247247657093 3105537160160296358935705)
                      ·
                        rfl

theorem cell23_6048012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_6048012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048012 prefixEnd_6048012 := by exact prefixLift 6048012
  have htrace : WordTrace (prefixWord ++ tailWord_6048012) baseStart_6048012 baseEnd_6048012 := by
    simpa [prefixWord, tailWord_6048012, baseEnd_6048012] using wordTrace_append hprefix tailTrace_6048012
  have hstable : (prefixWord ++ tailWord_6048012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048012).length < 2 ^ (prefixWord ++ tailWord_6048012).sum := by decide
  have hdescent : baseEnd_6048012 < baseStart_6048012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048082 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 3, 5]
def baseStart_6048082 : Nat := 118140960795 + 6048082 * 2 ^ 59
def prefixEnd_6048082 : Nat := 4983230072969 + 3 ^ 40 * 6048082 * 2
def baseEnd_6048082 : Nat := 1035191034602037028353461

theorem tailTrace_6048082 : CollatzResearch.WordTrace tailWord_6048082 prefixEnd_6048082 1035191034602037028353461 := by
  unfold tailWord_6048082
  simp only [CollatzResearch.WordTrace]
  refine ⟨55147918218709829753734625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147061115249892879343292333 55147918218709829753734625)
  ·
    refine ⟨41360938664032372315300969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55147918218709829753734625 41360938664032372315300969)
    ·
      refine ⟨31020703998024279236475727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41360938664032372315300969 31020703998024279236475727)
      ·
        refine ⟨46531055997036418854713591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31020703998024279236475727 46531055997036418854713591)
        ·
          refine ⟨69796583995554628282070387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46531055997036418854713591 69796583995554628282070387)
          ·
            refine ⟨104694875993331942423105581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69796583995554628282070387 104694875993331942423105581)
            ·
              refine ⟨39260578497499478408664593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104694875993331942423105581 39260578497499478408664593)
              ·
                refine ⟨29445433873124608806498445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39260578497499478408664593 29445433873124608806498445)
                ·
                  refine ⟨11042037702421728302436917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29445433873124608806498445 11042037702421728302436917)
                  ·
                    refine ⟨1035191034602037028353461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11042037702421728302436917 1035191034602037028353461)
                    ·
                      rfl

theorem cell23_6048082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_6048082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048082 prefixEnd_6048082 := by exact prefixLift 6048082
  have htrace : WordTrace (prefixWord ++ tailWord_6048082) baseStart_6048082 baseEnd_6048082 := by
    simpa [prefixWord, tailWord_6048082, baseEnd_6048082] using wordTrace_append hprefix tailTrace_6048082
  have hstable : (prefixWord ++ tailWord_6048082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048082).length < 2 ^ (prefixWord ++ tailWord_6048082).sum := by decide
  have hdescent : baseEnd_6048082 < baseStart_6048082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048096 : List Nat := [2, 1, 1, 3, 5, 1, 1, 2, 3, 1, 3]
def baseStart_6048096 : Nat := 118140960795 + 6048096 * 2 ^ 59
def prefixEnd_6048096 : Nat := 4983230072969 + 3 ^ 40 * 6048096 * 2
def baseEnd_6048096 : Nat := 3105580292535274030285319

theorem tailTrace_6048096 : CollatzResearch.WordTrace tailWord_6048096 prefixEnd_6048096 3105580292535274030285319 := by
  unfold tailWord_6048096
  simp only [CollatzResearch.WordTrace]
  refine ⟨110296091748394299702974071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147061455664525732937298761 110296091748394299702974071)
  ·
    refine ⟨165444137622591449554461107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110296091748394299702974071 165444137622591449554461107)
    ·
      refine ⟨248166206433887174331691661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165444137622591449554461107 248166206433887174331691661)
      ·
        refine ⟨93062327412707690374384373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248166206433887174331691661 93062327412707690374384373)
        ·
          refine ⟨8724593194941345972598535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93062327412707690374384373 8724593194941345972598535)
          ·
            refine ⟨13086889792412018958897803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8724593194941345972598535 13086889792412018958897803)
            ·
              refine ⟨19630334688618028438346705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13086889792412018958897803 19630334688618028438346705)
              ·
                refine ⟨14722751016463521328760029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19630334688618028438346705 14722751016463521328760029)
                ·
                  refine ⟨5521031631173820498285011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14722751016463521328760029 5521031631173820498285011)
                  ·
                    refine ⟨8281547446760730747427517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5521031631173820498285011 8281547446760730747427517)
                    ·
                      refine ⟨3105580292535274030285319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8281547446760730747427517 3105580292535274030285319)
                      ·
                        rfl

theorem cell23_6048096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_6048096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048096 prefixEnd_6048096 := by exact prefixLift 6048096
  have htrace : WordTrace (prefixWord ++ tailWord_6048096) baseStart_6048096 baseEnd_6048096 := by
    simpa [prefixWord, tailWord_6048096, baseEnd_6048096] using wordTrace_append hprefix tailTrace_6048096
  have hstable : (prefixWord ++ tailWord_6048096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048096).length < 2 ^ (prefixWord ++ tailWord_6048096).sum := by decide
  have hdescent : baseEnd_6048096 < baseStart_6048096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048106 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 1, 5, 2]
def baseStart_6048106 : Nat := 118140960795 + 6048106 * 2 ^ 59
def prefixEnd_6048106 : Nat := 4983230072969 + 3 ^ 40 * 6048106 * 2
def baseEnd_6048106 : Nat := 3105585427341818991160273

theorem tailTrace_6048106 : CollatzResearch.WordTrace tailWord_6048106 prefixEnd_6048106 3105585427341818991160273 := by
  unfold tailWord_6048106
  simp only [CollatzResearch.WordTrace]
  refine ⟨55148137056688092778453043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147061698817834914075874781 55148137056688092778453043)
  ·
    refine ⟨82722205585032139167679565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55148137056688092778453043 82722205585032139167679565)
    ·
      refine ⟨31020827094387052187879837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82722205585032139167679565 31020827094387052187879837)
      ·
        refine ⟨11632810160395144570454939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31020827094387052187879837 11632810160395144570454939)
        ·
          refine ⟨17449215240592716855682409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11632810160395144570454939 17449215240592716855682409)
          ·
            refine ⟨13086911430444537641761807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17449215240592716855682409 13086911430444537641761807)
            ·
              refine ⟨19630367145666806462642711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13086911430444537641761807 19630367145666806462642711)
              ·
                refine ⟨29445550718500209693964067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19630367145666806462642711 29445550718500209693964067)
                ·
                  refine ⟨44168326077750314540946101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29445550718500209693964067 44168326077750314540946101)
                  ·
                    refine ⟨4140780569789091988213697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44168326077750314540946101 4140780569789091988213697)
                    ·
                      refine ⟨3105585427341818991160273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4140780569789091988213697 3105585427341818991160273)
                      ·
                        rfl

theorem cell23_6048106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_6048106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048106 prefixEnd_6048106 := by exact prefixLift 6048106
  have htrace : WordTrace (prefixWord ++ tailWord_6048106) baseStart_6048106 baseEnd_6048106 := by
    simpa [prefixWord, tailWord_6048106, baseEnd_6048106] using wordTrace_append hprefix tailTrace_6048106
  have hstable : (prefixWord ++ tailWord_6048106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048106).length < 2 ^ (prefixWord ++ tailWord_6048106).sum := by decide
  have hdescent : baseEnd_6048106 < baseStart_6048106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048112 : List Nat := [2, 1, 1, 1, 4, 3, 2, 2, 1, 6]
def baseStart_6048112 : Nat := 118140960795 + 6048112 * 2 ^ 59
def prefixEnd_6048112 : Nat := 4983230072969 + 3 ^ 40 * 6048112 * 2
def baseEnd_6048112 : Nat := 1035196169408581989228415

theorem tailTrace_6048112 : CollatzResearch.WordTrace tailWord_6048112 prefixEnd_6048112 1035196169408581989228415 := by
  unfold tailWord_6048112
  simp only [CollatzResearch.WordTrace]
  refine ⟨110296383532365317069265295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147061844709820422759020393 110296383532365317069265295)
  ·
    refine ⟨165444575298547975603897943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110296383532365317069265295 165444575298547975603897943)
    ·
      refine ⟨248166862947821963405846915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165444575298547975603897943 248166862947821963405846915)
      ·
        refine ⟨372250294421732945108770373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248166862947821963405846915 372250294421732945108770373)
        ·
          refine ⟨69796930204074927207894445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 372250294421732945108770373 69796930204074927207894445)
          ·
            refine ⟨26173848826528097702960417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69796930204074927207894445 26173848826528097702960417)
            ·
              refine ⟨19630386619896073277220313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26173848826528097702960417 19630386619896073277220313)
              ·
                refine ⟨14722789964922054957915235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19630386619896073277220313 14722789964922054957915235)
                ·
                  refine ⟨22084184947383082436872853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14722789964922054957915235 22084184947383082436872853)
                  ·
                    refine ⟨1035196169408581989228415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22084184947383082436872853 1035196169408581989228415)
                    ·
                      rfl

theorem cell23_6048112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 1, 6].length) (baseStart_6048112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048112 prefixEnd_6048112 := by exact prefixLift 6048112
  have htrace : WordTrace (prefixWord ++ tailWord_6048112) baseStart_6048112 baseEnd_6048112 := by
    simpa [prefixWord, tailWord_6048112, baseEnd_6048112] using wordTrace_append hprefix tailTrace_6048112
  have hstable : (prefixWord ++ tailWord_6048112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048112).length < 2 ^ (prefixWord ++ tailWord_6048112).sum := by decide
  have hdescent : baseEnd_6048112 < baseStart_6048112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048130 : List Nat := [3, 4, 2, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_6048130 : Nat := 118140960795 + 6048130 * 2 ^ 59
def prefixEnd_6048130 : Nat := 4983230072969 + 3 ^ 40 * 6048130 * 2
def baseEnd_6048130 : Nat := 3105597750877526897260163

theorem tailTrace_6048130 : CollatzResearch.WordTrace tailWord_6048130 prefixEnd_6048130 3105597750877526897260163 := by
  unfold tailWord_6048130
  simp only [CollatzResearch.WordTrace]
  refine ⟨55148355894666355803171461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147062282385776948808457229 55148355894666355803171461)
  ·
    refine ⟨10340316730249941713094649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55148355894666355803171461 10340316730249941713094649)
    ·
      refine ⟨7755237547687456284820987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10340316730249941713094649 7755237547687456284820987)
      ·
        refine ⟨11632856321531184427231481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7755237547687456284820987 11632856321531184427231481)
        ·
          refine ⟨8724642241148388320423611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11632856321531184427231481 8724642241148388320423611)
          ·
            refine ⟨13086963361722582480635417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8724642241148388320423611 13086963361722582480635417)
            ·
              refine ⟨9815222521291936860476563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13086963361722582480635417 9815222521291936860476563)
              ·
                refine ⟨14722833781937905290714845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9815222521291936860476563 14722833781937905290714845)
                ·
                  refine ⟨5521062668226714484018067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14722833781937905290714845 5521062668226714484018067)
                  ·
                    refine ⟨8281594002340071726027101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5521062668226714484018067 8281594002340071726027101)
                    ·
                      refine ⟨3105597750877526897260163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8281594002340071726027101 3105597750877526897260163)
                      ·
                        rfl

theorem cell23_6048130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_6048130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048130 prefixEnd_6048130 := by exact prefixLift 6048130
  have htrace : WordTrace (prefixWord ++ tailWord_6048130) baseStart_6048130 baseEnd_6048130 := by
    simpa [prefixWord, tailWord_6048130, baseEnd_6048130] using wordTrace_append hprefix tailTrace_6048130
  have hstable : (prefixWord ++ tailWord_6048130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048130).length < 2 ^ (prefixWord ++ tailWord_6048130).sum := by decide
  have hdescent : baseEnd_6048130 < baseStart_6048130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048132 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_6048132 : Nat := 118140960795 + 6048132 * 2 ^ 59
def prefixEnd_6048132 : Nat := 4983230072969 + 3 ^ 40 * 6048132 * 2
def baseEnd_6048132 : Nat := 3105598777838835889435153

theorem tailTrace_6048132 : CollatzResearch.WordTrace tailWord_6048132 prefixEnd_6048132 3105598777838835889435153 := by
  unfold tailWord_6048132
  simp only [CollatzResearch.WordTrace]
  refine ⟨110296748262329088777129325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147062331016438785036172433 110296748262329088777129325)
  ·
    refine ⟨41361280598373408291423497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110296748262329088777129325 41361280598373408291423497)
    ·
      refine ⟨31020960448780056218567623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41361280598373408291423497 31020960448780056218567623)
      ·
        refine ⟨46531440673170084327851435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31020960448780056218567623 46531440673170084327851435)
        ·
          refine ⟨69797161009755126491777153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46531440673170084327851435 69797161009755126491777153)
          ·
            refine ⟨52347870757316344868832865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69797161009755126491777153 52347870757316344868832865)
            ·
              refine ⟨39260903067987258651624649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52347870757316344868832865 39260903067987258651624649)
              ·
                refine ⟨29445677300990443988718487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39260903067987258651624649 29445677300990443988718487)
                ·
                  refine ⟨44168515951485665983077731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29445677300990443988718487 44168515951485665983077731)
                  ·
                    refine ⟨66252773927228498974616597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44168515951485665983077731 66252773927228498974616597)
                    ·
                      refine ⟨3105598777838835889435153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66252773927228498974616597 3105598777838835889435153)
                      ·
                        rfl

theorem cell23_6048132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_6048132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048132 prefixEnd_6048132 := by exact prefixLift 6048132
  have htrace : WordTrace (prefixWord ++ tailWord_6048132) baseStart_6048132 baseEnd_6048132 := by
    simpa [prefixWord, tailWord_6048132, baseEnd_6048132] using wordTrace_append hprefix tailTrace_6048132
  have hstable : (prefixWord ++ tailWord_6048132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048132).length < 2 ^ (prefixWord ++ tailWord_6048132).sum := by decide
  have hdescent : baseEnd_6048132 < baseStart_6048132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048179 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 7, 3, 2]
def baseStart_6048179 : Nat := 118140960795 + 6048179 * 2 ^ 59
def prefixEnd_6048179 : Nat := 4983230072969 + 3 ^ 40 * 6048179 * 2
def baseEnd_6048179 : Nat := 3105622911429597205547437

theorem tailTrace_6048179 : CollatzResearch.WordTrace tailWord_6048179 prefixEnd_6048179 3105622911429597205547437 := by
  unfold tailWord_6048179
  simp only [CollatzResearch.WordTrace]
  refine ⟨220595210755487904581219591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147063473836991936387479727 220595210755487904581219591)
  ·
    refine ⟨330892816133231856871829387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220595210755487904581219591 330892816133231856871829387)
    ·
      refine ⟨496339224199847785307744081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330892816133231856871829387 496339224199847785307744081)
      ·
        refine ⟨372254418149885838980808061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496339224199847785307744081 372254418149885838980808061)
        ·
          refine ⟨139595406806207189617803023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 372254418149885838980808061 139595406806207189617803023)
          ·
            refine ⟨209393110209310784426704535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139595406806207189617803023 209393110209310784426704535)
            ·
              refine ⟨314089665313966176640056803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209393110209310784426704535 314089665313966176640056803)
              ·
                refine ⟨471134497970949264960085205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314089665313966176640056803 471134497970949264960085205)
                ·
                  refine ⟨11042214796194123397501997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 471134497970949264960085205 11042214796194123397501997)
                  ·
                    refine ⟨4140830548572796274063249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11042214796194123397501997 4140830548572796274063249)
                    ·
                      refine ⟨3105622911429597205547437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4140830548572796274063249 3105622911429597205547437)
                      ·
                        rfl

theorem cell23_6048179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 3, 2].length) (baseStart_6048179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048179 prefixEnd_6048179 := by exact prefixLift 6048179
  have htrace : WordTrace (prefixWord ++ tailWord_6048179) baseStart_6048179 baseEnd_6048179 := by
    simpa [prefixWord, tailWord_6048179, baseEnd_6048179] using wordTrace_append hprefix tailTrace_6048179
  have hstable : (prefixWord ++ tailWord_6048179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048179).length < 2 ^ (prefixWord ++ tailWord_6048179).sum := by decide
  have hdescent : baseEnd_6048179 < baseStart_6048179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048192 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 4]
def baseStart_6048192 : Nat := 118140960795 + 6048192 * 2 ^ 59
def prefixEnd_6048192 : Nat := 4983230072969 + 3 ^ 40 * 6048192 * 2
def baseEnd_6048192 : Nat := 3105629586678105654684877

theorem tailTrace_6048192 : CollatzResearch.WordTrace tailWord_6048192 prefixEnd_6048192 3105629586678105654684877 := by
  unfold tailWord_6048192
  simp only [CollatzResearch.WordTrace]
  refine ⟨110297842452220403900721415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147063789936293871867628553 110297842452220403900721415)
  ·
    refine ⟨165446763678330605851082123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110297842452220403900721415 165446763678330605851082123)
    ·
      refine ⟨248170145517495908776623185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165446763678330605851082123 248170145517495908776623185)
      ·
        refine ⟨186127609138121931582467389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248170145517495908776623185 186127609138121931582467389)
        ·
          refine ⟨69797853426795724343425271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186127609138121931582467389 69797853426795724343425271)
          ·
            refine ⟨104696780140193586515137907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69797853426795724343425271 104696780140193586515137907)
            ·
              refine ⟨157045170210290379772706861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104696780140193586515137907 157045170210290379772706861)
              ·
                refine ⟨58891938828858892414765073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157045170210290379772706861 58891938828858892414765073)
                ·
                  refine ⟨44168954121644169311073805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58891938828858892414765073 44168954121644169311073805)
                  ·
                    refine ⟨16563357795616563491652677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44168954121644169311073805 16563357795616563491652677)
                    ·
                      refine ⟨3105629586678105654684877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16563357795616563491652677 3105629586678105654684877)
                      ·
                        rfl

theorem cell23_6048192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_6048192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048192 prefixEnd_6048192 := by exact prefixLift 6048192
  have htrace : WordTrace (prefixWord ++ tailWord_6048192) baseStart_6048192 baseEnd_6048192 := by
    simpa [prefixWord, tailWord_6048192, baseEnd_6048192] using wordTrace_append hprefix tailTrace_6048192
  have hstable : (prefixWord ++ tailWord_6048192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048192).length < 2 ^ (prefixWord ++ tailWord_6048192).sum := by decide
  have hdescent : baseEnd_6048192 < baseStart_6048192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048193 : List Nat := [1, 2, 7, 1, 1, 1, 2, 8]
def baseStart_6048193 : Nat := 118140960795 + 6048193 * 2 ^ 59
def prefixEnd_6048193 : Nat := 4983230072969 + 3 ^ 40 * 6048193 * 2
def baseEnd_6048193 : Nat := 115023337042917042621199

theorem tailTrace_6048193 : CollatzResearch.WordTrace tailWord_6048193 prefixEnd_6048193 115023337042917042621199 := by
  unfold tailWord_6048193
  simp only [CollatzResearch.WordTrace]
  refine ⟨220595721377437184972229233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147063814251624789981486155 220595721377437184972229233)
  ·
    refine ⟨165446791033077888729171925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220595721377437184972229233 165446791033077888729171925)
    ·
      refine ⟨3877659164837763017089967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 165446791033077888729171925 3877659164837763017089967)
      ·
        refine ⟨5816488747256644525634951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3877659164837763017089967 5816488747256644525634951)
        ·
          refine ⟨8724733120884966788452427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5816488747256644525634951 8724733120884966788452427)
          ·
            refine ⟨13087099681327450182678641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8724733120884966788452427 13087099681327450182678641)
            ·
              refine ⟨9815324760995587637008981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13087099681327450182678641 9815324760995587637008981)
              ·
                refine ⟨115023337042917042621199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9815324760995587637008981 115023337042917042621199)
                ·
                  rfl

theorem cell23_6048193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 8].length) (baseStart_6048193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048193 prefixEnd_6048193 := by exact prefixLift 6048193
  have htrace : WordTrace (prefixWord ++ tailWord_6048193) baseStart_6048193 baseEnd_6048193 := by
    simpa [prefixWord, tailWord_6048193, baseEnd_6048193] using wordTrace_append hprefix tailTrace_6048193
  have hstable : (prefixWord ++ tailWord_6048193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048193).length < 2 ^ (prefixWord ++ tailWord_6048193).sum := by decide
  have hdescent : baseEnd_6048193 < baseStart_6048193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048202 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 1, 8]
def baseStart_6048202 : Nat := 118140960795 + 6048202 * 2 ^ 59
def prefixEnd_6048202 : Nat := 4983230072969 + 3 ^ 40 * 6048202 * 2
def baseEnd_6048202 : Nat := 1035211573828216871853277

theorem tailTrace_6048202 : CollatzResearch.WordTrace tailWord_6048202 prefixEnd_6048202 1035211573828216871853277 := by
  unfold tailWord_6048202
  simp only [CollatzResearch.WordTrace]
  refine ⟨55149012408601144877326715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147064033089603053006204573 55149012408601144877326715)
  ·
    refine ⟨82723518612901717315990073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55149012408601144877326715 82723518612901717315990073)
    ·
      refine ⟨62042638959676287986992555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82723518612901717315990073 62042638959676287986992555)
      ·
        refine ⟨93063958439514431980488833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62042638959676287986992555 93063958439514431980488833)
        ·
          refine ⟨69797968829635823985366625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93063958439514431980488833 69797968829635823985366625)
          ·
            refine ⟨52348476622226867989024969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69797968829635823985366625 52348476622226867989024969)
            ·
              refine ⟨39261357466670150991768727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52348476622226867989024969 39261357466670150991768727)
              ·
                refine ⟨58892036200005226487653091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39261357466670150991768727 58892036200005226487653091)
                ·
                  refine ⟨88338054300007839731479637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58892036200005226487653091 88338054300007839731479637)
                  ·
                    refine ⟨1035211573828216871853277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88338054300007839731479637 1035211573828216871853277)
                    ·
                      rfl

theorem cell23_6048202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_6048202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048202 prefixEnd_6048202 := by exact prefixLift 6048202
  have htrace : WordTrace (prefixWord ++ tailWord_6048202) baseStart_6048202 baseEnd_6048202 := by
    simpa [prefixWord, tailWord_6048202, baseEnd_6048202] using wordTrace_append hprefix tailTrace_6048202
  have hstable : (prefixWord ++ tailWord_6048202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048202).length < 2 ^ (prefixWord ++ tailWord_6048202).sum := by decide
  have hdescent : baseEnd_6048202 < baseStart_6048202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048209 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 5, 4, 2]
def baseStart_6048209 : Nat := 118140960795 + 6048209 * 2 ^ 59
def prefixEnd_6048209 : Nat := 4983230072969 + 3 ^ 40 * 6048209 * 2
def baseEnd_6048209 : Nat := 3105638315849232088172299

theorem tailTrace_6048209 : CollatzResearch.WordTrace tailWord_6048209 prefixEnd_6048209 3105638315849232088172299 := by
  unfold tailWord_6048209
  simp only [CollatzResearch.WordTrace]
  refine ⟨220596304945379219704811681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147064203296919479803207787 220596304945379219704811681)
  ·
    refine ⟨165447228709034414778608761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220596304945379219704811681 165447228709034414778608761)
    ·
      refine ⟨124085421531775811083956571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165447228709034414778608761 124085421531775811083956571)
      ·
        refine ⟨186128132297663716625934857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124085421531775811083956571 186128132297663716625934857)
        ·
          refine ⟨139596099223247787469451143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186128132297663716625934857 139596099223247787469451143)
          ·
            refine ⟨209394148834871681204176715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139596099223247787469451143 209394148834871681204176715)
            ·
              refine ⟨314091223252307521806265073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209394148834871681204176715 314091223252307521806265073)
              ·
                refine ⟨235568417439230641354698805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314091223252307521806265073 235568417439230641354698805)
                ·
                  refine ⟨22084539134927872627003013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 235568417439230641354698805 22084539134927872627003013)
                  ·
                    refine ⟨4140851087798976117563065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22084539134927872627003013 4140851087798976117563065)
                    ·
                      refine ⟨3105638315849232088172299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4140851087798976117563065 3105638315849232088172299)
                      ·
                        rfl

theorem cell23_6048209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 4, 2].length) (baseStart_6048209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048209 prefixEnd_6048209 := by exact prefixLift 6048209
  have htrace : WordTrace (prefixWord ++ tailWord_6048209) baseStart_6048209 baseEnd_6048209 := by
    simpa [prefixWord, tailWord_6048209, baseEnd_6048209] using wordTrace_append hprefix tailTrace_6048209
  have hstable : (prefixWord ++ tailWord_6048209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048209).length < 2 ^ (prefixWord ++ tailWord_6048209).sum := by decide
  have hdescent : baseEnd_6048209 < baseStart_6048209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048213 : List Nat := [1, 3, 2, 3, 1, 2, 3, 2, 1, 3, 2]
def baseStart_6048213 : Nat := 118140960795 + 6048213 * 2 ^ 59
def prefixEnd_6048213 : Nat := 4983230072969 + 3 ^ 40 * 6048213 * 2
def baseEnd_6048213 : Nat := 3105640369771850072522281

theorem tailTrace_6048213 : CollatzResearch.WordTrace tailWord_6048213 prefixEnd_6048213 3105640369771850072522281 := by
  unfold tailWord_6048213
  simp only [CollatzResearch.WordTrace]
  refine ⟨220596450837364728387957293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147064300558243152258638195 220596450837364728387957293)
  ·
    refine ⟨82723669064011773145483985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220596450837364728387957293 82723669064011773145483985)
    ·
      refine ⟨62042751798008829859112989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82723669064011773145483985 62042751798008829859112989)
      ·
        refine ⟨23266031924253311197167371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62042751798008829859112989 23266031924253311197167371)
        ·
          refine ⟨34899047886379966795751057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23266031924253311197167371 34899047886379966795751057)
          ·
            refine ⟨26174285914784975096813293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34899047886379966795751057 26174285914784975096813293)
            ·
              refine ⟨9815357218044365661304985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26174285914784975096813293 9815357218044365661304985)
              ·
                refine ⟨7361517913533274245978739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9815357218044365661304985 7361517913533274245978739)
                ·
                  refine ⟨11042276870299911368968109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7361517913533274245978739 11042276870299911368968109)
                  ·
                    refine ⟨4140853826362466763363041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11042276870299911368968109 4140853826362466763363041)
                    ·
                      refine ⟨3105640369771850072522281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4140853826362466763363041 3105640369771850072522281)
                      ·
                        rfl

theorem cell23_6048213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_6048213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048213 prefixEnd_6048213 := by exact prefixLift 6048213
  have htrace : WordTrace (prefixWord ++ tailWord_6048213) baseStart_6048213 baseEnd_6048213 := by
    simpa [prefixWord, tailWord_6048213, baseEnd_6048213] using wordTrace_append hprefix tailTrace_6048213
  have hstable : (prefixWord ++ tailWord_6048213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048213).length < 2 ^ (prefixWord ++ tailWord_6048213).sum := by decide
  have hdescent : baseEnd_6048213 < baseStart_6048213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048243 : List Nat := [1, 1, 1, 2, 2, 2, 6, 2, 2, 2, 2]
def baseStart_6048243 : Nat := 118140960795 + 6048243 * 2 ^ 59
def prefixEnd_6048243 : Nat := 4983230072969 + 3 ^ 40 * 6048243 * 2
def baseEnd_6048243 : Nat := 3105655774191484955147143

theorem tailTrace_6048243 : CollatzResearch.WordTrace tailWord_6048243 prefixEnd_6048243 3105655774191484955147143 := by
  unfold tailWord_6048243
  simp only [CollatzResearch.WordTrace]
  refine ⟨220597545027256043511549383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147065030018170695674366255 220597545027256043511549383)
  ·
    refine ⟨330896317540884065267324075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220597545027256043511549383 330896317540884065267324075)
    ·
      refine ⟨496344476311326097900986113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330896317540884065267324075 496344476311326097900986113)
      ·
        refine ⟨372258357233494573425739585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496344476311326097900986113 372258357233494573425739585)
        ·
          refine ⟨279193767925120930069304689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372258357233494573425739585 279193767925120930069304689)
          ·
            refine ⟨209395325943840697551978517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279193767925120930069304689 209395325943840697551978517)
            ·
              refine ⟨9815405903617532697748993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 209395325943840697551978517 9815405903617532697748993)
              ·
                refine ⟨7361554427713149523311745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9815405903617532697748993 7361554427713149523311745)
                ·
                  refine ⟨5521165820784862142483809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7361554427713149523311745 5521165820784862142483809)
                  ·
                    refine ⟨4140874365588646606862857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5521165820784862142483809 4140874365588646606862857)
                    ·
                      refine ⟨3105655774191484955147143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4140874365588646606862857 3105655774191484955147143)
                      ·
                        rfl

theorem cell23_6048243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 2, 2].length) (baseStart_6048243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048243 prefixEnd_6048243 := by exact prefixLift 6048243
  have htrace : WordTrace (prefixWord ++ tailWord_6048243) baseStart_6048243 baseEnd_6048243 := by
    simpa [prefixWord, tailWord_6048243, baseEnd_6048243] using wordTrace_append hprefix tailTrace_6048243
  have hstable : (prefixWord ++ tailWord_6048243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048243).length < 2 ^ (prefixWord ++ tailWord_6048243).sum := by decide
  have hdescent : baseEnd_6048243 < baseStart_6048243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048252 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_6048252 : Nat := 118140960795 + 6048252 * 2 ^ 59
def prefixEnd_6048252 : Nat := 4983230072969 + 3 ^ 40 * 6048252 * 2
def baseEnd_6048252 : Nat := 3105660395517375419934601

theorem tailTrace_6048252 : CollatzResearch.WordTrace tailWord_6048252 prefixEnd_6048252 3105660395517375419934601 := by
  unfold tailWord_6048252
  simp only [CollatzResearch.WordTrace]
  refine ⟨110298936642111719024313505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147065248856148958699084673 110298936642111719024313505)
  ·
    refine ⟨82724202481583789268235129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110298936642111719024313505 82724202481583789268235129)
    ·
      refine ⟨62043151861187841951176347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82724202481583789268235129 62043151861187841951176347)
      ·
        refine ⟨93064727791781762926764521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62043151861187841951176347 93064727791781762926764521)
        ·
          refine ⟨69798545843836322195073391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93064727791781762926764521 69798545843836322195073391)
          ·
            refine ⟨104697818765754483292610087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69798545843836322195073391 104697818765754483292610087)
            ·
              refine ⟨157046728148631724938915131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104697818765754483292610087 157046728148631724938915131)
              ·
                refine ⟨235570092222947587408372697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157046728148631724938915131 235570092222947587408372697)
                ·
                  refine ⟨176677569167210690556279523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235570092222947587408372697 176677569167210690556279523)
                  ·
                    refine ⟨265016353750816035834419285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 176677569167210690556279523 265016353750816035834419285)
                    ·
                      refine ⟨3105660395517375419934601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 265016353750816035834419285 3105660395517375419934601)
                      ·
                        rfl

theorem cell23_6048252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_6048252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048252 prefixEnd_6048252 := by exact prefixLift 6048252
  have htrace : WordTrace (prefixWord ++ tailWord_6048252) baseStart_6048252 baseEnd_6048252 := by
    simpa [prefixWord, tailWord_6048252, baseEnd_6048252] using wordTrace_append hprefix tailTrace_6048252
  have hstable : (prefixWord ++ tailWord_6048252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048252).length < 2 ^ (prefixWord ++ tailWord_6048252).sum := by decide
  have hdescent : baseEnd_6048252 < baseStart_6048252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048259 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 3]
def baseStart_6048259 : Nat := 118140960795 + 6048259 * 2 ^ 59
def prefixEnd_6048259 : Nat := 4983230072969 + 3 ^ 40 * 6048259 * 2
def baseEnd_6048259 : Nat := 3105663989881956892547069

theorem tailTrace_6048259 : CollatzResearch.WordTrace tailWord_6048259 prefixEnd_6048259 3105663989881956892547069 := by
  unfold tailWord_6048259
  simp only [CollatzResearch.WordTrace]
  refine ⟨220598128595198078244131831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147065419063465385496087887 220598128595198078244131831)
  ·
    refine ⟨330897192892797117366197747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220598128595198078244131831 330897192892797117366197747)
    ·
      refine ⟨496345789339195676049296621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330897192892797117366197747 496345789339195676049296621)
      ·
        refine ⟨186129671002198378518486233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 496345789339195676049296621 186129671002198378518486233)
        ·
          refine ⟨139597253251648783888864675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186129671002198378518486233 139597253251648783888864675)
          ·
            refine ⟨209395879877473175833297013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139597253251648783888864675 209395879877473175833297013)
            ·
              refine ⟨19630863738513110234371595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 209395879877473175833297013 19630863738513110234371595)
              ·
                refine ⟨29446295607769665351557393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19630863738513110234371595 29446295607769665351557393)
                ·
                  refine ⟨22084721705827249013668045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29446295607769665351557393 22084721705827249013668045)
                  ·
                    refine ⟨8281770639685218380125517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22084721705827249013668045 8281770639685218380125517)
                    ·
                      refine ⟨3105663989881956892547069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8281770639685218380125517 3105663989881956892547069)
                      ·
                        rfl

theorem cell23_6048259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_6048259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048259 prefixEnd_6048259 := by exact prefixLift 6048259
  have htrace : WordTrace (prefixWord ++ tailWord_6048259) baseStart_6048259 baseEnd_6048259 := by
    simpa [prefixWord, tailWord_6048259, baseEnd_6048259] using wordTrace_append hprefix tailTrace_6048259
  have hstable : (prefixWord ++ tailWord_6048259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048259).length < 2 ^ (prefixWord ++ tailWord_6048259).sum := by decide
  have hdescent : baseEnd_6048259 < baseStart_6048259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048260 : List Nat := [2, 3, 2, 3, 1, 1, 2, 3, 2, 2, 2]
def baseStart_6048260 : Nat := 118140960795 + 6048260 * 2 ^ 59
def prefixEnd_6048260 : Nat := 4983230072969 + 3 ^ 40 * 6048260 * 2
def baseEnd_6048260 : Nat := 3105664503362611388634565

theorem tailTrace_6048260 : CollatzResearch.WordTrace tailWord_6048260 prefixEnd_6048260 3105664503362611388634565 := by
  unfold tailWord_6048260
  simp only [CollatzResearch.WordTrace]
  refine ⟨110299082534097227707459117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147065443378796303609945489 110299082534097227707459117)
  ·
    refine ⟨41362155950286460390297169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110299082534097227707459117 41362155950286460390297169)
    ·
      refine ⟨31021616962714845292722877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41362155950286460390297169 31021616962714845292722877)
      ·
        refine ⟨11633106361018066984771079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31021616962714845292722877 11633106361018066984771079)
        ·
          refine ⟨17449659541527100477156619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11633106361018066984771079 17449659541527100477156619)
          ·
            refine ⟨26174489312290650715734929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17449659541527100477156619 26174489312290650715734929)
            ·
              refine ⟨19630866984217988036801197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26174489312290650715734929 19630866984217988036801197)
              ·
                refine ⟨7361575119081745513800449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19630866984217988036801197 7361575119081745513800449)
                ·
                  refine ⟨5521181339311309135350337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7361575119081745513800449 5521181339311309135350337)
                  ·
                    refine ⟨4140886004483481851512753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5521181339311309135350337 4140886004483481851512753)
                    ·
                      refine ⟨3105664503362611388634565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4140886004483481851512753 3105664503362611388634565)
                      ·
                        rfl

theorem cell23_6048260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_6048260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048260 prefixEnd_6048260 := by exact prefixLift 6048260
  have htrace : WordTrace (prefixWord ++ tailWord_6048260) baseStart_6048260 baseEnd_6048260 := by
    simpa [prefixWord, tailWord_6048260, baseEnd_6048260] using wordTrace_append hprefix tailTrace_6048260
  have hstable : (prefixWord ++ tailWord_6048260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048260).length < 2 ^ (prefixWord ++ tailWord_6048260).sum := by decide
  have hdescent : baseEnd_6048260 < baseStart_6048260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048299 : List Nat := [1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 4]
def baseStart_6048299 : Nat := 118140960795 + 6048299 * 2 ^ 59
def prefixEnd_6048299 : Nat := 4983230072969 + 3 ^ 40 * 6048299 * 2
def baseEnd_6048299 : Nat := 3105684529108136736046885

theorem tailTrace_6048299 : CollatzResearch.WordTrace tailWord_6048299 prefixEnd_6048299 3105684529108136736046885 := by
  unfold tailWord_6048299
  simp only [CollatzResearch.WordTrace]
  refine ⟨220599587515053165075587951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147066391676702110050391967 220599587515053165075587951)
  ·
    refine ⟨330899381272579747613381927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220599587515053165075587951 330899381272579747613381927)
    ·
      refine ⟨496349071908869621420072891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330899381272579747613381927 496349071908869621420072891)
      ·
        refine ⟨744523607863304432130109337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496349071908869621420072891 744523607863304432130109337)
        ·
          refine ⟨558392705897478324097582003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 744523607863304432130109337 558392705897478324097582003)
          ·
            refine ⟨837589058846217486146373005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558392705897478324097582003 837589058846217486146373005)
            ·
              refine ⟨314095897067331557304889877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 837589058846217486146373005 314095897067331557304889877)
              ·
                refine ⟨14723245175031166748666713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 314095897067331557304889877 14723245175031166748666713)
                ·
                  refine ⟨11042433881273375061500035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14723245175031166748666713 11042433881273375061500035)
                  ·
                    refine ⟨16563650821910062592250053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11042433881273375061500035 16563650821910062592250053)
                    ·
                      refine ⟨3105684529108136736046885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16563650821910062592250053 3105684529108136736046885)
                      ·
                        rfl

theorem cell23_6048299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 4].length) (baseStart_6048299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048299 prefixEnd_6048299 := by exact prefixLift 6048299
  have htrace : WordTrace (prefixWord ++ tailWord_6048299) baseStart_6048299 baseEnd_6048299 := by
    simpa [prefixWord, tailWord_6048299, baseEnd_6048299] using wordTrace_append hprefix tailTrace_6048299
  have hstable : (prefixWord ++ tailWord_6048299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048299).length < 2 ^ (prefixWord ++ tailWord_6048299).sum := by decide
  have hdescent : baseEnd_6048299 < baseStart_6048299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048319 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 3]
def baseStart_6048319 : Nat := 118140960795 + 6048319 * 2 ^ 59
def prefixEnd_6048319 : Nat := 4983230072969 + 3 ^ 40 * 6048319 * 2
def baseEnd_6048319 : Nat := 3105694798721226657796793

theorem tailTrace_6048319 : CollatzResearch.WordTrace tailWord_6048319 prefixEnd_6048319 3105694798721226657796793 := by
  unfold tailWord_6048319
  simp only [CollatzResearch.WordTrace]
  refine ⟨220600316974980708491316011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147066877983320472327544007 220600316974980708491316011)
  ·
    refine ⟨330900475462471062736974017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220600316974980708491316011 330900475462471062736974017)
    ·
      refine ⟨248175356596853297052730513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330900475462471062736974017 248175356596853297052730513)
      ·
        refine ⟨186131517447639972789547885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248175356596853297052730513 186131517447639972789547885)
        ·
          refine ⟨69799319042864989796080457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186131517447639972789547885 69799319042864989796080457)
          ·
            refine ⟨52349489282148742347060343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69799319042864989796080457 52349489282148742347060343)
            ·
              refine ⟨78524233923223113520590515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52349489282148742347060343 78524233923223113520590515)
              ·
                refine ⟨117786350884834670280885773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78524233923223113520590515 117786350884834670280885773)
                ·
                  refine ⟨44169881581813001355332165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117786350884834670280885773 44169881581813001355332165)
                  ·
                    refine ⟨8281852796589937754124781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44169881581813001355332165 8281852796589937754124781)
                    ·
                      refine ⟨3105694798721226657796793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8281852796589937754124781 3105694798721226657796793)
                      ·
                        rfl

theorem cell23_6048319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_6048319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048319 prefixEnd_6048319 := by exact prefixLift 6048319
  have htrace : WordTrace (prefixWord ++ tailWord_6048319) baseStart_6048319 baseEnd_6048319 := by
    simpa [prefixWord, tailWord_6048319, baseEnd_6048319] using wordTrace_append hprefix tailTrace_6048319
  have hstable : (prefixWord ++ tailWord_6048319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048319).length < 2 ^ (prefixWord ++ tailWord_6048319).sum := by decide
  have hdescent : baseEnd_6048319 < baseStart_6048319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048360 : List Nat := [2, 1, 4, 3, 2, 2, 1, 1, 3, 4]
def baseStart_6048360 : Nat := 118140960795 + 6048360 * 2 ^ 59
def prefixEnd_6048360 : Nat := 4983230072969 + 3 ^ 40 * 6048360 * 2
def baseEnd_6048360 : Nat := 1035238617142686999128035

theorem tailTrace_6048360 : CollatzResearch.WordTrace tailWord_6048360 prefixEnd_6048360 1035238617142686999128035 := by
  unfold tailWord_6048360
  simp only [CollatzResearch.WordTrace]
  refine ⟨110300906183916086246779267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147067874911888114995705689 110300906183916086246779267)
  ·
    refine ⟨165451359275874129370168901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110300906183916086246779267 165451359275874129370168901)
    ·
      refine ⟨31022129864226399256906669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165451359275874129370168901 31022129864226399256906669)
      ·
        refine ⟨11633298699084899721340001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31022129864226399256906669 11633298699084899721340001)
        ·
          refine ⟨8724974024313674791005001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11633298699084899721340001 8724974024313674791005001)
          ·
            refine ⟨6543730518235256093253751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8724974024313674791005001 6543730518235256093253751)
            ·
              refine ⟨9815595777352884139880627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6543730518235256093253751 9815595777352884139880627)
              ·
                refine ⟨14723393666029326209820941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9815595777352884139880627 14723393666029326209820941)
                ·
                  refine ⟨5521272624760997328682853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14723393666029326209820941 5521272624760997328682853)
                  ·
                    refine ⟨1035238617142686999128035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5521272624760997328682853 1035238617142686999128035)
                    ·
                      rfl

theorem cell23_6048360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_6048360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048360 prefixEnd_6048360 := by exact prefixLift 6048360
  have htrace : WordTrace (prefixWord ++ tailWord_6048360) baseStart_6048360 baseEnd_6048360 := by
    simpa [prefixWord, tailWord_6048360, baseEnd_6048360] using wordTrace_append hprefix tailTrace_6048360
  have hstable : (prefixWord ++ tailWord_6048360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048360).length < 2 ^ (prefixWord ++ tailWord_6048360).sum := by decide
  have hdescent : baseEnd_6048360 < baseStart_6048360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048373 : List Nat := [1, 3, 4, 2, 2, 1, 1, 3, 6]
def baseStart_6048373 : Nat := 118140960795 + 6048373 * 2 ^ 59
def prefixEnd_6048373 : Nat := 4983230072969 + 3 ^ 40 * 6048373 * 2
def baseEnd_6048373 : Nat := 345080280741841049613505

theorem tailTrace_6048373 : CollatzResearch.WordTrace tailWord_6048373 prefixEnd_6048373 345080280741841049613505 := by
  unfold tailWord_6048373
  simp only [CollatzResearch.WordTrace]
  refine ⟨220602286516785075713781773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147068191011190050475854515 220602286516785075713781773)
  ·
    refine ⟨82725857443794403392668165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220602286516785075713781773 82725857443794403392668165)
    ·
      refine ⟨15511098270711450636125281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82725857443794403392668165 15511098270711450636125281)
      ·
        refine ⟨11633323703033587977093961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15511098270711450636125281 11633323703033587977093961)
        ·
          refine ⟨8724992777275190982820471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11633323703033587977093961 8724992777275190982820471)
          ·
            refine ⟨13087489165912786474230707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8724992777275190982820471 13087489165912786474230707)
            ·
              refine ⟨19631233748869179711346061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13087489165912786474230707 19631233748869179711346061)
              ·
                refine ⟨7361712655825942391754773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19631233748869179711346061 7361712655825942391754773)
                ·
                  refine ⟨345080280741841049613505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7361712655825942391754773 345080280741841049613505)
                  ·
                    rfl

theorem cell23_6048373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 6].length) (baseStart_6048373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048373 prefixEnd_6048373 := by exact prefixLift 6048373
  have htrace : WordTrace (prefixWord ++ tailWord_6048373) baseStart_6048373 baseEnd_6048373 := by
    simpa [prefixWord, tailWord_6048373, baseEnd_6048373] using wordTrace_append hprefix tailTrace_6048373
  have hstable : (prefixWord ++ tailWord_6048373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048373).length < 2 ^ (prefixWord ++ tailWord_6048373).sum := by decide
  have hdescent : baseEnd_6048373 < baseStart_6048373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048399 : List Nat := [1, 1, 2, 1, 1, 1, 1, 8, 1, 6]
def baseStart_6048399 : Nat := 118140960795 + 6048399 * 2 ^ 59
def prefixEnd_6048399 : Nat := 4983230072969 + 3 ^ 40 * 6048399 * 2
def baseEnd_6048399 : Nat := 1035245292391195448265475

theorem tailTrace_6048399 : CollatzResearch.WordTrace tailWord_6048399 prefixEnd_6048399 1035245292391195448265475 := by
  unfold tailWord_6048399
  simp only [CollatzResearch.WordTrace]
  refine ⟨220603234814690882154228251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147068823209793921436152167 220603234814690882154228251)
  ·
    refine ⟨330904852222036323231342377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220603234814690882154228251 330904852222036323231342377)
    ·
      refine ⟨248178639166527242423506783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330904852222036323231342377 248178639166527242423506783)
      ·
        refine ⟨372267958749790863635260175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248178639166527242423506783 372267958749790863635260175)
        ·
          refine ⟨558401938124686295452890263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372267958749790863635260175 558401938124686295452890263)
          ·
            refine ⟨837602907187029443179335395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558401938124686295452890263 837602907187029443179335395)
            ·
              refine ⟨1256404360780544164769003093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837602907187029443179335395 1256404360780544164769003093)
              ·
                refine ⟨14723488602897001930886755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1256404360780544164769003093 14723488602897001930886755)
                ·
                  refine ⟨22085232904345502896330133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14723488602897001930886755 22085232904345502896330133)
                  ·
                    refine ⟨1035245292391195448265475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22085232904345502896330133 1035245292391195448265475)
                    ·
                      rfl

theorem cell23_6048399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 6].length) (baseStart_6048399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048399 prefixEnd_6048399 := by exact prefixLift 6048399
  have htrace : WordTrace (prefixWord ++ tailWord_6048399) baseStart_6048399 baseEnd_6048399 := by
    simpa [prefixWord, tailWord_6048399, baseEnd_6048399] using wordTrace_append hprefix tailTrace_6048399
  have hstable : (prefixWord ++ tailWord_6048399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048399).length < 2 ^ (prefixWord ++ tailWord_6048399).sum := by decide
  have hdescent : baseEnd_6048399 < baseStart_6048399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048417 : List Nat := [1, 2, 3, 3, 3, 1, 1, 4, 1, 1, 3]
def baseStart_6048417 : Nat := 118140960795 + 6048417 * 2 ^ 59
def prefixEnd_6048417 : Nat := 4983230072969 + 3 ^ 40 * 6048417 * 2
def baseEnd_6048417 : Nat := 3105745119825367274371343

theorem tailTrace_6048417 : CollatzResearch.WordTrace tailWord_6048417 prefixEnd_6048417 3105745119825367274371343 := by
  unfold tailWord_6048417
  simp only [CollatzResearch.WordTrace]
  refine ⟨220603891328625671228383505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147069260885750447485589003 220603891328625671228383505)
  ·
    refine ⟨165452918496469253421287629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220603891328625671228383505 165452918496469253421287629)
    ·
      refine ⟨62044844436175970032982861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165452918496469253421287629 62044844436175970032982861)
      ·
        refine ⟨23266816663565988762368573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62044844436175970032982861 23266816663565988762368573)
        ·
          refine ⟨8725056248837245785888215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23266816663565988762368573 8725056248837245785888215)
          ·
            refine ⟨13087584373255868678832323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8725056248837245785888215 13087584373255868678832323)
            ·
              refine ⟨19631376559883803018248485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13087584373255868678832323 19631376559883803018248485)
              ·
                refine ⟨3680883104978213065921591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19631376559883803018248485 3680883104978213065921591)
                ·
                  refine ⟨5521324657467319598882387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3680883104978213065921591 5521324657467319598882387)
                  ·
                    refine ⟨8281986986200979398323581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5521324657467319598882387 8281986986200979398323581)
                    ·
                      refine ⟨3105745119825367274371343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8281986986200979398323581 3105745119825367274371343)
                      ·
                        rfl

theorem cell23_6048417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_6048417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048417 prefixEnd_6048417 := by exact prefixLift 6048417
  have htrace : WordTrace (prefixWord ++ tailWord_6048417) baseStart_6048417 baseEnd_6048417 := by
    simpa [prefixWord, tailWord_6048417, baseEnd_6048417] using wordTrace_append hprefix tailTrace_6048417
  have hstable : (prefixWord ++ tailWord_6048417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048417).length < 2 ^ (prefixWord ++ tailWord_6048417).sum := by decide
  have hdescent : baseEnd_6048417 < baseStart_6048417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048419 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 6]
def baseStart_6048419 : Nat := 118140960795 + 6048419 * 2 ^ 59
def prefixEnd_6048419 : Nat := 4983230072969 + 3 ^ 40 * 6048419 * 2
def baseEnd_6048419 : Nat := 3105746146786676266546333

theorem tailTrace_6048419 : CollatzResearch.WordTrace tailWord_6048419 prefixEnd_6048419 3105746146786676266546333 := by
  unfold tailWord_6048419
  simp only [CollatzResearch.WordTrace]
  refine ⟨220603964274618425569956311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147069309516412283713304207 220603964274618425569956311)
  ·
    refine ⟨330905946411927638354934467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220603964274618425569956311 330905946411927638354934467)
    ·
      refine ⟨496358919617891457532401701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330905946411927638354934467 496358919617891457532401701)
      ·
        refine ⟨93067297428354648287325319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 496358919617891457532401701 93067297428354648287325319)
        ·
          refine ⟨139600946142531972430987979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93067297428354648287325319 139600946142531972430987979)
          ·
            refine ⟨209401419213797958646481969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139600946142531972430987979 209401419213797958646481969)
            ·
              refine ⟨157051064410348468984861477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209401419213797958646481969 157051064410348468984861477)
              ·
                refine ⟨29447074576940337934661527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157051064410348468984861477 29447074576940337934661527)
                ·
                  refine ⟨44170611865410506901992291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29447074576940337934661527 44170611865410506901992291)
                  ·
                    refine ⟨66255917798115760352988437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44170611865410506901992291 66255917798115760352988437)
                    ·
                      refine ⟨3105746146786676266546333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66255917798115760352988437 3105746146786676266546333)
                      ·
                        rfl

theorem cell23_6048419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_6048419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048419 prefixEnd_6048419 := by exact prefixLift 6048419
  have htrace : WordTrace (prefixWord ++ tailWord_6048419) baseStart_6048419 baseEnd_6048419 := by
    simpa [prefixWord, tailWord_6048419, baseEnd_6048419] using wordTrace_append hprefix tailTrace_6048419
  have hstable : (prefixWord ++ tailWord_6048419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048419).length < 2 ^ (prefixWord ++ tailWord_6048419).sum := by decide
  have hdescent : baseEnd_6048419 < baseStart_6048419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048460 : List Nat := [2, 2, 1, 5, 1, 2, 1, 3, 1, 2, 3]
def baseStart_6048460 : Nat := 118140960795 + 6048460 * 2 ^ 59
def prefixEnd_6048460 : Nat := 4983230072969 + 3 ^ 40 * 6048460 * 2
def baseEnd_6048460 : Nat := 3105767199493510606133645

theorem tailTrace_6048460 : CollatzResearch.WordTrace tailWord_6048460 prefixEnd_6048460 3105767199493510606133645 := by
  unfold tailWord_6048460
  simp only [CollatzResearch.WordTrace]
  refine ⟨110302729833734944786099417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147070306444979926381465889 110302729833734944786099417)
  ·
    refine ⟨82727047375301208589574563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110302729833734944786099417 82727047375301208589574563)
    ·
      refine ⟨124090571062951812884361845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82727047375301208589574563 124090571062951812884361845)
      ·
        refine ⟨11633491037151732457908923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124090571062951812884361845 11633491037151732457908923)
        ·
          refine ⟨17450236555727598686863385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11633491037151732457908923 17450236555727598686863385)
          ·
            refine ⟨13087677416795699015147539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17450236555727598686863385 13087677416795699015147539)
            ·
              refine ⟨19631516125193548522721309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13087677416795699015147539 19631516125193548522721309)
              ·
                refine ⟨7361818546947580696020491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19631516125193548522721309 7361818546947580696020491)
                ·
                  refine ⟨11042727820421371044030737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7361818546947580696020491 11042727820421371044030737)
                  ·
                    refine ⟨8282045865316028283023053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11042727820421371044030737 8282045865316028283023053)
                    ·
                      refine ⟨3105767199493510606133645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8282045865316028283023053 3105767199493510606133645)
                      ·
                        rfl

theorem cell23_6048460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_6048460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048460 prefixEnd_6048460 := by exact prefixLift 6048460
  have htrace : WordTrace (prefixWord ++ tailWord_6048460) baseStart_6048460 baseEnd_6048460 := by
    simpa [prefixWord, tailWord_6048460, baseEnd_6048460] using wordTrace_append hprefix tailTrace_6048460
  have hstable : (prefixWord ++ tailWord_6048460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048460).length < 2 ^ (prefixWord ++ tailWord_6048460).sum := by decide
  have hdescent : baseEnd_6048460 < baseStart_6048460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048473 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 4, 1, 3]
def baseStart_6048473 : Nat := 118140960795 + 6048473 * 2 ^ 59
def prefixEnd_6048473 : Nat := 4983230072969 + 3 ^ 40 * 6048473 * 2
def baseEnd_6048473 : Nat := 3105773874742019055271085

theorem tailTrace_6048473 : CollatzResearch.WordTrace tailWord_6048473 prefixEnd_6048473 3105773874742019055271085 := by
  unfold tailWord_6048473
  simp only [CollatzResearch.WordTrace]
  refine ⟨220605933816422792792422073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147070622544281861861614715 220605933816422792792422073)
  ·
    refine ⟨165454450362317094594316555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220605933816422792792422073 165454450362317094594316555)
    ·
      refine ⟨248181675543475641891474833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165454450362317094594316555 248181675543475641891474833)
      ·
        refine ⟨186136256657606731418606125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248181675543475641891474833 186136256657606731418606125)
        ·
          refine ⟨69801096246602524281977297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186136256657606731418606125 69801096246602524281977297)
          ·
            refine ⟨52350822184951893211482973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69801096246602524281977297 52350822184951893211482973)
            ·
              refine ⟨19631558319356959954306115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52350822184951893211482973 19631558319356959954306115)
              ·
                refine ⟨29447337479035439931459173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19631558319356959954306115 29447337479035439931459173)
                ·
                  refine ⟨5521375777319144987148595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29447337479035439931459173 5521375777319144987148595)
                  ·
                    refine ⟨8282063665978717480722893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5521375777319144987148595 8282063665978717480722893)
                    ·
                      refine ⟨3105773874742019055271085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8282063665978717480722893 3105773874742019055271085)
                      ·
                        rfl

theorem cell23_6048473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 1, 3].length) (baseStart_6048473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048473 prefixEnd_6048473 := by exact prefixLift 6048473
  have htrace : WordTrace (prefixWord ++ tailWord_6048473) baseStart_6048473 baseEnd_6048473 := by
    simpa [prefixWord, tailWord_6048473, baseEnd_6048473] using wordTrace_append hprefix tailTrace_6048473
  have hstable : (prefixWord ++ tailWord_6048473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048473).length < 2 ^ (prefixWord ++ tailWord_6048473).sum := by decide
  have hdescent : baseEnd_6048473 < baseStart_6048473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048513 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 3, 4, 2]
def baseStart_6048513 : Nat := 118140960795 + 6048513 * 2 ^ 59
def prefixEnd_6048513 : Nat := 4983230072969 + 3 ^ 40 * 6048513 * 2
def baseEnd_6048513 : Nat := 3105794413968198898770901

theorem tailTrace_6048513 : CollatzResearch.WordTrace tailWord_6048513 prefixEnd_6048513 3105794413968198898770901 := by
  unfold tailWord_6048513
  simp only [CollatzResearch.WordTrace]
  refine ⟨220607392736277879623878193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147071595157518586415918795 220607392736277879623878193)
  ·
    refine ⟨165455544552208409717908645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220607392736277879623878193 165455544552208409717908645)
    ·
      refine ⟨31022914603539076822107871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165455544552208409717908645 31022914603539076822107871)
      ·
        refine ⟨46534371905308615233161807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31022914603539076822107871 46534371905308615233161807)
        ·
          refine ⟨69801557857962922849742711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46534371905308615233161807 69801557857962922849742711)
          ·
            refine ⟨104702336786944384274614067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69801557857962922849742711 104702336786944384274614067)
            ·
              refine ⟨157053505180416576411921101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104702336786944384274614067 157053505180416576411921101)
              ·
                refine ⟨58895064442656216154470413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157053505180416576411921101 58895064442656216154470413)
                ·
                  refine ⟨22085649165996081057926405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58895064442656216154470413 22085649165996081057926405)
                  ·
                    refine ⟨4141059218624265198361201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22085649165996081057926405 4141059218624265198361201)
                    ·
                      refine ⟨3105794413968198898770901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4141059218624265198361201 3105794413968198898770901)
                      ·
                        rfl

theorem cell23_6048513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_6048513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048513 prefixEnd_6048513 := by exact prefixLift 6048513
  have htrace : WordTrace (prefixWord ++ tailWord_6048513) baseStart_6048513 baseEnd_6048513 := by
    simpa [prefixWord, tailWord_6048513, baseEnd_6048513] using wordTrace_append hprefix tailTrace_6048513
  have hstable : (prefixWord ++ tailWord_6048513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048513).length < 2 ^ (prefixWord ++ tailWord_6048513).sum := by decide
  have hdescent : baseEnd_6048513 < baseStart_6048513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048541 : List Nat := [1, 4, 2, 4, 1, 2, 2, 1, 2, 1, 3]
def baseStart_6048541 : Nat := 118140960795 + 6048541 * 2 ^ 59
def prefixEnd_6048541 : Nat := 4983230072969 + 3 ^ 40 * 6048541 * 2
def baseEnd_6048541 : Nat := 3105808791426524789220773

theorem tailTrace_6048541 : CollatzResearch.WordTrace tailWord_6048541 prefixEnd_6048541 3105808791426524789220773 := by
  unfold tailWord_6048541
  simp only [CollatzResearch.WordTrace]
  refine ⟨220608413980176440405897477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147072275986784293603931651 220608413980176440405897477)
  ·
    refine ⟨41364077621283082576105777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220608413980176440405897477 41364077621283082576105777)
    ·
      refine ⟨31023058215962311932079333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41364077621283082576105777 31023058215962311932079333)
      ·
        refine ⟨5816823415492933487264875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31023058215962311932079333 5816823415492933487264875)
        ·
          refine ⟨8725235123239400230897313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5816823415492933487264875 8725235123239400230897313)
          ·
            refine ⟨6543926342429550173172985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8725235123239400230897313 6543926342429550173172985)
            ·
              refine ⟨4907944756822162629879739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6543926342429550173172985 4907944756822162629879739)
              ·
                refine ⟨7361917135233243944819609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4907944756822162629879739 7361917135233243944819609)
                ·
                  refine ⟨5521437851424932958614707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7361917135233243944819609 5521437851424932958614707)
                  ·
                    refine ⟨8282156777137399437922061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5521437851424932958614707 8282156777137399437922061)
                    ·
                      refine ⟨3105808791426524789220773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8282156777137399437922061 3105808791426524789220773)
                      ·
                        rfl

theorem cell23_6048541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_6048541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048541 prefixEnd_6048541 := by exact prefixLift 6048541
  have htrace : WordTrace (prefixWord ++ tailWord_6048541) baseStart_6048541 baseEnd_6048541 := by
    simpa [prefixWord, tailWord_6048541, baseEnd_6048541] using wordTrace_append hprefix tailTrace_6048541
  have hstable : (prefixWord ++ tailWord_6048541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048541).length < 2 ^ (prefixWord ++ tailWord_6048541).sum := by decide
  have hdescent : baseEnd_6048541 < baseStart_6048541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048613 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 5, 4]
def baseStart_6048613 : Nat := 118140960795 + 6048613 * 2 ^ 59
def prefixEnd_6048613 : Nat := 4983230072969 + 3 ^ 40 * 6048613 * 2
def baseEnd_6048613 : Nat := 1035281920677882835840147

theorem tailTrace_6048613 : CollatzResearch.WordTrace tailWord_6048613 prefixEnd_6048613 1035281920677882835840147 := by
  unfold tailWord_6048613
  simp only [CollatzResearch.WordTrace]
  refine ⟨220611040035915596702518493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147074026690610397801678995 220611040035915596702518493)
  ·
    refine ⟨82729140013468348763444435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220611040035915596702518493 82729140013468348763444435)
    ·
      refine ⟨124093710020202523145166653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82729140013468348763444435 124093710020202523145166653)
      ·
        refine ⟨46535141257575946179437495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124093710020202523145166653 46535141257575946179437495)
        ·
          refine ⟨69802711886363919269156243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46535141257575946179437495 69802711886363919269156243)
          ·
            refine ⟨104704067829545878903734365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69802711886363919269156243 104704067829545878903734365)
            ·
              refine ⟨39264025436079704588900387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104704067829545878903734365 39264025436079704588900387)
              ·
                refine ⟨58896038154119556883350581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39264025436079704588900387 58896038154119556883350581)
                ·
                  refine ⟨5521503576948708457814117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58896038154119556883350581 5521503576948708457814117)
                  ·
                    refine ⟨1035281920677882835840147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5521503576948708457814117 1035281920677882835840147)
                    ·
                      rfl

theorem cell23_6048613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_6048613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048613 prefixEnd_6048613 := by exact prefixLift 6048613
  have htrace : WordTrace (prefixWord ++ tailWord_6048613) baseStart_6048613 baseEnd_6048613 := by
    simpa [prefixWord, tailWord_6048613, baseEnd_6048613] using wordTrace_append hprefix tailTrace_6048613
  have hstable : (prefixWord ++ tailWord_6048613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048613).length < 2 ^ (prefixWord ++ tailWord_6048613).sum := by decide
  have hdescent : baseEnd_6048613 < baseStart_6048613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048647 : List Nat := [1, 1, 4, 2, 3, 1, 2, 4, 1, 4]
def baseStart_6048647 : Nat := 118140960795 + 6048647 * 2 ^ 59
def prefixEnd_6048647 : Nat := 4983230072969 + 3 ^ 40 * 6048647 * 2
def baseEnd_6048647 : Nat := 1035287740125300458165095

theorem tailTrace_6048647 : CollatzResearch.WordTrace tailWord_6048647 prefixEnd_6048647 1035287740125300458165095 := by
  unfold tailWord_6048647
  simp only [CollatzResearch.WordTrace]
  refine ⟨220612280117792420509256195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147074853411861613672837463 220612280117792420509256195)
  ·
    refine ⟨330918420176688630763884293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220612280117792420509256195 330918420176688630763884293)
    ·
      refine ⟨62047203783129118268228305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 330918420176688630763884293 62047203783129118268228305)
      ·
        refine ⟨46535402837346838701171229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62047203783129118268228305 46535402837346838701171229)
        ·
          refine ⟨17450776064005064512939211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46535402837346838701171229 17450776064005064512939211)
          ·
            refine ⟨26176164096007596769408817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17450776064005064512939211 26176164096007596769408817)
            ·
              refine ⟨19632123072005697577056613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26176164096007596769408817 19632123072005697577056613)
              ·
                refine ⟨3681023076001068295698115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19632123072005697577056613 3681023076001068295698115)
                ·
                  refine ⟨5521534614001602443547173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3681023076001068295698115 5521534614001602443547173)
                  ·
                    refine ⟨1035287740125300458165095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5521534614001602443547173 1035287740125300458165095)
                    ·
                      rfl

theorem cell23_6048647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_6048647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048647 prefixEnd_6048647 := by exact prefixLift 6048647
  have htrace : WordTrace (prefixWord ++ tailWord_6048647) baseStart_6048647 baseEnd_6048647 := by
    simpa [prefixWord, tailWord_6048647, baseEnd_6048647] using wordTrace_append hprefix tailTrace_6048647
  have hstable : (prefixWord ++ tailWord_6048647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048647).length < 2 ^ (prefixWord ++ tailWord_6048647).sum := by decide
  have hdescent : baseEnd_6048647 < baseStart_6048647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048687 : List Nat := [1, 1, 2, 1, 2, 2, 2, 7, 1, 1, 3]
def baseStart_6048687 : Nat := 118140960795 + 6048687 * 2 ^ 59
def prefixEnd_6048687 : Nat := 4983230072969 + 3 ^ 40 * 6048687 * 2
def baseEnd_6048687 : Nat := 3105883759602081217995101

theorem tailTrace_6048687 : CollatzResearch.WordTrace tailWord_6048687 prefixEnd_6048687 3105883759602081217995101 := by
  unfold tailWord_6048687
  simp only [CollatzResearch.WordTrace]
  refine ⟨220613739037647507340712315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147075826025098338227141543 220613739037647507340712315)
  ·
    refine ⟨330920608556471261011068473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220613739037647507340712315 330920608556471261011068473)
    ·
      refine ⟨248190456417353445758301355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330920608556471261011068473 248190456417353445758301355)
      ·
        refine ⟨372285684626030168637452033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248190456417353445758301355 372285684626030168637452033)
        ·
          refine ⟨279214263469522626478089025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372285684626030168637452033 279214263469522626478089025)
          ·
            refine ⟨209410697602141969858566769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279214263469522626478089025 209410697602141969858566769)
            ·
              refine ⟨157058023201606477393925077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209410697602141969858566769 157058023201606477393925077)
              ·
                refine ⟨3681047418787651813920119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 157058023201606477393925077 3681047418787651813920119)
                ·
                  refine ⟨5521571128181477720880179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3681047418787651813920119 5521571128181477720880179)
                  ·
                    refine ⟨8282356692272216581320269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5521571128181477720880179 8282356692272216581320269)
                    ·
                      refine ⟨3105883759602081217995101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8282356692272216581320269 3105883759602081217995101)
                      ·
                        rfl

theorem cell23_6048687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 1, 1, 3].length) (baseStart_6048687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048687 prefixEnd_6048687 := by exact prefixLift 6048687
  have htrace : WordTrace (prefixWord ++ tailWord_6048687) baseStart_6048687 baseEnd_6048687 := by
    simpa [prefixWord, tailWord_6048687, baseEnd_6048687] using wordTrace_append hprefix tailTrace_6048687
  have hstable : (prefixWord ++ tailWord_6048687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048687).length < 2 ^ (prefixWord ++ tailWord_6048687).sum := by decide
  have hdescent : baseEnd_6048687 < baseStart_6048687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048697 : List Nat := [1, 2, 1, 4, 2, 3, 1, 2, 2, 3, 2]
def baseStart_6048697 : Nat := 118140960795 + 6048697 * 2 ^ 59
def prefixEnd_6048697 : Nat := 4983230072969 + 3 ^ 40 * 6048697 * 2
def baseEnd_6048697 : Nat := 3105888894408626178870055

theorem tailTrace_6048697 : CollatzResearch.WordTrace tailWord_6048697 prefixEnd_6048697 3105888894408626178870055 := by
  unfold tailWord_6048697
  simp only [CollatzResearch.WordTrace]
  refine ⟨220614103767611279048576345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147076069178407519365717563 220614103767611279048576345)
  ·
    refine ⟨165460577825708459286432259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220614103767611279048576345 165460577825708459286432259)
    ·
      refine ⟨248190866738562688929648389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165460577825708459286432259 248190866738562688929648389)
      ·
        refine ⟨46535787513480504174309073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248190866738562688929648389 46535787513480504174309073)
        ·
          refine ⟨34901840635110378130731805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46535787513480504174309073 34901840635110378130731805)
          ·
            refine ⟨13088190238166391799024427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34901840635110378130731805 13088190238166391799024427)
            ·
              refine ⟨19632285357249587698536641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13088190238166391799024427 19632285357249587698536641)
              ·
                refine ⟨14724214017937190773902481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19632285357249587698536641 14724214017937190773902481)
                ·
                  refine ⟨11043160513452893080426861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14724214017937190773902481 11043160513452893080426861)
                  ·
                    refine ⟨4141185192544834905160073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11043160513452893080426861 4141185192544834905160073)
                    ·
                      refine ⟨3105888894408626178870055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4141185192544834905160073 3105888894408626178870055)
                      ·
                        rfl

theorem cell23_6048697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_6048697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048697 prefixEnd_6048697 := by exact prefixLift 6048697
  have htrace : WordTrace (prefixWord ++ tailWord_6048697) baseStart_6048697 baseEnd_6048697 := by
    simpa [prefixWord, tailWord_6048697, baseEnd_6048697] using wordTrace_append hprefix tailTrace_6048697
  have hstable : (prefixWord ++ tailWord_6048697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048697).length < 2 ^ (prefixWord ++ tailWord_6048697).sum := by decide
  have hdescent : baseEnd_6048697 < baseStart_6048697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048750 : List Nat := [4, 1, 2, 1, 5, 10]
def baseStart_6048750 : Nat := 118140960795 + 6048750 * 2 ^ 59
def prefixEnd_6048750 : Nat := 4983230072969 + 3 ^ 40 * 6048750 * 2
def baseEnd_6048750 : Nat := 12781547773182364080277

theorem tailTrace_6048750 : CollatzResearch.WordTrace tailWord_6048750 prefixEnd_6048750 12781547773182364080277 := by
  unfold tailWord_6048750
  simp only [CollatzResearch.WordTrace]
  refine ⟨27577004604552408637531963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147077357890946179400170469 27577004604552408637531963)
  ·
    refine ⟨41365506906828612956297945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27577004604552408637531963 41365506906828612956297945)
    ·
      refine ⟨31024130180121459717223459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41365506906828612956297945 31024130180121459717223459)
      ·
        refine ⟨46536195270182189575835189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31024130180121459717223459 46536195270182189575835189)
        ·
          refine ⟨4362768306579580272734549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46536195270182189575835189 4362768306579580272734549)
          ·
            refine ⟨12781547773182364080277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4362768306579580272734549 12781547773182364080277)
            ·
              rfl

theorem cell23_6048750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 10].length) (baseStart_6048750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048750 prefixEnd_6048750 := by exact prefixLift 6048750
  have htrace : WordTrace (prefixWord ++ tailWord_6048750) baseStart_6048750 baseEnd_6048750 := by
    simpa [prefixWord, tailWord_6048750, baseEnd_6048750] using wordTrace_append hprefix tailTrace_6048750
  have hstable : (prefixWord ++ tailWord_6048750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048750).length < 2 ^ (prefixWord ++ tailWord_6048750).sum := by decide
  have hdescent : baseEnd_6048750 < baseStart_6048750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048787 : List Nat := [1, 1, 1, 2, 1, 4, 1, 6, 1, 3, 2]
def baseStart_6048787 : Nat := 118140960795 + 6048787 * 2 ^ 59
def prefixEnd_6048787 : Nat := 4983230072969 + 3 ^ 40 * 6048787 * 2
def baseEnd_6048787 : Nat := 3105935107667530826744641

theorem tailTrace_6048787 : CollatzResearch.WordTrace tailWord_6048787 prefixEnd_6048787 3105935107667530826744641 := by
  unfold tailWord_6048787
  simp only [CollatzResearch.WordTrace]
  refine ⟨220617386337285224419352615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147078257558190149612901743 220617386337285224419352615)
  ·
    refine ⟨330926079505927836629028923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220617386337285224419352615 330926079505927836629028923)
    ·
      refine ⟨496389119258891754943543385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330926079505927836629028923 496389119258891754943543385)
      ·
        refine ⟨372291839444168816207657539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496389119258891754943543385 372291839444168816207657539)
        ·
          refine ⟨558437759166253224311486309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372291839444168816207657539 558437759166253224311486309)
          ·
            refine ⟨104707079843672479558403683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 558437759166253224311486309 104707079843672479558403683)
            ·
              refine ⟨157060619765508719337605525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104707079843672479558403683 157060619765508719337605525)
              ·
                refine ⟨7362216551508221218950259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 157060619765508719337605525 7362216551508221218950259)
                ·
                  refine ⟨11043324827262331828425389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7362216551508221218950259 11043324827262331828425389)
                  ·
                    refine ⟨4141246810223374435659521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11043324827262331828425389 4141246810223374435659521)
                    ·
                      refine ⟨3105935107667530826744641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4141246810223374435659521 3105935107667530826744641)
                      ·
                        rfl

theorem cell23_6048787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 3, 2].length) (baseStart_6048787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048787 prefixEnd_6048787 := by exact prefixLift 6048787
  have htrace : WordTrace (prefixWord ++ tailWord_6048787) baseStart_6048787 baseEnd_6048787 := by
    simpa [prefixWord, tailWord_6048787, baseEnd_6048787] using wordTrace_append hprefix tailTrace_6048787
  have hstable : (prefixWord ++ tailWord_6048787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048787).length < 2 ^ (prefixWord ++ tailWord_6048787).sum := by decide
  have hdescent : baseEnd_6048787 < baseStart_6048787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048838 : List Nat := [6, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_6048838 : Nat := 118140960795 + 6048838 * 2 ^ 59
def prefixEnd_6048838 : Nat := 4983230072969 + 3 ^ 40 * 6048838 * 2
def baseEnd_6048838 : Nat := 3105961295180910127206907

theorem tailTrace_6048838 : CollatzResearch.WordTrace tailWord_6048838 prefixEnd_6048838 3105961295180910127206907 := by
  unfold tailWord_6048838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6894351451878139379045599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 147079497640066973419639445 6894351451878139379045599)
  ·
    refine ⟨10341527177817209068568399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6894351451878139379045599 10341527177817209068568399)
    ·
      refine ⟨15512290766725813602852599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10341527177817209068568399 15512290766725813602852599)
      ·
        refine ⟨23268436150088720404278899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15512290766725813602852599 23268436150088720404278899)
        ·
          refine ⟨34902654225133080606418349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23268436150088720404278899 34902654225133080606418349)
          ·
            refine ⟨13088495334424905227406881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34902654225133080606418349 13088495334424905227406881)
            ·
              refine ⟨9816371500818678920555161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13088495334424905227406881 9816371500818678920555161)
              ·
                refine ⟨7362278625614009190416371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9816371500818678920555161 7362278625614009190416371)
                ·
                  refine ⟨11043417938421013785624557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7362278625614009190416371 11043417938421013785624557)
                  ·
                    refine ⟨4141281726907880169609209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11043417938421013785624557 4141281726907880169609209)
                    ·
                      refine ⟨3105961295180910127206907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4141281726907880169609209 3105961295180910127206907)
                      ·
                        rfl

theorem cell23_6048838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_6048838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048838 prefixEnd_6048838 := by exact prefixLift 6048838
  have htrace : WordTrace (prefixWord ++ tailWord_6048838) baseStart_6048838 baseEnd_6048838 := by
    simpa [prefixWord, tailWord_6048838, baseEnd_6048838] using wordTrace_append hprefix tailTrace_6048838
  have hstable : (prefixWord ++ tailWord_6048838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048838).length < 2 ^ (prefixWord ++ tailWord_6048838).sum := by decide
  have hdescent : baseEnd_6048838 < baseStart_6048838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048880 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 5]
def baseStart_6048880 : Nat := 118140960795 + 6048880 * 2 ^ 59
def prefixEnd_6048880 : Nat := 4983230072969 + 3 ^ 40 * 6048880 * 2
def baseEnd_6048880 : Nat := 3105982861368398962881713

theorem tailTrace_6048880 : CollatzResearch.WordTrace tailWord_6048880 prefixEnd_6048880 3105982861368398962881713 := by
  unfold tailWord_6048880
  simp only [CollatzResearch.WordTrace]
  refine ⟨110310389162974150651244047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147080518883965534201658729 110310389162974150651244047)
  ·
    refine ⟨165465583744461225976866071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110310389162974150651244047 165465583744461225976866071)
    ·
      refine ⟨248198375616691838965299107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165465583744461225976866071 248198375616691838965299107)
      ·
        refine ⟨372297563425037758447948661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248198375616691838965299107 372297563425037758447948661)
        ·
          refine ⟨34902896571097289854495187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 372297563425037758447948661 34902896571097289854495187)
          ·
            refine ⟨52354344856645934781742781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34902896571097289854495187 52354344856645934781742781)
            ·
              refine ⟨19632879321242225543153543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52354344856645934781742781 19632879321242225543153543)
              ·
                refine ⟨29449318981863338314730315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19632879321242225543153543 29449318981863338314730315)
                ·
                  refine ⟨44173978472795007472095473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29449318981863338314730315 44173978472795007472095473)
                  ·
                    refine ⟨33130483854596255604071605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44173978472795007472095473 33130483854596255604071605)
                    ·
                      refine ⟨3105982861368398962881713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33130483854596255604071605 3105982861368398962881713)
                      ·
                        rfl

theorem cell23_6048880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_6048880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048880 prefixEnd_6048880 := by exact prefixLift 6048880
  have htrace : WordTrace (prefixWord ++ tailWord_6048880) baseStart_6048880 baseEnd_6048880 := by
    simpa [prefixWord, tailWord_6048880, baseEnd_6048880] using wordTrace_append hprefix tailTrace_6048880
  have hstable : (prefixWord ++ tailWord_6048880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048880).length < 2 ^ (prefixWord ++ tailWord_6048880).sum := by decide
  have hdescent : baseEnd_6048880 < baseStart_6048880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048904 : List Nat := [2, 1, 3, 4, 2, 1, 2, 1, 2, 5]
def baseStart_6048904 : Nat := 118140960795 + 6048904 * 2 ^ 59
def prefixEnd_6048904 : Nat := 4983230072969 + 3 ^ 40 * 6048904 * 2
def baseEnd_6048904 : Nat := 1035331728301368956327201

theorem tailTrace_6048904 : CollatzResearch.WordTrace tailWord_6048904 prefixEnd_6048904 1035331728301368956327201 := by
  unfold tailWord_6048904
  simp only [CollatzResearch.WordTrace]
  refine ⟨110310826838930676700680883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147081102451907568934241177 110310826838930676700680883)
  ·
    refine ⟨165466240258396015051021325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110310826838930676700680883 165466240258396015051021325)
    ·
      refine ⟨62049840096898505644132997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165466240258396015051021325 62049840096898505644132997)
      ·
        refine ⟨11634345018168469808274937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62049840096898505644132997 11634345018168469808274937)
        ·
          refine ⟨8725758763626352356206203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11634345018168469808274937 8725758763626352356206203)
          ·
            refine ⟨13088638145439528534309305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8725758763626352356206203 13088638145439528534309305)
            ·
              refine ⟨9816478609079646400731979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13088638145439528534309305 9816478609079646400731979)
              ·
                refine ⟨14724717913619469601097969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9816478609079646400731979 14724717913619469601097969)
                ·
                  refine ⟨11043538435214602200823477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14724717913619469601097969 11043538435214602200823477)
                  ·
                    refine ⟨1035331728301368956327201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11043538435214602200823477 1035331728301368956327201)
                    ·
                      rfl

theorem cell23_6048904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_6048904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048904 prefixEnd_6048904 := by exact prefixLift 6048904
  have htrace : WordTrace (prefixWord ++ tailWord_6048904) baseStart_6048904 baseEnd_6048904 := by
    simpa [prefixWord, tailWord_6048904, baseEnd_6048904] using wordTrace_append hprefix tailTrace_6048904
  have hstable : (prefixWord ++ tailWord_6048904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048904).length < 2 ^ (prefixWord ++ tailWord_6048904).sum := by decide
  have hdescent : baseEnd_6048904 < baseStart_6048904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048941 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_6048941 : Nat := 118140960795 + 6048941 * 2 ^ 59
def prefixEnd_6048941 : Nat := 4983230072969 + 3 ^ 40 * 6048941 * 2
def baseEnd_6048941 : Nat := 3106014183688323224218933

theorem tailTrace_6048941 : CollatzResearch.WordTrace tailWord_6048941 prefixEnd_6048941 3106014183688323224218933 := by
  unfold tailWord_6048941
  simp only [CollatzResearch.WordTrace]
  refine ⟨220623003178727308720458677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147082002119151539146972451 220623003178727308720458677)
  ·
    refine ⟨20683406548005685192543001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220623003178727308720458677 20683406548005685192543001)
    ·
      refine ⟨15512554911004263894407251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20683406548005685192543001 15512554911004263894407251)
      ·
        refine ⟨23268832366506395841610877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15512554911004263894407251 23268832366506395841610877)
        ·
          refine ⟨8725812137439898440604079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23268832366506395841610877 8725812137439898440604079)
          ·
            refine ⟨13088718206159847660906119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8725812137439898440604079 13088718206159847660906119)
            ·
              refine ⟨19633077309239771491359179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13088718206159847660906119 19633077309239771491359179)
              ·
                refine ⟨29449615963859657237038769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19633077309239771491359179 29449615963859657237038769)
                ·
                  refine ⟨22087211972894742927779077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29449615963859657237038769 22087211972894742927779077)
                  ·
                    refine ⟨4141352244917764298958577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22087211972894742927779077 4141352244917764298958577)
                    ·
                      refine ⟨3106014183688323224218933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4141352244917764298958577 3106014183688323224218933)
                      ·
                        rfl

theorem cell23_6048941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_6048941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048941 prefixEnd_6048941 := by exact prefixLift 6048941
  have htrace : WordTrace (prefixWord ++ tailWord_6048941) baseStart_6048941 baseEnd_6048941 := by
    simpa [prefixWord, tailWord_6048941, baseEnd_6048941] using wordTrace_append hprefix tailTrace_6048941
  have hstable : (prefixWord ++ tailWord_6048941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048941).length < 2 ^ (prefixWord ++ tailWord_6048941).sum := by decide
  have hdescent : baseEnd_6048941 < baseStart_6048941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048961 : List Nat := [1, 2, 6, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_6048961 : Nat := 118140960795 + 6048961 * 2 ^ 59
def prefixEnd_6048961 : Nat := 4983230072969 + 3 ^ 40 * 6048961 * 2
def baseEnd_6048961 : Nat := 3106024453301413145968841

theorem tailTrace_6048961 : CollatzResearch.WordTrace tailWord_6048961 prefixEnd_6048961 3106024453301413145968841 := by
  unfold tailWord_6048961
  simp only [CollatzResearch.WordTrace]
  refine ⟨220623732638654852136186737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147082488425769901424124491 220623732638654852136186737)
  ·
    refine ⟨165467799478991139102140053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220623732638654852136186737 165467799478991139102140053)
    ·
      refine ⟨7756303100577709645412815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 165467799478991139102140053 7756303100577709645412815)
      ·
        refine ⟨11634454650866564468119223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7756303100577709645412815 11634454650866564468119223)
        ·
          refine ⟨17451681976299846702178835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11634454650866564468119223 17451681976299846702178835)
          ·
            refine ⟨26177522964449770053268253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17451681976299846702178835 26177522964449770053268253)
            ·
              refine ⟨9816571111668663769975595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26177522964449770053268253 9816571111668663769975595)
              ·
                refine ⟨14724856667502995654963393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9816571111668663769975595 14724856667502995654963393)
                ·
                  refine ⟨11043642500627246741222545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14724856667502995654963393 11043642500627246741222545)
                  ·
                    refine ⟨8282731875470435055916909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11043642500627246741222545 8282731875470435055916909)
                    ·
                      refine ⟨3106024453301413145968841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8282731875470435055916909 3106024453301413145968841)
                      ·
                        rfl

theorem cell23_6048961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_6048961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048961 prefixEnd_6048961 := by exact prefixLift 6048961
  have htrace : WordTrace (prefixWord ++ tailWord_6048961) baseStart_6048961 baseEnd_6048961 := by
    simpa [prefixWord, tailWord_6048961, baseEnd_6048961] using wordTrace_append hprefix tailTrace_6048961
  have hstable : (prefixWord ++ tailWord_6048961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048961).length < 2 ^ (prefixWord ++ tailWord_6048961).sum := by decide
  have hdescent : baseEnd_6048961 < baseStart_6048961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6048991 : List Nat := [1, 1, 2, 3, 2, 1, 4, 4, 1, 1, 3]
def baseStart_6048991 : Nat := 118140960795 + 6048991 * 2 ^ 59
def prefixEnd_6048991 : Nat := 4983230072969 + 3 ^ 40 * 6048991 * 2
def baseEnd_6048991 : Nat := 3106039857721048028593703

theorem tailTrace_6048991 : CollatzResearch.WordTrace tailWord_6048991 prefixEnd_6048991 3106039857721048028593703 := by
  unfold tailWord_6048991
  simp only [CollatzResearch.WordTrace]
  refine ⟨220624826828546167259778827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147083217885697444839852551 220624826828546167259778827)
  ·
    refine ⟨330937240242819250889668241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220624826828546167259778827 330937240242819250889668241)
    ·
      refine ⟨248202930182114438167251181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330937240242819250889668241 248202930182114438167251181)
      ·
        refine ⟨93076098818292914312719193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248202930182114438167251181 93076098818292914312719193)
        ·
          refine ⟨69807074113719685734539395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93076098818292914312719193 69807074113719685734539395)
          ·
            refine ⟨104710611170579528601809093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69807074113719685734539395 104710611170579528601809093)
            ·
              refine ⟨19633239594483661612839205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104710611170579528601809093 19633239594483661612839205)
              ·
                refine ⟨3681232423965686552407351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19633239594483661612839205 3681232423965686552407351)
                ·
                  refine ⟨5521848635948529828611027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3681232423965686552407351 5521848635948529828611027)
                  ·
                    refine ⟨8282772953922794742916541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5521848635948529828611027 8282772953922794742916541)
                    ·
                      refine ⟨3106039857721048028593703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8282772953922794742916541 3106039857721048028593703)
                      ·
                        rfl

theorem cell23_6048991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 1, 1, 3].length) (baseStart_6048991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6048991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6048991 prefixEnd_6048991 := by exact prefixLift 6048991
  have htrace : WordTrace (prefixWord ++ tailWord_6048991) baseStart_6048991 baseEnd_6048991 := by
    simpa [prefixWord, tailWord_6048991, baseEnd_6048991] using wordTrace_append hprefix tailTrace_6048991
  have hstable : (prefixWord ++ tailWord_6048991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6048991).length < 2 ^ (prefixWord ++ tailWord_6048991).sum := by decide
  have hdescent : baseEnd_6048991 < baseStart_6048991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6048991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049014 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2]
def baseStart_6049014 : Nat := 118140960795 + 6049014 * 2 ^ 59
def prefixEnd_6049014 : Nat := 4983230072969 + 3 ^ 40 * 6049014 * 2
def baseEnd_6049014 : Nat := 3106051667776101438606097

theorem tailTrace_6049014 : CollatzResearch.WordTrace tailWord_6049014 prefixEnd_6049014 3106051667776101438606097 := by
  unfold tailWord_6049014
  simp only [CollatzResearch.WordTrace]
  refine ⟨13789104106716427636741631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147083777138308561458577397 13789104106716427636741631)
  ·
    refine ⟨20683656160074641455112447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13789104106716427636741631 20683656160074641455112447)
    ·
      refine ⟨31025484240111962182668671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20683656160074641455112447 31025484240111962182668671)
      ·
        refine ⟨46538226360167943274003007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31025484240111962182668671 46538226360167943274003007)
        ·
          refine ⟨69807339540251914911004511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46538226360167943274003007 69807339540251914911004511)
          ·
            refine ⟨104711009310377872366506767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69807339540251914911004511 104711009310377872366506767)
            ·
              refine ⟨157066513965566808549760151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104711009310377872366506767 157066513965566808549760151)
              ·
                refine ⟨235599770948350212824640227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157066513965566808549760151 235599770948350212824640227)
                ·
                  refine ⟨353399656422525319236960341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235599770948350212824640227 353399656422525319236960341)
                  ·
                    refine ⟨4141402223701468584808129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 353399656422525319236960341 4141402223701468584808129)
                    ·
                      refine ⟨3106051667776101438606097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4141402223701468584808129 3106051667776101438606097)
                      ·
                        rfl

theorem cell23_6049014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_6049014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049014 prefixEnd_6049014 := by exact prefixLift 6049014
  have htrace : WordTrace (prefixWord ++ tailWord_6049014) baseStart_6049014 baseEnd_6049014 := by
    simpa [prefixWord, tailWord_6049014, baseEnd_6049014] using wordTrace_append hprefix tailTrace_6049014
  have hstable : (prefixWord ++ tailWord_6049014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049014).length < 2 ^ (prefixWord ++ tailWord_6049014).sum := by decide
  have hdescent : baseEnd_6049014 < baseStart_6049014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049042 : List Nat := [3, 2, 4, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_6049042 : Nat := 118140960795 + 6049042 * 2 ^ 59
def prefixEnd_6049042 : Nat := 4983230072969 + 3 ^ 40 * 6049042 * 2
def baseEnd_6049042 : Nat := 3106066045234427329055969

theorem tailTrace_6049042 : CollatzResearch.WordTrace tailWord_6049042 prefixEnd_6049042 3106066045234427329055969 := by
  unfold tailWord_6049042
  simp only [CollatzResearch.WordTrace]
  refine ⟨55156671737840350742471345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147084457967574268646590253 55156671737840350742471345)
  ·
    refine ⟨41367503803380263056853509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55156671737840350742471345 41367503803380263056853509)
    ·
      refine ⟨7756406963133799323160033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41367503803380263056853509 7756406963133799323160033)
      ·
        refine ⟨5817305222350349492370025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7756406963133799323160033 5817305222350349492370025)
        ·
          refine ⟨4362978916762762119277519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5817305222350349492370025 4362978916762762119277519)
          ·
            refine ⟨6544468375144143178916279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4362978916762762119277519 6544468375144143178916279)
            ·
              refine ⟨9816702562716214768374419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6544468375144143178916279 9816702562716214768374419)
              ·
                refine ⟨14725053844074322152561629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9816702562716214768374419 14725053844074322152561629)
                ·
                  refine ⟨5521895191527870807210611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14725053844074322152561629 5521895191527870807210611)
                  ·
                    refine ⟨8282842787291806210815917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5521895191527870807210611 8282842787291806210815917)
                    ·
                      refine ⟨3106066045234427329055969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8282842787291806210815917 3106066045234427329055969)
                      ·
                        rfl

theorem cell23_6049042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_6049042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049042 prefixEnd_6049042 := by exact prefixLift 6049042
  have htrace : WordTrace (prefixWord ++ tailWord_6049042) baseStart_6049042 baseEnd_6049042 := by
    simpa [prefixWord, tailWord_6049042, baseEnd_6049042] using wordTrace_append hprefix tailTrace_6049042
  have hstable : (prefixWord ++ tailWord_6049042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049042).length < 2 ^ (prefixWord ++ tailWord_6049042).sum := by decide
  have hdescent : baseEnd_6049042 < baseStart_6049042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049048 : List Nat := [2, 1, 2, 3, 1, 5, 1, 1, 3, 2, 2]
def baseStart_6049048 : Nat := 118140960795 + 6049048 * 2 ^ 59
def prefixEnd_6049048 : Nat := 4983230072969 + 3 ^ 40 * 6049048 * 2
def baseEnd_6049048 : Nat := 3106069126118354305580941

theorem tailTrace_6049048 : CollatzResearch.WordTrace tailWord_6049048 prefixEnd_6049048 3106069126118354305580941 := by
  unfold tailWord_6049048
  simp only [CollatzResearch.WordTrace]
  refine ⟨110313452894669832997301899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147084603859559777329735865 110313452894669832997301899)
  ·
    refine ⟨165470179342004749495952849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110313452894669832997301899 165470179342004749495952849)
    ·
      refine ⟨124102634506503562121964637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165470179342004749495952849 124102634506503562121964637)
      ·
        refine ⟨46538487939938835795736739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124102634506503562121964637 46538487939938835795736739)
        ·
          refine ⟨69807731909908253693605109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46538487939938835795736739 69807731909908253693605109)
          ·
            refine ⟨6544474866553898783775479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69807731909908253693605109 6544474866553898783775479)
            ·
              refine ⟨9816712299830848175663219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6544474866553898783775479 9816712299830848175663219)
              ·
                refine ⟨14725068449746272263494829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9816712299830848175663219 14725068449746272263494829)
                ·
                  refine ⟨5521900668654852098810561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14725068449746272263494829 5521900668654852098810561)
                  ·
                    refine ⟨4141425501491139074107921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5521900668654852098810561 4141425501491139074107921)
                    ·
                      refine ⟨3106069126118354305580941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4141425501491139074107921 3106069126118354305580941)
                      ·
                        rfl

theorem cell23_6049048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_6049048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049048 prefixEnd_6049048 := by exact prefixLift 6049048
  have htrace : WordTrace (prefixWord ++ tailWord_6049048) baseStart_6049048 baseEnd_6049048 := by
    simpa [prefixWord, tailWord_6049048, baseEnd_6049048] using wordTrace_append hprefix tailTrace_6049048
  have hstable : (prefixWord ++ tailWord_6049048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049048).length < 2 ^ (prefixWord ++ tailWord_6049048).sum := by decide
  have hdescent : baseEnd_6049048 < baseStart_6049048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049078 : List Nat := [5, 1, 2, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_6049078 : Nat := 118140960795 + 6049078 * 2 ^ 59
def prefixEnd_6049078 : Nat := 4983230072969 + 3 ^ 40 * 6049078 * 2
def baseEnd_6049078 : Nat := 3106084530537989188205803

theorem tailTrace_6049078 : CollatzResearch.WordTrace tailWord_6049078 prefixEnd_6049078 3106084530537989188205803 := by
  unfold tailWord_6049078
  simp only [CollatzResearch.WordTrace]
  refine ⟨13789249998701936319887243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147085333319487320745463925 13789249998701936319887243)
  ·
    refine ⟨20683874998052904479830865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13789249998701936319887243 20683874998052904479830865)
    ·
      refine ⟨15512906248539678359873149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20683874998052904479830865 15512906248539678359873149)
      ·
        refine ⟨5817339843202379384952431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15512906248539678359873149 5817339843202379384952431)
        ·
          refine ⟨8726009764803569077428647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5817339843202379384952431 8726009764803569077428647)
          ·
            refine ⟨13089014647205353616142971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8726009764803569077428647 13089014647205353616142971)
            ·
              refine ⟨19633521970808030424214457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13089014647205353616142971 19633521970808030424214457)
              ·
                refine ⟨14725141478106022818160843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19633521970808030424214457 14725141478106022818160843)
                ·
                  refine ⟨22087712217159034227241265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14725141478106022818160843 22087712217159034227241265)
                  ·
                    refine ⟨16565784162869275670430949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22087712217159034227241265 16565784162869275670430949)
                    ·
                      refine ⟨3106084530537989188205803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16565784162869275670430949 3106084530537989188205803)
                      ·
                        rfl

theorem cell23_6049078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_6049078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049078 prefixEnd_6049078 := by exact prefixLift 6049078
  have htrace : WordTrace (prefixWord ++ tailWord_6049078) baseStart_6049078 baseEnd_6049078 := by
    simpa [prefixWord, tailWord_6049078, baseEnd_6049078] using wordTrace_append hprefix tailTrace_6049078
  have hstable : (prefixWord ++ tailWord_6049078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049078).length < 2 ^ (prefixWord ++ tailWord_6049078).sum := by decide
  have hdescent : baseEnd_6049078 < baseStart_6049078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049081 : List Nat := [1, 2, 1, 6, 2, 1, 1, 2, 1, 3, 3]
def baseStart_6049081 : Nat := 118140960795 + 6049081 * 2 ^ 59
def prefixEnd_6049081 : Nat := 4983230072969 + 3 ^ 40 * 6049081 * 2
def baseEnd_6049081 : Nat := 3106086070979952676468289

theorem tailTrace_6049081 : CollatzResearch.WordTrace tailWord_6049081 prefixEnd_6049081 3106086070979952676468289 := by
  unfold tailWord_6049081
  simp only [CollatzResearch.WordTrace]
  refine ⟨220628109398220112630555097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147085406265480075087036731 220628109398220112630555097)
  ·
    refine ⟨165471082048665084472916323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220628109398220112630555097 165471082048665084472916323)
    ·
      refine ⟨248206623072997626709374485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165471082048665084472916323 248206623072997626709374485)
      ·
        refine ⟨11634685456546763752001929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 248206623072997626709374485 11634685456546763752001929)
        ·
          refine ⟨8726014092410072814001447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11634685456546763752001929 8726014092410072814001447)
          ·
            refine ⟨13089021138615109221002171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8726014092410072814001447 13089021138615109221002171)
            ·
              refine ⟨19633531707922663831503257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13089021138615109221002171 19633531707922663831503257)
              ·
                refine ⟨14725148780941997873627443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19633531707922663831503257 14725148780941997873627443)
                ·
                  refine ⟨22087723171412996810441165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14725148780941997873627443 22087723171412996810441165)
                  ·
                    refine ⟨8282896189279873803915437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22087723171412996810441165 8282896189279873803915437)
                    ·
                      refine ⟨3106086070979952676468289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8282896189279873803915437 3106086070979952676468289)
                      ·
                        rfl

theorem cell23_6049081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_6049081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049081 prefixEnd_6049081 := by exact prefixLift 6049081
  have htrace : WordTrace (prefixWord ++ tailWord_6049081) baseStart_6049081 baseEnd_6049081 := by
    simpa [prefixWord, tailWord_6049081, baseEnd_6049081] using wordTrace_append hprefix tailTrace_6049081
  have hstable : (prefixWord ++ tailWord_6049081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049081).length < 2 ^ (prefixWord ++ tailWord_6049081).sum := by decide
  have hdescent : baseEnd_6049081 < baseStart_6049081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049085 : List Nat := [1, 4, 1, 5, 1, 1, 3, 1, 1, 2, 3]
def baseStart_6049085 : Nat := 118140960795 + 6049085 * 2 ^ 59
def prefixEnd_6049085 : Nat := 4983230072969 + 3 ^ 40 * 6049085 * 2
def baseEnd_6049085 : Nat := 3106088124902570660818271

theorem tailTrace_6049085 : CollatzResearch.WordTrace tailWord_6049085 prefixEnd_6049085 3106088124902570660818271 := by
  unfold tailWord_6049085
  simp only [CollatzResearch.WordTrace]
  refine ⟨220628255290205621313700709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147085503526803747542467139 220628255290205621313700709)
  ·
    refine ⟨41367797866913553996318883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220628255290205621313700709 41367797866913553996318883)
    ·
      refine ⟨62051696800370330994478325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41367797866913553996318883 62051696800370330994478325)
      ·
        refine ⟨5817346575034718530732343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62051696800370330994478325 5817346575034718530732343)
        ·
          refine ⟨8726019862552077796098515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5817346575034718530732343 8726019862552077796098515)
          ·
            refine ⟨13089029793828116694147773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8726019862552077796098515 13089029793828116694147773)
            ·
              refine ⟨4908386172685543760305415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13089029793828116694147773 4908386172685543760305415)
              ·
                refine ⟨7362579259028315640458123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4908386172685543760305415 7362579259028315640458123)
                ·
                  refine ⟨11043868888542473460687185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7362579259028315640458123 11043868888542473460687185)
                  ·
                    refine ⟨8282901666406855095515389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11043868888542473460687185 8282901666406855095515389)
                    ·
                      refine ⟨3106088124902570660818271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8282901666406855095515389 3106088124902570660818271)
                      ·
                        rfl

theorem cell23_6049085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_6049085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049085 prefixEnd_6049085 := by exact prefixLift 6049085
  have htrace : WordTrace (prefixWord ++ tailWord_6049085) baseStart_6049085 baseEnd_6049085 := by
    simpa [prefixWord, tailWord_6049085, baseEnd_6049085] using wordTrace_append hprefix tailTrace_6049085
  have hstable : (prefixWord ++ tailWord_6049085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049085).length < 2 ^ (prefixWord ++ tailWord_6049085).sum := by decide
  have hdescent : baseEnd_6049085 < baseStart_6049085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049104 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 3, 4, 2]
def baseStart_6049104 : Nat := 118140960795 + 6049104 * 2 ^ 59
def prefixEnd_6049104 : Nat := 4983230072969 + 3 ^ 40 * 6049104 * 2
def baseEnd_6049104 : Nat := 3106097881035006086480683

theorem tailTrace_6049104 : CollatzResearch.WordTrace tailWord_6049104 prefixEnd_6049104 3106097881035006086480683 := by
  unfold tailWord_6049104
  simp only [CollatzResearch.WordTrace]
  refine ⟨110314474138568393779321183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147085965518091191705761577 110314474138568393779321183)
  ·
    refine ⟨165471711207852590668981775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110314474138568393779321183 165471711207852590668981775)
    ·
      refine ⟨248207566811778886003472663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165471711207852590668981775 248207566811778886003472663)
      ·
        refine ⟨372311350217668329005208995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248207566811778886003472663 372311350217668329005208995)
        ·
          refine ⟨558467025326502493507813493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372311350217668329005208995 558467025326502493507813493)
          ·
            refine ⟨52356283624359608766357515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 558467025326502493507813493 52356283624359608766357515)
            ·
              refine ⟨78534425436539413149536273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52356283624359608766357515 78534425436539413149536273)
              ·
                refine ⟨58900819077404559862152205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78534425436539413149536273 58900819077404559862152205)
                ·
                  refine ⟨22087807154026709948307077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58900819077404559862152205 22087807154026709948307077)
                  ·
                    refine ⟨4141463841380008115307577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22087807154026709948307077 4141463841380008115307577)
                    ·
                      refine ⟨3106097881035006086480683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4141463841380008115307577 3106097881035006086480683)
                      ·
                        rfl

theorem cell23_6049104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 3, 4, 2].length) (baseStart_6049104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049104 prefixEnd_6049104 := by exact prefixLift 6049104
  have htrace : WordTrace (prefixWord ++ tailWord_6049104) baseStart_6049104 baseEnd_6049104 := by
    simpa [prefixWord, tailWord_6049104, baseEnd_6049104] using wordTrace_append hprefix tailTrace_6049104
  have hstable : (prefixWord ++ tailWord_6049104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049104).length < 2 ^ (prefixWord ++ tailWord_6049104).sum := by decide
  have hdescent : baseEnd_6049104 < baseStart_6049104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049107 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 3]
def baseStart_6049107 : Nat := 118140960795 + 6049107 * 2 ^ 59
def prefixEnd_6049107 : Nat := 4983230072969 + 3 ^ 40 * 6049107 * 2
def baseEnd_6049107 : Nat := 3106099421476969574743169

theorem tailTrace_6049107 : CollatzResearch.WordTrace tailWord_6049107 prefixEnd_6049107 3106099421476969574743169 := by
  unfold tailWord_6049107
  simp only [CollatzResearch.WordTrace]
  refine ⟨220629057696125919071001575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147086038464083946047334383 220629057696125919071001575)
  ·
    refine ⟨330943586544188878606502363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220629057696125919071001575 330943586544188878606502363)
    ·
      refine ⟨496415379816283317909753545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330943586544188878606502363 496415379816283317909753545)
      ·
        refine ⟨372311534862212488432315159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496415379816283317909753545 372311534862212488432315159)
        ·
          refine ⟨558467302293318732648472739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372311534862212488432315159 558467302293318732648472739)
          ·
            refine ⟨837700953439978098972709109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558467302293318732648472739 837700953439978098972709109)
            ·
              refine ⟨78534464384997946778691479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 837700953439978098972709109 78534464384997946778691479)
              ·
                refine ⟨117801696577496920168037219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78534464384997946778691479 117801696577496920168037219)
                ·
                  refine ⟨176702544866245380252055829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117801696577496920168037219 176702544866245380252055829)
                  ·
                    refine ⟨8282931790605252199315117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 176702544866245380252055829 8282931790605252199315117)
                    ·
                      refine ⟨3106099421476969574743169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8282931790605252199315117 3106099421476969574743169)
                      ·
                        rfl

theorem cell23_6049107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 3].length) (baseStart_6049107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049107 prefixEnd_6049107 := by exact prefixLift 6049107
  have htrace : WordTrace (prefixWord ++ tailWord_6049107) baseStart_6049107 baseEnd_6049107 := by
    simpa [prefixWord, tailWord_6049107, baseEnd_6049107] using wordTrace_append hprefix tailTrace_6049107
  have hstable : (prefixWord ++ tailWord_6049107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049107).length < 2 ^ (prefixWord ++ tailWord_6049107).sum := by decide
  have hdescent : baseEnd_6049107 < baseStart_6049107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049155 : List Nat := [1, 1, 1, 3, 5, 3, 1, 2, 2, 2, 2]
def baseStart_6049155 : Nat := 118140960795 + 6049155 * 2 ^ 59
def prefixEnd_6049155 : Nat := 4983230072969 + 3 ^ 40 * 6049155 * 2
def baseEnd_6049155 : Nat := 3106124068548385386942949

theorem tailTrace_6049155 : CollatzResearch.WordTrace tailWord_6049155 prefixEnd_6049155 3106124068548385386942949 := by
  unfold tailWord_6049155
  simp only [CollatzResearch.WordTrace]
  refine ⟨220630808399952023268748919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147087205599968015512499279 220630808399952023268748919)
  ·
    refine ⟨330946212599928034903123379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220630808399952023268748919 330946212599928034903123379)
    ·
      refine ⟨496419318899892052354685069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330946212599928034903123379 496419318899892052354685069)
      ·
        refine ⟨186157244587459519633006901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 496419318899892052354685069 186157244587459519633006901)
        ·
          refine ⟨17452241680074329965594397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 186157244587459519633006901 17452241680074329965594397)
          ·
            refine ⟨6544590630027873737097899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17452241680074329965594397 6544590630027873737097899)
            ·
              refine ⟨9816885945041810605646849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6544590630027873737097899 9816885945041810605646849)
              ·
                refine ⟨7362664458781357954235137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9816885945041810605646849 7362664458781357954235137)
                ·
                  refine ⟨5521998344086018465676353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7362664458781357954235137 5521998344086018465676353)
                  ·
                    refine ⟨4141498758064513849257265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5521998344086018465676353 4141498758064513849257265)
                    ·
                      refine ⟨3106124068548385386942949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4141498758064513849257265 3106124068548385386942949)
                      ·
                        rfl

theorem cell23_6049155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 2, 2].length) (baseStart_6049155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049155 prefixEnd_6049155 := by exact prefixLift 6049155
  have htrace : WordTrace (prefixWord ++ tailWord_6049155) baseStart_6049155 baseEnd_6049155 := by
    simpa [prefixWord, tailWord_6049155, baseEnd_6049155] using wordTrace_append hprefix tailTrace_6049155
  have hstable : (prefixWord ++ tailWord_6049155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049155).length < 2 ^ (prefixWord ++ tailWord_6049155).sum := by decide
  have hdescent : baseEnd_6049155 < baseStart_6049155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049172 : List Nat := [2, 4, 2, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_6049172 : Nat := 118140960795 + 6049172 * 2 ^ 59
def prefixEnd_6049172 : Nat := 4983230072969 + 3 ^ 40 * 6049172 * 2
def baseEnd_6049172 : Nat := 3106132797719511820430371

theorem tailTrace_6049172 : CollatzResearch.WordTrace tailWord_6049172 prefixEnd_6049172 3106132797719511820430371 := by
  unfold tailWord_6049172
  simp only [CollatzResearch.WordTrace]
  refine ⟨110315714220445217586058885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147087618960593623448078513 110315714220445217586058885)
  ·
    refine ⟨20684196416333478297386041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110315714220445217586058885 20684196416333478297386041)
    ·
      refine ⟨15513147312250108723039531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20684196416333478297386041 15513147312250108723039531)
      ·
        refine ⟨23269720968375163084559297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15513147312250108723039531 23269720968375163084559297)
        ·
          refine ⟨17452290726281372313419473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23269720968375163084559297 17452290726281372313419473)
          ·
            refine ⟨13089218044711029235064605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17452290726281372313419473 13089218044711029235064605)
            ·
              refine ⟨4908456766766635963149227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13089218044711029235064605 4908456766766635963149227)
              ·
                refine ⟨7362685150149953944723841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4908456766766635963149227 7362685150149953944723841)
                ·
                  refine ⟨5522013862612465458542881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7362685150149953944723841 5522013862612465458542881)
                  ·
                    refine ⟨4141510396959349093907161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5522013862612465458542881 4141510396959349093907161)
                    ·
                      refine ⟨3106132797719511820430371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4141510396959349093907161 3106132797719511820430371)
                      ·
                        rfl

theorem cell23_6049172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_6049172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049172 prefixEnd_6049172 := by exact prefixLift 6049172
  have htrace : WordTrace (prefixWord ++ tailWord_6049172) baseStart_6049172 baseEnd_6049172 := by
    simpa [prefixWord, tailWord_6049172, baseEnd_6049172] using wordTrace_append hprefix tailTrace_6049172
  have hstable : (prefixWord ++ tailWord_6049172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049172).length < 2 ^ (prefixWord ++ tailWord_6049172).sum := by decide
  have hdescent : baseEnd_6049172 < baseStart_6049172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049187 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 2, 8]
def baseStart_6049187 : Nat := 118140960795 + 6049187 * 2 ^ 59
def prefixEnd_6049187 : Nat := 4983230072969 + 3 ^ 40 * 6049187 * 2
def baseEnd_6049187 : Nat := 1035380166643109753914267

theorem tailTrace_6049187 : CollatzResearch.WordTrace tailWord_6049187 prefixEnd_6049187 1035380166643109753914267 := by
  unfold tailWord_6049187
  simp only [CollatzResearch.WordTrace]
  refine ⟨220631975535836092733913815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147087983690557395155942543 220631975535836092733913815)
  ·
    refine ⟨330947963303754139100870723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220631975535836092733913815 330947963303754139100870723)
    ·
      refine ⟨496421944955631208651306085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330947963303754139100870723 496421944955631208651306085)
      ·
        refine ⟨93079114679180851622119891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 496421944955631208651306085 93079114679180851622119891)
        ·
          refine ⟨139618672018771277433179837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93079114679180851622119891 139618672018771277433179837)
          ·
            refine ⟨52357002007039229037442439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139618672018771277433179837 52357002007039229037442439)
            ·
              refine ⟨78535503010558843556163659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52357002007039229037442439 78535503010558843556163659)
              ·
                refine ⟨117803254515838265334245489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78535503010558843556163659 117803254515838265334245489)
                ·
                  refine ⟨88352440886878699000684117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117803254515838265334245489 88352440886878699000684117)
                  ·
                    refine ⟨1035380166643109753914267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88352440886878699000684117 1035380166643109753914267)
                    ·
                      rfl

theorem cell23_6049187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 8].length) (baseStart_6049187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049187 prefixEnd_6049187 := by exact prefixLift 6049187
  have htrace : WordTrace (prefixWord ++ tailWord_6049187) baseStart_6049187 baseEnd_6049187 := by
    simpa [prefixWord, tailWord_6049187, baseEnd_6049187] using wordTrace_append hprefix tailTrace_6049187
  have hstable : (prefixWord ++ tailWord_6049187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049187).length < 2 ^ (prefixWord ++ tailWord_6049187).sum := by decide
  have hdescent : baseEnd_6049187 < baseStart_6049187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049271 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 4, 3, 2]
def baseStart_6049271 : Nat := 118140960795 + 6049271 * 2 ^ 59
def prefixEnd_6049271 : Nat := 4983230072969 + 3 ^ 40 * 6049271 * 2
def baseEnd_6049271 : Nat := 3106183632304306933092415

theorem tailTrace_6049271 : CollatzResearch.WordTrace tailWord_6049271 prefixEnd_6049271 3106183632304306933092415 := by
  unfold tailWord_6049271
  simp only [CollatzResearch.WordTrace]
  refine ⟨220635039267531775079971667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147090026178354516719981111 220635039267531775079971667)
  ·
    refine ⟨330952558901297662619957501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220635039267531775079971667 330952558901297662619957501)
    ·
      refine ⟨124107209587986623482484063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330952558901297662619957501 124107209587986623482484063)
      ·
        refine ⟨186160814381979935223726095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124107209587986623482484063 186160814381979935223726095)
        ·
          refine ⟨279241221572969902835589143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186160814381979935223726095 279241221572969902835589143)
          ·
            refine ⟨418861832359454854253383715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279241221572969902835589143 418861832359454854253383715)
            ·
              refine ⟨628292748539182281380075573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418861832359454854253383715 628292748539182281380075573)
              ·
                refine ⟨58902445175548338879382085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 628292748539182281380075573 58902445175548338879382085)
                ·
                  refine ⟨11044208470415313539884141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58902445175548338879382085 11044208470415313539884141)
                  ·
                    refine ⟨4141578176405742577456553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11044208470415313539884141 4141578176405742577456553)
                    ·
                      refine ⟨3106183632304306933092415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4141578176405742577456553 3106183632304306933092415)
                      ·
                        rfl

theorem cell23_6049271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 3, 2].length) (baseStart_6049271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049271 prefixEnd_6049271 := by exact prefixLift 6049271
  have htrace : WordTrace (prefixWord ++ tailWord_6049271) baseStart_6049271 baseEnd_6049271 := by
    simpa [prefixWord, tailWord_6049271, baseEnd_6049271] using wordTrace_append hprefix tailTrace_6049271
  have hstable : (prefixWord ++ tailWord_6049271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049271).length < 2 ^ (prefixWord ++ tailWord_6049271).sum := by decide
  have hdescent : baseEnd_6049271 < baseStart_6049271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049301 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_6049301 : Nat := 118140960795 + 6049301 * 2 ^ 59
def prefixEnd_6049301 : Nat := 4983230072969 + 3 ^ 40 * 6049301 * 2
def baseEnd_6049301 : Nat := 3106199036723941815717277

theorem tailTrace_6049301 : CollatzResearch.WordTrace tailWord_6049301 prefixEnd_6049301 3106199036723941815717277 := by
  unfold tailWord_6049301
  simp only [CollatzResearch.WordTrace]
  refine ⟨220636133457423090203563757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147090755638282060135709171 220636133457423090203563757)
  ·
    refine ⟨82738550046533658826336409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220636133457423090203563757 82738550046533658826336409)
    ·
      refine ⟨62053912534900244119752307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82738550046533658826336409 62053912534900244119752307)
      ·
        refine ⟨93080868802350366179628461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62053912534900244119752307 93080868802350366179628461)
        ·
          refine ⟨34905325800881387317360673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93080868802350366179628461 34905325800881387317360673)
          ·
            refine ⟨26178994350661040488020505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34905325800881387317360673 26178994350661040488020505)
            ·
              refine ⟨19634245762995780366015379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26178994350661040488020505 19634245762995780366015379)
              ·
                refine ⟨29451368644493670549023069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19634245762995780366015379 29451368644493670549023069)
                ·
                  refine ⟨11044263241685126455883651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29451368644493670549023069 11044263241685126455883651)
                  ·
                    refine ⟨16566394862527689683825477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11044263241685126455883651 16566394862527689683825477)
                    ·
                      refine ⟨3106199036723941815717277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16566394862527689683825477 3106199036723941815717277)
                      ·
                        rfl

theorem cell23_6049301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_6049301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049301 prefixEnd_6049301 := by exact prefixLift 6049301
  have htrace : WordTrace (prefixWord ++ tailWord_6049301) baseStart_6049301 baseEnd_6049301 := by
    simpa [prefixWord, tailWord_6049301, baseEnd_6049301] using wordTrace_append hprefix tailTrace_6049301
  have hstable : (prefixWord ++ tailWord_6049301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049301).length < 2 ^ (prefixWord ++ tailWord_6049301).sum := by decide
  have hdescent : baseEnd_6049301 < baseStart_6049301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049312 : List Nat := [2, 1, 1, 6, 1, 2, 2, 3, 1, 1, 3]
def baseStart_6049312 : Nat := 118140960795 + 6049312 * 2 ^ 59
def prefixEnd_6049312 : Nat := 4983230072969 + 3 ^ 40 * 6049312 * 2
def baseEnd_6049312 : Nat := 3106204685011141272679727

theorem tailTrace_6049312 : CollatzResearch.WordTrace tailWord_6049312 prefixEnd_6049312 3106204685011141272679727 := by
  unfold tailWord_6049312
  simp only [CollatzResearch.WordTrace]
  refine ⟨110318267330191619541107095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147091023106922159388142793 110318267330191619541107095)
  ·
    refine ⟨165477400995287429311660643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110318267330191619541107095 165477400995287429311660643)
    ·
      refine ⟨248216101492931143967490965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165477400995287429311660643 248216101492931143967490965)
      ·
        refine ⟨11635129757481147373476139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 248216101492931143967490965 11635129757481147373476139)
        ·
          refine ⟨17452694636221721060214209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11635129757481147373476139 17452694636221721060214209)
          ·
            refine ⟨13089520977166290795160657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17452694636221721060214209 13089520977166290795160657)
            ·
              refine ⟨9817140732874718096370493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13089520977166290795160657 9817140732874718096370493)
              ·
                refine ⟨3681427774828019286138935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9817140732874718096370493 3681427774828019286138935)
                ·
                  refine ⟨5522141662242028929208403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3681427774828019286138935 5522141662242028929208403)
                  ·
                    refine ⟨8283212493363043393812605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5522141662242028929208403 8283212493363043393812605)
                    ·
                      refine ⟨3106204685011141272679727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8283212493363043393812605 3106204685011141272679727)
                      ·
                        rfl

theorem cell23_6049312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_6049312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049312 prefixEnd_6049312 := by exact prefixLift 6049312
  have htrace : WordTrace (prefixWord ++ tailWord_6049312) baseStart_6049312 baseEnd_6049312 := by
    simpa [prefixWord, tailWord_6049312, baseEnd_6049312] using wordTrace_append hprefix tailTrace_6049312
  have hstable : (prefixWord ++ tailWord_6049312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049312).length < 2 ^ (prefixWord ++ tailWord_6049312).sum := by decide
  have hdescent : baseEnd_6049312 < baseStart_6049312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049315 : List Nat := [1, 1, 1, 4, 5, 2, 2, 1, 1, 5]
def baseStart_6049315 : Nat := 118140960795 + 6049315 * 2 ^ 59
def prefixEnd_6049315 : Nat := 4983230072969 + 3 ^ 40 * 6049315 * 2
def baseEnd_6049315 : Nat := 1035402075151034920314071

theorem tailTrace_6049315 : CollatzResearch.WordTrace tailWord_6049315 prefixEnd_6049315 1035402075151034920314071 := by
  unfold tailWord_6049315
  simp only [CollatzResearch.WordTrace]
  refine ⟨220636644079372370594573399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147091096052914913729715599 220636644079372370594573399)
  ·
    refine ⟨330954966119058555891860099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220636644079372370594573399 330954966119058555891860099)
    ·
      refine ⟨496432449178587833837790149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330954966119058555891860099 496432449178587833837790149)
      ·
        refine ⟨93081084220985218844585653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 496432449178587833837790149 93081084220985218844585653)
        ·
          refine ⟨8726351645717364266679905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93081084220985218844585653 8726351645717364266679905)
          ·
            refine ⟨6544763734288023200009929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8726351645717364266679905 6544763734288023200009929)
            ·
              refine ⟨4908572800716017400007447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6544763734288023200009929 4908572800716017400007447)
              ·
                refine ⟨7362859201074026100011171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4908572800716017400007447 7362859201074026100011171)
                ·
                  refine ⟨11044288801611039150016757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7362859201074026100011171 11044288801611039150016757)
                  ·
                    refine ⟨1035402075151034920314071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11044288801611039150016757 1035402075151034920314071)
                    ·
                      rfl

theorem cell23_6049315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 1, 5].length) (baseStart_6049315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049315 prefixEnd_6049315 := by exact prefixLift 6049315
  have htrace : WordTrace (prefixWord ++ tailWord_6049315) baseStart_6049315 baseEnd_6049315 := by
    simpa [prefixWord, tailWord_6049315, baseEnd_6049315] using wordTrace_append hprefix tailTrace_6049315
  have hstable : (prefixWord ++ tailWord_6049315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049315).length < 2 ^ (prefixWord ++ tailWord_6049315).sum := by decide
  have hdescent : baseEnd_6049315 < baseStart_6049315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049335 : List Nat := [1, 1, 3, 1, 2, 5, 2, 1, 3, 2, 2]
def baseStart_6049335 : Nat := 118140960795 + 6049335 * 2 ^ 59
def prefixEnd_6049335 : Nat := 4983230072969 + 3 ^ 40 * 6049335 * 2
def baseEnd_6049335 : Nat := 3106216495066194682692121

theorem tailTrace_6049335 : CollatzResearch.WordTrace tailWord_6049335 prefixEnd_6049335 3106216495066194682692121 := by
  unfold tailWord_6049335
  simp only [CollatzResearch.WordTrace]
  refine ⟨220637373539299914010301459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147091582359533276006867639 220637373539299914010301459)
  ·
    refine ⟨330956060308949871015452189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220637373539299914010301459 330956060308949871015452189)
    ·
      refine ⟨124108522615856201630794571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330956060308949871015452189 124108522615856201630794571)
      ·
        refine ⟨186162783923784302446191857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124108522615856201630794571 186162783923784302446191857)
        ·
          refine ⟨139622087942838226834643893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186162783923784302446191857 139622087942838226834643893)
          ·
            refine ⟨13089570744641083765747865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139622087942838226834643893 13089570744641083765747865)
            ·
              refine ⟨9817178058480812824310899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13089570744641083765747865 9817178058480812824310899)
              ·
                refine ⟨14725767087721219236466349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9817178058480812824310899 14725767087721219236466349)
                ·
                  refine ⟨5522162657895457213674881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14725767087721219236466349 5522162657895457213674881)
                  ·
                    refine ⟨4141621993421592910256161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5522162657895457213674881 4141621993421592910256161)
                    ·
                      refine ⟨3106216495066194682692121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4141621993421592910256161 3106216495066194682692121)
                      ·
                        rfl

theorem cell23_6049335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 2, 2].length) (baseStart_6049335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049335 prefixEnd_6049335 := by exact prefixLift 6049335
  have htrace : WordTrace (prefixWord ++ tailWord_6049335) baseStart_6049335 baseEnd_6049335 := by
    simpa [prefixWord, tailWord_6049335, baseEnd_6049335] using wordTrace_append hprefix tailTrace_6049335
  have hstable : (prefixWord ++ tailWord_6049335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049335).length < 2 ^ (prefixWord ++ tailWord_6049335).sum := by decide
  have hdescent : baseEnd_6049335 < baseStart_6049335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049345 : List Nat := [1, 2, 5, 1, 1, 1, 5, 1, 2, 4]
def baseStart_6049345 : Nat := 118140960795 + 6049345 * 2 ^ 59
def prefixEnd_6049345 : Nat := 4983230072969 + 3 ^ 40 * 6049345 * 2
def baseEnd_6049345 : Nat := 1035407209957579881189025

theorem tailTrace_6049345 : CollatzResearch.WordTrace tailWord_6049345 prefixEnd_6049345 1035407209957579881189025 := by
  unfold tailWord_6049345
  simp only [CollatzResearch.WordTrace]
  refine ⟨220637738269263685718165489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147091825512842457145443659 220637738269263685718165489)
  ·
    refine ⟨165478303701947764288624117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220637738269263685718165489 165478303701947764288624117)
    ·
      refine ⟨15513590972057602902058511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165478303701947764288624117 15513590972057602902058511)
      ·
        refine ⟨23270386458086404353087767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15513590972057602902058511 23270386458086404353087767)
        ·
          refine ⟨34905579687129606529631651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23270386458086404353087767 34905579687129606529631651)
          ·
            refine ⟨52358369530694409794447477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34905579687129606529631651 52358369530694409794447477)
            ·
              refine ⟨4908597143502600918229451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52358369530694409794447477 4908597143502600918229451)
              ·
                refine ⟨7362895715253901377344177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4908597143502600918229451 7362895715253901377344177)
                ·
                  refine ⟨5522171786440426033008133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7362895715253901377344177 5522171786440426033008133)
                  ·
                    refine ⟨1035407209957579881189025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5522171786440426033008133 1035407209957579881189025)
                    ·
                      rfl

theorem cell23_6049345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_6049345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049345 prefixEnd_6049345 := by exact prefixLift 6049345
  have htrace : WordTrace (prefixWord ++ tailWord_6049345) baseStart_6049345 baseEnd_6049345 := by
    simpa [prefixWord, tailWord_6049345, baseEnd_6049345] using wordTrace_append hprefix tailTrace_6049345
  have hstable : (prefixWord ++ tailWord_6049345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049345).length < 2 ^ (prefixWord ++ tailWord_6049345).sum := by decide
  have hdescent : baseEnd_6049345 < baseStart_6049345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049408 : List Nat := [2, 1, 1, 2, 1, 4, 2, 3, 1, 4, 2]
def baseStart_6049408 : Nat := 118140960795 + 6049408 * 2 ^ 59
def prefixEnd_6049408 : Nat := 4983230072969 + 3 ^ 40 * 6049408 * 2
def baseEnd_6049408 : Nat := 3106253979153972897079285

theorem tailTrace_6049408 : CollatzResearch.WordTrace tailWord_6049408 prefixEnd_6049408 3106253979153972897079285 := by
  unfold tailWord_6049408
  simp only [CollatzResearch.WordTrace]
  refine ⟨110320018034017723738854439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147093357378690298318472585 110320018034017723738854439)
  ·
    refine ⟨165480027051026585608281659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110320018034017723738854439 165480027051026585608281659)
    ·
      refine ⟨248220040576539878412422489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165480027051026585608281659 248220040576539878412422489)
      ·
        refine ⟨186165030432404908809316867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248220040576539878412422489 186165030432404908809316867)
        ·
          refine ⟨279247545648607363213975301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186165030432404908809316867 279247545648607363213975301)
          ·
            refine ⟨52358914809113880602620369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 279247545648607363213975301 52358914809113880602620369)
            ·
              refine ⟨39269186106835410451965277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52358914809113880602620369 39269186106835410451965277)
              ·
                refine ⟨14725944790063278919486979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39269186106835410451965277 14725944790063278919486979)
                ·
                  refine ⟨22088917185094918379230469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14725944790063278919486979 22088917185094918379230469)
                  ·
                    refine ⟨4141671972205297196105713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22088917185094918379230469 4141671972205297196105713)
                    ·
                      refine ⟨3106253979153972897079285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4141671972205297196105713 3106253979153972897079285)
                      ·
                        rfl

theorem cell23_6049408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 1, 4, 2].length) (baseStart_6049408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049408 prefixEnd_6049408 := by exact prefixLift 6049408
  have htrace : WordTrace (prefixWord ++ tailWord_6049408) baseStart_6049408 baseEnd_6049408 := by
    simpa [prefixWord, tailWord_6049408, baseEnd_6049408] using wordTrace_append hprefix tailTrace_6049408
  have hstable : (prefixWord ++ tailWord_6049408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049408).length < 2 ^ (prefixWord ++ tailWord_6049408).sum := by decide
  have hdescent : baseEnd_6049408 < baseStart_6049408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049518 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_6049518 : Nat := 118140960795 + 6049518 * 2 ^ 59
def prefixEnd_6049518 : Nat := 4983230072969 + 3 ^ 40 * 6049518 * 2
def baseEnd_6049518 : Nat := 3106310462025967466703779

theorem tailTrace_6049518 : CollatzResearch.WordTrace tailWord_6049518 prefixEnd_6049518 3106310462025967466703779 := by
  unfold tailWord_6049518
  simp only [CollatzResearch.WordTrace]
  refine ⟨27580506012204617033026651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147096032065091290842808805 27580506012204617033026651)
  ·
    refine ⟨41370759018306925549539977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27580506012204617033026651 41370759018306925549539977)
    ·
      refine ⟨31028069263730194162154983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41370759018306925549539977 31028069263730194162154983)
      ·
        refine ⟨46542103895595291243232475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31028069263730194162154983 46542103895595291243232475)
        ·
          refine ⟨69813155843392936864848713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46542103895595291243232475 69813155843392936864848713)
          ·
            refine ⟨52359866882544702648636535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69813155843392936864848713 52359866882544702648636535)
            ·
              refine ⟨78539800323817053972954803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52359866882544702648636535 78539800323817053972954803)
              ·
                refine ⟨117809700485725580959432205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78539800323817053972954803 117809700485725580959432205)
                ·
                  refine ⟨44178637682147092859787077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117809700485725580959432205 44178637682147092859787077)
                  ·
                    refine ⟨8283494565402579911210077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44178637682147092859787077 8283494565402579911210077)
                    ·
                      refine ⟨3106310462025967466703779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8283494565402579911210077 3106310462025967466703779)
                      ·
                        rfl

theorem cell23_6049518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_6049518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049518 prefixEnd_6049518 := by exact prefixLift 6049518
  have htrace : WordTrace (prefixWord ++ tailWord_6049518) baseStart_6049518 baseEnd_6049518 := by
    simpa [prefixWord, tailWord_6049518, baseEnd_6049518] using wordTrace_append hprefix tailTrace_6049518
  have hstable : (prefixWord ++ tailWord_6049518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049518).length < 2 ^ (prefixWord ++ tailWord_6049518).sum := by decide
  have hdescent : baseEnd_6049518 < baseStart_6049518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049538 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 10]
def baseStart_6049538 : Nat := 118140960795 + 6049538 * 2 ^ 59
def prefixEnd_6049538 : Nat := 4983230072969 + 3 ^ 40 * 6049538 * 2
def baseEnd_6049538 : Nat := 345146747959895265383743

theorem tailTrace_6049538 : CollatzResearch.WordTrace tailWord_6049538 prefixEnd_6049538 345146747959895265383743 := by
  unfold tailWord_6049538
  simp only [CollatzResearch.WordTrace]
  refine ⟨55161194389391119919985317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147096518371709653119960845 55161194389391119919985317)
  ·
    refine ⟨10342723948010834984997247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55161194389391119919985317 10342723948010834984997247)
    ·
      refine ⟨15514085922016252477495871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10342723948010834984997247 15514085922016252477495871)
      ·
        refine ⟨23271128883024378716243807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15514085922016252477495871 23271128883024378716243807)
        ·
          refine ⟨34906693324536568074365711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23271128883024378716243807 34906693324536568074365711)
          ·
            refine ⟨52360039986804852111548567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34906693324536568074365711 52360039986804852111548567)
            ·
              refine ⟨78540059980207278167322851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52360039986804852111548567 78540059980207278167322851)
              ·
                refine ⟨117810089970310917250984277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78540059980207278167322851 117810089970310917250984277)
                ·
                  refine ⟨345146747959895265383743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 117810089970310917250984277 345146747959895265383743)
                  ·
                    rfl

theorem cell23_6049538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_6049538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049538 prefixEnd_6049538 := by exact prefixLift 6049538
  have htrace : WordTrace (prefixWord ++ tailWord_6049538) baseStart_6049538 baseEnd_6049538 := by
    simpa [prefixWord, tailWord_6049538, baseEnd_6049538] using wordTrace_append hprefix tailTrace_6049538
  have hstable : (prefixWord ++ tailWord_6049538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049538).length < 2 ^ (prefixWord ++ tailWord_6049538).sum := by decide
  have hdescent : baseEnd_6049538 < baseStart_6049538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049559 : List Nat := [1, 1, 3, 4, 2, 2, 3, 2, 1, 4]
def baseStart_6049559 : Nat := 118140960795 + 6049559 * 2 ^ 59
def prefixEnd_6049559 : Nat := 4983230072969 + 3 ^ 40 * 6049559 * 2
def baseEnd_6049559 : Nat := 1035443838244267268763697

theorem tailTrace_6049559 : CollatzResearch.WordTrace tailWord_6049559 prefixEnd_6049559 1035443838244267268763697 := by
  unfold tailWord_6049559
  simp only [CollatzResearch.WordTrace]
  refine ⟨220645543490488400266455731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147097028993658933510970487 220645543490488400266455731)
  ·
    refine ⟨330968315235732600399683597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220645543490488400266455731 330968315235732600399683597)
    ·
      refine ⟨124113118213399725149881349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330968315235732600399683597 124113118213399725149881349)
      ·
        refine ⟨23271209665012448465602753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124113118213399725149881349 23271209665012448465602753)
        ·
          refine ⟨17453407248759336349202065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23271209665012448465602753 17453407248759336349202065)
          ·
            refine ⟨13090055436569502261901549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17453407248759336349202065 13090055436569502261901549)
            ·
              refine ⟨4908770788713563348213081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13090055436569502261901549 4908770788713563348213081)
              ·
                refine ⟨3681578091535172511159811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4908770788713563348213081 3681578091535172511159811)
                ·
                  refine ⟨5522367137302758766739717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3681578091535172511159811 5522367137302758766739717)
                  ·
                    refine ⟨1035443838244267268763697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5522367137302758766739717 1035443838244267268763697)
                    ·
                      rfl

theorem cell23_6049559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 1, 4].length) (baseStart_6049559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049559 prefixEnd_6049559 := by exact prefixLift 6049559
  have htrace : WordTrace (prefixWord ++ tailWord_6049559) baseStart_6049559 baseEnd_6049559 := by
    simpa [prefixWord, tailWord_6049559, baseEnd_6049559] using wordTrace_append hprefix tailTrace_6049559
  have hstable : (prefixWord ++ tailWord_6049559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049559).length < 2 ^ (prefixWord ++ tailWord_6049559).sum := by decide
  have hdescent : baseEnd_6049559 < baseStart_6049559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049568 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 3, 5]
def baseStart_6049568 : Nat := 118140960795 + 6049568 * 2 ^ 59
def prefixEnd_6049568 : Nat := 4983230072969 + 3 ^ 40 * 6049568 * 2
def baseEnd_6049568 : Nat := 1035445378686230757026183

theorem tailTrace_6049568 : CollatzResearch.WordTrace tailWord_6049568 prefixEnd_6049568 1035445378686230757026183 := by
  unfold tailWord_6049568
  simp only [CollatzResearch.WordTrace]
  refine ⟨110322935873727897401766679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147097247831637196535688905 110322935873727897401766679)
  ·
    refine ⟨165484403810591846102650019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110322935873727897401766679 165484403810591846102650019)
    ·
      refine ⟨248226605715887769153975029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165484403810591846102650019 248226605715887769153975029)
      ·
        refine ⟨23271244285864478358185159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 248226605715887769153975029 23271244285864478358185159)
        ·
          refine ⟨34906866428796717537277739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23271244285864478358185159 34906866428796717537277739)
          ·
            refine ⟨52360299643195076305916609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34906866428796717537277739 52360299643195076305916609)
            ·
              refine ⟨39270224732396307229437457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52360299643195076305916609 39270224732396307229437457)
              ·
                refine ⟨29452668549297230422078093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39270224732396307229437457 29452668549297230422078093)
                ·
                  refine ⟨11044750705986461408279285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29452668549297230422078093 11044750705986461408279285)
                  ·
                    refine ⟨1035445378686230757026183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11044750705986461408279285 1035445378686230757026183)
                    ·
                      rfl

theorem cell23_6049568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 3, 5].length) (baseStart_6049568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049568 prefixEnd_6049568 := by exact prefixLift 6049568
  have htrace : WordTrace (prefixWord ++ tailWord_6049568) baseStart_6049568 baseEnd_6049568 := by
    simpa [prefixWord, tailWord_6049568, baseEnd_6049568] using wordTrace_append hprefix tailTrace_6049568
  have hstable : (prefixWord ++ tailWord_6049568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049568).length < 2 ^ (prefixWord ++ tailWord_6049568).sum := by decide
  have hdescent : baseEnd_6049568 < baseStart_6049568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049572 : List Nat := [2, 3, 1, 3, 2, 3, 2, 1, 6]
def baseStart_6049572 : Nat := 118140960795 + 6049572 * 2 ^ 59
def prefixEnd_6049572 : Nat := 4983230072969 + 3 ^ 40 * 6049572 * 2
def baseEnd_6049572 : Nat := 345148687775701139492059

theorem tailTrace_6049572 : CollatzResearch.WordTrace tailWord_6049572 prefixEnd_6049572 345148687775701139492059 := by
  unfold tailWord_6049572
  simp only [CollatzResearch.WordTrace]
  refine ⟨110323008819720651743339485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147097345092960868991119313 110323008819720651743339485)
  ·
    refine ⟨41371128307395244403752307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110323008819720651743339485 41371128307395244403752307)
    ·
      refine ⟨62056692461092866605628461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41371128307395244403752307 62056692461092866605628461)
      ·
        refine ⟨23271259672909824977110673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62056692461092866605628461 23271259672909824977110673)
        ·
          refine ⟨17453444754682368732833005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23271259672909824977110673 17453444754682368732833005)
          ·
            refine ⟨6545041783005888274812377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17453444754682368732833005 6545041783005888274812377)
            ·
              refine ⟨4908781337254416206109283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6545041783005888274812377 4908781337254416206109283)
              ·
                refine ⟨7363172005881624309163925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4908781337254416206109283 7363172005881624309163925)
                ·
                  refine ⟨345148687775701139492059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7363172005881624309163925 345148687775701139492059)
                  ·
                    rfl

theorem cell23_6049572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_6049572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049572 prefixEnd_6049572 := by exact prefixLift 6049572
  have htrace : WordTrace (prefixWord ++ tailWord_6049572) baseStart_6049572 baseEnd_6049572 := by
    simpa [prefixWord, tailWord_6049572, baseEnd_6049572] using wordTrace_append hprefix tailTrace_6049572
  have hstable : (prefixWord ++ tailWord_6049572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049572).length < 2 ^ (prefixWord ++ tailWord_6049572).sum := by decide
  have hdescent : baseEnd_6049572 < baseStart_6049572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049585 : List Nat := [1, 2, 2, 3, 2, 2, 3, 2, 1, 5]
def baseStart_6049585 : Nat := 118140960795 + 6049585 * 2 ^ 59
def prefixEnd_6049585 : Nat := 4983230072969 + 3 ^ 40 * 6049585 * 2
def baseEnd_6049585 : Nat := 1035448288409939568188657

theorem tailTrace_6049585 : CollatzResearch.WordTrace tailWord_6049585 prefixEnd_6049585 1035448288409939568188657 := by
  unfold tailWord_6049585
  simp only [CollatzResearch.WordTrace]
  refine ⟨220646491788394206706902209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147097661192262804471268139 220646491788394206706902209)
  ·
    refine ⟨165484868841295655030176657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220646491788394206706902209 165484868841295655030176657)
    ·
      refine ⟨124113651630971741272632493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165484868841295655030176657 124113651630971741272632493)
      ·
        refine ⟨46542619361614402977237185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124113651630971741272632493 46542619361614402977237185)
        ·
          refine ⟨34906964521210802232927889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46542619361614402977237185 34906964521210802232927889)
          ·
            refine ⟨26180223390908101674695917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34906964521210802232927889 26180223390908101674695917)
            ·
              refine ⟨9817583771590538128010969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26180223390908101674695917 9817583771590538128010969)
              ·
                refine ⟨7363187828692903596008227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9817583771590538128010969 7363187828692903596008227)
                ·
                  refine ⟨11044781743039355394012341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7363187828692903596008227 11044781743039355394012341)
                  ·
                    refine ⟨1035448288409939568188657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11044781743039355394012341 1035448288409939568188657)
                    ·
                      rfl

theorem cell23_6049585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_6049585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049585 prefixEnd_6049585 := by exact prefixLift 6049585
  have htrace : WordTrace (prefixWord ++ tailWord_6049585) baseStart_6049585 baseEnd_6049585 := by
    simpa [prefixWord, tailWord_6049585, baseEnd_6049585] using wordTrace_append hprefix tailTrace_6049585
  have hstable : (prefixWord ++ tailWord_6049585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049585).length < 2 ^ (prefixWord ++ tailWord_6049585).sum := by decide
  have hdescent : baseEnd_6049585 < baseStart_6049585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049592 : List Nat := [2, 1, 2, 1, 3, 4, 2, 1, 2, 3, 2]
def baseStart_6049592 : Nat := 118140960795 + 6049592 * 2 ^ 59
def prefixEnd_6049592 : Nat := 4983230072969 + 3 ^ 40 * 6049592 * 2
def baseEnd_6049592 : Nat := 3106348459594400177178439

theorem tailTrace_6049592 : CollatzResearch.WordTrace tailWord_6049592 prefixEnd_6049592 3106348459594400177178439 := by
  unfold tailWord_6049592
  simp only [CollatzResearch.WordTrace]
  refine ⟨110323373549684423451203515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147097831399579231268271353 110323373549684423451203515)
  ·
    refine ⟨165485060324526635176805273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110323373549684423451203515 165485060324526635176805273)
    ·
      refine ⟨124113795243394976382603955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165485060324526635176805273 124113795243394976382603955)
      ·
        refine ⟨186170692865092464573905933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124113795243394976382603955 186170692865092464573905933)
        ·
          refine ⟨69814009824409674215214725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186170692865092464573905933 69814009824409674215214725)
          ·
            refine ⟨13090126842076813915352761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69814009824409674215214725 13090126842076813915352761)
            ·
              refine ⟨9817595131557610436514571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13090126842076813915352761 9817595131557610436514571)
              ·
                refine ⟨14726392697336415654771857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9817595131557610436514571 14726392697336415654771857)
                ·
                  refine ⟨11044794523002311741078893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14726392697336415654771857 11044794523002311741078893)
                  ·
                    refine ⟨4141797946125866902904585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11044794523002311741078893 4141797946125866902904585)
                    ·
                      refine ⟨3106348459594400177178439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4141797946125866902904585 3106348459594400177178439)
                      ·
                        rfl

theorem cell23_6049592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 2, 3, 2].length) (baseStart_6049592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049592 prefixEnd_6049592 := by exact prefixLift 6049592
  have htrace : WordTrace (prefixWord ++ tailWord_6049592) baseStart_6049592 baseEnd_6049592 := by
    simpa [prefixWord, tailWord_6049592, baseEnd_6049592] using wordTrace_append hprefix tailTrace_6049592
  have hstable : (prefixWord ++ tailWord_6049592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049592).length < 2 ^ (prefixWord ++ tailWord_6049592).sum := by decide
  have hdescent : baseEnd_6049592 < baseStart_6049592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049728 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 7]
def baseStart_6049728 : Nat := 118140960795 + 6049728 * 2 ^ 59
def prefixEnd_6049728 : Nat := 4983230072969 + 3 ^ 40 * 6049728 * 2
def baseEnd_6049728 : Nat := 3106418292963411645077813

theorem tailTrace_6049728 : CollatzResearch.WordTrace tailWord_6049728 prefixEnd_6049728 3106418292963411645077813 := by
  unfold tailWord_6049728
  simp only [CollatzResearch.WordTrace]
  refine ⟨110325853713438071064678919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147101138284584094752905225 110325853713438071064678919)
  ·
    refine ⟨165488780570157106597018379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110325853713438071064678919 165488780570157106597018379)
    ·
      refine ⟨248233170855235659895527569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165488780570157106597018379 248233170855235659895527569)
      ·
        refine ⟨186174878141426744921645677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248233170855235659895527569 186174878141426744921645677)
        ·
          refine ⟨69815579303035029345617129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186174878141426744921645677 69815579303035029345617129)
          ·
            refine ⟨52361684477276272009212847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69815579303035029345617129 52361684477276272009212847)
            ·
              refine ⟨78542526715914408013819271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52361684477276272009212847 78542526715914408013819271)
              ·
                refine ⟨117813790073871612020728907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78542526715914408013819271 117813790073871612020728907)
                ·
                  refine ⟨176720685110807418031093361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117813790073871612020728907 176720685110807418031093361)
                  ·
                    refine ⟨132540513833105563523320021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 176720685110807418031093361 132540513833105563523320021)
                    ·
                      refine ⟨3106418292963411645077813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132540513833105563523320021 3106418292963411645077813)
                      ·
                        rfl

theorem cell23_6049728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_6049728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049728 prefixEnd_6049728 := by exact prefixLift 6049728
  have htrace : WordTrace (prefixWord ++ tailWord_6049728) baseStart_6049728 baseEnd_6049728 := by
    simpa [prefixWord, tailWord_6049728, baseEnd_6049728] using wordTrace_append hprefix tailTrace_6049728
  have hstable : (prefixWord ++ tailWord_6049728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049728).length < 2 ^ (prefixWord ++ tailWord_6049728).sum := by decide
  have hdescent : baseEnd_6049728 < baseStart_6049728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049750 : List Nat := [5, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_6049750 : Nat := 118140960795 + 6049750 * 2 ^ 59
def prefixEnd_6049750 : Nat := 4983230072969 + 3 ^ 40 * 6049750 * 2
def baseEnd_6049750 : Nat := 3106429589537810559002713

theorem tailTrace_6049750 : CollatzResearch.WordTrace tailWord_6049750 prefixEnd_6049750 3106429589537810559002713 := by
  unfold tailWord_6049750
  simp only [CollatzResearch.WordTrace]
  refine ⟨13790781864549777492916169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147101673221864293257772469 13790781864549777492916169)
  ·
    refine ⟨10343086398412333119687127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13790781864549777492916169 10343086398412333119687127)
    ·
      refine ⟨15514629597618499679530691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10343086398412333119687127 15514629597618499679530691)
      ·
        refine ⟨23271944396427749519296037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15514629597618499679530691 23271944396427749519296037)
        ·
          refine ⟨4363489574330203034868007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23271944396427749519296037 4363489574330203034868007)
          ·
            refine ⟨6545234361495304552302011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4363489574330203034868007 6545234361495304552302011)
            ·
              refine ⟨9817851542242956828453017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6545234361495304552302011 9817851542242956828453017)
              ·
                refine ⟨7363388656682217621339763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9817851542242956828453017 7363388656682217621339763)
                ·
                  refine ⟨11045082985023326432009645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7363388656682217621339763 11045082985023326432009645)
                  ·
                    refine ⟨4141906119383747412003617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11045082985023326432009645 4141906119383747412003617)
                    ·
                      refine ⟨3106429589537810559002713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4141906119383747412003617 3106429589537810559002713)
                      ·
                        rfl

theorem cell23_6049750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_6049750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049750 prefixEnd_6049750 := by exact prefixLift 6049750
  have htrace : WordTrace (prefixWord ++ tailWord_6049750) baseStart_6049750 baseEnd_6049750 := by
    simpa [prefixWord, tailWord_6049750, baseEnd_6049750] using wordTrace_append hprefix tailTrace_6049750
  have hstable : (prefixWord ++ tailWord_6049750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049750).length < 2 ^ (prefixWord ++ tailWord_6049750).sum := by decide
  have hdescent : baseEnd_6049750 < baseStart_6049750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049795 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 7, 4]
def baseStart_6049795 : Nat := 118140960795 + 6049795 * 2 ^ 59
def prefixEnd_6049795 : Nat := 4983230072969 + 3 ^ 40 * 6049795 * 2
def baseEnd_6049795 : Nat := 1035484232055754294313335

theorem tailTrace_6049795 : CollatzResearch.WordTrace tailWord_6049795 prefixEnd_6049795 1035484232055754294313335 := by
  unfold tailWord_6049795
  simp only [CollatzResearch.WordTrace]
  refine ⟨220654151117633412572046839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147102767411755608381364559 220654151117633412572046839)
  ·
    refine ⟨330981226676450118858070259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220654151117633412572046839 330981226676450118858070259)
    ·
      refine ⟨496471840014675178287105389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330981226676450118858070259 496471840014675178287105389)
      ·
        refine ⟨186176940005503191857664521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 496471840014675178287105389 186176940005503191857664521)
        ·
          refine ⟨139632705004127393893248391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186176940005503191857664521 139632705004127393893248391)
          ·
            refine ⟨209449057506191090839872587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139632705004127393893248391 209449057506191090839872587)
            ·
              refine ⟨314173586259286636259808881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209449057506191090839872587 314173586259286636259808881)
              ·
                refine ⟨235630189694464977194856661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314173586259286636259808881 235630189694464977194856661)
                ·
                  refine ⟨5522582570964022903004453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 235630189694464977194856661 5522582570964022903004453)
                  ·
                    refine ⟨1035484232055754294313335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5522582570964022903004453 1035484232055754294313335)
                    ·
                      rfl

theorem cell23_6049795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 4].length) (baseStart_6049795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049795 prefixEnd_6049795 := by exact prefixLift 6049795
  have htrace : WordTrace (prefixWord ++ tailWord_6049795) baseStart_6049795 baseEnd_6049795 := by
    simpa [prefixWord, tailWord_6049795, baseEnd_6049795] using wordTrace_append hprefix tailTrace_6049795
  have hstable : (prefixWord ++ tailWord_6049795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049795).length < 2 ^ (prefixWord ++ tailWord_6049795).sum := by decide
  have hdescent : baseEnd_6049795 < baseStart_6049795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049829 : List Nat := [1, 3, 1, 2, 2, 3, 1, 5, 1, 4]
def baseStart_6049829 : Nat := 118140960795 + 6049829 * 2 ^ 59
def prefixEnd_6049829 : Nat := 4983230072969 + 3 ^ 40 * 6049829 * 2
def baseEnd_6049829 : Nat := 1035490051503171916638283

theorem tailTrace_6049829 : CollatzResearch.WordTrace tailWord_6049829 prefixEnd_6049829 1035490051503171916638283 := by
  unfold tailWord_6049829
  simp only [CollatzResearch.WordTrace]
  refine ⟨220655391199510236378784541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147103594133006824252523027 220655391199510236378784541)
  ·
    refine ⟨82745771699816338642044203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220655391199510236378784541 82745771699816338642044203)
    ·
      refine ⟨124118657549724507963066305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82745771699816338642044203 124118657549724507963066305)
      ·
        refine ⟨93088993162293380972299729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124118657549724507963066305 93088993162293380972299729)
        ·
          refine ⟨69816744871720035729224797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93088993162293380972299729 69816744871720035729224797)
          ·
            refine ⟨26181279326895013398459299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69816744871720035729224797 26181279326895013398459299)
            ·
              refine ⟨39271918990342520097688949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26181279326895013398459299 39271918990342520097688949)
              ·
                refine ⟨3681742405344611259158339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39271918990342520097688949 3681742405344611259158339)
                ·
                  refine ⟨5522613608016916888737509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3681742405344611259158339 5522613608016916888737509)
                  ·
                    refine ⟨1035490051503171916638283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5522613608016916888737509 1035490051503171916638283)
                    ·
                      rfl

theorem cell23_6049829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 1, 4].length) (baseStart_6049829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049829 prefixEnd_6049829 := by exact prefixLift 6049829
  have htrace : WordTrace (prefixWord ++ tailWord_6049829) baseStart_6049829 baseEnd_6049829 := by
    simpa [prefixWord, tailWord_6049829, baseEnd_6049829] using wordTrace_append hprefix tailTrace_6049829
  have hstable : (prefixWord ++ tailWord_6049829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049829).length < 2 ^ (prefixWord ++ tailWord_6049829).sum := by decide
  have hdescent : baseEnd_6049829 < baseStart_6049829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049842 : List Nat := [3, 2, 1, 1, 2, 3, 3, 2, 6]
def baseStart_6049842 : Nat := 118140960795 + 6049842 * 2 ^ 59
def prefixEnd_6049842 : Nat := 4983230072969 + 3 ^ 40 * 6049842 * 2
def baseEnd_6049842 : Nat := 345164092195336022116921

theorem tailTrace_6049842 : CollatzResearch.WordTrace tailWord_6049842 prefixEnd_6049842 345164092195336022116921 := by
  unfold tailWord_6049842
  simp only [CollatzResearch.WordTrace]
  refine ⟨55163966337115784899751945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147103910232308759732671853 55163966337115784899751945)
  ·
    refine ⟨41372974752836838674813959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55163966337115784899751945 41372974752836838674813959)
    ·
      refine ⟨62059462129255258012220939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41372974752836838674813959 62059462129255258012220939)
      ·
        refine ⟨93089193193882887018331409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62059462129255258012220939 93089193193882887018331409)
        ·
          refine ⟨69816894895412165263748557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93089193193882887018331409 69816894895412165263748557)
          ·
            refine ⟨26181335585779561973905709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69816894895412165263748557 26181335585779561973905709)
            ·
              refine ⟨9818000844667335740214641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26181335585779561973905709 9818000844667335740214641)
              ·
                refine ⟨7363500633500501805160981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9818000844667335740214641 7363500633500501805160981)
                ·
                  refine ⟨345164092195336022116921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7363500633500501805160981 345164092195336022116921)
                  ·
                    rfl

theorem cell23_6049842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_6049842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049842 prefixEnd_6049842 := by exact prefixLift 6049842
  have htrace : WordTrace (prefixWord ++ tailWord_6049842) baseStart_6049842 baseEnd_6049842 := by
    simpa [prefixWord, tailWord_6049842, baseEnd_6049842] using wordTrace_append hprefix tailTrace_6049842
  have hstable : (prefixWord ++ tailWord_6049842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049842).length < 2 ^ (prefixWord ++ tailWord_6049842).sum := by decide
  have hdescent : baseEnd_6049842 < baseStart_6049842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049845 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_6049845 : Nat := 118140960795 + 6049845 * 2 ^ 59
def prefixEnd_6049845 : Nat := 4983230072969 + 3 ^ 40 * 6049845 * 2
def baseEnd_6049845 : Nat := 3106478370199987687314775

theorem tailTrace_6049845 : CollatzResearch.WordTrace tailWord_6049845 prefixEnd_6049845 3106478370199987687314775 := by
  unfold tailWord_6049845
  simp only [CollatzResearch.WordTrace]
  refine ⟨220655974767452271111366989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147103983178301514074244659 220655974767452271111366989)
  ·
    refine ⟨82745990537794601666762621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220655974767452271111366989 82745990537794601666762621)
    ·
      refine ⟨31029746451672975625035983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82745990537794601666762621 31029746451672975625035983)
      ·
        refine ⟨46544619677509463437553975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31029746451672975625035983 46544619677509463437553975)
        ·
          refine ⟨69816929516264195156330963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46544619677509463437553975 69816929516264195156330963)
          ·
            refine ⟨104725394274396292734496445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69816929516264195156330963 104725394274396292734496445)
            ·
              refine ⟨39272022852898609775436167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104725394274396292734496445 39272022852898609775436167)
              ·
                refine ⟨58908034279347914663154251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39272022852898609775436167 58908034279347914663154251)
                ·
                  refine ⟨88362051419021871994731377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58908034279347914663154251 88362051419021871994731377)
                  ·
                    refine ⟨66271538564266403996048533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88362051419021871994731377 66271538564266403996048533)
                    ·
                      refine ⟨3106478370199987687314775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66271538564266403996048533 3106478370199987687314775)
                      ·
                        rfl

theorem cell23_6049845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_6049845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049845 prefixEnd_6049845 := by exact prefixLift 6049845
  have htrace : WordTrace (prefixWord ++ tailWord_6049845) baseStart_6049845 baseEnd_6049845 := by
    simpa [prefixWord, tailWord_6049845, baseEnd_6049845] using wordTrace_append hprefix tailTrace_6049845
  have hstable : (prefixWord ++ tailWord_6049845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049845).length < 2 ^ (prefixWord ++ tailWord_6049845).sum := by decide
  have hdescent : baseEnd_6049845 < baseStart_6049845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049846 : List Nat := [5, 1, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_6049846 : Nat := 118140960795 + 6049846 * 2 ^ 59
def prefixEnd_6049846 : Nat := 4983230072969 + 3 ^ 40 * 6049846 * 2
def baseEnd_6049846 : Nat := 1035492961226880727800757

theorem tailTrace_6049846 : CollatzResearch.WordTrace tailWord_6049846 prefixEnd_6049846 1035492961226880727800757 := by
  unfold tailWord_6049846
  simp only [CollatzResearch.WordTrace]
  refine ⟨13791000702528040517634587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147104007493632432188102261 13791000702528040517634587)
  ·
    refine ⟨20686501053792060776451881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13791000702528040517634587 20686501053792060776451881)
    ·
      refine ⟨15514875790344045582338911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20686501053792060776451881 15514875790344045582338911)
      ·
        refine ⟨23272313685516068373508367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15514875790344045582338911 23272313685516068373508367)
        ·
          refine ⟨34908470528274102560262551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23272313685516068373508367 34908470528274102560262551)
          ·
            refine ⟨52362705792411153840393827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34908470528274102560262551 52362705792411153840393827)
            ·
              refine ⟨78544058688616730760590741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52362705792411153840393827 78544058688616730760590741)
              ·
                refine ⟨3681752751028909254402691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78544058688616730760590741 3681752751028909254402691)
                ·
                  refine ⟨5522629126543363881604037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3681752751028909254402691 5522629126543363881604037)
                  ·
                    refine ⟨1035492961226880727800757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5522629126543363881604037 1035492961226880727800757)
                    ·
                      rfl

theorem cell23_6049846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_6049846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049846 prefixEnd_6049846 := by exact prefixLift 6049846
  have htrace : WordTrace (prefixWord ++ tailWord_6049846) baseStart_6049846 baseEnd_6049846 := by
    simpa [prefixWord, tailWord_6049846, baseEnd_6049846] using wordTrace_append hprefix tailTrace_6049846
  have hstable : (prefixWord ++ tailWord_6049846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049846).length < 2 ^ (prefixWord ++ tailWord_6049846).sum := by decide
  have hdescent : baseEnd_6049846 < baseStart_6049846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049855 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 5, 5]
def baseStart_6049855 : Nat := 118140960795 + 6049855 * 2 ^ 59
def prefixEnd_6049855 : Nat := 4983230072969 + 3 ^ 40 * 6049855 * 2
def baseEnd_6049855 : Nat := 1035494501668844216063243

theorem tailTrace_6049855 : CollatzResearch.WordTrace tailWord_6049855 prefixEnd_6049855 1035494501668844216063243 := by
  unfold tailWord_6049855
  simp only [CollatzResearch.WordTrace]
  refine ⟨220656339497416042819231019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147104226331610695212820679 220656339497416042819231019)
  ·
    refine ⟨330984509246124064228846529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220656339497416042819231019 330984509246124064228846529)
    ·
      refine ⟨248238381934593048171634897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330984509246124064228846529 248238381934593048171634897)
      ·
        refine ⟨186178786450944786128726173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248238381934593048171634897 186178786450944786128726173)
        ·
          refine ⟨69817044919104294798272315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186178786450944786128726173 69817044919104294798272315)
          ·
            refine ⟨104725567378656442197408473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69817044919104294798272315 104725567378656442197408473)
            ·
              refine ⟨78544175533992331648056355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104725567378656442197408473 78544175533992331648056355)
              ·
                refine ⟨117816263300988497472084533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78544175533992331648056355 117816263300988497472084533)
                ·
                  refine ⟨11045274684467671638007925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117816263300988497472084533 11045274684467671638007925)
                  ·
                    refine ⟨1035494501668844216063243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11045274684467671638007925 1035494501668844216063243)
                    ·
                      rfl

theorem cell23_6049855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 5].length) (baseStart_6049855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049855 prefixEnd_6049855 := by exact prefixLift 6049855
  have htrace : WordTrace (prefixWord ++ tailWord_6049855) baseStart_6049855 baseEnd_6049855 := by
    simpa [prefixWord, tailWord_6049855, baseEnd_6049855] using wordTrace_append hprefix tailTrace_6049855
  have hstable : (prefixWord ++ tailWord_6049855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049855).length < 2 ^ (prefixWord ++ tailWord_6049855).sum := by decide
  have hdescent : baseEnd_6049855 < baseStart_6049855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049903 : List Nat := [1, 1, 2, 1, 3, 5, 3, 2, 1, 1, 3]
def baseStart_6049903 : Nat := 118140960795 + 6049903 * 2 ^ 59
def prefixEnd_6049903 : Nat := 4983230072969 + 3 ^ 40 * 6049903 * 2
def baseEnd_6049903 : Nat := 3106508152077948460389509

theorem tailTrace_6049903 : CollatzResearch.WordTrace tailWord_6049903 prefixEnd_6049903 3106508152077948460389509 := by
  unfold tailWord_6049903
  simp only [CollatzResearch.WordTrace]
  refine ⟨220658090201242147016978363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147105393467494764677985575 220658090201242147016978363)
  ·
    refine ⟨330987135301863220525467545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220658090201242147016978363 330987135301863220525467545)
    ·
      refine ⟨248240351476397415394100659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330987135301863220525467545 248240351476397415394100659)
      ·
        refine ⟨372360527214596123091150989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248240351476397415394100659 372360527214596123091150989)
        ·
          refine ⟨139635197705473546159181621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 372360527214596123091150989 139635197705473546159181621)
          ·
            refine ⟨13090799784888144952423277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139635197705473546159181621 13090799784888144952423277)
            ·
              refine ⟨4909049919333054357158729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13090799784888144952423277 4909049919333054357158729)
              ·
                refine ⟨3681787439499790767869047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4909049919333054357158729 3681787439499790767869047)
                ·
                  refine ⟨5522681159249686151803571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3681787439499790767869047 5522681159249686151803571)
                  ·
                    refine ⟨8284021738874529227705357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5522681159249686151803571 8284021738874529227705357)
                    ·
                      refine ⟨3106508152077948460389509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8284021738874529227705357 3106508152077948460389509)
                      ·
                        rfl

theorem cell23_6049903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 1, 1, 3].length) (baseStart_6049903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049903 prefixEnd_6049903 := by exact prefixLift 6049903
  have htrace : WordTrace (prefixWord ++ tailWord_6049903) baseStart_6049903 baseEnd_6049903 := by
    simpa [prefixWord, tailWord_6049903, baseEnd_6049903] using wordTrace_append hprefix tailTrace_6049903
  have hstable : (prefixWord ++ tailWord_6049903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049903).length < 2 ^ (prefixWord ++ tailWord_6049903).sum := by decide
  have hdescent : baseEnd_6049903 < baseStart_6049903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049905 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 3, 1, 6]
def baseStart_6049905 : Nat := 118140960795 + 6049905 * 2 ^ 59
def prefixEnd_6049905 : Nat := 4983230072969 + 3 ^ 40 * 6049905 * 2
def baseEnd_6049905 : Nat := 3106509179039257452564499

theorem tailTrace_6049905 : CollatzResearch.WordTrace tailWord_6049905 prefixEnd_6049905 3106509179039257452564499 := by
  unfold tailWord_6049905
  simp only [CollatzResearch.WordTrace]
  refine ⟨220658163147234901358551169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147105442098156600905700779 220658163147234901358551169)
  ·
    refine ⟨165493622360426176018913377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220658163147234901358551169 165493622360426176018913377)
    ·
      refine ⟨124120216770319632014185033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165493622360426176018913377 124120216770319632014185033)
      ·
        refine ⟨93090162577739724010638775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124120216770319632014185033 93090162577739724010638775)
        ·
          refine ⟨139635243866609586015958163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93090162577739724010638775 139635243866609586015958163)
          ·
            refine ⟨209452865799914379023937245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139635243866609586015958163 209452865799914379023937245)
            ·
              refine ⟨78544824674967892133976467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209452865799914379023937245 78544824674967892133976467)
              ·
                refine ⟨117817237012451838200964701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78544824674967892133976467 117817237012451838200964701)
                ·
                  refine ⟨44181463879669439325361763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117817237012451838200964701 44181463879669439325361763)
                  ·
                    refine ⟨66272195819504158988042645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44181463879669439325361763 66272195819504158988042645)
                    ·
                      refine ⟨3106509179039257452564499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66272195819504158988042645 3106509179039257452564499)
                      ·
                        rfl

theorem cell23_6049905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_6049905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049905 prefixEnd_6049905 := by exact prefixLift 6049905
  have htrace : WordTrace (prefixWord ++ tailWord_6049905) baseStart_6049905 baseEnd_6049905 := by
    simpa [prefixWord, tailWord_6049905, baseEnd_6049905] using wordTrace_append hprefix tailTrace_6049905
  have hstable : (prefixWord ++ tailWord_6049905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049905).length < 2 ^ (prefixWord ++ tailWord_6049905).sum := by decide
  have hdescent : baseEnd_6049905 < baseStart_6049905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049912 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 3, 2, 3]
def baseStart_6049912 : Nat := 118140960795 + 6049912 * 2 ^ 59
def prefixEnd_6049912 : Nat := 4983230072969 + 3 ^ 40 * 6049912 * 2
def baseEnd_6049912 : Nat := 3106512773403838925176967

theorem tailTrace_6049912 : CollatzResearch.WordTrace tailWord_6049912 prefixEnd_6049912 3106512773403838925176967 := by
  unfold tailWord_6049912
  simp only [CollatzResearch.WordTrace]
  refine ⟨110329209229104770777027995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147105612305473027702703993 110329209229104770777027995)
  ·
    refine ⟨165493813843657156165541993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110329209229104770777027995 165493813843657156165541993)
    ·
      refine ⟨124120360382742867124156495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165493813843657156165541993 124120360382742867124156495)
      ·
        refine ⟨186180540574114300686234743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124120360382742867124156495 186180540574114300686234743)
        ·
          refine ⟨279270810861171451029352115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186180540574114300686234743 279270810861171451029352115)
          ·
            refine ⟨418906216291757176544028173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279270810861171451029352115 418906216291757176544028173)
            ·
              refine ⟨157089831109408941204010565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 418906216291757176544028173 157089831109408941204010565)
              ·
                refine ⟨29454343333014176475751981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157089831109408941204010565 29454343333014176475751981)
                ·
                  refine ⟨11045378749880316178406993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29454343333014176475751981 11045378749880316178406993)
                  ·
                    refine ⟨8284034062410237133805245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11045378749880316178406993 8284034062410237133805245)
                    ·
                      refine ⟨3106512773403838925176967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8284034062410237133805245 3106512773403838925176967)
                      ·
                        rfl

theorem cell23_6049912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_6049912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049912 prefixEnd_6049912 := by exact prefixLift 6049912
  have htrace : WordTrace (prefixWord ++ tailWord_6049912) baseStart_6049912 baseEnd_6049912 := by
    simpa [prefixWord, tailWord_6049912, baseEnd_6049912] using wordTrace_append hprefix tailTrace_6049912
  have hstable : (prefixWord ++ tailWord_6049912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049912).length < 2 ^ (prefixWord ++ tailWord_6049912).sum := by decide
  have hdescent : baseEnd_6049912 < baseStart_6049912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049945 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 4, 7]
def baseStart_6049945 : Nat := 118140960795 + 6049945 * 2 ^ 59
def prefixEnd_6049945 : Nat := 4983230072969 + 3 ^ 40 * 6049945 * 2
def baseEnd_6049945 : Nat := 1035509906088479098688105

theorem tailTrace_6049945 : CollatzResearch.WordTrace tailWord_6049945 prefixEnd_6049945 1035509906088479098688105 := by
  unfold tailWord_6049945
  simp only [CollatzResearch.WordTrace]
  refine ⟨220659622067089988190007289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147106414711393325460004859 220659622067089988190007289)
  ·
    refine ⟨165494716550317491142505467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220659622067089988190007289 165494716550317491142505467)
    ·
      refine ⟨248242074825476236713758201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165494716550317491142505467 248242074825476236713758201)
      ·
        refine ⟨186181556119107177535318651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248242074825476236713758201 186181556119107177535318651)
        ·
          refine ⟨279272334178660766302977977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186181556119107177535318651 279272334178660766302977977)
          ·
            refine ⟨209454250633995574727233483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279272334178660766302977977 209454250633995574727233483)
            ·
              refine ⟨314181375950993362090850225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209454250633995574727233483 314181375950993362090850225)
              ·
                refine ⟨235636031963245021568137669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314181375950993362090850225 235636031963245021568137669)
                ·
                  refine ⟨44181755993108441544025813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235636031963245021568137669 44181755993108441544025813)
                  ·
                    refine ⟨1035509906088479098688105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44181755993108441544025813 1035509906088479098688105)
                    ·
                      rfl

theorem cell23_6049945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 7].length) (baseStart_6049945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049945 prefixEnd_6049945 := by exact prefixLift 6049945
  have htrace : WordTrace (prefixWord ++ tailWord_6049945) baseStart_6049945 baseEnd_6049945 := by
    simpa [prefixWord, tailWord_6049945, baseEnd_6049945] using wordTrace_append hprefix tailTrace_6049945
  have hstable : (prefixWord ++ tailWord_6049945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049945).length < 2 ^ (prefixWord ++ tailWord_6049945).sum := by decide
  have hdescent : baseEnd_6049945 < baseStart_6049945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049946 : List Nat := [3, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5]
def baseStart_6049946 : Nat := 118140960795 + 6049946 * 2 ^ 59
def prefixEnd_6049946 : Nat := 4983230072969 + 3 ^ 40 * 6049946 * 2
def baseEnd_6049946 : Nat := 3106530231746091792151811

theorem tailTrace_6049946 : CollatzResearch.WordTrace tailWord_6049946 prefixEnd_6049946 3106530231746091792151811 := by
  unfold tailWord_6049946
  simp only [CollatzResearch.WordTrace]
  refine ⟨55164914635021591340198423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147106439026724243573862461 55164914635021591340198423)
  ·
    refine ⟨82747371952532387010297635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55164914635021591340198423 82747371952532387010297635)
    ·
      refine ⟨124121057928798580515446453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82747371952532387010297635 124121057928798580515446453)
      ·
        refine ⟨11636349180824866923323105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124121057928798580515446453 11636349180824866923323105)
        ·
          refine ⟨8727261885618650192492329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11636349180824866923323105 8727261885618650192492329)
          ·
            refine ⟨6545446414213987644369247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8727261885618650192492329 6545446414213987644369247)
            ·
              refine ⟨9818169621320981466553871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6545446414213987644369247 9818169621320981466553871)
              ·
                refine ⟨14727254431981472199830807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9818169621320981466553871 14727254431981472199830807)
                ·
                  refine ⟨22090881647972208299746211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14727254431981472199830807 22090881647972208299746211)
                  ·
                    refine ⟨33136322471958312449619317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22090881647972208299746211 33136322471958312449619317)
                    ·
                      refine ⟨3106530231746091792151811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33136322471958312449619317 3106530231746091792151811)
                      ·
                        rfl

theorem cell23_6049946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_6049946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049946 prefixEnd_6049946 := by exact prefixLift 6049946
  have htrace : WordTrace (prefixWord ++ tailWord_6049946) baseStart_6049946 baseEnd_6049946 := by
    simpa [prefixWord, tailWord_6049946, baseEnd_6049946] using wordTrace_append hprefix tailTrace_6049946
  have hstable : (prefixWord ++ tailWord_6049946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049946).length < 2 ^ (prefixWord ++ tailWord_6049946).sum := by decide
  have hdescent : baseEnd_6049946 < baseStart_6049946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049955 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 7]
def baseStart_6049955 : Nat := 118140960795 + 6049955 * 2 ^ 59
def prefixEnd_6049955 : Nat := 4983230072969 + 3 ^ 40 * 6049955 * 2
def baseEnd_6049955 : Nat := 3106534853071982256939269

theorem tailTrace_6049955 : CollatzResearch.WordTrace tailWord_6049955 prefixEnd_6049955 3106534853071982256939269 := by
  unfold tailWord_6049955
  simp only [CollatzResearch.WordTrace]
  refine ⟨220659986797053759897871319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147106657864702506598580879 220659986797053759897871319)
  ·
    refine ⟨330989980195580639846806979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220659986797053759897871319 330989980195580639846806979)
    ·
      refine ⟨496484970293370959770210469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330989980195580639846806979 496484970293370959770210469)
      ·
        refine ⟨93090931930007054956914463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 496484970293370959770210469 93090931930007054956914463)
        ·
          refine ⟨139636397895010582435371695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93090931930007054956914463 139636397895010582435371695)
          ·
            refine ⟨209454596842515873653057543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139636397895010582435371695 209454596842515873653057543)
            ·
              refine ⟨314181895263773810479586315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209454596842515873653057543 314181895263773810479586315)
              ·
                refine ⟨471272842895660715719379473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314181895263773810479586315 471272842895660715719379473)
                ·
                  refine ⟨353454632171745536789534605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471272842895660715719379473 353454632171745536789534605)
                  ·
                    refine ⟨132545487064404576296075477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 353454632171745536789534605 132545487064404576296075477)
                    ·
                      refine ⟨3106534853071982256939269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132545487064404576296075477 3106534853071982256939269)
                      ·
                        rfl

theorem cell23_6049955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_6049955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049955 prefixEnd_6049955 := by exact prefixLift 6049955
  have htrace : WordTrace (prefixWord ++ tailWord_6049955) baseStart_6049955 baseEnd_6049955 := by
    simpa [prefixWord, tailWord_6049955, baseEnd_6049955] using wordTrace_append hprefix tailTrace_6049955
  have hstable : (prefixWord ++ tailWord_6049955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049955).length < 2 ^ (prefixWord ++ tailWord_6049955).sum := by decide
  have hdescent : baseEnd_6049955 < baseStart_6049955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6049999 : List Nat := [1, 1, 2, 1, 1, 3, 3, 4, 1, 4, 2]
def baseStart_6049999 : Nat := 118140960795 + 6049999 * 2 ^ 59
def prefixEnd_6049999 : Nat := 4983230072969 + 3 ^ 40 * 6049999 * 2
def baseEnd_6049999 : Nat := 3106557446220780084789067

theorem tailTrace_6049999 : CollatzResearch.WordTrace tailWord_6049999 prefixEnd_6049999 3106557446220780084789067 := by
  unfold tailWord_6049999
  simp only [CollatzResearch.WordTrace]
  refine ⟨220661591608894355412473051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147107727739262903608315367 220661591608894355412473051)
  ·
    refine ⟨330992387413341533118709577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220661591608894355412473051 330992387413341533118709577)
    ·
      refine ⟨248244290560006149839032183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330992387413341533118709577 248244290560006149839032183)
      ·
        refine ⟨372366435840009224758548275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248244290560006149839032183 372366435840009224758548275)
        ·
          refine ⟨558549653760013837137822413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372366435840009224758548275 558549653760013837137822413)
          ·
            refine ⟨209456120160005188926683405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 558549653760013837137822413 209456120160005188926683405)
            ·
              refine ⟨78546045060001945847506277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209456120160005188926683405 78546045060001945847506277)
              ·
                refine ⟨14727383448750364846407427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78546045060001945847506277 14727383448750364846407427)
                ·
                  refine ⟨22091075173125547269611141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14727383448750364846407427 22091075173125547269611141)
                  ·
                    refine ⟨4142076594961040113052089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22091075173125547269611141 4142076594961040113052089)
                    ·
                      refine ⟨3106557446220780084789067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4142076594961040113052089 3106557446220780084789067)
                      ·
                        rfl

theorem cell23_6049999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 4, 2].length) (baseStart_6049999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6049999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6049999 prefixEnd_6049999 := by exact prefixLift 6049999
  have htrace : WordTrace (prefixWord ++ tailWord_6049999) baseStart_6049999 baseEnd_6049999 := by
    simpa [prefixWord, tailWord_6049999, baseEnd_6049999] using wordTrace_append hprefix tailTrace_6049999
  have hstable : (prefixWord ++ tailWord_6049999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6049999).length < 2 ^ (prefixWord ++ tailWord_6049999).sum := by decide
  have hdescent : baseEnd_6049999 < baseStart_6049999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6049999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050016 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 4, 2, 2]
def baseStart_6050016 : Nat := 118140960795 + 6050016 * 2 ^ 59
def prefixEnd_6050016 : Nat := 4983230072969 + 3 ^ 40 * 6050016 * 2
def baseEnd_6050016 : Nat := 3106566175391906518276489

theorem tailTrace_6050016 : CollatzResearch.WordTrace tailWord_6050016 prefixEnd_6050016 3106566175391906518276489 := by
  unfold tailWord_6050016
  simp only [CollatzResearch.WordTrace]
  refine ⟨110331105824916383657920951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147108141099888511543894601 110331105824916383657920951)
  ·
    refine ⟨165496658737374575486881427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110331105824916383657920951 165496658737374575486881427)
    ·
      refine ⟨248244988106061863230322141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165496658737374575486881427 248244988106061863230322141)
      ·
        refine ⟨93091870539773198711370803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248244988106061863230322141 93091870539773198711370803)
        ·
          refine ⟨139637805809659798067056205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93091870539773198711370803 139637805809659798067056205)
          ·
            refine ⟨52364177178622424275146077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139637805809659798067056205 52364177178622424275146077)
            ·
              refine ⟨19636566441983409103179779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52364177178622424275146077 19636566441983409103179779)
              ·
                refine ⟨29454849662975113654769669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19636566441983409103179779 29454849662975113654769669)
                ·
                  refine ⟨5522784311807833810269313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29454849662975113654769669 5522784311807833810269313)
                  ·
                    refine ⟨4142088233855875357701985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5522784311807833810269313 4142088233855875357701985)
                    ·
                      refine ⟨3106566175391906518276489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4142088233855875357701985 3106566175391906518276489)
                      ·
                        rfl

theorem cell23_6050016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_6050016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050016 prefixEnd_6050016 := by exact prefixLift 6050016
  have htrace : WordTrace (prefixWord ++ tailWord_6050016) baseStart_6050016 baseEnd_6050016 := by
    simpa [prefixWord, tailWord_6050016, baseEnd_6050016] using wordTrace_append hprefix tailTrace_6050016
  have hstable : (prefixWord ++ tailWord_6050016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050016).length < 2 ^ (prefixWord ++ tailWord_6050016).sum := by decide
  have hdescent : baseEnd_6050016 < baseStart_6050016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050056 : List Nat := [2, 1, 3, 2, 3, 1, 3, 3, 5]
def baseStart_6050056 : Nat := 118140960795 + 6050056 * 2 ^ 59
def prefixEnd_6050056 : Nat := 4983230072969 + 3 ^ 40 * 6050056 * 2
def baseEnd_6050056 : Nat := 345176301624231817975145

theorem tailTrace_6050056 : CollatzResearch.WordTrace tailWord_6050056 prefixEnd_6050056 345176301624231817975145 := by
  unfold tailWord_6050056
  simp only [CollatzResearch.WordTrace]
  refine ⟨110331835284843927073649011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147109113713125236098198681 110331835284843927073649011)
  ·
    refine ⟨165497752927265890610473517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110331835284843927073649011 165497752927265890610473517)
    ·
      refine ⟨62061657347724708978927569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165497752927265890610473517 62061657347724708978927569)
      ·
        refine ⟨46546243010793531734195677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62061657347724708978927569 46546243010793531734195677)
        ·
          refine ⟨17454841129047574400323379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46546243010793531734195677 17454841129047574400323379)
          ·
            refine ⟨26182261693571361600485069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17454841129047574400323379 26182261693571361600485069)
            ·
              refine ⟨9818348135089260600181901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26182261693571361600485069 9818348135089260600181901)
              ·
                refine ⟨3681880550658472725068213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9818348135089260600181901 3681880550658472725068213)
                ·
                  refine ⟨345176301624231817975145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3681880550658472725068213 345176301624231817975145)
                  ·
                    rfl

theorem cell23_6050056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 5].length) (baseStart_6050056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050056 prefixEnd_6050056 := by exact prefixLift 6050056
  have htrace : WordTrace (prefixWord ++ tailWord_6050056) baseStart_6050056 baseEnd_6050056 := by
    simpa [prefixWord, tailWord_6050056, baseEnd_6050056] using wordTrace_append hprefix tailTrace_6050056
  have hstable : (prefixWord ++ tailWord_6050056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050056).length < 2 ^ (prefixWord ++ tailWord_6050056).sum := by decide
  have hdescent : baseEnd_6050056 < baseStart_6050056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050079 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 5]
def baseStart_6050079 : Nat := 118140960795 + 6050079 * 2 ^ 59
def prefixEnd_6050079 : Nat := 4983230072969 + 3 ^ 40 * 6050079 * 2
def baseEnd_6050079 : Nat := 3106598524673139771788699

theorem tailTrace_6050079 : CollatzResearch.WordTrace tailWord_6050079 prefixEnd_6050079 3106598524673139771788699 := by
  unfold tailWord_6050079
  simp only [CollatzResearch.WordTrace]
  refine ⟨220664509448604529075385291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147109672965736352716923527 220664509448604529075385291)
  ·
    refine ⟨330996764172906793613077937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220664509448604529075385291 330996764172906793613077937)
    ·
      refine ⟨248247573129680095209808453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330996764172906793613077937 248247573129680095209808453)
      ·
        refine ⟨46546419961815017851839085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248247573129680095209808453 46546419961815017851839085)
        ·
          refine ⟨17454907485680631694439657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46546419961815017851839085 17454907485680631694439657)
          ·
            refine ⟨13091180614260473770829743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17454907485680631694439657 13091180614260473770829743)
            ·
              refine ⟨19636770921390710656244615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13091180614260473770829743 19636770921390710656244615)
              ·
                refine ⟨29455156382086065984366923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19636770921390710656244615 29455156382086065984366923)
                ·
                  refine ⟨44182734573129098976550385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29455156382086065984366923 44182734573129098976550385)
                  ·
                    refine ⟨33137050929846824232412789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44182734573129098976550385 33137050929846824232412789)
                    ·
                      refine ⟨3106598524673139771788699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33137050929846824232412789 3106598524673139771788699)
                      ·
                        rfl

theorem cell23_6050079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_6050079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050079 prefixEnd_6050079 := by exact prefixLift 6050079
  have htrace : WordTrace (prefixWord ++ tailWord_6050079) baseStart_6050079 baseEnd_6050079 := by
    simpa [prefixWord, tailWord_6050079, baseEnd_6050079] using wordTrace_append hprefix tailTrace_6050079
  have hstable : (prefixWord ++ tailWord_6050079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050079).length < 2 ^ (prefixWord ++ tailWord_6050079).sum := by decide
  have hdescent : baseEnd_6050079 < baseStart_6050079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050099 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 5, 4]
def baseStart_6050099 : Nat := 118140960795 + 6050099 * 2 ^ 59
def prefixEnd_6050099 : Nat := 4983230072969 + 3 ^ 40 * 6050099 * 2
def baseEnd_6050099 : Nat := 1035536264762076564512869

theorem tailTrace_6050099 : CollatzResearch.WordTrace tailWord_6050099 prefixEnd_6050099 1035536264762076564512869 := by
  unfold tailWord_6050099
  simp only [CollatzResearch.WordTrace]
  refine ⟨220665238908532072491113351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147110159272354714994075567 220665238908532072491113351)
  ·
    refine ⟨330997858362798108736670027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220665238908532072491113351 330997858362798108736670027)
    ·
      refine ⟨496496787544197163105005041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330997858362798108736670027 496496787544197163105005041)
      ·
        refine ⟨372372590658147872328753781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496496787544197163105005041 372372590658147872328753781)
        ·
          refine ⟨34909930374201363030820667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 372372590658147872328753781 34909930374201363030820667)
          ·
            refine ⟨52364895561302044546231001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34909930374201363030820667 52364895561302044546231001)
            ·
              refine ⟨39273671670976533409673251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52364895561302044546231001 39273671670976533409673251)
              ·
                refine ⟨58910507506464800114509877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39273671670976533409673251 58910507506464800114509877)
                ·
                  refine ⟨5522860078731075010735301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58910507506464800114509877 5522860078731075010735301)
                  ·
                    refine ⟨1035536264762076564512869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5522860078731075010735301 1035536264762076564512869)
                    ·
                      rfl

theorem cell23_6050099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 4].length) (baseStart_6050099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050099 prefixEnd_6050099 := by exact prefixLift 6050099
  have htrace : WordTrace (prefixWord ++ tailWord_6050099) baseStart_6050099 baseEnd_6050099 := by
    simpa [prefixWord, tailWord_6050099, baseEnd_6050099] using wordTrace_append hprefix tailTrace_6050099
  have hstable : (prefixWord ++ tailWord_6050099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050099).length < 2 ^ (prefixWord ++ tailWord_6050099).sum := by decide
  have hdescent : baseEnd_6050099 < baseStart_6050099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050106 : List Nat := [3, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4]
def baseStart_6050106 : Nat := 118140960795 + 6050106 * 2 ^ 59
def prefixEnd_6050106 : Nat := 4983230072969 + 3 ^ 40 * 6050106 * 2
def baseEnd_6050106 : Nat := 3106612388650811166151075

theorem tailTrace_6050106 : CollatzResearch.WordTrace tailWord_6050106 prefixEnd_6050106 3106612388650811166151075 := by
  unfold tailWord_6050106
  simp only [CollatzResearch.WordTrace]
  refine ⟨55166373554876678171654543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147110329479671141791078781 55166373554876678171654543)
  ·
    refine ⟨82749560332315017257481815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55166373554876678171654543 82749560332315017257481815)
    ·
      refine ⟨124124340498472525886222723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82749560332315017257481815 124124340498472525886222723)
      ·
        refine ⟨186186510747708788829334085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124124340498472525886222723 186186510747708788829334085)
        ·
          refine ⟨34909970765195397905500141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186186510747708788829334085 34909970765195397905500141)
          ·
            refine ⟨13091239036948274214562553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34909970765195397905500141 13091239036948274214562553)
            ·
              refine ⟨9818429277711205660921915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13091239036948274214562553 9818429277711205660921915)
              ·
                refine ⟨14727643916566808491382873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9818429277711205660921915 14727643916566808491382873)
                ·
                  refine ⟨11045732937425106368537155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14727643916566808491382873 11045732937425106368537155)
                  ·
                    refine ⟨16568599406137659552805733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11045732937425106368537155 16568599406137659552805733)
                    ·
                      refine ⟨3106612388650811166151075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16568599406137659552805733 3106612388650811166151075)
                      ·
                        rfl

theorem cell23_6050106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_6050106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050106 prefixEnd_6050106 := by exact prefixLift 6050106
  have htrace : WordTrace (prefixWord ++ tailWord_6050106) baseStart_6050106 baseEnd_6050106 := by
    simpa [prefixWord, tailWord_6050106, baseEnd_6050106] using wordTrace_append hprefix tailTrace_6050106
  have hstable : (prefixWord ++ tailWord_6050106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050106).length < 2 ^ (prefixWord ++ tailWord_6050106).sum := by decide
  have hdescent : baseEnd_6050106 < baseStart_6050106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050112 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 8]
def baseStart_6050112 : Nat := 118140960795 + 6050112 * 2 ^ 59
def prefixEnd_6050112 : Nat := 4983230072969 + 3 ^ 40 * 6050112 * 2
def baseEnd_6050112 : Nat := 345179496614970904741783

theorem tailTrace_6050112 : CollatzResearch.WordTrace tailWord_6050112 prefixEnd_6050112 345179496614970904741783 := by
  unfold tailWord_6050112
  simp only [CollatzResearch.WordTrace]
  refine ⟨110332856528742487855668295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147110475371656650474224393 110332856528742487855668295)
  ·
    refine ⟨165499284793113731783502443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110332856528742487855668295 165499284793113731783502443)
    ·
      refine ⟨248248927189670597675253665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165499284793113731783502443 248248927189670597675253665)
      ·
        refine ⟨186186695392252948256440249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248248927189670597675253665 186186695392252948256440249)
        ·
          refine ⟨139640021544189711192330187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186186695392252948256440249 139640021544189711192330187)
          ·
            refine ⟨209460032316284566788495281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139640021544189711192330187 209460032316284566788495281)
            ·
              refine ⟨157095024237213425091371461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209460032316284566788495281 157095024237213425091371461)
              ·
                refine ⟨29455317044477517204632149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157095024237213425091371461 29455317044477517204632149)
                ·
                  refine ⟨345179496614970904741783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29455317044477517204632149 345179496614970904741783)
                  ·
                    rfl

theorem cell23_6050112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 8].length) (baseStart_6050112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050112 prefixEnd_6050112 := by exact prefixLift 6050112
  have htrace : WordTrace (prefixWord ++ tailWord_6050112) baseStart_6050112 baseEnd_6050112 := by
    simpa [prefixWord, tailWord_6050112, baseEnd_6050112] using wordTrace_append hprefix tailTrace_6050112
  have hstable : (prefixWord ++ tailWord_6050112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050112).length < 2 ^ (prefixWord ++ tailWord_6050112).sum := by decide
  have hdescent : baseEnd_6050112 < baseStart_6050112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050129 : List Nat := [1, 2, 2, 1, 4, 2, 1, 4, 6]
def baseStart_6050129 : Nat := 118140960795 + 6050129 * 2 ^ 59
def prefixEnd_6050129 : Nat := 4983230072969 + 3 ^ 40 * 6050129 * 2
def baseEnd_6050129 : Nat := 345180466522873841795941

theorem tailTrace_6050129 : CollatzResearch.WordTrace tailWord_6050129 prefixEnd_6050129 345180466522873841795941 := by
  unfold tailWord_6050129
  simp only [CollatzResearch.WordTrace]
  refine ⟨220666333098423387614705441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147110888732282258409803627 220666333098423387614705441)
  ·
    refine ⟨165499749823817540711029081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220666333098423387614705441 165499749823817540711029081)
    ·
      refine ⟨124124812367863155533271811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165499749823817540711029081 124124812367863155533271811)
      ·
        refine ⟨186187218551794733299907717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124124812367863155533271811 186187218551794733299907717)
        ·
          refine ⟨34910103478461512493732697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186187218551794733299907717 34910103478461512493732697)
          ·
            refine ⟨26182577608846134370299523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34910103478461512493732697 26182577608846134370299523)
            ·
              refine ⟨39273866413269201555449285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26182577608846134370299523 39273866413269201555449285)
              ·
                refine ⟨7363849952487975291646741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39273866413269201555449285 7363849952487975291646741)
                ·
                  refine ⟨345180466522873841795941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7363849952487975291646741 345180466522873841795941)
                  ·
                    rfl

theorem cell23_6050129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 6].length) (baseStart_6050129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050129 prefixEnd_6050129 := by exact prefixLift 6050129
  have htrace : WordTrace (prefixWord ++ tailWord_6050129) baseStart_6050129 baseEnd_6050129 := by
    simpa [prefixWord, tailWord_6050129, baseEnd_6050129] using wordTrace_append hprefix tailTrace_6050129
  have hstable : (prefixWord ++ tailWord_6050129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050129).length < 2 ^ (prefixWord ++ tailWord_6050129).sum := by decide
  have hdescent : baseEnd_6050129 < baseStart_6050129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050140 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_6050140 : Nat := 118140960795 + 6050140 * 2 ^ 59
def prefixEnd_6050140 : Nat := 4983230072969 + 3 ^ 40 * 6050140 * 2
def baseEnd_6050140 : Nat := 3106629846993064033125919

theorem tailTrace_6050140 : CollatzResearch.WordTrace tailWord_6050140 prefixEnd_6050140 3106629846993064033125919 := by
  unfold tailWord_6050140
  simp only [CollatzResearch.WordTrace]
  refine ⟨110333367150691768246677937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147111156200922357662237249 110333367150691768246677937)
  ·
    refine ⟨82750025363018826185008453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110333367150691768246677937 82750025363018826185008453)
    ·
      refine ⟨15515629755566029909689085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82750025363018826185008453 15515629755566029909689085)
      ·
        refine ⟨5818361158337261216133407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15515629755566029909689085 5818361158337261216133407)
        ·
          refine ⟨8727541737505891824200111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5818361158337261216133407 8727541737505891824200111)
          ·
            refine ⟨13091312606258837736300167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8727541737505891824200111 13091312606258837736300167)
            ·
              refine ⟨19636968909388256604450251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13091312606258837736300167 19636968909388256604450251)
              ·
                refine ⟨29455453364082384906675377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19636968909388256604450251 29455453364082384906675377)
                ·
                  refine ⟨22091590023061788680006533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29455453364082384906675377 22091590023061788680006533)
                  ·
                    refine ⟨4142173129324085377501225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22091590023061788680006533 4142173129324085377501225)
                    ·
                      refine ⟨3106629846993064033125919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4142173129324085377501225 3106629846993064033125919)
                      ·
                        rfl

theorem cell23_6050140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_6050140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050140 prefixEnd_6050140 := by exact prefixLift 6050140
  have htrace : WordTrace (prefixWord ++ tailWord_6050140) baseStart_6050140 baseEnd_6050140 := by
    simpa [prefixWord, tailWord_6050140, baseEnd_6050140] using wordTrace_append hprefix tailTrace_6050140
  have hstable : (prefixWord ++ tailWord_6050140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050140).length < 2 ^ (prefixWord ++ tailWord_6050140).sum := by decide
  have hdescent : baseEnd_6050140 < baseStart_6050140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050146 : List Nat := [3, 3, 2, 1, 1, 2, 2, 3, 6]
def baseStart_6050146 : Nat := 118140960795 + 6050146 * 2 ^ 59
def prefixEnd_6050146 : Nat := 4983230072969 + 3 ^ 40 * 6050146 * 2
def baseEnd_6050146 : Nat := 345181436430776778850099

theorem tailTrace_6050146 : CollatzResearch.WordTrace tailWord_6050146 prefixEnd_6050146 345181436430776778850099 := by
  unfold tailWord_6050146
  simp only [CollatzResearch.WordTrace]
  refine ⟨55166738284840449879518573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147111302092907866345382861 55166738284840449879518573)
  ·
    refine ⟨20687526856815168704819465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55166738284840449879518573 20687526856815168704819465)
    ·
      refine ⟨15515645142611376528614599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20687526856815168704819465 15515645142611376528614599)
      ·
        refine ⟨23273467713917064792921899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15515645142611376528614599 23273467713917064792921899)
        ·
          refine ⟨34910201570875597189382849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23273467713917064792921899 34910201570875597189382849)
          ·
            refine ⟨26182651178156697892037137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34910201570875597189382849 26182651178156697892037137)
            ·
              refine ⟨19636988383617523419027853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26182651178156697892037137 19636988383617523419027853)
              ·
                refine ⟨7363870643856571282135445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19636988383617523419027853 7363870643856571282135445)
                ·
                  refine ⟨345181436430776778850099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7363870643856571282135445 345181436430776778850099)
                  ·
                    rfl

theorem cell23_6050146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_6050146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050146 prefixEnd_6050146 := by exact prefixLift 6050146
  have htrace : WordTrace (prefixWord ++ tailWord_6050146) baseStart_6050146 baseEnd_6050146 := by
    simpa [prefixWord, tailWord_6050146, baseEnd_6050146] using wordTrace_append hprefix tailTrace_6050146
  have hstable : (prefixWord ++ tailWord_6050146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050146).length < 2 ^ (prefixWord ++ tailWord_6050146).sum := by decide
  have hdescent : baseEnd_6050146 < baseStart_6050146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
