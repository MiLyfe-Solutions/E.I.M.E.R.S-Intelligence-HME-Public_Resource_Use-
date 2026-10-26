import V185TrunkScan23Chunk0555

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3286382 : List Nat := [4, 1, 2, 4, 1, 1, 2, 2, 2, 2, 2]
def baseStart_3286382 : Nat := 118140960795 + 3286382 * 2 ^ 59
def prefixEnd_3286382 : Nat := 4983230072969 + 3 ^ 40 * 3286382 * 2
def baseEnd_3286382 : Nat := 1687493580284266249011211

theorem tailTrace_3286382 : CollatzResearch.WordTrace tailWord_3286382 prefixEnd_3286382 1687493580284266249011211 := by
  unfold tailWord_3286382
  simp only [CollatzResearch.WordTrace]
  refine ⟨14983024847500844775721675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79909465853337838803848933 14983024847500844775721675)
  ·
    refine ⟨22474537271251267163582513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14983024847500844775721675 22474537271251267163582513)
    ·
      refine ⟨16855902953438450372686885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22474537271251267163582513 16855902953438450372686885)
      ·
        refine ⟨3160481803769709444878791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16855902953438450372686885 3160481803769709444878791)
        ·
          refine ⟨4740722705654564167318187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3160481803769709444878791 4740722705654564167318187)
          ·
            refine ⟨7111084058481846250977281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4740722705654564167318187 7111084058481846250977281)
            ·
              refine ⟨5333313043861384688232961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7111084058481846250977281 5333313043861384688232961)
              ·
                refine ⟨3999984782896038516174721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5333313043861384688232961 3999984782896038516174721)
                ·
                  refine ⟨2999988587172028887131041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3999984782896038516174721 2999988587172028887131041)
                  ·
                    refine ⟨2249991440379021665348281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2999988587172028887131041 2249991440379021665348281)
                    ·
                      refine ⟨1687493580284266249011211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2249991440379021665348281 1687493580284266249011211)
                      ·
                        rfl

theorem cell23_3286382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_3286382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286382 prefixEnd_3286382 := by exact prefixLift 3286382
  have htrace : WordTrace (prefixWord ++ tailWord_3286382) baseStart_3286382 baseEnd_3286382 := by
    simpa [prefixWord, tailWord_3286382, baseEnd_3286382] using wordTrace_append hprefix tailTrace_3286382
  have hstable : (prefixWord ++ tailWord_3286382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286382).length < 2 ^ (prefixWord ++ tailWord_3286382).sum := by decide
  have hdescent : baseEnd_3286382 < baseStart_3286382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286417 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 4]
def baseStart_3286417 : Nat := 118140960795 + 3286417 * 2 ^ 59
def prefixEnd_3286417 : Nat := 4983230072969 + 3 ^ 40 * 3286417 * 2
def baseEnd_3286417 : Nat := 1687511552107173612073549

theorem tailTrace_3286417 : CollatzResearch.WordTrace tailWord_3286417 prefixEnd_3286417 1687511552107173612073549 := by
  unfold tailWord_3286417
  simp only [CollatzResearch.WordTrace]
  refine ⟨119865475334879959183297505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79910316889919972788865003 119865475334879959183297505)
  ·
    refine ⟨89899106501159969387473129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119865475334879959183297505 89899106501159969387473129)
    ·
      refine ⟨67424329875869977040604847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89899106501159969387473129 67424329875869977040604847)
      ·
        refine ⟨101136494813804965560907271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67424329875869977040604847 101136494813804965560907271)
        ·
          refine ⟨151704742220707448341360907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101136494813804965560907271 151704742220707448341360907)
          ·
            refine ⟨227557113331061172512041361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151704742220707448341360907 227557113331061172512041361)
            ·
              refine ⟨170667834998295879384031021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227557113331061172512041361 170667834998295879384031021)
              ·
                refine ⟨64000438124360954769011633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170667834998295879384031021 64000438124360954769011633)
                ·
                  refine ⟨48000328593270716076758725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64000438124360954769011633 48000328593270716076758725)
                  ·
                    refine ⟨9000061611238259264392261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48000328593270716076758725 9000061611238259264392261)
                    ·
                      refine ⟨1687511552107173612073549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9000061611238259264392261 1687511552107173612073549)
                      ·
                        rfl

theorem cell23_3286417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_3286417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286417 prefixEnd_3286417 := by exact prefixLift 3286417
  have htrace : WordTrace (prefixWord ++ tailWord_3286417) baseStart_3286417 baseEnd_3286417 := by
    simpa [prefixWord, tailWord_3286417, baseEnd_3286417] using wordTrace_append hprefix tailTrace_3286417
  have hstable : (prefixWord ++ tailWord_3286417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286417).length < 2 ^ (prefixWord ++ tailWord_3286417).sum := by decide
  have hdescent : baseEnd_3286417 < baseStart_3286417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286434 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_3286434 : Nat := 118140960795 + 3286434 * 2 ^ 59
def prefixEnd_3286434 : Nat := 4983230072969 + 3 ^ 40 * 3286434 * 2
def baseEnd_3286434 : Nat := 1687520281278300045560971

theorem tailTrace_3286434 : CollatzResearch.WordTrace tailWord_3286434 prefixEnd_3286434 1687520281278300045560971 := by
  unfold tailWord_3286434
  simp only [CollatzResearch.WordTrace]
  refine ⟨29966523843954592771666589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79910730250545580724444237 29966523843954592771666589)
  ·
    refine ⟨11237446441482972289374971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29966523843954592771666589 11237446441482972289374971)
    ·
      refine ⟨16856169662224458434062457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11237446441482972289374971 16856169662224458434062457)
      ·
        refine ⟨12642127246668343825546843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16856169662224458434062457 12642127246668343825546843)
        ·
          refine ⟨18963190870002515738320265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12642127246668343825546843 18963190870002515738320265)
          ·
            refine ⟨14222393152501886803740199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18963190870002515738320265 14222393152501886803740199)
            ·
              refine ⟨21333589728752830205610299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14222393152501886803740199 21333589728752830205610299)
              ·
                refine ⟨32000384593129245308415449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21333589728752830205610299 32000384593129245308415449)
                ·
                  refine ⟨24000288444846933981311587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32000384593129245308415449 24000288444846933981311587)
                  ·
                    refine ⟨36000432667270400971967381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24000288444846933981311587 36000432667270400971967381)
                    ·
                      refine ⟨1687520281278300045560971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36000432667270400971967381 1687520281278300045560971)
                      ·
                        rfl

theorem cell23_3286434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_3286434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286434 prefixEnd_3286434 := by exact prefixLift 3286434
  have htrace : WordTrace (prefixWord ++ tailWord_3286434) baseStart_3286434 baseEnd_3286434 := by
    simpa [prefixWord, tailWord_3286434, baseEnd_3286434] using wordTrace_append hprefix tailTrace_3286434
  have hstable : (prefixWord ++ tailWord_3286434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286434).length < 2 ^ (prefixWord ++ tailWord_3286434).sum := by decide
  have hdescent : baseEnd_3286434 < baseStart_3286434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286444 : List Nat := [2, 2, 1, 1, 1, 1, 7, 2, 6]
def baseStart_3286444 : Nat := 118140960795 + 3286444 * 2 ^ 59
def prefixEnd_3286444 : Nat := 4983230072969 + 3 ^ 40 * 3286444 * 2
def baseEnd_3286444 : Nat := 187502824009427222937325

theorem tailTrace_3286444 : CollatzResearch.WordTrace tailWord_3286444 prefixEnd_3286444 187502824009427222937325 := by
  unfold tailWord_3286444
  simp only [CollatzResearch.WordTrace]
  refine ⟨59933230052891071397265193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79910973403854761863020257 59933230052891071397265193)
  ·
    refine ⟨44949922539668303547948895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59933230052891071397265193 44949922539668303547948895)
    ·
      refine ⟨67424883809502455321923343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44949922539668303547948895 67424883809502455321923343)
      ·
        refine ⟨101137325714253682982885015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67424883809502455321923343 101137325714253682982885015)
        ·
          refine ⟨151705988571380524474327523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101137325714253682982885015 151705988571380524474327523)
          ·
            refine ⟨227558982857070786711491285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151705988571380524474327523 227558982857070786711491285)
            ·
              refine ⟨5333413660712596563550577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 227558982857070786711491285 5333413660712596563550577)
              ·
                refine ⟨4000060245534447422662933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5333413660712596563550577 4000060245534447422662933)
                ·
                  refine ⟨187502824009427222937325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4000060245534447422662933 187502824009427222937325)
                  ·
                    rfl

theorem cell23_3286444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 6].length) (baseStart_3286444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286444 prefixEnd_3286444 := by exact prefixLift 3286444
  have htrace : WordTrace (prefixWord ++ tailWord_3286444) baseStart_3286444 baseEnd_3286444 := by
    simpa [prefixWord, tailWord_3286444, baseEnd_3286444] using wordTrace_append hprefix tailTrace_3286444
  have hstable : (prefixWord ++ tailWord_3286444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286444).length < 2 ^ (prefixWord ++ tailWord_3286444).sum := by decide
  have hdescent : baseEnd_3286444 < baseStart_3286444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286461 : List Nat := [1, 4, 1, 2, 2, 1, 5, 1, 6]
def baseStart_3286461 : Nat := 118140960795 + 3286461 * 2 ^ 59
def prefixEnd_3286461 : Nat := 4983230072969 + 3 ^ 40 * 3286461 * 2
def baseEnd_3286461 : Nat := 187503793917330159991483

theorem tailTrace_3286461 : CollatzResearch.WordTrace tailWord_3286461 prefixEnd_3286461 187503793917330159991483 := by
  unfold tailWord_3286461
  simp only [CollatzResearch.WordTrace]
  refine ⟨119867080146720554697899237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79911386764480369798599491 119867080146720554697899237)
  ·
    refine ⟨22475077527510104005856107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119867080146720554697899237 22475077527510104005856107)
    ·
      refine ⟨33712616291265156008784161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22475077527510104005856107 33712616291265156008784161)
      ·
        refine ⟨25284462218448867006588121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33712616291265156008784161 25284462218448867006588121)
        ·
          refine ⟨18963346663836650254941091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25284462218448867006588121 18963346663836650254941091)
          ·
            refine ⟨28445019995754975382411637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18963346663836650254941091 28445019995754975382411637)
            ·
              refine ⟨2666720624602028942101091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28445019995754975382411637 2666720624602028942101091)
              ·
                refine ⟨4000080936903043413151637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2666720624602028942101091 4000080936903043413151637)
                ·
                  refine ⟨187503793917330159991483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4000080936903043413151637 187503793917330159991483)
                  ·
                    rfl

theorem cell23_3286461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_3286461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286461 prefixEnd_3286461 := by exact prefixLift 3286461
  have htrace : WordTrace (prefixWord ++ tailWord_3286461) baseStart_3286461 baseEnd_3286461 := by
    simpa [prefixWord, tailWord_3286461, baseEnd_3286461] using wordTrace_append hprefix tailTrace_3286461
  have hstable : (prefixWord ++ tailWord_3286461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286461).length < 2 ^ (prefixWord ++ tailWord_3286461).sum := by decide
  have hdescent : baseEnd_3286461 < baseStart_3286461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286467 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 7]
def baseStart_3286467 : Nat := 118140960795 + 3286467 * 2 ^ 59
def prefixEnd_3286467 : Nat := 4983230072969 + 3 ^ 40 * 3286467 * 2
def baseEnd_3286467 : Nat := 1687537226139898416448319

theorem tailTrace_3286467 : CollatzResearch.WordTrace tailWord_3286467 prefixEnd_3286467 1687537226139898416448319 := by
  unfold tailWord_3286467
  simp only [CollatzResearch.WordTrace]
  refine ⟨119867298984698817722617655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79911532656465878481745103 119867298984698817722617655)
  ·
    refine ⟨179800948477048226583926483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119867298984698817722617655 179800948477048226583926483)
    ·
      refine ⟨269701422715572339875889725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179800948477048226583926483 269701422715572339875889725)
      ·
        refine ⟨101138033518339627453458647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269701422715572339875889725 101138033518339627453458647)
        ·
          refine ⟨151707050277509441180187971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101138033518339627453458647 151707050277509441180187971)
          ·
            refine ⟨227560575416264161770281957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151707050277509441180187971 227560575416264161770281957)
            ·
              refine ⟨42667607890549530331927867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 227560575416264161770281957 42667607890549530331927867)
              ·
                refine ⟨64001411835824295497891801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42667607890549530331927867 64001411835824295497891801)
                ·
                  refine ⟨48001058876868221623418851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64001411835824295497891801 48001058876868221623418851)
                  ·
                    refine ⟨72001588315302332435128277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48001058876868221623418851 72001588315302332435128277)
                    ·
                      refine ⟨1687537226139898416448319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72001588315302332435128277 1687537226139898416448319)
                      ·
                        rfl

theorem cell23_3286467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_3286467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286467 prefixEnd_3286467 := by exact prefixLift 3286467
  have htrace : WordTrace (prefixWord ++ tailWord_3286467) baseStart_3286467 baseEnd_3286467 := by
    simpa [prefixWord, tailWord_3286467, baseEnd_3286467] using wordTrace_append hprefix tailTrace_3286467
  have hstable : (prefixWord ++ tailWord_3286467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286467).length < 2 ^ (prefixWord ++ tailWord_3286467).sum := by decide
  have hdescent : baseEnd_3286467 < baseStart_3286467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286471 : List Nat := [1, 1, 4, 1, 1, 3, 1, 4, 3, 1, 3]
def baseStart_3286471 : Nat := 118140960795 + 3286471 * 2 ^ 59
def prefixEnd_3286471 : Nat := 4983230072969 + 3 ^ 40 * 3286471 * 2
def baseEnd_3286471 : Nat := 1687539280062516400798301

theorem tailTrace_3286471 : CollatzResearch.WordTrace tailWord_3286471 prefixEnd_3286471 1687539280062516400798301 := by
  unfold tailWord_3286471
  simp only [CollatzResearch.WordTrace]
  refine ⟨119867444876684326405763267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79911629917789550937175511 119867444876684326405763267)
  ·
    refine ⟨179801167315026489608644901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119867444876684326405763267 179801167315026489608644901)
    ·
      refine ⟨33712718871567466801620919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179801167315026489608644901 33712718871567466801620919)
      ·
        refine ⟨50569078307351200202431379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33712718871567466801620919 50569078307351200202431379)
        ·
          refine ⟨75853617461026800303647069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50569078307351200202431379 75853617461026800303647069)
          ·
            refine ⟨28445106547885050113867651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75853617461026800303647069 28445106547885050113867651)
            ·
              refine ⟨42667659821827575170801477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28445106547885050113867651 42667659821827575170801477)
              ·
                refine ⟨8000186216592670344525277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42667659821827575170801477 8000186216592670344525277)
                ·
                  refine ⟨3000069831222251379196979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8000186216592670344525277 3000069831222251379196979)
                  ·
                    refine ⟨4500104746833377068795469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3000069831222251379196979 4500104746833377068795469)
                    ·
                      refine ⟨1687539280062516400798301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4500104746833377068795469 1687539280062516400798301)
                      ·
                        rfl

theorem cell23_3286471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_3286471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286471 prefixEnd_3286471 := by exact prefixLift 3286471
  have htrace : WordTrace (prefixWord ++ tailWord_3286471) baseStart_3286471 baseEnd_3286471 := by
    simpa [prefixWord, tailWord_3286471, baseEnd_3286471] using wordTrace_append hprefix tailTrace_3286471
  have hstable : (prefixWord ++ tailWord_3286471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286471).length < 2 ^ (prefixWord ++ tailWord_3286471).sum := by decide
  have hdescent : baseEnd_3286471 < baseStart_3286471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286524 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_3286524 : Nat := 118140960795 + 3286524 * 2 ^ 59
def prefixEnd_3286524 : Nat := 4983230072969 + 3 ^ 40 * 3286524 * 2
def baseEnd_3286524 : Nat := 1687566494537204693435557

theorem tailTrace_3286524 : CollatzResearch.WordTrace tailWord_3286524 prefixEnd_3286524 1687566494537204693435557 := by
  unfold tailWord_3286524
  simp only [CollatzResearch.WordTrace]
  refine ⟨59934688972746158228721313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79912918630328210971628417 59934688972746158228721313)
  ·
    refine ⟨44951016729559618671540985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59934688972746158228721313 44951016729559618671540985)
    ·
      refine ⟨33713262547169714003655739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44951016729559618671540985 33713262547169714003655739)
      ·
        refine ⟨50569893820754571005483609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33713262547169714003655739 50569893820754571005483609)
        ·
          refine ⟨37927420365565928254112707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50569893820754571005483609 37927420365565928254112707)
          ·
            refine ⟨56891130548348892381169061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37927420365565928254112707 56891130548348892381169061)
            ·
              refine ⟨10667086977815417321469199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56891130548348892381169061 10667086977815417321469199)
              ·
                refine ⟨16000630466723125982203799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10667086977815417321469199 16000630466723125982203799)
                ·
                  refine ⟨24000945700084688973305699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16000630466723125982203799 24000945700084688973305699)
                  ·
                    refine ⟨36001418550127033459958549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24000945700084688973305699 36001418550127033459958549)
                    ·
                      refine ⟨1687566494537204693435557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36001418550127033459958549 1687566494537204693435557)
                      ·
                        rfl

theorem cell23_3286524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_3286524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286524 prefixEnd_3286524 := by exact prefixLift 3286524
  have htrace : WordTrace (prefixWord ++ tailWord_3286524) baseStart_3286524 baseEnd_3286524 := by
    simpa [prefixWord, tailWord_3286524, baseEnd_3286524] using wordTrace_append hprefix tailTrace_3286524
  have hstable : (prefixWord ++ tailWord_3286524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286524).length < 2 ^ (prefixWord ++ tailWord_3286524).sum := by decide
  have hdescent : baseEnd_3286524 < baseStart_3286524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286531 : List Nat := [1, 1, 1, 3, 2, 1, 2, 6, 1, 2, 3]
def baseStart_3286531 : Nat := 118140960795 + 3286531 * 2 ^ 59
def prefixEnd_3286531 : Nat := 4983230072969 + 3 ^ 40 * 3286531 * 2
def baseEnd_3286531 : Nat := 1687570088901786166048025

theorem tailTrace_3286531 : CollatzResearch.WordTrace tailWord_3286531 prefixEnd_3286531 1687570088901786166048025 := by
  unfold tailWord_3286531
  simp only [CollatzResearch.WordTrace]
  refine ⟨119869633256466956652947447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79913088837644637768631631 119869633256466956652947447)
  ·
    refine ⟨179804449884700434979421171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119869633256466956652947447 179804449884700434979421171)
    ·
      refine ⟨269706674827050652469131757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179804449884700434979421171 269706674827050652469131757)
      ·
        refine ⟨101140003060143994675924409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269706674827050652469131757 101140003060143994675924409)
        ·
          refine ⟨75855002295107996006943307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101140003060143994675924409 75855002295107996006943307)
          ·
            refine ⟨113782503442661994010414961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75855002295107996006943307 113782503442661994010414961)
            ·
              refine ⟨85336877581996495507811221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113782503442661994010414961 85336877581996495507811221)
              ·
                refine ⟨4000166136656085726928651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85336877581996495507811221 4000166136656085726928651)
                ·
                  refine ⟨6000249204984128590392977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4000166136656085726928651 6000249204984128590392977)
                  ·
                    refine ⟨4500186903738096442794733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6000249204984128590392977 4500186903738096442794733)
                    ·
                      refine ⟨1687570088901786166048025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4500186903738096442794733 1687570088901786166048025)
                      ·
                        rfl

theorem cell23_3286531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 2, 3].length) (baseStart_3286531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286531 prefixEnd_3286531 := by exact prefixLift 3286531
  have htrace : WordTrace (prefixWord ++ tailWord_3286531) baseStart_3286531 baseEnd_3286531 := by
    simpa [prefixWord, tailWord_3286531, baseEnd_3286531] using wordTrace_append hprefix tailTrace_3286531
  have hstable : (prefixWord ++ tailWord_3286531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286531).length < 2 ^ (prefixWord ++ tailWord_3286531).sum := by decide
  have hdescent : baseEnd_3286531 < baseStart_3286531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286545 : List Nat := [1, 2, 2, 1, 1, 2, 4, 5, 1, 2, 2]
def baseStart_3286545 : Nat := 118140960795 + 3286545 * 2 ^ 59
def prefixEnd_3286545 : Nat := 4983230072969 + 3 ^ 40 * 3286545 * 2
def baseEnd_3286545 : Nat := 1687577277630949111272961

theorem tailTrace_3286545 : CollatzResearch.WordTrace tailWord_3286545 prefixEnd_3286545 1687577277630949111272961 := by
  unfold tailWord_3286545
  simp only [CollatzResearch.WordTrace]
  refine ⟨119870143878416237043957089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79913429252277491362638059 119870143878416237043957089)
  ·
    refine ⟨89902607908812177782967817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119870143878416237043957089 89902607908812177782967817)
    ·
      refine ⟨67426955931609133337225863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89902607908812177782967817 67426955931609133337225863)
      ·
        refine ⟨101140433897413700005838795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67426955931609133337225863 101140433897413700005838795)
        ·
          refine ⟨151710650846120550008758193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101140433897413700005838795 151710650846120550008758193)
          ·
            refine ⟨113782988134590412506568645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151710650846120550008758193 113782988134590412506568645)
            ·
              refine ⟨21334310275235702344981621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113782988134590412506568645 21334310275235702344981621)
              ·
                refine ⟨2000091588303347094842027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21334310275235702344981621 2000091588303347094842027)
                ·
                  refine ⟨3000137382455020642263041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2000091588303347094842027 3000137382455020642263041)
                  ·
                    refine ⟨2250103036841265481697281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3000137382455020642263041 2250103036841265481697281)
                    ·
                      refine ⟨1687577277630949111272961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2250103036841265481697281 1687577277630949111272961)
                      ·
                        rfl

theorem cell23_3286545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 1, 2, 2].length) (baseStart_3286545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286545 prefixEnd_3286545 := by exact prefixLift 3286545
  have htrace : WordTrace (prefixWord ++ tailWord_3286545) baseStart_3286545 baseEnd_3286545 := by
    simpa [prefixWord, tailWord_3286545, baseEnd_3286545] using wordTrace_append hprefix tailTrace_3286545
  have hstable : (prefixWord ++ tailWord_3286545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286545).length < 2 ^ (prefixWord ++ tailWord_3286545).sum := by decide
  have hdescent : baseEnd_3286545 < baseStart_3286545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286568 : List Nat := [2, 1, 5, 2, 2, 2, 1, 8]
def baseStart_3286568 : Nat := 118140960795 + 3286568 * 2 ^ 59
def prefixEnd_3286568 : Nat := 4983230072969 + 3 ^ 40 * 3286568 * 2
def baseEnd_3286568 : Nat := 62503299543926019306865

theorem tailTrace_3286568 : CollatzResearch.WordTrace tailWord_3286568 prefixEnd_3286568 62503299543926019306865 := by
  unfold tailWord_3286568
  simp only [CollatzResearch.WordTrace]
  refine ⟨59935491378666455986022179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79913988504888607981362905 59935491378666455986022179)
  ·
    refine ⟨89903237067999683979033269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59935491378666455986022179 89903237067999683979033269)
    ·
      refine ⟨8428428475124970373034369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89903237067999683979033269 8428428475124970373034369)
      ·
        refine ⟨6321321356343727779775777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8428428475124970373034369 6321321356343727779775777)
        ·
          refine ⟨4740991017257795834831833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6321321356343727779775777 4740991017257795834831833)
          ·
            refine ⟨3555743262943346876123875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4740991017257795834831833 3555743262943346876123875)
            ·
              refine ⟨5333614894415020314185813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3555743262943346876123875 5333614894415020314185813)
              ·
                refine ⟨62503299543926019306865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5333614894415020314185813 62503299543926019306865)
                ·
                  rfl

theorem cell23_3286568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 8].length) (baseStart_3286568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286568 prefixEnd_3286568 := by exact prefixLift 3286568
  have htrace : WordTrace (prefixWord ++ tailWord_3286568) baseStart_3286568 baseEnd_3286568 := by
    simpa [prefixWord, tailWord_3286568, baseEnd_3286568] using wordTrace_append hprefix tailTrace_3286568
  have hstable : (prefixWord ++ tailWord_3286568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286568).length < 2 ^ (prefixWord ++ tailWord_3286568).sum := by decide
  have hdescent : baseEnd_3286568 < baseStart_3286568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286631 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_3286631 : Nat := 118140960795 + 3286631 * 2 ^ 59
def prefixEnd_3286631 : Nat := 4983230072969 + 3 ^ 40 * 3286631 * 2
def baseEnd_3286631 : Nat := 1687621436967235774797565

theorem tailTrace_3286631 : CollatzResearch.WordTrace tailWord_3286631 prefixEnd_3286631 1687621436967235774797565 := by
  unfold tailWord_3286631
  simp only [CollatzResearch.WordTrace]
  refine ⟨119873280556104673731587747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79915520370736449154391831 119873280556104673731587747)
  ·
    refine ⟨179809920834157010597381621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119873280556104673731587747 179809920834157010597381621)
    ·
      refine ⟨16857180078202219743504527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179809920834157010597381621 16857180078202219743504527)
      ·
        refine ⟨25285770117303329615256791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16857180078202219743504527 25285770117303329615256791)
        ·
          refine ⟨37928655175954994422885187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25285770117303329615256791 37928655175954994422885187)
          ·
            refine ⟨56892982763932491634327781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37928655175954994422885187 56892982763932491634327781)
            ·
              refine ⟨10667434268237342181436459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56892982763932491634327781 10667434268237342181436459)
              ·
                refine ⟨16001151402356013272154689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10667434268237342181436459 16001151402356013272154689)
                ·
                  refine ⟨12000863551767009954116017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16001151402356013272154689 12000863551767009954116017)
                  ·
                    refine ⟨9000647663825257465587013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12000863551767009954116017 9000647663825257465587013)
                    ·
                      refine ⟨1687621436967235774797565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9000647663825257465587013 1687621436967235774797565)
                      ·
                        rfl

theorem cell23_3286631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_3286631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286631 prefixEnd_3286631 := by exact prefixLift 3286631
  have htrace : WordTrace (prefixWord ++ tailWord_3286631) baseStart_3286631 baseEnd_3286631 := by
    simpa [prefixWord, tailWord_3286631, baseEnd_3286631] using wordTrace_append hprefix tailTrace_3286631
  have hstable : (prefixWord ++ tailWord_3286631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286631).length < 2 ^ (prefixWord ++ tailWord_3286631).sum := by decide
  have hdescent : baseEnd_3286631 < baseStart_3286631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286686 : List Nat := [4, 3, 1, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_3286686 : Nat := 118140960795 + 3286686 * 2 ^ 59
def prefixEnd_3286686 : Nat := 4983230072969 + 3 ^ 40 * 3286686 * 2
def baseEnd_3286686 : Nat := 1687649678403233059609813

theorem tailTrace_3286686 : CollatzResearch.WordTrace tailWord_3286686 prefixEnd_3286686 1687649678403233059609813 := by
  unfold tailWord_3286686
  simp only [CollatzResearch.WordTrace]
  refine ⟨14984410821363177265604989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79916857713936945416559941 14984410821363177265604989)
  ·
    refine ⟨5619154058011191474601871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14984410821363177265604989 5619154058011191474601871)
    ·
      refine ⟨8428731087016787211902807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5619154058011191474601871 8428731087016787211902807)
      ·
        refine ⟨12643096630525180817854211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8428731087016787211902807 12643096630525180817854211)
        ·
          refine ⟨18964644945787771226781317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12643096630525180817854211 18964644945787771226781317)
          ·
            refine ⟨3555870927335207105021497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18964644945787771226781317 3555870927335207105021497)
            ·
              refine ⟨2666903195501405328766123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3555870927335207105021497 2666903195501405328766123)
              ·
                refine ⟨4000354793252107993149185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2666903195501405328766123 4000354793252107993149185)
                ·
                  refine ⟨3000266094939080994861889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4000354793252107993149185 3000266094939080994861889)
                  ·
                    refine ⟨2250199571204310746146417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3000266094939080994861889 2250199571204310746146417)
                    ·
                      refine ⟨1687649678403233059609813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2250199571204310746146417 1687649678403233059609813)
                      ·
                        rfl

theorem cell23_3286686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_3286686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286686 prefixEnd_3286686 := by exact prefixLift 3286686
  have htrace : WordTrace (prefixWord ++ tailWord_3286686) baseStart_3286686 baseEnd_3286686 := by
    simpa [prefixWord, tailWord_3286686, baseEnd_3286686] using wordTrace_append hprefix tailTrace_3286686
  have hstable : (prefixWord ++ tailWord_3286686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286686).length < 2 ^ (prefixWord ++ tailWord_3286686).sum := by decide
  have hdescent : baseEnd_3286686 < baseStart_3286686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286691 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 4]
def baseStart_3286691 : Nat := 118140960795 + 3286691 * 2 ^ 59
def prefixEnd_3286691 : Nat := 4983230072969 + 3 ^ 40 * 3286691 * 2
def baseEnd_3286691 : Nat := 1687652245806505540047289

theorem tailTrace_3286691 : CollatzResearch.WordTrace tailWord_3286691 prefixEnd_3286691 1687652245806505540047289 := by
  unfold tailWord_3286691
  simp only [CollatzResearch.WordTrace]
  refine ⟨119875468935887303978771927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79916979290591535985847951 119875468935887303978771927)
  ·
    refine ⟨179813203403830955968157891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119875468935887303978771927 179813203403830955968157891)
    ·
      refine ⟨269719805105746433952236837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179813203403830955968157891 269719805105746433952236837)
      ·
        refine ⟨50572463457327456366044407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269719805105746433952236837 50572463457327456366044407)
        ·
          refine ⟨75858695185991184549066611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50572463457327456366044407 75858695185991184549066611)
          ·
            refine ⟨113788042778986776823599917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75858695185991184549066611 113788042778986776823599917)
            ·
              refine ⟨42670516042120041308849969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113788042778986776823599917 42670516042120041308849969)
              ·
                refine ⟨32002887031590030981637477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42670516042120041308849969 32002887031590030981637477)
                ·
                  refine ⟨6000541318423130809057027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32002887031590030981637477 6000541318423130809057027)
                  ·
                    refine ⟨9000811977634696213585541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6000541318423130809057027 9000811977634696213585541)
                    ·
                      refine ⟨1687652245806505540047289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9000811977634696213585541 1687652245806505540047289)
                      ·
                        rfl

theorem cell23_3286691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_3286691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286691 prefixEnd_3286691 := by exact prefixLift 3286691
  have htrace : WordTrace (prefixWord ++ tailWord_3286691) baseStart_3286691 baseEnd_3286691 := by
    simpa [prefixWord, tailWord_3286691, baseEnd_3286691] using wordTrace_append hprefix tailTrace_3286691
  have hstable : (prefixWord ++ tailWord_3286691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286691).length < 2 ^ (prefixWord ++ tailWord_3286691).sum := by decide
  have hdescent : baseEnd_3286691 < baseStart_3286691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286726 : List Nat := [6, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_3286726 : Nat := 118140960795 + 3286726 * 2 ^ 59
def prefixEnd_3286726 : Nat := 4983230072969 + 3 ^ 40 * 3286726 * 2
def baseEnd_3286726 : Nat := 187518913069934767012181

theorem tailTrace_3286726 : CollatzResearch.WordTrace tailWord_3286726 prefixEnd_3286726 187518913069934767012181 := by
  unfold tailWord_3286726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3746148296586265779884251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79917830327173669970864021 3746148296586265779884251)
  ·
    refine ⟨5619222444879398669826377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3746148296586265779884251 5619222444879398669826377)
    ·
      refine ⟨4214416833659549002369783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5619222444879398669826377 4214416833659549002369783)
      ·
        refine ⟨6321625250489323503554675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4214416833659549002369783 6321625250489323503554675)
        ·
          refine ⟨9482437875733985255332013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6321625250489323503554675 9482437875733985255332013)
          ·
            refine ⟨3555914203400244470749505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9482437875733985255332013 3555914203400244470749505)
            ·
              refine ⟨2666935652550183353062129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3555914203400244470749505 2666935652550183353062129)
              ·
                refine ⟨2000201739412637514796597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2666935652550183353062129 2000201739412637514796597)
                ·
                  refine ⟨187518913069934767012181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2000201739412637514796597 187518913069934767012181)
                  ·
                    rfl

theorem cell23_3286726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_3286726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286726 prefixEnd_3286726 := by exact prefixLift 3286726
  have htrace : WordTrace (prefixWord ++ tailWord_3286726) baseStart_3286726 baseEnd_3286726 := by
    simpa [prefixWord, tailWord_3286726, baseEnd_3286726] using wordTrace_append hprefix tailTrace_3286726
  have hstable : (prefixWord ++ tailWord_3286726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286726).length < 2 ^ (prefixWord ++ tailWord_3286726).sum := by decide
  have hdescent : baseEnd_3286726 < baseStart_3286726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286728 : List Nat := [2, 1, 3, 1, 2, 2, 1, 4, 2, 2, 3]
def baseStart_3286728 : Nat := 118140960795 + 3286728 * 2 ^ 59
def prefixEnd_3286728 : Nat := 4983230072969 + 3 ^ 40 * 3286728 * 2
def baseEnd_3286728 : Nat := 1687671244590721895284619

theorem tailTrace_3286728 : CollatzResearch.WordTrace tailWord_3286728 prefixEnd_3286728 1687671244590721895284619 := by
  unfold tailWord_3286728
  simp only [CollatzResearch.WordTrace]
  refine ⟨59938409218376629648934419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79917878957835506198579225 59938409218376629648934419)
  ·
    refine ⟨89907613827564944473401629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59938409218376629648934419 89907613827564944473401629)
    ·
      refine ⟨33715355185336854177525611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89907613827564944473401629 33715355185336854177525611)
      ·
        refine ⟨50573032778005281266288417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33715355185336854177525611 50573032778005281266288417)
        ·
          refine ⟨37929774583503960949716313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50573032778005281266288417 37929774583503960949716313)
          ·
            refine ⟨28447330937627970712287235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37929774583503960949716313 28447330937627970712287235)
            ·
              refine ⟨42670996406441956068430853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28447330937627970712287235 42670996406441956068430853)
              ·
                refine ⟨8000811826207866762830785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42670996406441956068430853 8000811826207866762830785)
                ·
                  refine ⟨6000608869655900072123089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8000811826207866762830785 6000608869655900072123089)
                  ·
                    refine ⟨4500456652241925054092317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6000608869655900072123089 4500456652241925054092317)
                    ·
                      refine ⟨1687671244590721895284619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4500456652241925054092317 1687671244590721895284619)
                      ·
                        rfl

theorem cell23_3286728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_3286728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286728 prefixEnd_3286728 := by exact prefixLift 3286728
  have htrace : WordTrace (prefixWord ++ tailWord_3286728) baseStart_3286728 baseEnd_3286728 := by
    simpa [prefixWord, tailWord_3286728, baseEnd_3286728] using wordTrace_append hprefix tailTrace_3286728
  have hstable : (prefixWord ++ tailWord_3286728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286728).length < 2 ^ (prefixWord ++ tailWord_3286728).sum := by decide
  have hdescent : baseEnd_3286728 < baseStart_3286728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286759 : List Nat := [1, 1, 5, 4, 2, 1, 1, 1, 2, 1, 4]
def baseStart_3286759 : Nat := 118140960795 + 3286759 * 2 ^ 59
def prefixEnd_3286759 : Nat := 4983230072969 + 3 ^ 40 * 3286759 * 2
def baseEnd_3286759 : Nat := 1687687162491011273996977

theorem tailTrace_3286759 : CollatzResearch.WordTrace tailWord_3286759 prefixEnd_3286759 1687687162491011273996977 := by
  unfold tailWord_3286759
  simp only [CollatzResearch.WordTrace]
  refine ⟨119877949099640951592247331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79918632733093967728164887 119877949099640951592247331)
  ·
    refine ⟨179816923649461427388370997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119877949099640951592247331 179816923649461427388370997)
    ·
      refine ⟨16857836592137008817659781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179816923649461427388370997 16857836592137008817659781)
      ·
        refine ⟨3160844361025689153311209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16857836592137008817659781 3160844361025689153311209)
        ·
          refine ⟨2370633270769266864983407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3160844361025689153311209 2370633270769266864983407)
          ·
            refine ⟨3555949906153900297475111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370633270769266864983407 3555949906153900297475111)
            ·
              refine ⟨5333924859230850446212667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3555949906153900297475111 5333924859230850446212667)
              ·
                refine ⟨8000887288846275669319001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5333924859230850446212667 8000887288846275669319001)
                ·
                  refine ⟨6000665466634706751989251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8000887288846275669319001 6000665466634706751989251)
                  ·
                    refine ⟨9000998199952060127983877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6000665466634706751989251 9000998199952060127983877)
                    ·
                      refine ⟨1687687162491011273996977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9000998199952060127983877 1687687162491011273996977)
                      ·
                        rfl

theorem cell23_3286759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_3286759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286759 prefixEnd_3286759 := by exact prefixLift 3286759
  have htrace : WordTrace (prefixWord ++ tailWord_3286759) baseStart_3286759 baseEnd_3286759 := by
    simpa [prefixWord, tailWord_3286759, baseEnd_3286759] using wordTrace_append hprefix tailTrace_3286759
  have hstable : (prefixWord ++ tailWord_3286759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286759).length < 2 ^ (prefixWord ++ tailWord_3286759).sum := by decide
  have hdescent : baseEnd_3286759 < baseStart_3286759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286782 : List Nat := [4, 2, 2, 1, 3, 2, 1, 2, 6]
def baseStart_3286782 : Nat := 118140960795 + 3286782 * 2 ^ 59
def prefixEnd_3286782 : Nat := 4983230072969 + 3 ^ 40 * 3286782 * 2
def baseEnd_3286782 : Nat := 187522108060673853778819

theorem tailTrace_3286782 : CollatzResearch.WordTrace tailWord_3286782 prefixEnd_3286782 187522108060673853778819 := by
  unfold tailWord_3286782
  simp only [CollatzResearch.WordTrace]
  refine ⟨14984848497319703315041825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79919191985705084346889733 14984848497319703315041825)
  ·
    refine ⟨11238636372989777486281369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14984848497319703315041825 11238636372989777486281369)
    ·
      refine ⟨8428977279742333114711027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11238636372989777486281369 8428977279742333114711027)
      ·
        refine ⟨12643465919613499672066541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8428977279742333114711027 12643465919613499672066541)
        ·
          refine ⟨4741299719855062377024953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12643465919613499672066541 4741299719855062377024953)
          ·
            refine ⟨3555974789891296782768715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4741299719855062377024953 3555974789891296782768715)
            ·
              refine ⟨5333962184836945174153073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3555974789891296782768715 5333962184836945174153073)
              ·
                refine ⟨4000471638627708880614805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5333962184836945174153073 4000471638627708880614805)
                ·
                  refine ⟨187522108060673853778819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4000471638627708880614805 187522108060673853778819)
                  ·
                    rfl

theorem cell23_3286782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_3286782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286782 prefixEnd_3286782 := by exact prefixLift 3286782
  have htrace : WordTrace (prefixWord ++ tailWord_3286782) baseStart_3286782 baseEnd_3286782 := by
    simpa [prefixWord, tailWord_3286782, baseEnd_3286782] using wordTrace_append hprefix tailTrace_3286782
  have hstable : (prefixWord ++ tailWord_3286782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286782).length < 2 ^ (prefixWord ++ tailWord_3286782).sum := by decide
  have hdescent : baseEnd_3286782 < baseStart_3286782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286785 : List Nat := [1, 2, 4, 1, 1, 1, 2, 4, 2, 3, 2]
def baseStart_3286785 : Nat := 118140960795 + 3286785 * 2 ^ 59
def prefixEnd_3286785 : Nat := 4983230072969 + 3 ^ 40 * 3286785 * 2
def baseEnd_3286785 : Nat := 1687700512988028172271857

theorem tailTrace_3286785 : CollatzResearch.WordTrace tailWord_3286785 prefixEnd_3286785 1687700512988028172271857 := by
  unfold tailWord_3286785
  simp only [CollatzResearch.WordTrace]
  refine ⟨119878897397546758032693809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79919264931697838688462539 119878897397546758032693809)
  ·
    refine ⟨89909173048160068524520357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119878897397546758032693809 89909173048160068524520357)
    ·
      refine ⟨16857969946530012848347567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89909173048160068524520357 16857969946530012848347567)
      ·
        refine ⟨25286954919795019272521351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16857969946530012848347567 25286954919795019272521351)
        ·
          refine ⟨37930432379692528908782027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25286954919795019272521351 37930432379692528908782027)
          ·
            refine ⟨56895648569538793363173041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37930432379692528908782027 56895648569538793363173041)
            ·
              refine ⟨42671736427154095022379781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56895648569538793363173041 42671736427154095022379781)
              ·
                refine ⟨8000950580091392816696209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42671736427154095022379781 8000950580091392816696209)
                ·
                  refine ⟨6000712935068544612522157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8000950580091392816696209 6000712935068544612522157)
                  ·
                    refine ⟨2250267350650704229695809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6000712935068544612522157 2250267350650704229695809)
                    ·
                      refine ⟨1687700512988028172271857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2250267350650704229695809 1687700512988028172271857)
                      ·
                        rfl

theorem cell23_3286785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_3286785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286785 prefixEnd_3286785 := by exact prefixLift 3286785
  have htrace : WordTrace (prefixWord ++ tailWord_3286785) baseStart_3286785 baseEnd_3286785 := by
    simpa [prefixWord, tailWord_3286785, baseEnd_3286785] using wordTrace_append hprefix tailTrace_3286785
  have hstable : (prefixWord ++ tailWord_3286785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286785).length < 2 ^ (prefixWord ++ tailWord_3286785).sum := by decide
  have hdescent : baseEnd_3286785 < baseStart_3286785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286792 : List Nat := [2, 1, 3, 2, 2, 1, 1, 6, 1, 1, 3]
def baseStart_3286792 : Nat := 118140960795 + 3286792 * 2 ^ 59
def prefixEnd_3286792 : Nat := 4983230072969 + 3 ^ 40 * 3286792 * 2
def baseEnd_3286792 : Nat := 1687704107352609644884325

theorem tailTrace_3286792 : CollatzResearch.WordTrace tailWord_3286792 prefixEnd_3286792 1687704107352609644884325 := by
  unfold tailWord_3286792
  simp only [CollatzResearch.WordTrace]
  refine ⟨59939576354260699114099315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79919435139014265485465753 59939576354260699114099315)
  ·
    refine ⟨89909364531391048671148973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59939576354260699114099315 89909364531391048671148973)
    ·
      refine ⟨33716011699271643251680865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89909364531391048671148973 33716011699271643251680865)
      ·
        refine ⟨25287008774453732438760649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33716011699271643251680865 25287008774453732438760649)
        ·
          refine ⟨18965256580840299329070487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25287008774453732438760649 18965256580840299329070487)
          ·
            refine ⟨28447884871260448993605731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18965256580840299329070487 28447884871260448993605731)
            ·
              refine ⟨42671827306890673490408597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28447884871260448993605731 42671827306890673490408597)
              ·
                refine ⟨2000241905010500319862903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42671827306890673490408597 2000241905010500319862903)
                ·
                  refine ⟨3000362857515750479794355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2000241905010500319862903 3000362857515750479794355)
                  ·
                    refine ⟨4500544286273625719691533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3000362857515750479794355 4500544286273625719691533)
                    ·
                      refine ⟨1687704107352609644884325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4500544286273625719691533 1687704107352609644884325)
                      ·
                        rfl

theorem cell23_3286792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_3286792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286792 prefixEnd_3286792 := by exact prefixLift 3286792
  have htrace : WordTrace (prefixWord ++ tailWord_3286792) baseStart_3286792 baseEnd_3286792 := by
    simpa [prefixWord, tailWord_3286792, baseEnd_3286792] using wordTrace_append hprefix tailTrace_3286792
  have hstable : (prefixWord ++ tailWord_3286792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286792).length < 2 ^ (prefixWord ++ tailWord_3286792).sum := by decide
  have hdescent : baseEnd_3286792 < baseStart_3286792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286798 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_3286798 : Nat := 118140960795 + 3286798 * 2 ^ 59
def prefixEnd_3286798 : Nat := 4983230072969 + 3 ^ 40 * 3286798 * 2
def baseEnd_3286798 : Nat := 1687707188236536621409297

theorem tailTrace_3286798 : CollatzResearch.WordTrace tailWord_3286798 prefixEnd_3286798 1687707188236536621409297 := by
  unfold tailWord_3286798
  simp only [CollatzResearch.WordTrace]
  refine ⟨14984921443312457656614631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79919581030999774168611365 14984921443312457656614631)
  ·
    refine ⟨22477382164968686484921947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14984921443312457656614631 22477382164968686484921947)
    ·
      refine ⟨33716073247453029727382921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22477382164968686484921947 33716073247453029727382921)
      ·
        refine ⟨25287054935589772295537191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33716073247453029727382921 25287054935589772295537191)
        ·
          refine ⟨37930582403384658443305787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25287054935589772295537191 37930582403384658443305787)
          ·
            refine ⟨56895873605076987664958681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37930582403384658443305787 56895873605076987664958681)
            ·
              refine ⟨42671905203807740748719011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56895873605076987664958681 42671905203807740748719011)
              ·
                refine ⟨64007857805711611123078517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42671905203807740748719011 64007857805711611123078517)
                ·
                  refine ⟨6000736669285463542788611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64007857805711611123078517 6000736669285463542788611)
                  ·
                    refine ⟨9001105003928195314182917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6000736669285463542788611 9001105003928195314182917)
                    ·
                      refine ⟨1687707188236536621409297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9001105003928195314182917 1687707188236536621409297)
                      ·
                        rfl

theorem cell23_3286798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_3286798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286798 prefixEnd_3286798 := by exact prefixLift 3286798
  have htrace : WordTrace (prefixWord ++ tailWord_3286798) baseStart_3286798 baseEnd_3286798 := by
    simpa [prefixWord, tailWord_3286798, baseEnd_3286798] using wordTrace_append hprefix tailTrace_3286798
  have hstable : (prefixWord ++ tailWord_3286798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286798).length < 2 ^ (prefixWord ++ tailWord_3286798).sum := by decide
  have hdescent : baseEnd_3286798 < baseStart_3286798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286802 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_3286802 : Nat := 118140960795 + 3286802 * 2 ^ 59
def prefixEnd_3286802 : Nat := 4983230072969 + 3 ^ 40 * 3286802 * 2
def baseEnd_3286802 : Nat := 1687709242159154605759279

theorem tailTrace_3286802 : CollatzResearch.WordTrace tailWord_3286802 prefixEnd_3286802 1687709242159154605759279 := by
  unfold tailWord_3286802
  simp only [CollatzResearch.WordTrace]
  refine ⟨29969879359621292484015665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79919678292323446624041773 29969879359621292484015665)
  ·
    refine ⟨22477409519715969363011749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29969879359621292484015665 22477409519715969363011749)
    ·
      refine ⟨4214514284946744255564703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22477409519715969363011749 4214514284946744255564703)
      ·
        refine ⟨6321771427420116383347055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4214514284946744255564703 6321771427420116383347055)
        ·
          refine ⟨9482657141130174575020583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6321771427420116383347055 9482657141130174575020583)
          ·
            refine ⟨14223985711695261862530875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9482657141130174575020583 14223985711695261862530875)
            ·
              refine ⟨21335978567542892793796313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14223985711695261862530875 21335978567542892793796313)
              ·
                refine ⟨16001983925657169595347235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21335978567542892793796313 16001983925657169595347235)
                ·
                  refine ⟨24002975888485754393020853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16001983925657169595347235 24002975888485754393020853)
                  ·
                    refine ⟨2250278989545539474345705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24002975888485754393020853 2250278989545539474345705)
                    ·
                      refine ⟨1687709242159154605759279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2250278989545539474345705 1687709242159154605759279)
                      ·
                        rfl

theorem cell23_3286802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_3286802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286802 prefixEnd_3286802 := by exact prefixLift 3286802
  have htrace : WordTrace (prefixWord ++ tailWord_3286802) baseStart_3286802 baseEnd_3286802 := by
    simpa [prefixWord, tailWord_3286802, baseEnd_3286802] using wordTrace_append hprefix tailTrace_3286802
  have hstable : (prefixWord ++ tailWord_3286802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286802).length < 2 ^ (prefixWord ++ tailWord_3286802).sum := by decide
  have hdescent : baseEnd_3286802 < baseStart_3286802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286808 : List Nat := [2, 1, 2, 3, 1, 1, 5, 1, 1, 6]
def baseStart_3286808 : Nat := 118140960795 + 3286808 * 2 ^ 59
def prefixEnd_3286808 : Nat := 4983230072969 + 3 ^ 40 * 3286808 * 2
def baseEnd_3286808 : Nat := 562570774347693860761417

theorem tailTrace_3286808 : CollatzResearch.WordTrace tailWord_3286808 prefixEnd_3286808 562570774347693860761417 := by
  unfold tailWord_3286808
  simp only [CollatzResearch.WordTrace]
  refine ⟨59939868138231716480390539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79919824184308955307187385 59939868138231716480390539)
  ·
    refine ⟨89909802207347574720585809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59939868138231716480390539 89909802207347574720585809)
    ·
      refine ⟨67432351655510681040439357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89909802207347574720585809 67432351655510681040439357)
      ·
        refine ⟨25287131870816505390164759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67432351655510681040439357 25287131870816505390164759)
        ·
          refine ⟨37930697806224758085247139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25287131870816505390164759 37930697806224758085247139)
          ·
            refine ⟨56896046709337137127870709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37930697806224758085247139 56896046709337137127870709)
            ·
              refine ⟨5334004379000356605737879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56896046709337137127870709 5334004379000356605737879)
              ·
                refine ⟨8001006568500534908606819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5334004379000356605737879 8001006568500534908606819)
                ·
                  refine ⟨12001509852750802362910229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8001006568500534908606819 12001509852750802362910229)
                  ·
                    refine ⟨562570774347693860761417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12001509852750802362910229 562570774347693860761417)
                    ·
                      rfl

theorem cell23_3286808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_3286808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286808 prefixEnd_3286808 := by exact prefixLift 3286808
  have htrace : WordTrace (prefixWord ++ tailWord_3286808) baseStart_3286808 baseEnd_3286808 := by
    simpa [prefixWord, tailWord_3286808, baseEnd_3286808] using wordTrace_append hprefix tailTrace_3286808
  have hstable : (prefixWord ++ tailWord_3286808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286808).length < 2 ^ (prefixWord ++ tailWord_3286808).sum := by decide
  have hdescent : baseEnd_3286808 < baseStart_3286808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286811 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 6]
def baseStart_3286811 : Nat := 118140960795 + 3286811 * 2 ^ 59
def prefixEnd_3286811 : Nat := 4983230072969 + 3 ^ 40 * 3286811 * 2
def baseEnd_3286811 : Nat := 1687713863485045070546737

theorem tailTrace_3286811 : CollatzResearch.WordTrace tailWord_3286811 prefixEnd_3286811 1687713863485045070546737 := by
  unfold tailWord_3286811
  simp only [CollatzResearch.WordTrace]
  refine ⟨119879845695452564473140287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79919897130301709648760191 119879845695452564473140287)
  ·
    refine ⟨179819768543178846709710431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119879845695452564473140287 179819768543178846709710431)
    ·
      refine ⟨269729652814768270064565647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179819768543178846709710431 269729652814768270064565647)
      ·
        refine ⟨404594479222152405096848471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269729652814768270064565647 404594479222152405096848471)
        ·
          refine ⟨606891718833228607645272707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404594479222152405096848471 606891718833228607645272707)
          ·
            refine ⟨910337578249842911467909061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606891718833228607645272707 910337578249842911467909061)
            ·
              refine ⟨170688295921845545900232949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 910337578249842911467909061 170688295921845545900232949)
              ·
                refine ⟨16002027742673019928146839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 170688295921845545900232949 16002027742673019928146839)
                ·
                  refine ⟨24003041614009529892220259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16002027742673019928146839 24003041614009529892220259)
                  ·
                    refine ⟨36004562421014294838330389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24003041614009529892220259 36004562421014294838330389)
                    ·
                      refine ⟨1687713863485045070546737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36004562421014294838330389 1687713863485045070546737)
                      ·
                        rfl

theorem cell23_3286811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 6].length) (baseStart_3286811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286811 prefixEnd_3286811 := by exact prefixLift 3286811
  have htrace : WordTrace (prefixWord ++ tailWord_3286811) baseStart_3286811 baseEnd_3286811 := by
    simpa [prefixWord, tailWord_3286811, baseEnd_3286811] using wordTrace_append hprefix tailTrace_3286811
  have hstable : (prefixWord ++ tailWord_3286811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286811).length < 2 ^ (prefixWord ++ tailWord_3286811).sum := by decide
  have hdescent : baseEnd_3286811 < baseStart_3286811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286815 : List Nat := [1, 1, 2, 4, 2, 1, 4, 2, 1, 1, 4]
def baseStart_3286815 : Nat := 118140960795 + 3286815 * 2 ^ 59
def prefixEnd_3286815 : Nat := 4983230072969 + 3 ^ 40 * 3286815 * 2
def baseEnd_3286815 : Nat := 1687715917407663054896719

theorem tailTrace_3286815 : CollatzResearch.WordTrace tailWord_3286815 prefixEnd_3286815 1687715917407663054896719 := by
  unfold tailWord_3286815
  simp only [CollatzResearch.WordTrace]
  refine ⟨119879991587438073156285899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79919994391625382104190599 119879991587438073156285899)
  ·
    refine ⟨179819987381157109734428849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119879991587438073156285899 179819987381157109734428849)
    ·
      refine ⟨134864990535867832300821637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179819987381157109734428849 134864990535867832300821637)
      ·
        refine ⟨25287185725475218556404057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134864990535867832300821637 25287185725475218556404057)
        ·
          refine ⟨18965389294106413917303043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25287185725475218556404057 18965389294106413917303043)
          ·
            refine ⟨28448083941159620875954565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18965389294106413917303043 28448083941159620875954565)
            ·
              refine ⟨5334015738967428914241481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28448083941159620875954565 5334015738967428914241481)
              ·
                refine ⟨4000511804225571685681111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5334015738967428914241481 4000511804225571685681111)
                ·
                  refine ⟨6000767706338357528521667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4000511804225571685681111 6000767706338357528521667)
                  ·
                    refine ⟨9001151559507536292782501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6000767706338357528521667 9001151559507536292782501)
                    ·
                      refine ⟨1687715917407663054896719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9001151559507536292782501 1687715917407663054896719)
                      ·
                        rfl

theorem cell23_3286815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_3286815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286815 prefixEnd_3286815 := by exact prefixLift 3286815
  have htrace : WordTrace (prefixWord ++ tailWord_3286815) baseStart_3286815 baseEnd_3286815 := by
    simpa [prefixWord, tailWord_3286815, baseEnd_3286815] using wordTrace_append hprefix tailTrace_3286815
  have hstable : (prefixWord ++ tailWord_3286815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286815).length < 2 ^ (prefixWord ++ tailWord_3286815).sum := by decide
  have hdescent : baseEnd_3286815 < baseStart_3286815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286818 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_3286818 : Nat := 118140960795 + 3286818 * 2 ^ 59
def prefixEnd_3286818 : Nat := 4983230072969 + 3 ^ 40 * 3286818 * 2
def baseEnd_3286818 : Nat := 1687717457849626543159205

theorem tailTrace_3286818 : CollatzResearch.WordTrace tailWord_3286818 prefixEnd_3286818 1687717457849626543159205 := by
  unfold tailWord_3286818
  simp only [CollatzResearch.WordTrace]
  refine ⟨29970025251606801167161277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79920067337618136445763405 29970025251606801167161277)
  ·
    refine ⟨11238759469352550437685479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29970025251606801167161277 11238759469352550437685479)
    ·
      refine ⟨16858139204028825656528219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11238759469352550437685479 16858139204028825656528219)
      ·
        refine ⟨25287208806043238484792329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16858139204028825656528219 25287208806043238484792329)
        ·
          refine ⟨18965406604532428863594247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25287208806043238484792329 18965406604532428863594247)
          ·
            refine ⟨28448109906798643295391371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18965406604532428863594247 28448109906798643295391371)
            ·
              refine ⟨42672164860197964943087057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28448109906798643295391371 42672164860197964943087057)
              ·
                refine ⟨32004123645148473707315293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42672164860197964943087057 32004123645148473707315293)
                ·
                  refine ⟨12001546366930677640243235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32004123645148473707315293 12001546366930677640243235)
                  ·
                    refine ⟨18002319550396016460364853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12001546366930677640243235 18002319550396016460364853)
                    ·
                      refine ⟨1687717457849626543159205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18002319550396016460364853 1687717457849626543159205)
                      ·
                        rfl

theorem cell23_3286818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_3286818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286818 prefixEnd_3286818 := by exact prefixLift 3286818
  have htrace : WordTrace (prefixWord ++ tailWord_3286818) baseStart_3286818 baseEnd_3286818 := by
    simpa [prefixWord, tailWord_3286818, baseEnd_3286818] using wordTrace_append hprefix tailTrace_3286818
  have hstable : (prefixWord ++ tailWord_3286818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286818).length < 2 ^ (prefixWord ++ tailWord_3286818).sum := by decide
  have hdescent : baseEnd_3286818 < baseStart_3286818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286835 : List Nat := [1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 5]
def baseStart_3286835 : Nat := 118140960795 + 3286835 * 2 ^ 59
def prefixEnd_3286835 : Nat := 4983230072969 + 3 ^ 40 * 3286835 * 2
def baseEnd_3286835 : Nat := 1687726187020752976646627

theorem tailTrace_3286835 : CollatzResearch.WordTrace tailWord_3286835 prefixEnd_3286835 1687726187020752976646627 := by
  unfold tailWord_3286835
  simp only [CollatzResearch.WordTrace]
  refine ⟨119880721047365616572013959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79920480698243744381342639 119880721047365616572013959)
  ·
    refine ⟨179821081571048424858020939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119880721047365616572013959 179821081571048424858020939)
    ·
      refine ⟨269731622356572637287031409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179821081571048424858020939 269731622356572637287031409)
      ·
        refine ⟨202298716767429477965273557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269731622356572637287031409 202298716767429477965273557)
        ·
          refine ⟨4741376174236628389811099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 202298716767429477965273557 4741376174236628389811099)
          ·
            refine ⟨7112064261354942584716649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4741376174236628389811099 7112064261354942584716649)
            ·
              refine ⟨5334048196016206938537487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7112064261354942584716649 5334048196016206938537487)
              ·
                refine ⟨8001072294024310407806231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5334048196016206938537487 8001072294024310407806231)
                ·
                  refine ⟨12001608441036465611709347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8001072294024310407806231 12001608441036465611709347)
                  ·
                    refine ⟨18002412661554698417564021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12001608441036465611709347 18002412661554698417564021)
                    ·
                      refine ⟨1687726187020752976646627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18002412661554698417564021 1687726187020752976646627)
                      ·
                        rfl

theorem cell23_3286835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 5].length) (baseStart_3286835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286835 prefixEnd_3286835 := by exact prefixLift 3286835
  have htrace : WordTrace (prefixWord ++ tailWord_3286835) baseStart_3286835 baseEnd_3286835 := by
    simpa [prefixWord, tailWord_3286835, baseEnd_3286835] using wordTrace_append hprefix tailTrace_3286835
  have hstable : (prefixWord ++ tailWord_3286835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286835).length < 2 ^ (prefixWord ++ tailWord_3286835).sum := by decide
  have hdescent : baseEnd_3286835 < baseStart_3286835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286882 : List Nat := [3, 3, 2, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_3286882 : Nat := 118140960795 + 3286882 * 2 ^ 59
def prefixEnd_3286882 : Nat := 4983230072969 + 3 ^ 40 * 3286882 * 2
def baseEnd_3286882 : Nat := 1687750320611514292758911

theorem tailTrace_3286882 : CollatzResearch.WordTrace tailWord_3286882 prefixEnd_3286882 1687750320611514292758911 := by
  unfold tailWord_3286882
  simp only [CollatzResearch.WordTrace]
  refine ⟨29970608819548835899743725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79921623518796895732649933 29970608819548835899743725)
  ·
    refine ⟨11238978307330813462403897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29970608819548835899743725 11238978307330813462403897)
    ·
      refine ⟨8429233730498110096802923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11238978307330813462403897 8429233730498110096802923)
      ·
        refine ⟨12643850595747165145204385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8429233730498110096802923 12643850595747165145204385)
        ·
          refine ⟨9482887946810373858903289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12643850595747165145204385 9482887946810373858903289)
          ·
            refine ⟨7112165960107780394177467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9482887946810373858903289 7112165960107780394177467)
            ·
              refine ⟨10668248940161670591266201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7112165960107780394177467 10668248940161670591266201)
              ·
                refine ⟨8001186705121252943449651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10668248940161670591266201 8001186705121252943449651)
                ·
                  refine ⟨12001780057681879415174477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8001186705121252943449651 12001780057681879415174477)
                  ·
                    refine ⟨4500667521630704780690429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12001780057681879415174477 4500667521630704780690429)
                    ·
                      refine ⟨1687750320611514292758911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4500667521630704780690429 1687750320611514292758911)
                      ·
                        rfl

theorem cell23_3286882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_3286882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286882 prefixEnd_3286882 := by exact prefixLift 3286882
  have htrace : WordTrace (prefixWord ++ tailWord_3286882) baseStart_3286882 baseEnd_3286882 := by
    simpa [prefixWord, tailWord_3286882, baseEnd_3286882] using wordTrace_append hprefix tailTrace_3286882
  have hstable : (prefixWord ++ tailWord_3286882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286882).length < 2 ^ (prefixWord ++ tailWord_3286882).sum := by decide
  have hdescent : baseEnd_3286882 < baseStart_3286882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286898 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 2, 6]
def baseStart_3286898 : Nat := 118140960795 + 3286898 * 2 ^ 59
def prefixEnd_3286898 : Nat := 4983230072969 + 3 ^ 40 * 3286898 * 2
def baseEnd_3286898 : Nat := 562586178767328743386279

theorem tailTrace_3286898 : CollatzResearch.WordTrace tailWord_3286898 prefixEnd_3286898 562586178767328743386279 := by
  unfold tailWord_3286898
  simp only [CollatzResearch.WordTrace]
  refine ⟨29970754711534344582889337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79922012564091585554371565 29970754711534344582889337)
  ·
    refine ⟨22478066033650758437167003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29970754711534344582889337 22478066033650758437167003)
    ·
      refine ⟨33717099050476137655750505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22478066033650758437167003 33717099050476137655750505)
      ·
        refine ⟨25287824287857103241812879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33717099050476137655750505 25287824287857103241812879)
        ·
          refine ⟨37931736431785654862719319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25287824287857103241812879 37931736431785654862719319)
          ·
            refine ⟨56897604647678482294078979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37931736431785654862719319 56897604647678482294078979)
            ·
              refine ⟨85346406971517723441118469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56897604647678482294078979 85346406971517723441118469)
              ·
                refine ⟨16002451307159573145209713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85346406971517723441118469 16002451307159573145209713)
                ·
                  refine ⟨12001838480369679858907285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16002451307159573145209713 12001838480369679858907285)
                  ·
                    refine ⟨562586178767328743386279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12001838480369679858907285 562586178767328743386279)
                    ·
                      rfl

theorem cell23_3286898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_3286898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286898 prefixEnd_3286898 := by exact prefixLift 3286898
  have htrace : WordTrace (prefixWord ++ tailWord_3286898) baseStart_3286898 baseEnd_3286898 := by
    simpa [prefixWord, tailWord_3286898, baseEnd_3286898] using wordTrace_append hprefix tailTrace_3286898
  have hstable : (prefixWord ++ tailWord_3286898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286898).length < 2 ^ (prefixWord ++ tailWord_3286898).sum := by decide
  have hdescent : baseEnd_3286898 < baseStart_3286898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286905 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 3, 4, 2]
def baseStart_3286905 : Nat := 118140960795 + 3286905 * 2 ^ 59
def prefixEnd_3286905 : Nat := 4983230072969 + 3 ^ 40 * 3286905 * 2
def baseEnd_3286905 : Nat := 1687762130666567702771305

theorem tailTrace_3286905 : CollatzResearch.WordTrace tailWord_3286905 prefixEnd_3286905 1687762130666567702771305 := by
  unfold tailWord_3286905
  simp only [CollatzResearch.WordTrace]
  refine ⟨119883274157112018527062169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79922182771408012351374779 119883274157112018527062169)
  ·
    refine ⟨89912455617834013895296627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119883274157112018527062169 89912455617834013895296627)
    ·
      refine ⟨134868683426751020842944941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89912455617834013895296627 134868683426751020842944941)
      ·
        refine ⟨50575756285031632816104353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134868683426751020842944941 50575756285031632816104353)
        ·
          refine ⟨37931817213773724612078265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50575756285031632816104353 37931817213773724612078265)
          ·
            refine ⟨28448862910330293459058699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37931817213773724612078265 28448862910330293459058699)
            ·
              refine ⟨42673294365495440188588049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28448862910330293459058699 42673294365495440188588049)
              ·
                refine ⟨32004970774121580141441037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42673294365495440188588049 32004970774121580141441037)
                ·
                  refine ⟨12001864040295592553040389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32004970774121580141441037 12001864040295592553040389)
                  ·
                    refine ⟨2250349507555423603695073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12001864040295592553040389 2250349507555423603695073)
                    ·
                      refine ⟨1687762130666567702771305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2250349507555423603695073 1687762130666567702771305)
                      ·
                        rfl

theorem cell23_3286905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_3286905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286905 prefixEnd_3286905 := by exact prefixLift 3286905
  have htrace : WordTrace (prefixWord ++ tailWord_3286905) baseStart_3286905 baseEnd_3286905 := by
    simpa [prefixWord, tailWord_3286905, baseEnd_3286905] using wordTrace_append hprefix tailTrace_3286905
  have hstable : (prefixWord ++ tailWord_3286905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286905).length < 2 ^ (prefixWord ++ tailWord_3286905).sum := by decide
  have hdescent : baseEnd_3286905 < baseStart_3286905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286943 : List Nat := [1, 1, 2, 5, 4, 1, 2, 1, 1, 3, 2]
def baseStart_3286943 : Nat := 118140960795 + 3286943 * 2 ^ 59
def prefixEnd_3286943 : Nat := 4983230072969 + 3 ^ 40 * 3286943 * 2
def baseEnd_3286943 : Nat := 1687781642931438554096131

theorem tailTrace_3286943 : CollatzResearch.WordTrace tailWord_3286943 prefixEnd_3286943 1687781642931438554096131 := by
  unfold tailWord_3286943
  simp only [CollatzResearch.WordTrace]
  refine ⟨119884660130974351016945483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79923106753982900677963655 119884660130974351016945483)
  ·
    refine ⟨179826990196461526525418225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119884660130974351016945483 179826990196461526525418225)
    ·
      refine ⟨134870242647346144894063669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179826990196461526525418225 134870242647346144894063669)
      ·
        refine ⟨12644085248188701083818469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134870242647346144894063669 12644085248188701083818469)
        ·
          refine ⟨2370765984035381453215963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12644085248188701083818469 2370765984035381453215963)
          ·
            refine ⟨3556148976053072179823945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370765984035381453215963 3556148976053072179823945)
            ·
              refine ⟨2667111732039804134867959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3556148976053072179823945 2667111732039804134867959)
              ·
                refine ⟨4000667598059706202301939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2667111732039804134867959 4000667598059706202301939)
                ·
                  refine ⟨6001001397089559303452909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4000667598059706202301939 6001001397089559303452909)
                  ·
                    refine ⟨2250375523908584738794841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6001001397089559303452909 2250375523908584738794841)
                    ·
                      refine ⟨1687781642931438554096131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2250375523908584738794841 1687781642931438554096131)
                      ·
                        rfl

theorem cell23_3286943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_3286943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286943 prefixEnd_3286943 := by exact prefixLift 3286943
  have htrace : WordTrace (prefixWord ++ tailWord_3286943) baseStart_3286943 baseEnd_3286943 := by
    simpa [prefixWord, tailWord_3286943, baseEnd_3286943] using wordTrace_append hprefix tailTrace_3286943
  have hstable : (prefixWord ++ tailWord_3286943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286943).length < 2 ^ (prefixWord ++ tailWord_3286943).sum := by decide
  have hdescent : baseEnd_3286943 < baseStart_3286943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286968 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 1, 1, 7]
def baseStart_3286968 : Nat := 118140960795 + 3286968 * 2 ^ 59
def prefixEnd_3286968 : Nat := 4983230072969 + 3 ^ 40 * 3286968 * 2
def baseEnd_3286968 : Nat := 1687794479947800956283515

theorem tailTrace_3286968 : CollatzResearch.WordTrace tailWord_3286968 prefixEnd_3286968 1687794479947800956283515 := by
  unfold tailWord_3286968
  simp only [CollatzResearch.WordTrace]
  refine ⟨59942785977941890143302779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79923714637255853524403705 59942785977941890143302779)
  ·
    refine ⟨89914178966912835214954169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59942785977941890143302779 89914178966912835214954169)
    ·
      refine ⟨67435634225184626411215627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89914178966912835214954169 67435634225184626411215627)
      ·
        refine ⟨101153451337776939616823441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67435634225184626411215627 101153451337776939616823441)
        ·
          refine ⟨75865088503332704712617581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101153451337776939616823441 75865088503332704712617581)
          ·
            refine ⟨28449408188749764267231593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75865088503332704712617581 28449408188749764267231593)
            ·
              refine ⟨21337056141562323200423695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28449408188749764267231593 21337056141562323200423695)
              ·
                refine ⟨32005584212343484800635543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21337056141562323200423695 32005584212343484800635543)
                ·
                  refine ⟨48008376318515227200953315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32005584212343484800635543 48008376318515227200953315)
                  ·
                    refine ⟨72012564477772840801429973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48008376318515227200953315 72012564477772840801429973)
                    ·
                      refine ⟨1687794479947800956283515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72012564477772840801429973 1687794479947800956283515)
                      ·
                        rfl

theorem cell23_3286968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_3286968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286968 prefixEnd_3286968 := by exact prefixLift 3286968
  have htrace : WordTrace (prefixWord ++ tailWord_3286968) baseStart_3286968 baseEnd_3286968 := by
    simpa [prefixWord, tailWord_3286968, baseEnd_3286968] using wordTrace_append hprefix tailTrace_3286968
  have hstable : (prefixWord ++ tailWord_3286968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286968).length < 2 ^ (prefixWord ++ tailWord_3286968).sum := by decide
  have hdescent : baseEnd_3286968 < baseStart_3286968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287008 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 6]
def baseStart_3287008 : Nat := 118140960795 + 3287008 * 2 ^ 59
def prefixEnd_3287008 : Nat := 4983230072969 + 3 ^ 40 * 3287008 * 2
def baseEnd_3287008 : Nat := 1687815019173980799783331

theorem tailTrace_3287008 : CollatzResearch.WordTrace tailWord_3287008 prefixEnd_3287008 1687815019173980799783331 := by
  unfold tailWord_3287008
  simp only [CollatzResearch.WordTrace]
  refine ⟨59943515437869433559030839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79924687250492578078707785 59943515437869433559030839)
  ·
    refine ⟨89915273156804150338546259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59943515437869433559030839 89915273156804150338546259)
    ·
      refine ⟨134872909735206225507819389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89915273156804150338546259 134872909735206225507819389)
      ·
        refine ⟨50577341150702334565432271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134872909735206225507819389 50577341150702334565432271)
        ·
          refine ⟨75866011726053501848148407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50577341150702334565432271 75866011726053501848148407)
          ·
            refine ⟨113799017589080252772222611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75866011726053501848148407 113799017589080252772222611)
            ·
              refine ⟨170698526383620379158333917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113799017589080252772222611 170698526383620379158333917)
              ·
                refine ⟨64011947393857642184375219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170698526383620379158333917 64011947393857642184375219)
                ·
                  refine ⟨96017921090786463276562829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64011947393857642184375219 96017921090786463276562829)
                  ·
                    refine ⟨36006720409044923728711061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96017921090786463276562829 36006720409044923728711061)
                    ·
                      refine ⟨1687815019173980799783331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36006720409044923728711061 1687815019173980799783331)
                      ·
                        rfl

theorem cell23_3287008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_3287008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287008 prefixEnd_3287008 := by exact prefixLift 3287008
  have htrace : WordTrace (prefixWord ++ tailWord_3287008) baseStart_3287008 baseEnd_3287008 := by
    simpa [prefixWord, tailWord_3287008, baseEnd_3287008] using wordTrace_append hprefix tailTrace_3287008
  have hstable : (prefixWord ++ tailWord_3287008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287008).length < 2 ^ (prefixWord ++ tailWord_3287008).sum := by decide
  have hdescent : baseEnd_3287008 < baseStart_3287008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287073 : List Nat := [1, 2, 3, 2, 4, 2, 2, 2, 1, 4]
def baseStart_3287073 : Nat := 118140960795 + 3287073 * 2 ^ 59
def prefixEnd_3287073 : Nat := 4983230072969 + 3 ^ 40 * 3287073 * 2
def baseEnd_3287073 : Nat := 562616131805507681823511

theorem tailTrace_3287073 : CollatzResearch.WordTrace tailWord_3287073 prefixEnd_3287073 562616131805507681823511 := by
  unfold tailWord_3287073
  simp only [CollatzResearch.WordTrace]
  refine ⟨119889401620503383219177873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79926267747002255479451915 119889401620503383219177873)
  ·
    refine ⟨89917051215377537414383405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119889401620503383219177873 89917051215377537414383405)
    ·
      refine ⟨33718894205766576530393777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89917051215377537414383405 33718894205766576530393777)
      ·
        refine ⟨25289170654324932397795333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33718894205766576530393777 25289170654324932397795333)
        ·
          refine ⟨4741719497685924824586625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25289170654324932397795333 4741719497685924824586625)
          ·
            refine ⟨3556289623264443618439969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4741719497685924824586625 3556289623264443618439969)
            ·
              refine ⟨2667217217448332713829977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3556289623264443618439969 2667217217448332713829977)
              ·
                refine ⟨2000412913086249535372483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2667217217448332713829977 2000412913086249535372483)
                ·
                  refine ⟨3000619369629374303058725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2000412913086249535372483 3000619369629374303058725)
                  ·
                    refine ⟨562616131805507681823511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3000619369629374303058725 562616131805507681823511)
                    ·
                      rfl

theorem cell23_3287073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_3287073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287073 prefixEnd_3287073 := by exact prefixLift 3287073
  have htrace : WordTrace (prefixWord ++ tailWord_3287073) baseStart_3287073 baseEnd_3287073 := by
    simpa [prefixWord, tailWord_3287073, baseEnd_3287073] using wordTrace_append hprefix tailTrace_3287073
  have hstable : (prefixWord ++ tailWord_3287073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287073).length < 2 ^ (prefixWord ++ tailWord_3287073).sum := by decide
  have hdescent : baseEnd_3287073 < baseStart_3287073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287082 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 3, 5]
def baseStart_3287082 : Nat := 118140960795 + 3287082 * 2 ^ 59
def prefixEnd_3287082 : Nat := 4983230072969 + 3 ^ 40 * 3287082 * 2
def baseEnd_3287082 : Nat := 562617672247471170085997

theorem tailTrace_3287082 : CollatzResearch.WordTrace tailWord_3287082 prefixEnd_3287082 562617672247471170085997 := by
  unfold tailWord_3287082
  simp only [CollatzResearch.WordTrace]
  refine ⟨29972432469367694439063875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79926486584980518504170333 29972432469367694439063875)
  ·
    refine ⟨44958648704051541658595813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29972432469367694439063875 44958648704051541658595813)
    ·
      refine ⟨8429746632009664060986715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44958648704051541658595813 8429746632009664060986715)
      ·
        refine ⟨12644619948014496091480073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8429746632009664060986715 12644619948014496091480073)
        ·
          refine ⟨9483464961010872068610055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12644619948014496091480073 9483464961010872068610055)
          ·
            refine ⟨14225197441516308102915083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9483464961010872068610055 14225197441516308102915083)
            ·
              refine ⟨21337796162274462154372625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14225197441516308102915083 21337796162274462154372625)
              ·
                refine ⟨16003347121705846615779469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21337796162274462154372625 16003347121705846615779469)
                ·
                  refine ⟨6001255170639692480917301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16003347121705846615779469 6001255170639692480917301)
                  ·
                    refine ⟨562617672247471170085997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6001255170639692480917301 562617672247471170085997)
                    ·
                      rfl

theorem cell23_3287082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_3287082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287082 prefixEnd_3287082 := by exact prefixLift 3287082
  have htrace : WordTrace (prefixWord ++ tailWord_3287082) baseStart_3287082 baseEnd_3287082 := by
    simpa [prefixWord, tailWord_3287082, baseEnd_3287082] using wordTrace_append hprefix tailTrace_3287082
  have hstable : (prefixWord ++ tailWord_3287082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287082).length < 2 ^ (prefixWord ++ tailWord_3287082).sum := by decide
  have hdescent : baseEnd_3287082 < baseStart_3287082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287095 : List Nat := [1, 1, 3, 1, 2, 2, 3, 3, 1, 6]
def baseStart_3287095 : Nat := 118140960795 + 3287095 * 2 ^ 59
def prefixEnd_3287095 : Nat := 4983230072969 + 3 ^ 40 * 3287095 * 2
def baseEnd_3287095 : Nat := 562619897330307319798477

theorem tailTrace_3287095 : CollatzResearch.WordTrace tailWord_3287095 prefixEnd_3287095 562619897330307319798477 := by
  unfold tailWord_3287095
  simp only [CollatzResearch.WordTrace]
  refine ⟨119890204026423680976478739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79926802684282453984319159 119890204026423680976478739)
  ·
    refine ⟨179835306039635521464718109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119890204026423680976478739 179835306039635521464718109)
    ·
      refine ⟨67438239764863320549269291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179835306039635521464718109 67438239764863320549269291)
      ·
        refine ⟨101157359647294980823903937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67438239764863320549269291 101157359647294980823903937)
        ·
          refine ⟨75868019735471235617927953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101157359647294980823903937 75868019735471235617927953)
          ·
            refine ⟨56901014801603426713445965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75868019735471235617927953 56901014801603426713445965)
            ·
              refine ⟨21337880550601285017542237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56901014801603426713445965 21337880550601285017542237)
              ·
                refine ⟨8001705206475481881578339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21337880550601285017542237 8001705206475481881578339)
                ·
                  refine ⟨12002557809713222822367509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8001705206475481881578339 12002557809713222822367509)
                  ·
                    refine ⟨562619897330307319798477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12002557809713222822367509 562619897330307319798477)
                    ·
                      rfl

theorem cell23_3287095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_3287095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287095 prefixEnd_3287095 := by exact prefixLift 3287095
  have htrace : WordTrace (prefixWord ++ tailWord_3287095) baseStart_3287095 baseEnd_3287095 := by
    simpa [prefixWord, tailWord_3287095, baseEnd_3287095] using wordTrace_append hprefix tailTrace_3287095
  have hstable : (prefixWord ++ tailWord_3287095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287095).length < 2 ^ (prefixWord ++ tailWord_3287095).sum := by decide
  have hdescent : baseEnd_3287095 < baseStart_3287095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287125 : List Nat := [1, 3, 2, 2, 1, 4, 10]
def baseStart_3287125 : Nat := 118140960795 + 3287125 * 2 ^ 59
def prefixEnd_3287125 : Nat := 4983230072969 + 3 ^ 40 * 3287125 * 2
def baseEnd_3287125 : Nat := 20837964153216751136053

theorem tailTrace_3287125 : CollatzResearch.WordTrace tailWord_3287125 prefixEnd_3287125 20837964153216751136053 := by
  unfold tailWord_3287125
  simp only [CollatzResearch.WordTrace]
  refine ⟨119891298216314996100070829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79927532144209997400047219 119891298216314996100070829)
  ·
    refine ⟨44959236831118123537526561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119891298216314996100070829 44959236831118123537526561)
    ·
      refine ⟨33719427623338592653144921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44959236831118123537526561 33719427623338592653144921)
      ·
        refine ⟨25289570717503944489858691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33719427623338592653144921 25289570717503944489858691)
        ·
          refine ⟨37934356076255916734788037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25289570717503944489858691 37934356076255916734788037)
          ·
            refine ⟨7112691764297984387772757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37934356076255916734788037 7112691764297984387772757)
            ·
              refine ⟨20837964153216751136053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7112691764297984387772757 20837964153216751136053)
              ·
                rfl

theorem cell23_3287125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 10].length) (baseStart_3287125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287125 prefixEnd_3287125 := by exact prefixLift 3287125
  have htrace : WordTrace (prefixWord ++ tailWord_3287125) baseStart_3287125 baseEnd_3287125 := by
    simpa [prefixWord, tailWord_3287125, baseEnd_3287125] using wordTrace_append hprefix tailTrace_3287125
  have hstable : (prefixWord ++ tailWord_3287125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287125).length < 2 ^ (prefixWord ++ tailWord_3287125).sum := by decide
  have hdescent : baseEnd_3287125 < baseStart_3287125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287136 : List Nat := [2, 1, 1, 3, 2, 4, 2, 1, 3, 2, 2]
def baseStart_3287136 : Nat := 118140960795 + 3287136 * 2 ^ 59
def prefixEnd_3287136 : Nat := 4983230072969 + 3 ^ 40 * 3287136 * 2
def baseEnd_3287136 : Nat := 1687880744697756298982743

theorem tailTrace_3287136 : CollatzResearch.WordTrace tailWord_3287136 prefixEnd_3287136 1687880744697756298982743 := by
  unfold tailWord_3287136
  simp only [CollatzResearch.WordTrace]
  refine ⟨59945849709637572489360631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79927799612850096652480841 59945849709637572489360631)
  ·
    refine ⟨89918774564456358734040947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59945849709637572489360631 89918774564456358734040947)
    ·
      refine ⟨134878161846684538101061421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89918774564456358734040947 134878161846684538101061421)
      ·
        refine ⟨50579310692506701787898033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134878161846684538101061421 50579310692506701787898033)
        ·
          refine ⟨37934483019380026340923525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50579310692506701787898033 37934483019380026340923525)
          ·
            refine ⟨7112715566133754938923161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37934483019380026340923525 7112715566133754938923161)
            ·
              refine ⟨5334536674600316204192371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7112715566133754938923161 5334536674600316204192371)
              ·
                refine ⟨8001805011900474306288557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5334536674600316204192371 8001805011900474306288557)
                ·
                  refine ⟨3000676879462677864858209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8001805011900474306288557 3000676879462677864858209)
                  ·
                    refine ⟨2250507659597008398643657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3000676879462677864858209 2250507659597008398643657)
                    ·
                      refine ⟨1687880744697756298982743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2250507659597008398643657 1687880744697756298982743)
                      ·
                        rfl

theorem cell23_3287136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_3287136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287136 prefixEnd_3287136 := by exact prefixLift 3287136
  have htrace : WordTrace (prefixWord ++ tailWord_3287136) baseStart_3287136 baseEnd_3287136 := by
    simpa [prefixWord, tailWord_3287136, baseEnd_3287136] using wordTrace_append hprefix tailTrace_3287136
  have hstable : (prefixWord ++ tailWord_3287136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287136).length < 2 ^ (prefixWord ++ tailWord_3287136).sum := by decide
  have hdescent : baseEnd_3287136 < baseStart_3287136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287146 : List Nat := [3, 1, 3, 2, 4, 1, 1, 1, 1, 6]
def baseStart_3287146 : Nat := 118140960795 + 3287146 * 2 ^ 59
def prefixEnd_3287146 : Nat := 4983230072969 + 3 ^ 40 * 3287146 * 2
def baseEnd_3287146 : Nat := 562628626501433753285899

theorem tailTrace_3287146 : CollatzResearch.WordTrace tailWord_3287146 prefixEnd_3287146 562628626501433753285899 := by
  unfold tailWord_3287146
  simp only [CollatzResearch.WordTrace]
  refine ⟨29973016037309729171646323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79928042766159277791056861 29973016037309729171646323)
  ·
    refine ⟨44959524055964593757469485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29973016037309729171646323 44959524055964593757469485)
    ·
      refine ⟨16859821520986722659051057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44959524055964593757469485 16859821520986722659051057)
      ·
        refine ⟨12644866140740041994288293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16859821520986722659051057 12644866140740041994288293)
        ·
          refine ⟨2370912401388757873929055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12644866140740041994288293 2370912401388757873929055)
          ·
            refine ⟨3556368602083136810893583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370912401388757873929055 3556368602083136810893583)
            ·
              refine ⟨5334552903124705216340375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3556368602083136810893583 5334552903124705216340375)
              ·
                refine ⟨8001829354687057824510563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5334552903124705216340375 8001829354687057824510563)
                ·
                  refine ⟨12002744032030586736765845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8001829354687057824510563 12002744032030586736765845)
                  ·
                    refine ⟨562628626501433753285899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12002744032030586736765845 562628626501433753285899)
                    ·
                      rfl

theorem cell23_3287146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_3287146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287146 prefixEnd_3287146 := by exact prefixLift 3287146
  have htrace : WordTrace (prefixWord ++ tailWord_3287146) baseStart_3287146 baseEnd_3287146 := by
    simpa [prefixWord, tailWord_3287146, baseEnd_3287146] using wordTrace_append hprefix tailTrace_3287146
  have hstable : (prefixWord ++ tailWord_3287146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287146).length < 2 ^ (prefixWord ++ tailWord_3287146).sum := by decide
  have hdescent : baseEnd_3287146 < baseStart_3287146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287162 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2]
def baseStart_3287162 : Nat := 118140960795 + 3287162 * 2 ^ 59
def prefixEnd_3287162 : Nat := 4983230072969 + 3 ^ 40 * 3287162 * 2
def baseEnd_3287162 : Nat := 1687894095194773197257623

theorem tailTrace_3287162 : CollatzResearch.WordTrace tailWord_3287162 prefixEnd_3287162 1687894095194773197257623 := by
  unfold tailWord_3287162
  simp only [CollatzResearch.WordTrace]
  refine ⟨29973161929295237854791935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79928431811453967612778493 29973161929295237854791935)
  ·
    refine ⟨44959742893942856782187903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29973161929295237854791935 44959742893942856782187903)
    ·
      refine ⟨67439614340914285173281855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44959742893942856782187903 67439614340914285173281855)
      ·
        refine ⟨101159421511371427759922783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67439614340914285173281855 101159421511371427759922783)
        ·
          refine ⟨151739132267057141639884175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101159421511371427759922783 151739132267057141639884175)
          ·
            refine ⟨227608698400585712459826263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151739132267057141639884175 227608698400585712459826263)
            ·
              refine ⟨341413047600878568689739395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227608698400585712459826263 341413047600878568689739395)
              ·
                refine ⟨512119571401317853034609093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341413047600878568689739395 512119571401317853034609093)
                ·
                  refine ⟨96022419637747097443989205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 512119571401317853034609093 96022419637747097443989205)
                  ·
                    refine ⟨2250525460259697596343497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 96022419637747097443989205 2250525460259697596343497)
                    ·
                      refine ⟨1687894095194773197257623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2250525460259697596343497 1687894095194773197257623)
                      ·
                        rfl

theorem cell23_3287162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2].length) (baseStart_3287162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287162 prefixEnd_3287162 := by exact prefixLift 3287162
  have htrace : WordTrace (prefixWord ++ tailWord_3287162) baseStart_3287162 baseEnd_3287162 := by
    simpa [prefixWord, tailWord_3287162, baseEnd_3287162] using wordTrace_append hprefix tailTrace_3287162
  have hstable : (prefixWord ++ tailWord_3287162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287162).length < 2 ^ (prefixWord ++ tailWord_3287162).sum := by decide
  have hdescent : baseEnd_3287162 < baseStart_3287162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287186 : List Nat := [3, 2, 3, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_3287186 : Nat := 118140960795 + 3287186 * 2 ^ 59
def prefixEnd_3287186 : Nat := 4983230072969 + 3 ^ 40 * 3287186 * 2
def baseEnd_3287186 : Nat := 1687906418730481103357513

theorem tailTrace_3287186 : CollatzResearch.WordTrace tailWord_3287186 prefixEnd_3287186 1687906418730481103357513 := by
  unfold tailWord_3287186
  simp only [CollatzResearch.WordTrace]
  refine ⟨29973380767273500879510353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79929015379396002345360941 29973380767273500879510353)
  ·
    refine ⟨22480035575455125659632765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29973380767273500879510353 22480035575455125659632765)
    ·
      refine ⟨8430013340795672122362287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22480035575455125659632765 8430013340795672122362287)
      ·
        refine ⟨12645020011193508183543431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8430013340795672122362287 12645020011193508183543431)
        ·
          refine ⟨18967530016790262275315147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12645020011193508183543431 18967530016790262275315147)
          ·
            refine ⟨28451295025185393412972721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18967530016790262275315147 28451295025185393412972721)
            ·
              refine ⟨21338471268889045059729541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28451295025185393412972721 21338471268889045059729541)
              ·
                refine ⟨4000963362916695948699289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21338471268889045059729541 4000963362916695948699289)
                ·
                  refine ⟨3000722522187521961524467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4000963362916695948699289 3000722522187521961524467)
                  ·
                    refine ⟨4501083783281282942286701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3000722522187521961524467 4501083783281282942286701)
                    ·
                      refine ⟨1687906418730481103357513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4501083783281282942286701 1687906418730481103357513)
                      ·
                        rfl

theorem cell23_3287186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_3287186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287186 prefixEnd_3287186 := by exact prefixLift 3287186
  have htrace : WordTrace (prefixWord ++ tailWord_3287186) baseStart_3287186 baseEnd_3287186 := by
    simpa [prefixWord, tailWord_3287186, baseEnd_3287186] using wordTrace_append hprefix tailTrace_3287186
  have hstable : (prefixWord ++ tailWord_3287186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287186).length < 2 ^ (prefixWord ++ tailWord_3287186).sum := by decide
  have hdescent : baseEnd_3287186 < baseStart_3287186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287195 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 5]
def baseStart_3287195 : Nat := 118140960795 + 3287195 * 2 ^ 59
def prefixEnd_3287195 : Nat := 4983230072969 + 3 ^ 40 * 3287195 * 2
def baseEnd_3287195 : Nat := 1687911040056371568144971

theorem tailTrace_3287195 : CollatzResearch.WordTrace tailWord_3287195 prefixEnd_3287195 1687911040056371568144971 := by
  unfold tailWord_3287195
  simp only [CollatzResearch.WordTrace]
  refine ⟨119893851326061398055119039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79929234217374265370079359 119893851326061398055119039)
  ·
    refine ⟨179840776989092097082678559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119893851326061398055119039 179840776989092097082678559)
    ·
      refine ⟨269761165483638145624017839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179840776989092097082678559 269761165483638145624017839)
      ·
        refine ⟨404641748225457218436026759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269761165483638145624017839 404641748225457218436026759)
        ·
          refine ⟨606962622338185827654040139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404641748225457218436026759 606962622338185827654040139)
          ·
            refine ⟨910443933507278741481060209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606962622338185827654040139 910443933507278741481060209)
            ·
              refine ⟨682832950130459056110795157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 910443933507278741481060209 682832950130459056110795157)
              ·
                refine ⟨32007794537365268255193523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 682832950130459056110795157 32007794537365268255193523)
                ·
                  refine ⟨48011691806047902382790285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32007794537365268255193523 48011691806047902382790285)
                  ·
                    refine ⟨18004384427267963393546357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48011691806047902382790285 18004384427267963393546357)
                    ·
                      refine ⟨1687911040056371568144971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18004384427267963393546357 1687911040056371568144971)
                      ·
                        rfl

theorem cell23_3287195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 5].length) (baseStart_3287195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287195 prefixEnd_3287195 := by exact prefixLift 3287195
  have htrace : WordTrace (prefixWord ++ tailWord_3287195) baseStart_3287195 baseEnd_3287195 := by
    simpa [prefixWord, tailWord_3287195, baseEnd_3287195] using wordTrace_append hprefix tailTrace_3287195
  have hstable : (prefixWord ++ tailWord_3287195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287195).length < 2 ^ (prefixWord ++ tailWord_3287195).sum := by decide
  have hdescent : baseEnd_3287195 < baseStart_3287195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287213 : List Nat := [1, 5, 2, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_3287213 : Nat := 118140960795 + 3287213 * 2 ^ 59
def prefixEnd_3287213 : Nat := 4983230072969 + 3 ^ 40 * 3287213 * 2
def baseEnd_3287213 : Nat := 1687920282708152497719889

theorem tailTrace_3287213 : CollatzResearch.WordTrace tailWord_3287213 prefixEnd_3287213 1687920282708152497719889 := by
  unfold tailWord_3287213
  simp only [CollatzResearch.WordTrace]
  refine ⟨119894507839996187129274293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79929671893330791419516195 119894507839996187129274293)
  ·
    refine ⟨11240110109999642543369465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119894507839996187129274293 11240110109999642543369465)
    ·
      refine ⟨8430082582499731907527099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11240110109999642543369465 8430082582499731907527099)
      ·
        refine ⟨12645123873749597861290649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8430082582499731907527099 12645123873749597861290649)
        ·
          refine ⟨9483842905312198395967987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12645123873749597861290649 9483842905312198395967987)
          ·
            refine ⟨14225764357968297593951981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9483842905312198395967987 14225764357968297593951981)
            ·
              refine ⟨5334661634238111597731993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14225764357968297593951981 5334661634238111597731993)
              ·
                refine ⟨4000996225678583698298995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5334661634238111597731993 4000996225678583698298995)
                ·
                  refine ⟨6001494338517875547448493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4000996225678583698298995 6001494338517875547448493)
                  ·
                    refine ⟨2250560376944203330293185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6001494338517875547448493 2250560376944203330293185)
                    ·
                      refine ⟨1687920282708152497719889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2250560376944203330293185 1687920282708152497719889)
                      ·
                        rfl

theorem cell23_3287213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_3287213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287213 prefixEnd_3287213 := by exact prefixLift 3287213
  have htrace : WordTrace (prefixWord ++ tailWord_3287213) baseStart_3287213 baseEnd_3287213 := by
    simpa [prefixWord, tailWord_3287213, baseEnd_3287213] using wordTrace_append hprefix tailTrace_3287213
  have hstable : (prefixWord ++ tailWord_3287213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287213).length < 2 ^ (prefixWord ++ tailWord_3287213).sum := by decide
  have hdescent : baseEnd_3287213 < baseStart_3287213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287215 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 9]
def baseStart_3287215 : Nat := 118140960795 + 3287215 * 2 ^ 59
def prefixEnd_3287215 : Nat := 4983230072969 + 3 ^ 40 * 3287215 * 2
def baseEnd_3287215 : Nat := 187546812185495721099431

theorem tailTrace_3287215 : CollatzResearch.WordTrace tailWord_3287215 prefixEnd_3287215 187546812185495721099431 := by
  unfold tailWord_3287215
  simp only [CollatzResearch.WordTrace]
  refine ⟨119894580785988941470847099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79929720523992627647231399 119894580785988941470847099)
  ·
    refine ⟨179841871178983412206270649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119894580785988941470847099 179841871178983412206270649)
    ·
      refine ⟨134881403384237559154702987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179841871178983412206270649 134881403384237559154702987)
      ·
        refine ⟨202322105076356338732054481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134881403384237559154702987 202322105076356338732054481)
        ·
          refine ⟨151741578807267254049040861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202322105076356338732054481 151741578807267254049040861)
          ·
            refine ⟨56903092052725220268390323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151741578807267254049040861 56903092052725220268390323)
            ·
              refine ⟨85354638079087830402585485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56903092052725220268390323 85354638079087830402585485)
              ·
                refine ⟨32007989279657936400969557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85354638079087830402585485 32007989279657936400969557)
                ·
                  refine ⟨187546812185495721099431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32007989279657936400969557 187546812185495721099431)
                  ·
                    rfl

theorem cell23_3287215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 9].length) (baseStart_3287215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287215 prefixEnd_3287215 := by exact prefixLift 3287215
  have htrace : WordTrace (prefixWord ++ tailWord_3287215) baseStart_3287215 baseEnd_3287215 := by
    simpa [prefixWord, tailWord_3287215, baseEnd_3287215] using wordTrace_append hprefix tailTrace_3287215
  have hstable : (prefixWord ++ tailWord_3287215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287215).length < 2 ^ (prefixWord ++ tailWord_3287215).sum := by decide
  have hdescent : baseEnd_3287215 < baseStart_3287215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287220 : List Nat := [2, 5, 3, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_3287220 : Nat := 118140960795 + 3287220 * 2 ^ 59
def prefixEnd_3287220 : Nat := 4983230072969 + 3 ^ 40 * 3287220 * 2
def baseEnd_3287220 : Nat := 1687923877072733970332357

theorem tailTrace_3287220 : CollatzResearch.WordTrace tailWord_3287220 prefixEnd_3287220 1687923877072733970332357 := by
  unfold tailWord_3287220
  simp only [CollatzResearch.WordTrace]
  refine ⟨59947381575485413662389557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79929842100647218216519409 59947381575485413662389557)
  ·
    refine ⟨5620067022701757530849021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59947381575485413662389557 5620067022701757530849021)
    ·
      refine ⟨2107525133513159074068383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5620067022701757530849021 2107525133513159074068383)
      ·
        refine ⟨3161287700269738611102575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2107525133513159074068383 3161287700269738611102575)
        ·
          refine ⟨4741931550404607916653863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3161287700269738611102575 4741931550404607916653863)
          ·
            refine ⟨7112897325606911874980795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4741931550404607916653863 7112897325606911874980795)
            ·
              refine ⟨10669345988410367812471193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7112897325606911874980795 10669345988410367812471193)
              ·
                refine ⟨8002009491307775859353395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10669345988410367812471193 8002009491307775859353395)
                ·
                  refine ⟨12003014236961663789030093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8002009491307775859353395 12003014236961663789030093)
                  ·
                    refine ⟨4501130338860623920886285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12003014236961663789030093 4501130338860623920886285)
                    ·
                      refine ⟨1687923877072733970332357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4501130338860623920886285 1687923877072733970332357)
                      ·
                        rfl

theorem cell23_3287220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_3287220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287220 prefixEnd_3287220 := by exact prefixLift 3287220
  have htrace : WordTrace (prefixWord ++ tailWord_3287220) baseStart_3287220 baseEnd_3287220 := by
    simpa [prefixWord, tailWord_3287220, baseEnd_3287220] using wordTrace_append hprefix tailTrace_3287220
  have hstable : (prefixWord ++ tailWord_3287220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287220).length < 2 ^ (prefixWord ++ tailWord_3287220).sum := by decide
  have hdescent : baseEnd_3287220 < baseStart_3287220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287230 : List Nat := [4, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2]
def baseStart_3287230 : Nat := 118140960795 + 3287230 * 2 ^ 59
def prefixEnd_3287230 : Nat := 4983230072969 + 3 ^ 40 * 3287230 * 2
def baseEnd_3287230 : Nat := 1687929011879278931207311

theorem tailTrace_3287230 : CollatzResearch.WordTrace tailWord_3287230 prefixEnd_3287230 1687929011879278931207311 := by
  unfold tailWord_3287230
  simp only [CollatzResearch.WordTrace]
  refine ⟨14986890985116824879080393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79930085253956399355095429 14986890985116824879080393)
  ·
    refine ⟨11240168238837618659310295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14986890985116824879080393 11240168238837618659310295)
    ·
      refine ⟨16860252358256427988965443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11240168238837618659310295 16860252358256427988965443)
      ·
        refine ⟨25290378537384641983448165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16860252358256427988965443 25290378537384641983448165)
        ·
          refine ⟨4741945975759620371896531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25290378537384641983448165 4741945975759620371896531)
          ·
            refine ⟨7112918963639430557844797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4741945975759620371896531 7112918963639430557844797)
            ·
              refine ⟨2667344611364786459191799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7112918963639430557844797 2667344611364786459191799)
              ·
                refine ⟨4001016917047179688787699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2667344611364786459191799 4001016917047179688787699)
                ·
                  refine ⟨6001525375570769533181549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4001016917047179688787699 6001525375570769533181549)
                  ·
                    refine ⟨2250572015839038574943081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6001525375570769533181549 2250572015839038574943081)
                    ·
                      refine ⟨1687929011879278931207311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2250572015839038574943081 1687929011879278931207311)
                      ·
                        rfl

theorem cell23_3287230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_3287230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287230 prefixEnd_3287230 := by exact prefixLift 3287230
  have htrace : WordTrace (prefixWord ++ tailWord_3287230) baseStart_3287230 baseEnd_3287230 := by
    simpa [prefixWord, tailWord_3287230, baseEnd_3287230] using wordTrace_append hprefix tailTrace_3287230
  have hstable : (prefixWord ++ tailWord_3287230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287230).length < 2 ^ (prefixWord ++ tailWord_3287230).sum := by decide
  have hdescent : baseEnd_3287230 < baseStart_3287230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287235 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 8]
def baseStart_3287235 : Nat := 118140960795 + 3287235 * 2 ^ 59
def prefixEnd_3287235 : Nat := 4983230072969 + 3 ^ 40 * 3287235 * 2
def baseEnd_3287235 : Nat := 1687931579282551411644787

theorem tailTrace_3287235 : CollatzResearch.WordTrace tailWord_3287235 prefixEnd_3287235 1687931579282551411644787 := by
  unfold tailWord_3287235
  simp only [CollatzResearch.WordTrace]
  refine ⟨119895310245916484886575159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79930206830610989924383439 119895310245916484886575159)
  ·
    refine ⟨179842965368874727329862739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119895310245916484886575159 179842965368874727329862739)
    ·
      refine ⟨269764448053312090994794109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179842965368874727329862739 269764448053312090994794109)
      ·
        refine ⟨101161668019992034123047791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269764448053312090994794109 101161668019992034123047791)
        ·
          refine ⟨151742502029988051184571687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101161668019992034123047791 151742502029988051184571687)
          ·
            refine ⟨227613753044982076776857531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151742502029988051184571687 227613753044982076776857531)
            ·
              refine ⟨341420629567473115165286297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227613753044982076776857531 341420629567473115165286297)
              ·
                refine ⟨256065472175604836373964723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 341420629567473115165286297 256065472175604836373964723)
                ·
                  refine ⟨384098208263407254560947085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256065472175604836373964723 384098208263407254560947085)
                  ·
                    refine ⟨144036828098777720460355157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 384098208263407254560947085 144036828098777720460355157)
                    ·
                      refine ⟨1687931579282551411644787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 144036828098777720460355157 1687931579282551411644787)
                      ·
                        rfl

theorem cell23_3287235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_3287235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287235 prefixEnd_3287235 := by exact prefixLift 3287235
  have htrace : WordTrace (prefixWord ++ tailWord_3287235) baseStart_3287235 baseEnd_3287235 := by
    simpa [prefixWord, tailWord_3287235, baseEnd_3287235] using wordTrace_append hprefix tailTrace_3287235
  have hstable : (prefixWord ++ tailWord_3287235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287235).length < 2 ^ (prefixWord ++ tailWord_3287235).sum := by decide
  have hdescent : baseEnd_3287235 < baseStart_3287235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287260 : List Nat := [2, 2, 5, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_3287260 : Nat := 118140960795 + 3287260 * 2 ^ 59
def prefixEnd_3287260 : Nat := 4983230072969 + 3 ^ 40 * 3287260 * 2
def baseEnd_3287260 : Nat := 1687944416298913813832173

theorem tailTrace_3287260 : CollatzResearch.WordTrace tailWord_3287260 prefixEnd_3287260 1687944416298913813832173 := by
  unfold tailWord_3287260
  simp only [CollatzResearch.WordTrace]
  refine ⟨59948111035412957078117617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79930814713883942770823489 59948111035412957078117617)
  ·
    refine ⟨44961083276559717808588213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59948111035412957078117617 44961083276559717808588213)
    ·
      refine ⟨4215101557177473544555145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44961083276559717808588213 4215101557177473544555145)
      ·
        refine ⟨3161326167883105158416359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4215101557177473544555145 3161326167883105158416359)
        ·
          refine ⟨4741989251824657737624539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3161326167883105158416359 4741989251824657737624539)
          ·
            refine ⟨7112983877736986606436809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4741989251824657737624539 7112983877736986606436809)
            ·
              refine ⟨5334737908302739954827607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7112983877736986606436809 5334737908302739954827607)
              ·
                refine ⟨8002106862454109932241411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5334737908302739954827607 8002106862454109932241411)
                ·
                  refine ⟨12003160293681164898362117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8002106862454109932241411 12003160293681164898362117)
                  ·
                    refine ⟨2250592555065218418442897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12003160293681164898362117 2250592555065218418442897)
                    ·
                      refine ⟨1687944416298913813832173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2250592555065218418442897 1687944416298913813832173)
                      ·
                        rfl

theorem cell23_3287260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_3287260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287260 prefixEnd_3287260 := by exact prefixLift 3287260
  have htrace : WordTrace (prefixWord ++ tailWord_3287260) baseStart_3287260 baseEnd_3287260 := by
    simpa [prefixWord, tailWord_3287260, baseEnd_3287260] using wordTrace_append hprefix tailTrace_3287260
  have hstable : (prefixWord ++ tailWord_3287260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287260).length < 2 ^ (prefixWord ++ tailWord_3287260).sum := by decide
  have hdescent : baseEnd_3287260 < baseStart_3287260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287279 : List Nat := [1, 1, 2, 1, 6, 1, 3, 1, 2, 5]
def baseStart_3287279 : Nat := 118140960795 + 3287279 * 2 ^ 59
def prefixEnd_3287279 : Nat := 4983230072969 + 3 ^ 40 * 3287279 * 2
def baseEnd_3287279 : Nat := 562651390810449746498195

theorem tailTrace_3287279 : CollatzResearch.WordTrace tailWord_3287279 prefixEnd_3287279 562651390810449746498195 := by
  unfold tailWord_3287279
  simp only [CollatzResearch.WordTrace]
  refine ⟨119896915057757080401176891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79931276705171386934117927 119896915057757080401176891)
  ·
    refine ⟨179845372586635620601765337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119896915057757080401176891 179845372586635620601765337)
    ·
      refine ⟨134884029439976715451324003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179845372586635620601765337 134884029439976715451324003)
      ·
        refine ⟨202326044159965073176986005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134884029439976715451324003 202326044159965073176986005)
        ·
          refine ⟨9484033319998362805171219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 202326044159965073176986005 9484033319998362805171219)
          ·
            refine ⟨14226049979997544207756829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9484033319998362805171219 14226049979997544207756829)
            ·
              refine ⟨5334768742499079077908811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14226049979997544207756829 5334768742499079077908811)
              ·
                refine ⟨8002153113748618616863217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5334768742499079077908811 8002153113748618616863217)
                ·
                  refine ⟨6001614835311463962647413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8002153113748618616863217 6001614835311463962647413)
                  ·
                    refine ⟨562651390810449746498195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6001614835311463962647413 562651390810449746498195)
                    ·
                      rfl

theorem cell23_3287279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 5].length) (baseStart_3287279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287279 prefixEnd_3287279 := by exact prefixLift 3287279
  have htrace : WordTrace (prefixWord ++ tailWord_3287279) baseStart_3287279 baseEnd_3287279 := by
    simpa [prefixWord, tailWord_3287279, baseEnd_3287279] using wordTrace_append hprefix tailTrace_3287279
  have hstable : (prefixWord ++ tailWord_3287279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287279).length < 2 ^ (prefixWord ++ tailWord_3287279).sum := by decide
  have hdescent : baseEnd_3287279 < baseStart_3287279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287299 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 4, 4, 2]
def baseStart_3287299 : Nat := 118140960795 + 3287299 * 2 ^ 59
def prefixEnd_3287299 : Nat := 4983230072969 + 3 ^ 40 * 3287299 * 2
def baseEnd_3287299 : Nat := 1687964442044439161244493

theorem tailTrace_3287299 : CollatzResearch.WordTrace tailWord_3287299 prefixEnd_3287299 1687964442044439161244493 := by
  unfold tailWord_3287299
  simp only [CollatzResearch.WordTrace]
  refine ⟨119897644517684623816904951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79931763011789749211269967 119897644517684623816904951)
  ·
    refine ⟨179846466776526935725357427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119897644517684623816904951 179846466776526935725357427)
    ·
      refine ⟨269769700164790403588036141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179846466776526935725357427 269769700164790403588036141)
      ·
        refine ⟨101163637561796401345513553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269769700164790403588036141 101163637561796401345513553)
        ·
          refine ⟨75872728171347301009135165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101163637561796401345513553 75872728171347301009135165)
          ·
            refine ⟨28452273064255237878425687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75872728171347301009135165 28452273064255237878425687)
            ·
              refine ⟨42678409596382856817638531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28452273064255237878425687 42678409596382856817638531)
              ·
                refine ⟨64017614394574285226457797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42678409596382856817638531 64017614394574285226457797)
                ·
                  refine ⟨12003302698982678479960837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64017614394574285226457797 12003302698982678479960837)
                  ·
                    refine ⟨2250619256059252214992657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12003302698982678479960837 2250619256059252214992657)
                    ·
                      refine ⟨1687964442044439161244493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2250619256059252214992657 1687964442044439161244493)
                      ·
                        rfl

theorem cell23_3287299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 4, 2].length) (baseStart_3287299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287299 prefixEnd_3287299 := by exact prefixLift 3287299
  have htrace : WordTrace (prefixWord ++ tailWord_3287299) baseStart_3287299 baseEnd_3287299 := by
    simpa [prefixWord, tailWord_3287299, baseEnd_3287299] using wordTrace_append hprefix tailTrace_3287299
  have hstable : (prefixWord ++ tailWord_3287299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287299).length < 2 ^ (prefixWord ++ tailWord_3287299).sum := by decide
  have hdescent : baseEnd_3287299 < baseStart_3287299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287319 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 3]
def baseStart_3287319 : Nat := 118140960795 + 3287319 * 2 ^ 59
def prefixEnd_3287319 : Nat := 4983230072969 + 3 ^ 40 * 3287319 * 2
def baseEnd_3287319 : Nat := 1687974711657529082994401

theorem tailTrace_3287319 : CollatzResearch.WordTrace tailWord_3287319 prefixEnd_3287319 1687974711657529082994401 := by
  unfold tailWord_3287319
  simp only [CollatzResearch.WordTrace]
  refine ⟨119898373977612167232633011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79932249318408111488422007 119898373977612167232633011)
  ·
    refine ⟨179847560966418250848949517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119898373977612167232633011 179847560966418250848949517)
    ·
      refine ⟨67442835362406844068356069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179847560966418250848949517 67442835362406844068356069)
      ·
        refine ⟨12645531630451283262816763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67442835362406844068356069 12645531630451283262816763)
        ·
          refine ⟨18968297445676924894225145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12645531630451283262816763 18968297445676924894225145)
          ·
            refine ⟨14226223084257693670668859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18968297445676924894225145 14226223084257693670668859)
            ·
              refine ⟨21339334626386540506003289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14226223084257693670668859 21339334626386540506003289)
              ·
                refine ⟨16004500969789905379502467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21339334626386540506003289 16004500969789905379502467)
                ·
                  refine ⟨24006751454684858069253701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16004500969789905379502467 24006751454684858069253701)
                  ·
                    refine ⟨4501265897753410887985069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24006751454684858069253701 4501265897753410887985069)
                    ·
                      refine ⟨1687974711657529082994401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4501265897753410887985069 1687974711657529082994401)
                      ·
                        rfl

theorem cell23_3287319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_3287319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287319 prefixEnd_3287319 := by exact prefixLift 3287319
  have htrace : WordTrace (prefixWord ++ tailWord_3287319) baseStart_3287319 baseEnd_3287319 := by
    simpa [prefixWord, tailWord_3287319, baseEnd_3287319] using wordTrace_append hprefix tailTrace_3287319
  have hstable : (prefixWord ++ tailWord_3287319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287319).length < 2 ^ (prefixWord ++ tailWord_3287319).sum := by decide
  have hdescent : baseEnd_3287319 < baseStart_3287319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287399 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 3, 6]
def baseStart_3287399 : Nat := 118140960795 + 3287399 * 2 ^ 59
def prefixEnd_3287399 : Nat := 4983230072969 + 3 ^ 40 * 3287399 * 2
def baseEnd_3287399 : Nat := 562671930036629589998011

theorem tailTrace_3287399 : CollatzResearch.WordTrace tailWord_3287399 prefixEnd_3287399 562671930036629589998011 := by
  unfold tailWord_3287399
  simp only [CollatzResearch.WordTrace]
  refine ⟨119901291817322340895545251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79934194544881560597030167 119901291817322340895545251)
  ·
    refine ⟨179851937725983511343317877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119901291817322340895545251 179851937725983511343317877)
    ·
      refine ⟨16861119161810954188436051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179851937725983511343317877 16861119161810954188436051)
      ·
        refine ⟨25291678742716431282654077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16861119161810954188436051 25291678742716431282654077)
        ·
          refine ⟨9484379528518661730995279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25291678742716431282654077 9484379528518661730995279)
          ·
            refine ⟨14226569292777992596492919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9484379528518661730995279 14226569292777992596492919)
            ·
              refine ⟨21339853939166988894739379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14226569292777992596492919 21339853939166988894739379)
              ·
                refine ⟨32009780908750483342109069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21339853939166988894739379 32009780908750483342109069)
                ·
                  refine ⟨12003667840781431253290901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32009780908750483342109069 12003667840781431253290901)
                  ·
                    refine ⟨562671930036629589998011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12003667840781431253290901 562671930036629589998011)
                    ·
                      rfl

theorem cell23_3287399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_3287399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287399 prefixEnd_3287399 := by exact prefixLift 3287399
  have htrace : WordTrace (prefixWord ++ tailWord_3287399) baseStart_3287399 baseEnd_3287399 := by
    simpa [prefixWord, tailWord_3287399, baseEnd_3287399] using wordTrace_append hprefix tailTrace_3287399
  have hstable : (prefixWord ++ tailWord_3287399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287399).length < 2 ^ (prefixWord ++ tailWord_3287399).sum := by decide
  have hdescent : baseEnd_3287399 < baseStart_3287399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287436 : List Nat := [2, 2, 1, 2, 1, 5, 2, 1, 1, 2, 4]
def baseStart_3287436 : Nat := 118140960795 + 3287436 * 2 ^ 59
def prefixEnd_3287436 : Nat := 4983230072969 + 3 ^ 40 * 3287436 * 2
def baseEnd_3287436 : Nat := 1688034788894105125231363

theorem tailTrace_3287436 : CollatzResearch.WordTrace tailWord_3287436 prefixEnd_3287436 1688034788894105125231363 := by
  unfold tailWord_3287436
  simp only [CollatzResearch.WordTrace]
  refine ⟨59951320659094148107321081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79935094212125530809761441 59951320659094148107321081)
  ·
    refine ⟨44963490494320611080490811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59951320659094148107321081 44963490494320611080490811)
    ·
      refine ⟨67445235741480916620736217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44963490494320611080490811 67445235741480916620736217)
      ·
        refine ⟨50583926806110687465552163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67445235741480916620736217 50583926806110687465552163)
        ·
          refine ⟨75875890209166031198328245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50583926806110687465552163 75875890209166031198328245)
          ·
            refine ⟨7113364707109315424843273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75875890209166031198328245 7113364707109315424843273)
            ·
              refine ⟨5335023530331986568632455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7113364707109315424843273 5335023530331986568632455)
              ·
                refine ⟨8002535295497979852948683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5335023530331986568632455 8002535295497979852948683)
                ·
                  refine ⟨12003802943246969779423025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8002535295497979852948683 12003802943246969779423025)
                  ·
                    refine ⟨9002852207435227334567269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12003802943246969779423025 9002852207435227334567269)
                    ·
                      refine ⟨1688034788894105125231363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9002852207435227334567269 1688034788894105125231363)
                      ·
                        rfl

theorem cell23_3287436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_3287436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287436 prefixEnd_3287436 := by exact prefixLift 3287436
  have htrace : WordTrace (prefixWord ++ tailWord_3287436) baseStart_3287436 baseEnd_3287436 := by
    simpa [prefixWord, tailWord_3287436, baseEnd_3287436] using wordTrace_append hprefix tailTrace_3287436
  have hstable : (prefixWord ++ tailWord_3287436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287436).length < 2 ^ (prefixWord ++ tailWord_3287436).sum := by decide
  have hdescent : baseEnd_3287436 < baseStart_3287436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287456 : List Nat := [2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 3]
def baseStart_3287456 : Nat := 118140960795 + 3287456 * 2 ^ 59
def prefixEnd_3287456 : Nat := 4983230072969 + 3 ^ 40 * 3287456 * 2
def baseEnd_3287456 : Nat := 1688045058507195046981271

theorem tailTrace_3287456 : CollatzResearch.WordTrace tailWord_3287456 prefixEnd_3287456 1688045058507195046981271 := by
  unfold tailWord_3287456
  simp only [CollatzResearch.WordTrace]
  refine ⟨59951685389057919815185111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79935580518743893086913481 59951685389057919815185111)
  ·
    refine ⟨89927528083586879722777667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59951685389057919815185111 89927528083586879722777667)
    ·
      refine ⟨134891292125380319584166501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89927528083586879722777667 134891292125380319584166501)
      ·
        refine ⟨25292117273508809922031219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134891292125380319584166501 25292117273508809922031219)
        ·
          refine ⟨37938175910263214883046829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25292117273508809922031219 37938175910263214883046829)
          ·
            refine ⟨14226815966348705581142561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37938175910263214883046829 14226815966348705581142561)
            ·
              refine ⟨10670111974761529185856921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14226815966348705581142561 10670111974761529185856921)
              ·
                refine ⟨8002583981071146889392691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10670111974761529185856921 8002583981071146889392691)
                ·
                  refine ⟨12003875971606720334089037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8002583981071146889392691 12003875971606720334089037)
                  ·
                    refine ⟨4501453489352520125283389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12003875971606720334089037 4501453489352520125283389)
                    ·
                      refine ⟨1688045058507195046981271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4501453489352520125283389 1688045058507195046981271)
                      ·
                        rfl

theorem cell23_3287456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_3287456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287456 prefixEnd_3287456 := by exact prefixLift 3287456
  have htrace : WordTrace (prefixWord ++ tailWord_3287456) baseStart_3287456 baseEnd_3287456 := by
    simpa [prefixWord, tailWord_3287456, baseEnd_3287456] using wordTrace_append hprefix tailTrace_3287456
  have hstable : (prefixWord ++ tailWord_3287456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287456).length < 2 ^ (prefixWord ++ tailWord_3287456).sum := by decide
  have hdescent : baseEnd_3287456 < baseStart_3287456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287457 : List Nat := [1, 2, 3, 5, 1, 2, 2, 1, 1, 1, 4]
def baseStart_3287457 : Nat := 118140960795 + 3287457 * 2 ^ 59
def prefixEnd_3287457 : Nat := 4983230072969 + 3 ^ 40 * 3287457 * 2
def baseEnd_3287457 : Nat := 1688045571987849543068767

theorem tailTrace_3287457 : CollatzResearch.WordTrace tailWord_3287457 prefixEnd_3287457 1688045571987849543068767 := by
  unfold tailWord_3287457
  simp only [CollatzResearch.WordTrace]
  refine ⟨119903407251112216801156625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79935604834074811200771083 119903407251112216801156625)
  ·
    refine ⟨89927555438334162600867469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119903407251112216801156625 89927555438334162600867469)
    ·
      refine ⟨33722833289375310975325301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89927555438334162600867469 33722833289375310975325301)
      ·
        refine ⟨3161515620878935403936747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33722833289375310975325301 3161515620878935403936747)
        ·
          refine ⟨4742273431318403105905121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3161515620878935403936747 4742273431318403105905121)
          ·
            refine ⟨3556705073488802329428841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4742273431318403105905121 3556705073488802329428841)
            ·
              refine ⟨2667528805116601747071631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3556705073488802329428841 2667528805116601747071631)
              ·
                refine ⟨4001293207674902620607447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2667528805116601747071631 4001293207674902620607447)
                ·
                  refine ⟨6001939811512353930911171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4001293207674902620607447 6001939811512353930911171)
                  ·
                    refine ⟨9002909717268530896366757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6001939811512353930911171 9002909717268530896366757)
                    ·
                      refine ⟨1688045571987849543068767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9002909717268530896366757 1688045571987849543068767)
                      ·
                        rfl

theorem cell23_3287457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_3287457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287457 prefixEnd_3287457 := by exact prefixLift 3287457
  have htrace : WordTrace (prefixWord ++ tailWord_3287457) baseStart_3287457 baseEnd_3287457 := by
    simpa [prefixWord, tailWord_3287457, baseEnd_3287457] using wordTrace_append hprefix tailTrace_3287457
  have hstable : (prefixWord ++ tailWord_3287457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287457).length < 2 ^ (prefixWord ++ tailWord_3287457).sum := by decide
  have hdescent : baseEnd_3287457 < baseStart_3287457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287473 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 4, 1, 3]
def baseStart_3287473 : Nat := 118140960795 + 3287473 * 2 ^ 59
def prefixEnd_3287473 : Nat := 4983230072969 + 3 ^ 40 * 3287473 * 2
def baseEnd_3287473 : Nat := 1688053787678321480468693

theorem tailTrace_3287473 : CollatzResearch.WordTrace tailWord_3287473 prefixEnd_3287473 1688053787678321480468693 := by
  unfold tailWord_3287473
  simp only [CollatzResearch.WordTrace]
  refine ⟨119903990819054251533739073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79935993879369501022492715 119903990819054251533739073)
  ·
    refine ⟨89927993114290688650304305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119903990819054251533739073 89927993114290688650304305)
    ·
      refine ⟨67445994835718016487728229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89927993114290688650304305 67445994835718016487728229)
      ·
        refine ⟨12646124031697128091449043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67445994835718016487728229 12646124031697128091449043)
        ·
          refine ⟨18969186047545692137173565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12646124031697128091449043 18969186047545692137173565)
          ·
            refine ⟨7113444767829634551440087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18969186047545692137173565 7113444767829634551440087)
            ·
              refine ⟨10670167151744451827160131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7113444767829634551440087 10670167151744451827160131)
              ·
                refine ⟨16005250727616677740740197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10670167151744451827160131 16005250727616677740740197)
                ·
                  refine ⟨3000984511428127076388787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16005250727616677740740197 3000984511428127076388787)
                  ·
                    refine ⟨4501476767142190614583181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3000984511428127076388787 4501476767142190614583181)
                    ·
                      refine ⟨1688053787678321480468693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4501476767142190614583181 1688053787678321480468693)
                      ·
                        rfl

theorem cell23_3287473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_3287473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287473 prefixEnd_3287473 := by exact prefixLift 3287473
  have htrace : WordTrace (prefixWord ++ tailWord_3287473) baseStart_3287473 baseEnd_3287473 := by
    simpa [prefixWord, tailWord_3287473, baseEnd_3287473] using wordTrace_append hprefix tailTrace_3287473
  have hstable : (prefixWord ++ tailWord_3287473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287473).length < 2 ^ (prefixWord ++ tailWord_3287473).sum := by decide
  have hdescent : baseEnd_3287473 < baseStart_3287473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287499 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 5]
def baseStart_3287499 : Nat := 118140960795 + 3287499 * 2 ^ 59
def prefixEnd_3287499 : Nat := 4983230072969 + 3 ^ 40 * 3287499 * 2
def baseEnd_3287499 : Nat := 1688067138175338378743573

theorem tailTrace_3287499 : CollatzResearch.WordTrace tailWord_3287499 prefixEnd_3287499 1688067138175338378743573 := by
  unfold tailWord_3287499
  simp only [CollatzResearch.WordTrace]
  refine ⟨119904939116960057974185551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79936626077973371982790367 119904939116960057974185551)
  ·
    refine ⟨179857408675440086961278327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119904939116960057974185551 179857408675440086961278327)
    ·
      refine ⟨269786113013160130441917491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179857408675440086961278327 269786113013160130441917491)
      ·
        refine ⟨404679169519740195662876237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269786113013160130441917491 404679169519740195662876237)
        ·
          refine ⟨151754688569902573373578589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 404679169519740195662876237 151754688569902573373578589)
          ·
            refine ⟨56908008213713465015091971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151754688569902573373578589 56908008213713465015091971)
            ·
              refine ⟨85362012320570197522637957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56908008213713465015091971 85362012320570197522637957)
              ·
                refine ⟨16005377310106912035494617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85362012320570197522637957 16005377310106912035494617)
                ·
                  refine ⟨12004032982580184026620963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16005377310106912035494617 12004032982580184026620963)
                  ·
                    refine ⟨18006049473870276039931445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12004032982580184026620963 18006049473870276039931445)
                    ·
                      refine ⟨1688067138175338378743573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18006049473870276039931445 1688067138175338378743573)
                      ·
                        rfl

theorem cell23_3287499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 5].length) (baseStart_3287499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287499 prefixEnd_3287499 := by exact prefixLift 3287499
  have htrace : WordTrace (prefixWord ++ tailWord_3287499) baseStart_3287499 baseEnd_3287499 := by
    simpa [prefixWord, tailWord_3287499, baseEnd_3287499] using wordTrace_append hprefix tailTrace_3287499
  have hstable : (prefixWord ++ tailWord_3287499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287499).length < 2 ^ (prefixWord ++ tailWord_3287499).sum := by decide
  have hdescent : baseEnd_3287499 < baseStart_3287499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287513 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 6, 2, 2]
def baseStart_3287513 : Nat := 118140960795 + 3287513 * 2 ^ 59
def prefixEnd_3287513 : Nat := 4983230072969 + 3 ^ 40 * 3287513 * 2
def baseEnd_3287513 : Nat := 1688074326904501323968509

theorem tailTrace_3287513 : CollatzResearch.WordTrace tailWord_3287513 prefixEnd_3287513 1688074326904501323968509 := by
  unfold tailWord_3287513
  simp only [CollatzResearch.WordTrace]
  refine ⟨119905449738909338365195193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79936966492606225576796795 119905449738909338365195193)
  ·
    refine ⟨89929087304182003773896395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119905449738909338365195193 89929087304182003773896395)
    ·
      refine ⟨134893630956273005660844593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89929087304182003773896395 134893630956273005660844593)
      ·
        refine ⟨101170223217204754245633445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134893630956273005660844593 101170223217204754245633445)
        ·
          refine ⟨18969416853225891421056271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101170223217204754245633445 18969416853225891421056271)
          ·
            refine ⟨28454125279838837131584407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18969416853225891421056271 28454125279838837131584407)
            ·
              refine ⟨42681187919758255697376611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28454125279838837131584407 42681187919758255697376611)
              ·
                refine ⟨64021781879637383546064917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42681187919758255697376611 64021781879637383546064917)
                ·
                  refine ⟨3001021025608002353721793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64021781879637383546064917 3001021025608002353721793)
                  ·
                    refine ⟨2250765769206001765291345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3001021025608002353721793 2250765769206001765291345)
                    ·
                      refine ⟨1688074326904501323968509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2250765769206001765291345 1688074326904501323968509)
                      ·
                        rfl

theorem cell23_3287513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 2, 2].length) (baseStart_3287513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287513 prefixEnd_3287513 := by exact prefixLift 3287513
  have htrace : WordTrace (prefixWord ++ tailWord_3287513) baseStart_3287513 baseEnd_3287513 := by
    simpa [prefixWord, tailWord_3287513, baseEnd_3287513] using wordTrace_append hprefix tailTrace_3287513
  have hstable : (prefixWord ++ tailWord_3287513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287513).length < 2 ^ (prefixWord ++ tailWord_3287513).sum := by decide
  have hdescent : baseEnd_3287513 < baseStart_3287513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287530 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 4, 2, 2]
def baseStart_3287530 : Nat := 118140960795 + 3287530 * 2 ^ 59
def prefixEnd_3287530 : Nat := 4983230072969 + 3 ^ 40 * 3287530 * 2
def baseEnd_3287530 : Nat := 1688083056075627757455931

theorem tailTrace_3287530 : CollatzResearch.WordTrace tailWord_3287530 prefixEnd_3287530 1688083056075627757455931 := by
  unfold tailWord_3287530
  simp only [CollatzResearch.WordTrace]
  refine ⟨29976517444961937567141011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79937379853231833512376029 29976517444961937567141011)
  ·
    refine ⟨44964776167442906350711517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29976517444961937567141011 44964776167442906350711517)
    ·
      refine ⟨16861791062791089881516819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44964776167442906350711517 16861791062791089881516819)
      ·
        refine ⟨25292686594186634822275229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16861791062791089881516819 25292686594186634822275229)
        ·
          refine ⟨9484757472819988058353211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25292686594186634822275229 9484757472819988058353211)
          ·
            refine ⟨14227136209229982087529817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9484757472819988058353211 14227136209229982087529817)
            ·
              refine ⟨10670352156922486565647363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14227136209229982087529817 10670352156922486565647363)
              ·
                refine ⟨16005528235383729848471045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10670352156922486565647363 16005528235383729848471045)
                ·
                  refine ⟨3001036544134449346588321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16005528235383729848471045 3001036544134449346588321)
                  ·
                    refine ⟨2250777408100837009941241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3001036544134449346588321 2250777408100837009941241)
                    ·
                      refine ⟨1688083056075627757455931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2250777408100837009941241 1688083056075627757455931)
                      ·
                        rfl

theorem cell23_3287530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_3287530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287530 prefixEnd_3287530 := by exact prefixLift 3287530
  have htrace : WordTrace (prefixWord ++ tailWord_3287530) baseStart_3287530 baseEnd_3287530 := by
    simpa [prefixWord, tailWord_3287530, baseEnd_3287530] using wordTrace_append hprefix tailTrace_3287530
  have hstable : (prefixWord ++ tailWord_3287530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287530).length < 2 ^ (prefixWord ++ tailWord_3287530).sum := by decide
  have hdescent : baseEnd_3287530 < baseStart_3287530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287541 : List Nat := [1, 3, 5, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_3287541 : Nat := 118140960795 + 3287541 * 2 ^ 59
def prefixEnd_3287541 : Nat := 4983230072969 + 3 ^ 40 * 3287541 * 2
def baseEnd_3287541 : Nat := 1688088704362827214418381

theorem tailTrace_3287541 : CollatzResearch.WordTrace tailWord_3287541 prefixEnd_3287541 1688088704362827214418381 := by
  unfold tailWord_3287541
  simp only [CollatzResearch.WordTrace]
  refine ⟨119906470982807899147214477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79937647321871932764809651 119906470982807899147214477)
  ·
    refine ⟨44964926618552962180205429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119906470982807899147214477 44964926618552962180205429)
    ·
      refine ⟨4215461870489340204394259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44964926618552962180205429 4215461870489340204394259)
      ·
        refine ⟨6323192805734010306591389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4215461870489340204394259 6323192805734010306591389)
        ·
          refine ⟨2371197302150253864971771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6323192805734010306591389 2371197302150253864971771)
          ·
            refine ⟨3556795953225380797457657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2371197302150253864971771 3556795953225380797457657)
            ·
              refine ⟨2667596964919035598093243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3556795953225380797457657 2667596964919035598093243)
              ·
                refine ⟨4001395447378553397139865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2667596964919035598093243 4001395447378553397139865)
                ·
                  refine ⟨3001046585533915047854899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4001395447378553397139865 3001046585533915047854899)
                  ·
                    refine ⟨4501569878300872571782349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3001046585533915047854899 4501569878300872571782349)
                    ·
                      refine ⟨1688088704362827214418381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4501569878300872571782349 1688088704362827214418381)
                      ·
                        rfl

theorem cell23_3287541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_3287541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287541 prefixEnd_3287541 := by exact prefixLift 3287541
  have htrace : WordTrace (prefixWord ++ tailWord_3287541) baseStart_3287541 baseEnd_3287541 := by
    simpa [prefixWord, tailWord_3287541, baseEnd_3287541] using wordTrace_append hprefix tailTrace_3287541
  have hstable : (prefixWord ++ tailWord_3287541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287541).length < 2 ^ (prefixWord ++ tailWord_3287541).sum := by decide
  have hdescent : baseEnd_3287541 < baseStart_3287541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287576 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 1, 2, 5]
def baseStart_3287576 : Nat := 118140960795 + 3287576 * 2 ^ 59
def prefixEnd_3287576 : Nat := 4983230072969 + 3 ^ 40 * 3287576 * 2
def baseEnd_3287576 : Nat := 1688106676185734577480719

theorem tailTrace_3287576 : CollatzResearch.WordTrace tailWord_3287576 prefixEnd_3287576 1688106676185734577480719 := by
  unfold tailWord_3287576
  simp only [CollatzResearch.WordTrace]
  refine ⟨59953873768840550062369291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79938498358454066749825721 59953873768840550062369291)
  ·
    refine ⟨89930810653260825093553937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59953873768840550062369291 89930810653260825093553937)
    ·
      refine ⟨67448107989945618820165453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89930810653260825093553937 67448107989945618820165453)
      ·
        refine ⟨25293040496229607057562045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67448107989945618820165453 25293040496229607057562045)
        ·
          refine ⟨9484890186086102646585767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25293040496229607057562045 9484890186086102646585767)
          ·
            refine ⟨14227335279129153969878651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9484890186086102646585767 14227335279129153969878651)
            ·
              refine ⟨21341002918693730954817977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14227335279129153969878651 21341002918693730954817977)
              ·
                refine ⟨16005752189020298216113483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21341002918693730954817977 16005752189020298216113483)
                ·
                  refine ⟨24008628283530447324170225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16005752189020298216113483 24008628283530447324170225)
                  ·
                    refine ⟨18006471212647835493127669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24008628283530447324170225 18006471212647835493127669)
                    ·
                      refine ⟨1688106676185734577480719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18006471212647835493127669 1688106676185734577480719)
                      ·
                        rfl

theorem cell23_3287576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_3287576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287576 prefixEnd_3287576 := by exact prefixLift 3287576
  have htrace : WordTrace (prefixWord ++ tailWord_3287576) baseStart_3287576 baseEnd_3287576 := by
    simpa [prefixWord, tailWord_3287576, baseEnd_3287576] using wordTrace_append hprefix tailTrace_3287576
  have hstable : (prefixWord ++ tailWord_3287576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287576).length < 2 ^ (prefixWord ++ tailWord_3287576).sum := by decide
  have hdescent : baseEnd_3287576 < baseStart_3287576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287586 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_3287586 : Nat := 118140960795 + 3287586 * 2 ^ 59
def prefixEnd_3287586 : Nat := 4983230072969 + 3 ^ 40 * 3287586 * 2
def baseEnd_3287586 : Nat := 1688111810992279538355673

theorem tailTrace_3287586 : CollatzResearch.WordTrace tailWord_3287586 prefixEnd_3287586 1688111810992279538355673 := by
  unfold tailWord_3287586
  simp only [CollatzResearch.WordTrace]
  refine ⟨29977028066911217958150653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79938741511763247888401741 29977028066911217958150653)
  ·
    refine ⟨11241385525091706734306495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29977028066911217958150653 11241385525091706734306495)
    ·
      refine ⟨16862078287637560101459743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11241385525091706734306495 16862078287637560101459743)
      ·
        refine ⟨25293117431456340152189615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16862078287637560101459743 25293117431456340152189615)
        ·
          refine ⟨37939676147184510228284423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25293117431456340152189615 37939676147184510228284423)
          ·
            refine ⟨56909514220776765342426635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37939676147184510228284423 56909514220776765342426635)
            ·
              refine ⟨85364271331165148013639953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56909514220776765342426635 85364271331165148013639953)
              ·
                refine ⟨64023203498373861010229965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85364271331165148013639953 64023203498373861010229965)
                ·
                  refine ⟨24008701311890197878836237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64023203498373861010229965 24008701311890197878836237)
                  ·
                    refine ⟨9003262991958824204563589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24008701311890197878836237 9003262991958824204563589)
                    ·
                      refine ⟨1688111810992279538355673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9003262991958824204563589 1688111810992279538355673)
                      ·
                        rfl

theorem cell23_3287586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_3287586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287586 prefixEnd_3287586 := by exact prefixLift 3287586
  have htrace : WordTrace (prefixWord ++ tailWord_3287586) baseStart_3287586 baseEnd_3287586 := by
    simpa [prefixWord, tailWord_3287586, baseEnd_3287586] using wordTrace_append hprefix tailTrace_3287586
  have hstable : (prefixWord ++ tailWord_3287586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287586).length < 2 ^ (prefixWord ++ tailWord_3287586).sum := by decide
  have hdescent : baseEnd_3287586 < baseStart_3287586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287596 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 7, 4]
def baseStart_3287596 : Nat := 118140960795 + 3287596 * 2 ^ 59
def prefixEnd_3287596 : Nat := 4983230072969 + 3 ^ 40 * 3287596 * 2
def baseEnd_3287596 : Nat := 562705648599608166410209

theorem tailTrace_3287596 : CollatzResearch.WordTrace tailWord_3287596 prefixEnd_3287596 562705648599608166410209 := by
  unfold tailWord_3287596
  simp only [CollatzResearch.WordTrace]
  refine ⟨59954238498804321770233321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79938984665072429026977761 59954238498804321770233321)
  ·
    refine ⟨44965678874103241327674991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59954238498804321770233321 44965678874103241327674991)
    ·
      refine ⟨67448518311154861991512487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44965678874103241327674991 67448518311154861991512487)
      ·
        refine ⟨101172777466732292987268731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67448518311154861991512487 101172777466732292987268731)
        ·
          refine ⟨151759166200098439480903097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101172777466732292987268731 151759166200098439480903097)
          ·
            refine ⟨113819374650073829610677323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151759166200098439480903097 113819374650073829610677323)
            ·
              refine ⟨170729061975110744416015985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113819374650073829610677323 170729061975110744416015985)
              ·
                refine ⟨128046796481333058312011989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170729061975110744416015985 128046796481333058312011989)
                ·
                  refine ⟨3001096792531243554187781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 128046796481333058312011989 3001096792531243554187781)
                  ·
                    refine ⟨562705648599608166410209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3001096792531243554187781 562705648599608166410209)
                    ·
                      rfl

theorem cell23_3287596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_3287596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287596 prefixEnd_3287596 := by exact prefixLift 3287596
  have htrace : WordTrace (prefixWord ++ tailWord_3287596) baseStart_3287596 baseEnd_3287596 := by
    simpa [prefixWord, tailWord_3287596, baseEnd_3287596] using wordTrace_append hprefix tailTrace_3287596
  have hstable : (prefixWord ++ tailWord_3287596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287596).length < 2 ^ (prefixWord ++ tailWord_3287596).sum := by decide
  have hdescent : baseEnd_3287596 < baseStart_3287596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287603 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 2, 4, 2]
def baseStart_3287603 : Nat := 118140960795 + 3287603 * 2 ^ 59
def prefixEnd_3287603 : Nat := 4983230072969 + 3 ^ 40 * 3287603 * 2
def baseEnd_3287603 : Nat := 1688120540163405971843095

theorem tailTrace_3287603 : CollatzResearch.WordTrace tailWord_3287603 prefixEnd_3287603 1688120540163405971843095 := by
  unfold tailWord_3287603
  simp only [CollatzResearch.WordTrace]
  refine ⟨119908732308583283735971463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79939154872388855823980975 119908732308583283735971463)
  ·
    refine ⟨179863098462874925603957195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119908732308583283735971463 179863098462874925603957195)
    ·
      refine ⟨269794647694312388405935793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179863098462874925603957195 269794647694312388405935793)
      ·
        refine ⟨202345985770734291304451845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269794647694312388405935793 202345985770734291304451845)
        ·
          refine ⟨37939872332012679619584721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202345985770734291304451845 37939872332012679619584721)
          ·
            refine ⟨28454904249009509714688541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37939872332012679619584721 28454904249009509714688541)
            ·
              refine ⟨10670589093378566143008203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28454904249009509714688541 10670589093378566143008203)
              ·
                refine ⟨16005883640067849214512305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10670589093378566143008203 16005883640067849214512305)
                ·
                  refine ⟨12004412730050886910884229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16005883640067849214512305 12004412730050886910884229)
                  ·
                    refine ⟨2250827386884541295790793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12004412730050886910884229 2250827386884541295790793)
                    ·
                      refine ⟨1688120540163405971843095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2250827386884541295790793 1688120540163405971843095)
                      ·
                        rfl

theorem cell23_3287603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 4, 2].length) (baseStart_3287603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287603 prefixEnd_3287603 := by exact prefixLift 3287603
  have htrace : WordTrace (prefixWord ++ tailWord_3287603) baseStart_3287603 baseEnd_3287603 := by
    simpa [prefixWord, tailWord_3287603, baseEnd_3287603] using wordTrace_append hprefix tailTrace_3287603
  have hstable : (prefixWord ++ tailWord_3287603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287603).length < 2 ^ (prefixWord ++ tailWord_3287603).sum := by decide
  have hdescent : baseEnd_3287603 < baseStart_3287603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287613 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 5, 4]
def baseStart_3287613 : Nat := 118140960795 + 3287613 * 2 ^ 59
def prefixEnd_3287613 : Nat := 4983230072969 + 3 ^ 40 * 3287613 * 2
def baseEnd_3287613 : Nat := 562708558323316977572683

theorem tailTrace_3287613 : CollatzResearch.WordTrace tailWord_3287613 prefixEnd_3287613 562708558323316977572683 := by
  unfold tailWord_3287613
  simp only [CollatzResearch.WordTrace]
  refine ⟨119909097038547055443835493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79939398025698036962556995 119909097038547055443835493)
  ·
    refine ⟨22482955694727572895719155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119909097038547055443835493 22482955694727572895719155)
    ·
      refine ⟨33724433542091359343578733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22482955694727572895719155 33724433542091359343578733)
      ·
        refine ⟨12646662578284259753842025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33724433542091359343578733 12646662578284259753842025)
        ·
          refine ⟨9484996933713194815381519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12646662578284259753842025 9484996933713194815381519)
          ·
            refine ⟨14227495400569792223072279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9484996933713194815381519 14227495400569792223072279)
            ·
              refine ⟨21341243100854688334608419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14227495400569792223072279 21341243100854688334608419)
              ·
                refine ⟨32011864651282032501912629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21341243100854688334608419 32011864651282032501912629)
                ·
                  refine ⟨3001112311057690547054309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32011864651282032501912629 3001112311057690547054309)
                  ·
                    refine ⟨562708558323316977572683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3001112311057690547054309 562708558323316977572683)
                    ·
                      rfl

theorem cell23_3287613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_3287613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287613 prefixEnd_3287613 := by exact prefixLift 3287613
  have htrace : WordTrace (prefixWord ++ tailWord_3287613) baseStart_3287613 baseEnd_3287613 := by
    simpa [prefixWord, tailWord_3287613, baseEnd_3287613] using wordTrace_append hprefix tailTrace_3287613
  have hstable : (prefixWord ++ tailWord_3287613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287613).length < 2 ^ (prefixWord ++ tailWord_3287613).sum := by decide
  have hdescent : baseEnd_3287613 < baseStart_3287613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287623 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 3]
def baseStart_3287623 : Nat := 118140960795 + 3287623 * 2 ^ 59
def prefixEnd_3287623 : Nat := 4983230072969 + 3 ^ 40 * 3287623 * 2
def baseEnd_3287623 : Nat := 1688130809776495893593003

theorem tailTrace_3287623 : CollatzResearch.WordTrace tailWord_3287623 prefixEnd_3287623 1688130809776495893593003 := by
  unfold tailWord_3287623
  simp only [CollatzResearch.WordTrace]
  refine ⟨119909461768510827151699523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79939641179007218101133015 119909461768510827151699523)
  ·
    refine ⟨179864192652766240727549285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119909461768510827151699523 179864192652766240727549285)
    ·
      refine ⟨33724536122393670136415491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179864192652766240727549285 33724536122393670136415491)
      ·
        refine ⟨50586804183590505204623237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33724536122393670136415491 50586804183590505204623237)
        ·
          refine ⟨9485025784423219725866857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50586804183590505204623237 9485025784423219725866857)
          ·
            refine ⟨7113769338317414794400143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9485025784423219725866857 7113769338317414794400143)
            ·
              refine ⟨10670654007476122191600215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7113769338317414794400143 10670654007476122191600215)
              ·
                refine ⟨16005981011214183287400323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10670654007476122191600215 16005981011214183287400323)
                ·
                  refine ⟨24008971516821274931100485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16005981011214183287400323 24008971516821274931100485)
                  ·
                    refine ⟨4501682159403989049581341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24008971516821274931100485 4501682159403989049581341)
                    ·
                      refine ⟨1688130809776495893593003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4501682159403989049581341 1688130809776495893593003)
                      ·
                        rfl

theorem cell23_3287623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_3287623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287623 prefixEnd_3287623 := by exact prefixLift 3287623
  have htrace : WordTrace (prefixWord ++ tailWord_3287623) baseStart_3287623 baseEnd_3287623 := by
    simpa [prefixWord, tailWord_3287623, baseEnd_3287623] using wordTrace_append hprefix tailTrace_3287623
  have hstable : (prefixWord ++ tailWord_3287623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287623).length < 2 ^ (prefixWord ++ tailWord_3287623).sum := by decide
  have hdescent : baseEnd_3287623 < baseStart_3287623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287630 : List Nat := [4, 1, 1, 1, 1, 2, 3, 5, 1, 4]
def baseStart_3287630 : Nat := 118140960795 + 3287630 * 2 ^ 59
def prefixEnd_3287630 : Nat := 4983230072969 + 3 ^ 40 * 3287630 * 2
def baseEnd_3287630 : Nat := 562711468047025788735157

theorem tailTrace_3287630 : CollatzResearch.WordTrace tailWord_3287630 prefixEnd_3287630 562711468047025788735157 := by
  unfold tailWord_3287630
  simp only [CollatzResearch.WordTrace]
  refine ⟨14988714634935683418400543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79939811386323644898136229 14988714634935683418400543)
  ·
    refine ⟨22483071952403525127600815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14988714634935683418400543 22483071952403525127600815)
    ·
      refine ⟨33724607928605287691401223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22483071952403525127600815 33724607928605287691401223)
      ·
        refine ⟨50586911892907931537101835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33724607928605287691401223 50586911892907931537101835)
        ·
          refine ⟨75880367839361897305652753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50586911892907931537101835 75880367839361897305652753)
          ·
            refine ⟨56910275879521422979239565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75880367839361897305652753 56910275879521422979239565)
            ·
              refine ⟨21341353454820533617214837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56910275879521422979239565 21341353454820533617214837)
              ·
                refine ⟨2000751886389425026613891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21341353454820533617214837 2000751886389425026613891)
                ·
                  refine ⟨3001127829584137539920837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2000751886389425026613891 3001127829584137539920837)
                  ·
                    refine ⟨562711468047025788735157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3001127829584137539920837 562711468047025788735157)
                    ·
                      rfl

theorem cell23_3287630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_3287630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287630 prefixEnd_3287630 := by exact prefixLift 3287630
  have htrace : WordTrace (prefixWord ++ tailWord_3287630) baseStart_3287630 baseEnd_3287630 := by
    simpa [prefixWord, tailWord_3287630, baseEnd_3287630] using wordTrace_append hprefix tailTrace_3287630
  have hstable : (prefixWord ++ tailWord_3287630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287630).length < 2 ^ (prefixWord ++ tailWord_3287630).sum := by decide
  have hdescent : baseEnd_3287630 < baseStart_3287630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287663 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 1, 5, 2]
def baseStart_3287663 : Nat := 118140960795 + 3287663 * 2 ^ 59
def prefixEnd_3287663 : Nat := 4983230072969 + 3 ^ 40 * 3287663 * 2
def baseEnd_3287663 : Nat := 1688151349002675737092819

theorem tailTrace_3287663 : CollatzResearch.WordTrace tailWord_3287663 prefixEnd_3287663 1688151349002675737092819 := by
  unfold tailWord_3287663
  simp only [CollatzResearch.WordTrace]
  refine ⟨119910920688365913983155643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79940613792243942655437095 119910920688365913983155643)
  ·
    refine ⟨179866381032548870974733465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119910920688365913983155643 179866381032548870974733465)
    ·
      refine ⟨134899785774411653231050099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179866381032548870974733465 134899785774411653231050099)
      ·
        refine ⟨202349678661617479846575149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134899785774411653231050099 202349678661617479846575149)
        ·
          refine ⟨75881129498106554942465681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202349678661617479846575149 75881129498106554942465681)
          ·
            refine ⟨56910847123579916206849261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75881129498106554942465681 56910847123579916206849261)
            ·
              refine ⟨21341567671342468577568473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56910847123579916206849261 21341567671342468577568473)
              ·
                refine ⟨16006175753506851433176355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21341567671342468577568473 16006175753506851433176355)
                ·
                  refine ⟨24009263630260277149764533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16006175753506851433176355 24009263630260277149764533)
                  ·
                    refine ⟨2250868465336900982790425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24009263630260277149764533 2250868465336900982790425)
                    ·
                      refine ⟨1688151349002675737092819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2250868465336900982790425 1688151349002675737092819)
                      ·
                        rfl

theorem cell23_3287663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 5, 2].length) (baseStart_3287663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287663 prefixEnd_3287663 := by exact prefixLift 3287663
  have htrace : WordTrace (prefixWord ++ tailWord_3287663) baseStart_3287663 baseEnd_3287663 := by
    simpa [prefixWord, tailWord_3287663, baseEnd_3287663] using wordTrace_append hprefix tailTrace_3287663
  have hstable : (prefixWord ++ tailWord_3287663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287663).length < 2 ^ (prefixWord ++ tailWord_3287663).sum := by decide
  have hdescent : baseEnd_3287663 < baseStart_3287663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287673 : List Nat := [1, 2, 1, 3, 3, 2, 1, 4, 1, 5]
def baseStart_3287673 : Nat := 118140960795 + 3287673 * 2 ^ 59
def prefixEnd_3287673 : Nat := 4983230072969 + 3 ^ 40 * 3287673 * 2
def baseEnd_3287673 : Nat := 562718827936406899322591

theorem tailTrace_3287673 : CollatzResearch.WordTrace tailWord_3287673 prefixEnd_3287673 562718827936406899322591 := by
  unfold tailWord_3287673
  simp only [CollatzResearch.WordTrace]
  refine ⟨119911285418329685691019673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79940856945553123794013115 119911285418329685691019673)
  ·
    refine ⟨89933464063747264268264755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119911285418329685691019673 89933464063747264268264755)
    ·
      refine ⟨134900196095620896402397133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89933464063747264268264755 134900196095620896402397133)
      ·
        refine ⟨50587573535857836150898925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134900196095620896402397133 50587573535857836150898925)
        ·
          refine ⟨18970340075946688556587097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50587573535857836150898925 18970340075946688556587097)
          ·
            refine ⟨14227755056960016417440323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18970340075946688556587097 14227755056960016417440323)
            ·
              refine ⟨21341632585440024626160485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14227755056960016417440323 21341632585440024626160485)
              ·
                refine ⟨4001556109770004617405091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21341632585440024626160485 4001556109770004617405091)
                ·
                  refine ⟨6002334164655006926107637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4001556109770004617405091 6002334164655006926107637)
                  ·
                    refine ⟨562718827936406899322591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6002334164655006926107637 562718827936406899322591)
                    ·
                      rfl

theorem cell23_3287673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 5].length) (baseStart_3287673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287673 prefixEnd_3287673 := by exact prefixLift 3287673
  have htrace : WordTrace (prefixWord ++ tailWord_3287673) baseStart_3287673 baseEnd_3287673 := by
    simpa [prefixWord, tailWord_3287673, baseEnd_3287673] using wordTrace_append hprefix tailTrace_3287673
  have hstable : (prefixWord ++ tailWord_3287673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287673).length < 2 ^ (prefixWord ++ tailWord_3287673).sum := by decide
  have hdescent : baseEnd_3287673 < baseStart_3287673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287703 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 4, 4]
def baseStart_3287703 : Nat := 118140960795 + 3287703 * 2 ^ 59
def prefixEnd_3287703 : Nat := 4983230072969 + 3 ^ 40 * 3287703 * 2
def baseEnd_3287703 : Nat := 562723962742951860197545

theorem tailTrace_3287703 : CollatzResearch.WordTrace tailWord_3287703 prefixEnd_3287703 562723962742951860197545 := by
  unfold tailWord_3287703
  simp only [CollatzResearch.WordTrace]
  refine ⟨119912379608221000814611763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79941586405480667209741175 119912379608221000814611763)
  ·
    refine ⟨179868569412331501221917645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119912379608221000814611763 179868569412331501221917645)
    ·
      refine ⟨67450713529624312958219117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179868569412331501221917645 67450713529624312958219117)
      ·
        refine ⟨25294017573609117359332169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67450713529624312958219117 25294017573609117359332169)
        ·
          refine ⟨18970513180206838019499127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25294017573609117359332169 18970513180206838019499127)
          ·
            refine ⟨28455769770310257029248691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18970513180206838019499127 28455769770310257029248691)
            ·
              refine ⟨42683654655465385543873037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28455769770310257029248691 42683654655465385543873037)
              ·
                refine ⟨16006370495799519578952389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42683654655465385543873037 16006370495799519578952389)
                ·
                  refine ⟨3001194467962409921053573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16006370495799519578952389 3001194467962409921053573)
                  ·
                    refine ⟨562723962742951860197545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3001194467962409921053573 562723962742951860197545)
                    ·
                      rfl

theorem cell23_3287703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_3287703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287703 prefixEnd_3287703 := by exact prefixLift 3287703
  have htrace : WordTrace (prefixWord ++ tailWord_3287703) baseStart_3287703 baseEnd_3287703 := by
    simpa [prefixWord, tailWord_3287703, baseEnd_3287703] using wordTrace_append hprefix tailTrace_3287703
  have hstable : (prefixWord ++ tailWord_3287703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287703).length < 2 ^ (prefixWord ++ tailWord_3287703).sum := by decide
  have hdescent : baseEnd_3287703 < baseStart_3287703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287704 : List Nat := [2, 1, 2, 4, 1, 1, 5, 2, 1, 1, 3]
def baseStart_3287704 : Nat := 118140960795 + 3287704 * 2 ^ 59
def prefixEnd_3287704 : Nat := 4983230072969 + 3 ^ 40 * 3287704 * 2
def baseEnd_3287704 : Nat := 1688172401709510076680131

theorem tailTrace_3287704 : CollatzResearch.WordTrace tailWord_3287704 prefixEnd_3287704 1688172401709510076680131 := by
  unfold tailWord_3287704
  simp only [CollatzResearch.WordTrace]
  refine ⟨59956208040608688992699083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79941610720811585323598777 59956208040608688992699083)
  ·
    refine ⟨89934312060913033489048625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59956208040608688992699083 89934312060913033489048625)
    ·
      refine ⟨67450734045684775116786469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89934312060913033489048625 67450734045684775116786469)
      ·
        refine ⟨12647012633565895334397463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67450734045684775116786469 12647012633565895334397463)
        ·
          refine ⟨18970518950348843001596195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12647012633565895334397463 18970518950348843001596195)
          ·
            refine ⟨28455778425523264502394293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18970518950348843001596195 28455778425523264502394293)
            ·
              refine ⟨2667729227392806047099465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28455778425523264502394293 2667729227392806047099465)
              ·
                refine ⟨2000796920544604535324599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2667729227392806047099465 2000796920544604535324599)
                ·
                  refine ⟨3001195380816906802986899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2000796920544604535324599 3001195380816906802986899)
                  ·
                    refine ⟨4501793071225360204480349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3001195380816906802986899 4501793071225360204480349)
                    ·
                      refine ⟨1688172401709510076680131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4501793071225360204480349 1688172401709510076680131)
                      ·
                        rfl

theorem cell23_3287704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_3287704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287704 prefixEnd_3287704 := by exact prefixLift 3287704
  have htrace : WordTrace (prefixWord ++ tailWord_3287704) baseStart_3287704 baseEnd_3287704 := by
    simpa [prefixWord, tailWord_3287704, baseEnd_3287704] using wordTrace_append hprefix tailTrace_3287704
  have hstable : (prefixWord ++ tailWord_3287704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287704).length < 2 ^ (prefixWord ++ tailWord_3287704).sum := by decide
  have hdescent : baseEnd_3287704 < baseStart_3287704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287710 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_3287710 : Nat := 118140960795 + 3287710 * 2 ^ 59
def prefixEnd_3287710 : Nat := 4983230072969 + 3 ^ 40 * 3287710 * 2
def baseEnd_3287710 : Nat := 1688175482593437053205103

theorem tailTrace_3287710 : CollatzResearch.WordTrace tailWord_3287710 prefixEnd_3287710 1688175482593437053205103 := by
  unfold tailWord_3287710
  simp only [CollatzResearch.WordTrace]
  refine ⟨14989079364899455126264573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79941756612797094006744389 14989079364899455126264573)
  ·
    refine ⟨5620904761837295672349215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14989079364899455126264573 5620904761837295672349215)
    ·
      refine ⟨8431357142755943508523823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5620904761837295672349215 8431357142755943508523823)
      ·
        refine ⟨12647035714133915262785735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8431357142755943508523823 12647035714133915262785735)
        ·
          refine ⟨18970553571200872894178603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12647035714133915262785735 18970553571200872894178603)
          ·
            refine ⟨28455830356801309341267905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18970553571200872894178603 28455830356801309341267905)
            ·
              refine ⟨21341872767600982005950929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28455830356801309341267905 21341872767600982005950929)
              ·
                refine ⟨16006404575700736504463197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21341872767600982005950929 16006404575700736504463197)
                ·
                  refine ⟨6002401715887776189173699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16006404575700736504463197 6002401715887776189173699)
                  ·
                    refine ⟨9003602573831664283760549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6002401715887776189173699 9003602573831664283760549)
                    ·
                      refine ⟨1688175482593437053205103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9003602573831664283760549 1688175482593437053205103)
                      ·
                        rfl

theorem cell23_3287710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_3287710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287710 prefixEnd_3287710 := by exact prefixLift 3287710
  have htrace : WordTrace (prefixWord ++ tailWord_3287710) baseStart_3287710 baseEnd_3287710 := by
    simpa [prefixWord, tailWord_3287710, baseEnd_3287710] using wordTrace_append hprefix tailTrace_3287710
  have hstable : (prefixWord ++ tailWord_3287710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287710).length < 2 ^ (prefixWord ++ tailWord_3287710).sum := by decide
  have hdescent : baseEnd_3287710 < baseStart_3287710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287733 : List Nat := [1, 3, 3, 3, 1, 1, 2, 9]
def baseStart_3287733 : Nat := 118140960795 + 3287733 * 2 ^ 59
def prefixEnd_3287733 : Nat := 4983230072969 + 3 ^ 40 * 3287733 * 2
def baseEnd_3287733 : Nat := 62525455283277424563611

theorem tailTrace_3287733 : CollatzResearch.WordTrace tailWord_3287733 prefixEnd_3287733 62525455283277424563611 := by
  unfold tailWord_3287733
  simp only [CollatzResearch.WordTrace]
  refine ⟨119913473798112315938203853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79942315865408210625469235 119913473798112315938203853)
  ·
    refine ⟨44967552674292118476826445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119913473798112315938203853 44967552674292118476826445)
    ·
      refine ⟨16862832252859544428809917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44967552674292118476826445 16862832252859544428809917)
      ·
        refine ⟨6323562094822329160803719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16862832252859544428809917 6323562094822329160803719)
        ·
          refine ⟨9485343142233493741205579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6323562094822329160803719 9485343142233493741205579)
          ·
            refine ⟨14228014713350240611808369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9485343142233493741205579 14228014713350240611808369)
            ·
              refine ⟨10671011035012680458856277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14228014713350240611808369 10671011035012680458856277)
              ·
                refine ⟨62525455283277424563611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10671011035012680458856277 62525455283277424563611)
                ·
                  rfl

theorem cell23_3287733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 9].length) (baseStart_3287733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287733 prefixEnd_3287733 := by exact prefixLift 3287733
  have htrace : WordTrace (prefixWord ++ tailWord_3287733) baseStart_3287733 baseEnd_3287733 := by
    simpa [prefixWord, tailWord_3287733, baseEnd_3287733] using wordTrace_append hprefix tailTrace_3287733
  have hstable : (prefixWord ++ tailWord_3287733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287733).length < 2 ^ (prefixWord ++ tailWord_3287733).sum := by decide
  have hdescent : baseEnd_3287733 < baseStart_3287733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287743 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 3]
def baseStart_3287743 : Nat := 118140960795 + 3287743 * 2 ^ 59
def prefixEnd_3287743 : Nat := 4983230072969 + 3 ^ 40 * 3287743 * 2
def baseEnd_3287743 : Nat := 1688192427455035424092451

theorem tailTrace_3287743 : CollatzResearch.WordTrace tailWord_3287743 prefixEnd_3287743 1688192427455035424092451 := by
  unfold tailWord_3287743
  simp only [CollatzResearch.WordTrace]
  refine ⟨119913838528076087646067883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79942559018717391764045255 119913838528076087646067883)
  ·
    refine ⟨179870757792114131469101825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119913838528076087646067883 179870757792114131469101825)
    ·
      refine ⟨134903068344085598601826369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179870757792114131469101825 134903068344085598601826369)
      ·
        refine ⟨101177301258064198951369777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134903068344085598601826369 101177301258064198951369777)
        ·
          refine ⟨75882975943548149213527333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101177301258064198951369777 75882975943548149213527333)
          ·
            refine ⟨14228057989415277977536375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75882975943548149213527333 14228057989415277977536375)
            ·
              refine ⟨21342086984122916966304563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14228057989415277977536375 21342086984122916966304563)
              ·
                refine ⟨32013130476184375449456845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21342086984122916966304563 32013130476184375449456845)
                ·
                  refine ⟨12004923928569140793546317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32013130476184375449456845 12004923928569140793546317)
                  ·
                    refine ⟨4501846473213427797579869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12004923928569140793546317 4501846473213427797579869)
                    ·
                      refine ⟨1688192427455035424092451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4501846473213427797579869 1688192427455035424092451)
                      ·
                        rfl

theorem cell23_3287743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_3287743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287743 prefixEnd_3287743 := by exact prefixLift 3287743
  have htrace : WordTrace (prefixWord ++ tailWord_3287743) baseStart_3287743 baseEnd_3287743 := by
    simpa [prefixWord, tailWord_3287743, baseEnd_3287743] using wordTrace_append hprefix tailTrace_3287743
  have hstable : (prefixWord ++ tailWord_3287743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287743).length < 2 ^ (prefixWord ++ tailWord_3287743).sum := by decide
  have hdescent : baseEnd_3287743 < baseStart_3287743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287750 : List Nat := [6, 1, 2, 1, 13]
def baseStart_3287750 : Nat := 118140960795 + 3287750 * 2 ^ 59
def prefixEnd_3287750 : Nat := 4983230072969 + 3 ^ 40 * 3287750 * 2
def baseEnd_3287750 : Nat := 2315769577255990256111

theorem tailTrace_3287750 : CollatzResearch.WordTrace tailWord_3287750 prefixEnd_3287750 2315769577255990256111 := by
  unfold tailWord_3287750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3747315432470335245049147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79942729226033818561048469 3747315432470335245049147)
  ·
    refine ⟨5620973148705502867573721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3747315432470335245049147 5620973148705502867573721)
    ·
      refine ⟨4215729861529127150680291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5620973148705502867573721 4215729861529127150680291)
      ·
        refine ⟨6323594792293690726020437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4215729861529127150680291 6323594792293690726020437)
        ·
          refine ⟨2315769577255990256111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 6323594792293690726020437 2315769577255990256111)
          ·
            rfl

theorem cell23_3287750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 13].length) (baseStart_3287750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287750 prefixEnd_3287750 := by exact prefixLift 3287750
  have htrace : WordTrace (prefixWord ++ tailWord_3287750) baseStart_3287750 baseEnd_3287750 := by
    simpa [prefixWord, tailWord_3287750, baseEnd_3287750] using wordTrace_append hprefix tailTrace_3287750
  have hstable : (prefixWord ++ tailWord_3287750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287750).length < 2 ^ (prefixWord ++ tailWord_3287750).sum := by decide
  have hdescent : baseEnd_3287750 < baseStart_3287750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287770 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2]
def baseStart_3287770 : Nat := 118140960795 + 3287770 * 2 ^ 59
def prefixEnd_3287770 : Nat := 4983230072969 + 3 ^ 40 * 3287770 * 2
def baseEnd_3287770 : Nat := 1688206291432706818454827

theorem tailTrace_3287770 : CollatzResearch.WordTrace tailWord_3287770 prefixEnd_3287770 1688206291432706818454827 := by
  unfold tailWord_3287770
  simp only [CollatzResearch.WordTrace]
  refine ⟨29978705824744567814325191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79943215532652180838200509 29978705824744567814325191)
  ·
    refine ⟨44968058737116851721487787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29978705824744567814325191 44968058737116851721487787)
    ·
      refine ⟨67452088105675277582231681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44968058737116851721487787 67452088105675277582231681)
      ·
        refine ⟨50589066079256458186673761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67452088105675277582231681 50589066079256458186673761)
        ·
          refine ⟨37941799559442343640005321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50589066079256458186673761 37941799559442343640005321)
          ·
            refine ⟨28456349669581757730003991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37941799559442343640005321 28456349669581757730003991)
            ·
              refine ⟨42684524504372636595005987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28456349669581757730003991 42684524504372636595005987)
              ·
                refine ⟨64026786756558954892508981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42684524504372636595005987 64026786756558954892508981)
                ·
                  refine ⟨6002511258427402021172717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64026786756558954892508981 6002511258427402021172717)
                  ·
                    refine ⟨2250941721910275757939769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6002511258427402021172717 2250941721910275757939769)
                    ·
                      refine ⟨1688206291432706818454827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2250941721910275757939769 1688206291432706818454827)
                      ·
                        rfl

theorem cell23_3287770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_3287770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287770 prefixEnd_3287770 := by exact prefixLift 3287770
  have htrace : WordTrace (prefixWord ++ tailWord_3287770) baseStart_3287770 baseEnd_3287770 := by
    simpa [prefixWord, tailWord_3287770, baseEnd_3287770] using wordTrace_append hprefix tailTrace_3287770
  have hstable : (prefixWord ++ tailWord_3287770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287770).length < 2 ^ (prefixWord ++ tailWord_3287770).sum := by decide
  have hdescent : baseEnd_3287770 < baseStart_3287770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287777 : List Nat := [1, 2, 3, 1, 4, 1, 2, 3, 2, 1, 3]
def baseStart_3287777 : Nat := 118140960795 + 3287777 * 2 ^ 59
def prefixEnd_3287777 : Nat := 4983230072969 + 3 ^ 40 * 3287777 * 2
def baseEnd_3287777 : Nat := 1688209885797288291067295

theorem tailTrace_3287777 : CollatzResearch.WordTrace tailWord_3287777 prefixEnd_3287777 1688209885797288291067295 := by
  unfold tailWord_3287777
  simp only [CollatzResearch.WordTrace]
  refine ⟨119915078609952911452805585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79943385739968607635203723 119915078609952911452805585)
  ·
    refine ⟨89936308957464683589604189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119915078609952911452805585 89936308957464683589604189)
    ·
      refine ⟨33726115859049256346101571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89936308957464683589604189 33726115859049256346101571)
      ·
        refine ⟨50589173788573884519152357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33726115859049256346101571 50589173788573884519152357)
        ·
          refine ⟨9485470085357603347341067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50589173788573884519152357 9485470085357603347341067)
          ·
            refine ⟨14228205128036405021011601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9485470085357603347341067 14228205128036405021011601)
            ·
              refine ⟨10671153846027303765758701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14228205128036405021011601 10671153846027303765758701)
              ·
                refine ⟨4001682692260238912159513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10671153846027303765758701 4001682692260238912159513)
                ·
                  refine ⟨3001262019195179184119635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4001682692260238912159513 3001262019195179184119635)
                  ·
                    refine ⟨4501893028792768776179453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3001262019195179184119635 4501893028792768776179453)
                    ·
                      refine ⟨1688209885797288291067295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4501893028792768776179453 1688209885797288291067295)
                      ·
                        rfl

theorem cell23_3287777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_3287777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287777 prefixEnd_3287777 := by exact prefixLift 3287777
  have htrace : WordTrace (prefixWord ++ tailWord_3287777) baseStart_3287777 baseEnd_3287777 := by
    simpa [prefixWord, tailWord_3287777, baseEnd_3287777] using wordTrace_append hprefix tailTrace_3287777
  have hstable : (prefixWord ++ tailWord_3287777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287777).length < 2 ^ (prefixWord ++ tailWord_3287777).sum := by decide
  have hdescent : baseEnd_3287777 < baseStart_3287777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287800 : List Nat := [2, 1, 2, 1, 1, 2, 3, 4, 1, 4, 2]
def baseStart_3287800 : Nat := 118140960795 + 3287800 * 2 ^ 59
def prefixEnd_3287800 : Nat := 4983230072969 + 3 ^ 40 * 3287800 * 2
def baseEnd_3287800 : Nat := 1688221695852341701079689

theorem tailTrace_3287800 : CollatzResearch.WordTrace tailWord_3287800 prefixEnd_3287800 1688221695852341701079689 := by
  unfold tailWord_3287800
  simp only [CollatzResearch.WordTrace]
  refine ⟨59957958744434793190446427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79943944992579724253928569 59957958744434793190446427)
  ·
    refine ⟨89936938116652189785669641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59957958744434793190446427 89936938116652189785669641)
    ·
      refine ⟨67452703587489142339252231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89936938116652189785669641 67452703587489142339252231)
      ·
        refine ⟨101179055381233713508878347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67452703587489142339252231 101179055381233713508878347)
        ·
          refine ⟨151768583071850570263317521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101179055381233713508878347 151768583071850570263317521)
          ·
            refine ⟨113826437303887927697488141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151768583071850570263317521 113826437303887927697488141)
            ·
              refine ⟨42684913988957972886558053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113826437303887927697488141 42684913988957972886558053)
              ·
                refine ⟨8003421372929619916229635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42684913988957972886558053 8003421372929619916229635)
                ·
                  refine ⟨12005132059394429874344453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8003421372929619916229635 12005132059394429874344453)
                  ·
                    refine ⟨2250962261136455601439585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12005132059394429874344453 2250962261136455601439585)
                    ·
                      refine ⟨1688221695852341701079689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2250962261136455601439585 1688221695852341701079689)
                      ·
                        rfl

theorem cell23_3287800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 1, 4, 2].length) (baseStart_3287800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287800 prefixEnd_3287800 := by exact prefixLift 3287800
  have htrace : WordTrace (prefixWord ++ tailWord_3287800) baseStart_3287800 baseEnd_3287800 := by
    simpa [prefixWord, tailWord_3287800, baseEnd_3287800] using wordTrace_append hprefix tailTrace_3287800
  have hstable : (prefixWord ++ tailWord_3287800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287800).length < 2 ^ (prefixWord ++ tailWord_3287800).sum := by decide
  have hdescent : baseEnd_3287800 < baseStart_3287800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287804 : List Nat := [2, 2, 2, 1, 3, 2, 4, 1, 1, 3, 2]
def baseStart_3287804 : Nat := 118140960795 + 3287804 * 2 ^ 59
def prefixEnd_3287804 : Nat := 4983230072969 + 3 ^ 40 * 3287804 * 2
def baseEnd_3287804 : Nat := 1688223749774959685429671

theorem tailTrace_3287804 : CollatzResearch.WordTrace tailWord_3287804 prefixEnd_3287804 1688223749774959685429671 := by
  unfold tailWord_3287804
  simp only [CollatzResearch.WordTrace]
  refine ⟨59958031690427547532019233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79944042253903396709358977 59958031690427547532019233)
  ·
    refine ⟨44968523767820660649014425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59958031690427547532019233 44968523767820660649014425)
    ·
      refine ⟨33726392825865495486760819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44968523767820660649014425 33726392825865495486760819)
      ·
        refine ⟨50589589238798243230141229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33726392825865495486760819 50589589238798243230141229)
        ·
          refine ⟨18971095964549341211302961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50589589238798243230141229 18971095964549341211302961)
          ·
            refine ⟨14228321973412005908477221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18971095964549341211302961 14228321973412005908477221)
            ·
              refine ⟨2667810370014751107839479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14228321973412005908477221 2667810370014751107839479)
              ·
                refine ⟨4001715555022126661759219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2667810370014751107839479 4001715555022126661759219)
                ·
                  refine ⟨6002573332533189992638829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4001715555022126661759219 6002573332533189992638829)
                  ·
                    refine ⟨2250964999699946247239561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6002573332533189992638829 2250964999699946247239561)
                    ·
                      refine ⟨1688223749774959685429671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2250964999699946247239561 1688223749774959685429671)
                      ·
                        rfl

theorem cell23_3287804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_3287804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287804 prefixEnd_3287804 := by exact prefixLift 3287804
  have htrace : WordTrace (prefixWord ++ tailWord_3287804) baseStart_3287804 baseEnd_3287804 := by
    simpa [prefixWord, tailWord_3287804, baseEnd_3287804] using wordTrace_append hprefix tailTrace_3287804
  have hstable : (prefixWord ++ tailWord_3287804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287804).length < 2 ^ (prefixWord ++ tailWord_3287804).sum := by decide
  have hdescent : baseEnd_3287804 < baseStart_3287804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287810 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_3287810 : Nat := 118140960795 + 3287810 * 2 ^ 59
def prefixEnd_3287810 : Nat := 4983230072969 + 3 ^ 40 * 3287810 * 2
def baseEnd_3287810 : Nat := 562742276886295553984881

theorem tailTrace_3287810 : CollatzResearch.WordTrace tailWord_3287810 prefixEnd_3287810 562742276886295553984881 := by
  unfold tailWord_3287810
  simp only [CollatzResearch.WordTrace]
  refine ⟨29979070554708339522189221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79944188145888905392504589 29979070554708339522189221)
  ·
    refine ⟨5621075729007813660410479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29979070554708339522189221 5621075729007813660410479)
    ·
      refine ⟨8431613593511720490615719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5621075729007813660410479 8431613593511720490615719)
      ·
        refine ⟨12647420390267580735923579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8431613593511720490615719 12647420390267580735923579)
        ·
          refine ⟨18971130585401371103885369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12647420390267580735923579 18971130585401371103885369)
          ·
            refine ⟨14228347939051028327914027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18971130585401371103885369 14228347939051028327914027)
            ·
              refine ⟨21342521908576542491871041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14228347939051028327914027 21342521908576542491871041)
              ·
                refine ⟨16006891431432406868903281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21342521908576542491871041 16006891431432406868903281)
                ·
                  refine ⟨12005168573574305151677461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16006891431432406868903281 12005168573574305151677461)
                  ·
                    refine ⟨562742276886295553984881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12005168573574305151677461 562742276886295553984881)
                    ·
                      rfl

theorem cell23_3287810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_3287810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287810 prefixEnd_3287810 := by exact prefixLift 3287810
  have htrace : WordTrace (prefixWord ++ tailWord_3287810) baseStart_3287810 baseEnd_3287810 := by
    simpa [prefixWord, tailWord_3287810, baseEnd_3287810] using wordTrace_append hprefix tailTrace_3287810
  have hstable : (prefixWord ++ tailWord_3287810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287810).length < 2 ^ (prefixWord ++ tailWord_3287810).sum := by decide
  have hdescent : baseEnd_3287810 < baseStart_3287810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287823 : List Nat := [1, 1, 2, 1, 1, 1, 8, 1, 7]
def baseStart_3287823 : Nat := 118140960795 + 3287823 * 2 ^ 59
def prefixEnd_3287823 : Nat := 4983230072969 + 3 ^ 40 * 3287823 * 2
def baseEnd_3287823 : Nat := 187581500656377234565787

theorem tailTrace_3287823 : CollatzResearch.WordTrace tailWord_3287823 prefixEnd_3287823 187581500656377234565787 := by
  unfold tailWord_3287823
  simp only [CollatzResearch.WordTrace]
  refine ⟨119916756367786261308980123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79944504245190840872653415 119916756367786261308980123)
  ·
    refine ⟨179875134551679391963470185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119916756367786261308980123 179875134551679391963470185)
    ·
      refine ⟨134906350913759543972602639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179875134551679391963470185 134906350913759543972602639)
      ·
        refine ⟨202359526370639315958903959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134906350913759543972602639 202359526370639315958903959)
        ·
          refine ⟨303539289555958973938355939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202359526370639315958903959 303539289555958973938355939)
          ·
            refine ⟨455308934333938460907533909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303539289555958973938355939 455308934333938460907533909)
            ·
              refine ⟨5335651574225841338760163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 455308934333938460907533909 5335651574225841338760163)
              ·
                refine ⟨8003477361338762008140245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5335651574225841338760163 8003477361338762008140245)
                ·
                  refine ⟨187581500656377234565787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8003477361338762008140245 187581500656377234565787)
                  ·
                    rfl

theorem cell23_3287823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 7].length) (baseStart_3287823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287823 prefixEnd_3287823 := by exact prefixLift 3287823
  have htrace : WordTrace (prefixWord ++ tailWord_3287823) baseStart_3287823 baseEnd_3287823 := by
    simpa [prefixWord, tailWord_3287823, baseEnd_3287823] using wordTrace_append hprefix tailTrace_3287823
  have hstable : (prefixWord ++ tailWord_3287823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287823).length < 2 ^ (prefixWord ++ tailWord_3287823).sum := by decide
  have hdescent : baseEnd_3287823 < baseStart_3287823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287833 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 1, 5, 3]
def baseStart_3287833 : Nat := 118140960795 + 3287833 * 2 ^ 59
def prefixEnd_3287833 : Nat := 4983230072969 + 3 ^ 40 * 3287833 * 2
def baseEnd_3287833 : Nat := 1688238640713940071967037

theorem tailTrace_3287833 : CollatzResearch.WordTrace tailWord_3287833 prefixEnd_3287833 1688238640713940071967037 := by
  unfold tailWord_3287833
  simp only [CollatzResearch.WordTrace]
  refine ⟨119917121097750033016844153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79944747398500022011229435 119917121097750033016844153)
  ·
    refine ⟨89937840823312524762633115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119917121097750033016844153 89937840823312524762633115)
    ·
      refine ⟨134906761234968787143949673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89937840823312524762633115 134906761234968787143949673)
      ·
        refine ⟨101180070926226590357962255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134906761234968787143949673 101180070926226590357962255)
        ·
          refine ⟨151770106389339885536943383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101180070926226590357962255 151770106389339885536943383)
          ·
            refine ⟨227655159584009828305415075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151770106389339885536943383 227655159584009828305415075)
            ·
              refine ⟨341482739376014742458122613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227655159584009828305415075 341482739376014742458122613)
              ·
                refine ⟨32014006816501382105448995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 341482739376014742458122613 32014006816501382105448995)
                ·
                  refine ⟨48021010224752073158173493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32014006816501382105448995 48021010224752073158173493)
                  ·
                    refine ⟨4501969708570506858578765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48021010224752073158173493 4501969708570506858578765)
                    ·
                      refine ⟨1688238640713940071967037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4501969708570506858578765 1688238640713940071967037)
                      ·
                        rfl

theorem cell23_3287833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_3287833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287833 prefixEnd_3287833 := by exact prefixLift 3287833
  have htrace : WordTrace (prefixWord ++ tailWord_3287833) baseStart_3287833 baseEnd_3287833 := by
    simpa [prefixWord, tailWord_3287833, baseEnd_3287833] using wordTrace_append hprefix tailTrace_3287833
  have hstable : (prefixWord ++ tailWord_3287833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287833).length < 2 ^ (prefixWord ++ tailWord_3287833).sum := by decide
  have hdescent : baseEnd_3287833 < baseStart_3287833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287863 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 5]
def baseStart_3287863 : Nat := 118140960795 + 3287863 * 2 ^ 59
def prefixEnd_3287863 : Nat := 4983230072969 + 3 ^ 40 * 3287863 * 2
def baseEnd_3287863 : Nat := 1688254045133574954591899

theorem tailTrace_3287863 : CollatzResearch.WordTrace tailWord_3287863 prefixEnd_3287863 1688254045133574954591899 := by
  unfold tailWord_3287863
  simp only [CollatzResearch.WordTrace]
  refine ⟨119918215287641348140436243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79945476858427565426957495 119918215287641348140436243)
  ·
    refine ⟨179877322931462022210654365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119918215287641348140436243 179877322931462022210654365)
    ·
      refine ⟨67453996099298258328995387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179877322931462022210654365 67453996099298258328995387)
      ·
        refine ⟨101180994148947387493493081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67453996099298258328995387 101180994148947387493493081)
        ·
          refine ⟨75885745611710540620119811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101180994148947387493493081 75885745611710540620119811)
          ·
            refine ⟨113828618417565810930179717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75885745611710540620119811 113828618417565810930179717)
            ·
              refine ⟨21342865953293589549408697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113828618417565810930179717 21342865953293589549408697)
              ·
                refine ⟨16007149464970192162056523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21342865953293589549408697 16007149464970192162056523)
                ·
                  refine ⟨24010724197455288243084785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16007149464970192162056523 24010724197455288243084785)
                  ·
                    refine ⟨18008043148091466182313589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24010724197455288243084785 18008043148091466182313589)
                    ·
                      refine ⟨1688254045133574954591899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18008043148091466182313589 1688254045133574954591899)
                      ·
                        rfl

theorem cell23_3287863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_3287863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287863 prefixEnd_3287863 := by exact prefixLift 3287863
  have htrace : WordTrace (prefixWord ++ tailWord_3287863) baseStart_3287863 baseEnd_3287863 := by
    simpa [prefixWord, tailWord_3287863, baseEnd_3287863] using wordTrace_append hprefix tailTrace_3287863
  have hstable : (prefixWord ++ tailWord_3287863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287863).length < 2 ^ (prefixWord ++ tailWord_3287863).sum := by decide
  have hdescent : baseEnd_3287863 < baseStart_3287863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287885 : List Nat := [1, 6, 1, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_3287885 : Nat := 118140960795 + 3287885 * 2 ^ 59
def prefixEnd_3287885 : Nat := 4983230072969 + 3 ^ 40 * 3287885 * 2
def baseEnd_3287885 : Nat := 1688265341707973868516799

theorem tailTrace_3287885 : CollatzResearch.WordTrace tailWord_3287885 prefixEnd_3287885 1688265341707973868516799 := by
  unfold tailWord_3287885
  simp only [CollatzResearch.WordTrace]
  refine ⟨119919017693561645897737109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79946011795707763931824739 119919017693561645897737109)
  ·
    refine ⟨5621203954385702151456427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 119919017693561645897737109 5621203954385702151456427)
    ·
      refine ⟨8431805931578553227184641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5621203954385702151456427 8431805931578553227184641)
      ·
        refine ⟨6323854448683914920388481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8431805931578553227184641 6323854448683914920388481)
        ·
          refine ⟨4742890836512936190291361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6323854448683914920388481 4742890836512936190291361)
          ·
            refine ⟨3557168127384702142718521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4742890836512936190291361 3557168127384702142718521)
            ·
              refine ⟨2667876095538526607038891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3557168127384702142718521 2667876095538526607038891)
              ·
                refine ⟨4001814143307789910558337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2667876095538526607038891 4001814143307789910558337)
                ·
                  refine ⟨3001360607480842432918753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4001814143307789910558337 3001360607480842432918753)
                  ·
                    refine ⟨2251020455610631824689065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3001360607480842432918753 2251020455610631824689065)
                    ·
                      refine ⟨1688265341707973868516799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2251020455610631824689065 1688265341707973868516799)
                      ·
                        rfl

theorem cell23_3287885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_3287885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287885 prefixEnd_3287885 := by exact prefixLift 3287885
  have htrace : WordTrace (prefixWord ++ tailWord_3287885) baseStart_3287885 baseEnd_3287885 := by
    simpa [prefixWord, tailWord_3287885, baseEnd_3287885] using wordTrace_append hprefix tailTrace_3287885
  have hstable : (prefixWord ++ tailWord_3287885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287885).length < 2 ^ (prefixWord ++ tailWord_3287885).sum := by decide
  have hdescent : baseEnd_3287885 < baseStart_3287885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287890 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_3287890 : Nat := 118140960795 + 3287890 * 2 ^ 59
def prefixEnd_3287890 : Nat := 4983230072969 + 3 ^ 40 * 3287890 * 2
def baseEnd_3287890 : Nat := 1688267909111246348954275

theorem tailTrace_3287890 : CollatzResearch.WordTrace tailWord_3287890 prefixEnd_3287890 1688267909111246348954275 := by
  unfold tailWord_3287890
  simp only [CollatzResearch.WordTrace]
  refine ⟨29979800014635882937917281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79946133372362354501112749 29979800014635882937917281)
  ·
    refine ⟨22484850010976912203437961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29979800014635882937917281 22484850010976912203437961)
    ·
      refine ⟨16863637508232684152578471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22484850010976912203437961 16863637508232684152578471)
      ·
        refine ⟨25295456262349026228867707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16863637508232684152578471 25295456262349026228867707)
        ·
          refine ⟨37943184393523539343301561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25295456262349026228867707 37943184393523539343301561)
          ·
            refine ⟨28457388295142654507476171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37943184393523539343301561 28457388295142654507476171)
            ·
              refine ⟨42686082442713981761214257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28457388295142654507476171 42686082442713981761214257)
              ·
                refine ⟨32014561832035486320910693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42686082442713981761214257 32014561832035486320910693)
                ·
                  refine ⟨6002730343506653685170755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32014561832035486320910693 6002730343506653685170755)
                  ·
                    refine ⟨9004095515259980527756133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6002730343506653685170755 9004095515259980527756133)
                    ·
                      refine ⟨1688267909111246348954275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9004095515259980527756133 1688267909111246348954275)
                      ·
                        rfl

theorem cell23_3287890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_3287890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287890 prefixEnd_3287890 := by exact prefixLift 3287890
  have htrace : WordTrace (prefixWord ++ tailWord_3287890) baseStart_3287890 baseEnd_3287890 := by
    simpa [prefixWord, tailWord_3287890, baseEnd_3287890] using wordTrace_append hprefix tailTrace_3287890
  have hstable : (prefixWord ++ tailWord_3287890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287890).length < 2 ^ (prefixWord ++ tailWord_3287890).sum := by decide
  have hdescent : baseEnd_3287890 < baseStart_3287890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287907 : List Nat := [1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 4]
def baseStart_3287907 : Nat := 118140960795 + 3287907 * 2 ^ 59
def prefixEnd_3287907 : Nat := 4983230072969 + 3 ^ 40 * 3287907 * 2
def baseEnd_3287907 : Nat := 1688276638282372782441697

theorem tailTrace_3287907 : CollatzResearch.WordTrace tailWord_3287907 prefixEnd_3287907 1688276638282372782441697 := by
  unfold tailWord_3287907
  simp only [CollatzResearch.WordTrace]
  refine ⟨119919820099481943655037975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79946546732987962436691983 119919820099481943655037975)
  ·
    refine ⟨179879730149222915482556963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119919820099481943655037975 179879730149222915482556963)
    ·
      refine ⟨269819595223834373223835445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179879730149222915482556963 269819595223834373223835445)
      ·
        refine ⟨25295587052234472489734573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 269819595223834373223835445 25295587052234472489734573)
        ·
          refine ⟨9485845144587927183650465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25295587052234472489734573 9485845144587927183650465)
          ·
            refine ⟨7114383858440945387737849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9485845144587927183650465 7114383858440945387737849)
            ·
              refine ⟨5335787893830709040803387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7114383858440945387737849 5335787893830709040803387)
              ·
                refine ⟨8003681840746063561205081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5335787893830709040803387 8003681840746063561205081)
                ·
                  refine ⟨6002761380559547670903811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8003681840746063561205081 6002761380559547670903811)
                  ·
                    refine ⟨9004142070839321506355717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6002761380559547670903811 9004142070839321506355717)
                    ·
                      refine ⟨1688276638282372782441697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9004142070839321506355717 1688276638282372782441697)
                      ·
                        rfl

theorem cell23_3287907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_3287907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287907 prefixEnd_3287907 := by exact prefixLift 3287907
  have htrace : WordTrace (prefixWord ++ tailWord_3287907) baseStart_3287907 baseEnd_3287907 := by
    simpa [prefixWord, tailWord_3287907, baseEnd_3287907] using wordTrace_append hprefix tailTrace_3287907
  have hstable : (prefixWord ++ tailWord_3287907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287907).length < 2 ^ (prefixWord ++ tailWord_3287907).sum := by decide
  have hdescent : baseEnd_3287907 < baseStart_3287907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287940 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_3287940 : Nat := 118140960795 + 3287940 * 2 ^ 59
def prefixEnd_3287940 : Nat := 4983230072969 + 3 ^ 40 * 3287940 * 2
def baseEnd_3287940 : Nat := 1688293583143971153329045

theorem tailTrace_3287940 : CollatzResearch.WordTrace tailWord_3287940 prefixEnd_3287940 1688293583143971153329045 := by
  unfold tailWord_3287940
  simp only [CollatzResearch.WordTrace]
  refine ⟨59960511854181195145494637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79947349138908260193992849 59960511854181195145494637)
  ·
    refine ⟨22485191945317948179560489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59960511854181195145494637 22485191945317948179560489)
    ·
      refine ⟨16863893958988461134670367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22485191945317948179560489 16863893958988461134670367)
      ·
        refine ⟨25295840938482691702005551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16863893958988461134670367 25295840938482691702005551)
        ·
          refine ⟨37943761407724037553008327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25295840938482691702005551 37943761407724037553008327)
          ·
            refine ⟨56915642111586056329512491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37943761407724037553008327 56915642111586056329512491)
            ·
              refine ⟨85373463167379084494268737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56915642111586056329512491 85373463167379084494268737)
              ·
                refine ⟨64030097375534313370701553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85373463167379084494268737 64030097375534313370701553)
                ·
                  refine ⟨48022573031650735028026165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64030097375534313370701553 48022573031650735028026165)
                  ·
                    refine ⟨4502116221717256408877453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48022573031650735028026165 4502116221717256408877453)
                    ·
                      refine ⟨1688293583143971153329045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4502116221717256408877453 1688293583143971153329045)
                      ·
                        rfl

theorem cell23_3287940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_3287940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287940 prefixEnd_3287940 := by exact prefixLift 3287940
  have htrace : WordTrace (prefixWord ++ tailWord_3287940) baseStart_3287940 baseEnd_3287940 := by
    simpa [prefixWord, tailWord_3287940, baseEnd_3287940] using wordTrace_append hprefix tailTrace_3287940
  have hstable : (prefixWord ++ tailWord_3287940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287940).length < 2 ^ (prefixWord ++ tailWord_3287940).sum := by decide
  have hdescent : baseEnd_3287940 < baseStart_3287940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287953 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 7]
def baseStart_3287953 : Nat := 118140960795 + 3287953 * 2 ^ 59
def prefixEnd_3287953 : Nat := 4983230072969 + 3 ^ 40 * 3287953 * 2
def baseEnd_3287953 : Nat := 1688300258392479602466485

theorem tailTrace_3287953 : CollatzResearch.WordTrace tailWord_3287953 prefixEnd_3287953 1688300258392479602466485 := by
  unfold tailWord_3287953
  simp only [CollatzResearch.WordTrace]
  refine ⟨119921497857315293511212513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79947665238210195674141675 119921497857315293511212513)
  ·
    refine ⟨89941123392986470133409385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119921497857315293511212513 89941123392986470133409385)
    ·
      refine ⟨67455842544739852600057039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89941123392986470133409385 67455842544739852600057039)
      ·
        refine ⟨101183763817109778900085559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67455842544739852600057039 101183763817109778900085559)
        ·
          refine ⟨151775645725664668350128339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101183763817109778900085559 151775645725664668350128339)
          ·
            refine ⟨227663468588497002525192509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151775645725664668350128339 227663468588497002525192509)
            ·
              refine ⟨85373800720686375946947191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227663468588497002525192509 85373800720686375946947191)
              ·
                refine ⟨128060701081029563920420787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85373800720686375946947191 128060701081029563920420787)
                ·
                  refine ⟨192091051621544345880631181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128060701081029563920420787 192091051621544345880631181)
                  ·
                    refine ⟨72034144358079129705236693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 192091051621544345880631181 72034144358079129705236693)
                    ·
                      refine ⟨1688300258392479602466485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72034144358079129705236693 1688300258392479602466485)
                      ·
                        rfl

theorem cell23_3287953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_3287953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287953 prefixEnd_3287953 := by exact prefixLift 3287953
  have htrace : WordTrace (prefixWord ++ tailWord_3287953) baseStart_3287953 baseEnd_3287953 := by
    simpa [prefixWord, tailWord_3287953, baseEnd_3287953] using wordTrace_append hprefix tailTrace_3287953
  have hstable : (prefixWord ++ tailWord_3287953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287953).length < 2 ^ (prefixWord ++ tailWord_3287953).sum := by decide
  have hdescent : baseEnd_3287953 < baseStart_3287953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287957 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 5, 1, 3]
def baseStart_3287957 : Nat := 118140960795 + 3287957 * 2 ^ 59
def prefixEnd_3287957 : Nat := 4983230072969 + 3 ^ 40 * 3287957 * 2
def baseEnd_3287957 : Nat := 1688302312315097586816467

theorem tailTrace_3287957 : CollatzResearch.WordTrace tailWord_3287957 prefixEnd_3287957 1688302312315097586816467 := by
  unfold tailWord_3287957
  simp only [CollatzResearch.WordTrace]
  refine ⟨119921643749300802194358125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79947762499533868129572083 119921643749300802194358125)
  ·
    refine ⟨44970616405987800822884297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119921643749300802194358125 44970616405987800822884297)
    ·
      refine ⟨33727962304490850617163223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44970616405987800822884297 33727962304490850617163223)
      ·
        refine ⟨50591943456736275925744835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33727962304490850617163223 50591943456736275925744835)
        ·
          refine ⟨75887915185104413888617253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50591943456736275925744835 75887915185104413888617253)
          ·
            refine ⟨14228984097207077604115735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75887915185104413888617253 14228984097207077604115735)
            ·
              refine ⟨21343476145810616406173603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14228984097207077604115735 21343476145810616406173603)
              ·
                refine ⟨32015214218715924609260405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21343476145810616406173603 32015214218715924609260405)
                ·
                  refine ⟨3001426333004617932118163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32015214218715924609260405 3001426333004617932118163)
                  ·
                    refine ⟨4502139499506926898177245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3001426333004617932118163 4502139499506926898177245)
                    ·
                      refine ⟨1688302312315097586816467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4502139499506926898177245 1688302312315097586816467)
                      ·
                        rfl

theorem cell23_3287957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_3287957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287957 prefixEnd_3287957 := by exact prefixLift 3287957
  have htrace : WordTrace (prefixWord ++ tailWord_3287957) baseStart_3287957 baseEnd_3287957 := by
    simpa [prefixWord, tailWord_3287957, baseEnd_3287957] using wordTrace_append hprefix tailTrace_3287957
  have hstable : (prefixWord ++ tailWord_3287957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287957).length < 2 ^ (prefixWord ++ tailWord_3287957).sum := by decide
  have hdescent : baseEnd_3287957 < baseStart_3287957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287958 : List Nat := [5, 3, 1, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_3287958 : Nat := 118140960795 + 3287958 * 2 ^ 59
def prefixEnd_3287958 : Nat := 4983230072969 + 3 ^ 40 * 3287958 * 2
def baseEnd_3287958 : Nat := 1688302825795752082903963

theorem tailTrace_3287958 : CollatzResearch.WordTrace tailWord_3287958 prefixEnd_3287958 1688302825795752082903963 := by
  unfold tailWord_3287958
  simp only [CollatzResearch.WordTrace]
  refine ⟨7495105013893573710321533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79947786814864786243429685 7495105013893573710321533)
  ·
    refine ⟨2810664380210090141370575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7495105013893573710321533 2810664380210090141370575)
    ·
      refine ⟨4215996570315135212055863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2810664380210090141370575 4215996570315135212055863)
      ·
        refine ⟨6323994855472702818083795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4215996570315135212055863 6323994855472702818083795)
        ·
          refine ⟨9485992283209054227125693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6323994855472702818083795 9485992283209054227125693)
          ·
            refine ⟨3557247106203395335172135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9485992283209054227125693 3557247106203395335172135)
            ·
              refine ⟨5335870659305093002758203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3557247106203395335172135 5335870659305093002758203)
              ·
                refine ⟨8003805988957639504137305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5335870659305093002758203 8003805988957639504137305)
                ·
                  refine ⟨6002854491718229628102979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8003805988957639504137305 6002854491718229628102979)
                  ·
                    refine ⟨9004281737577344442154469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6002854491718229628102979 9004281737577344442154469)
                    ·
                      refine ⟨1688302825795752082903963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9004281737577344442154469 1688302825795752082903963)
                      ·
                        rfl

theorem cell23_3287958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_3287958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287958 prefixEnd_3287958 := by exact prefixLift 3287958
  have htrace : WordTrace (prefixWord ++ tailWord_3287958) baseStart_3287958 baseEnd_3287958 := by
    simpa [prefixWord, tailWord_3287958, baseEnd_3287958] using wordTrace_append hprefix tailTrace_3287958
  have hstable : (prefixWord ++ tailWord_3287958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287958).length < 2 ^ (prefixWord ++ tailWord_3287958).sum := by decide
  have hdescent : baseEnd_3287958 < baseStart_3287958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287981 : List Nat := [1, 5, 2, 3, 1, 2, 1, 2, 6]
def baseStart_3287981 : Nat := 118140960795 + 3287981 * 2 ^ 59
def prefixEnd_3287981 : Nat := 4983230072969 + 3 ^ 40 * 3287981 * 2
def baseEnd_3287981 : Nat := 187590515094533943657373

theorem tailTrace_3287981 : CollatzResearch.WordTrace tailWord_3287981 prefixEnd_3287981 187590515094533943657373 := by
  unfold tailWord_3287981
  simp only [CollatzResearch.WordTrace]
  refine ⟨119922519101213854293231797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79948346067475902862154531 119922519101213854293231797)
  ·
    refine ⟨11242736165738798839990481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119922519101213854293231797 11242736165738798839990481)
    ·
      refine ⟨8432052124304099129992861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11242736165738798839990481 8432052124304099129992861)
      ·
        refine ⟨3162019546614037173747323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8432052124304099129992861 3162019546614037173747323)
        ·
          refine ⟨4743029319921055760620985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3162019546614037173747323 4743029319921055760620985)
          ·
            refine ⟨3557271989940791820465739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4743029319921055760620985 3557271989940791820465739)
            ·
              refine ⟨5335907984911187730698609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3557271989940791820465739 5335907984911187730698609)
              ·
                refine ⟨4001930988683390798023957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5335907984911187730698609 4001930988683390798023957)
                ·
                  refine ⟨187590515094533943657373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4001930988683390798023957 187590515094533943657373)
                  ·
                    rfl

theorem cell23_3287981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_3287981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287981 prefixEnd_3287981 := by exact prefixLift 3287981
  have htrace : WordTrace (prefixWord ++ tailWord_3287981) baseStart_3287981 baseEnd_3287981 := by
    simpa [prefixWord, tailWord_3287981, baseEnd_3287981] using wordTrace_append hprefix tailTrace_3287981
  have hstable : (prefixWord ++ tailWord_3287981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287981).length < 2 ^ (prefixWord ++ tailWord_3287981).sum := by decide
  have hdescent : baseEnd_3287981 < baseStart_3287981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288000 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 5]
def baseStart_3288000 : Nat := 118140960795 + 3288000 * 2 ^ 59
def prefixEnd_3288000 : Nat := 4983230072969 + 3 ^ 40 * 3288000 * 2
def baseEnd_3288000 : Nat := 1688324391983240918578769

theorem tailTrace_3288000 : CollatzResearch.WordTrace tailWord_3288000 prefixEnd_3288000 1688324391983240918578769 := by
  unfold tailWord_3288000
  simp only [CollatzResearch.WordTrace]
  refine ⟨59961606044072510269086727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79948808058763347025448969 59961606044072510269086727)
  ·
    refine ⟨89942409066108765403630091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59961606044072510269086727 89942409066108765403630091)
    ·
      refine ⟨134913613599163148105445137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89942409066108765403630091 134913613599163148105445137)
      ·
        refine ⟨101185210199372361079083853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134913613599163148105445137 101185210199372361079083853)
        ·
          refine ⟨37944453824764635404656445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101185210199372361079083853 37944453824764635404656445)
          ·
            refine ⟨14229170184286738276746167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37944453824764635404656445 14229170184286738276746167)
            ·
              refine ⟨21343755276430107415119251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14229170184286738276746167 21343755276430107415119251)
              ·
                refine ⟨32015632914645161122678877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21343755276430107415119251 32015632914645161122678877)
                ·
                  refine ⟨12005862342991935421004579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32015632914645161122678877 12005862342991935421004579)
                  ·
                    refine ⟨18008793514487903131506869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12005862342991935421004579 18008793514487903131506869)
                    ·
                      refine ⟨1688324391983240918578769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18008793514487903131506869 1688324391983240918578769)
                      ·
                        rfl

theorem cell23_3288000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_3288000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288000 prefixEnd_3288000 := by exact prefixLift 3288000
  have htrace : WordTrace (prefixWord ++ tailWord_3288000) baseStart_3288000 baseEnd_3288000 := by
    simpa [prefixWord, tailWord_3288000, baseEnd_3288000] using wordTrace_append hprefix tailTrace_3288000
  have hstable : (prefixWord ++ tailWord_3288000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288000).length < 2 ^ (prefixWord ++ tailWord_3288000).sum := by decide
  have hdescent : baseEnd_3288000 < baseStart_3288000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288007 : List Nat := [1, 1, 4, 1, 1, 2, 2, 5, 2, 4]
def baseStart_3288007 : Nat := 118140960795 + 3288007 * 2 ^ 59
def prefixEnd_3288007 : Nat := 4983230072969 + 3 ^ 40 * 3288007 * 2
def baseEnd_3288007 : Nat := 562775995449274130397079

theorem tailTrace_3288007 : CollatzResearch.WordTrace tailWord_3288007 prefixEnd_3288007 562775995449274130397079 := by
  unfold tailWord_3288007
  simp only [CollatzResearch.WordTrace]
  refine ⟨119923467399119660733678275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79948978266079773822452183 119923467399119660733678275)
  ·
    refine ⟨179885201098679491100517413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119923467399119660733678275 179885201098679491100517413)
    ·
      refine ⟨33728475206002404581347015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179885201098679491100517413 33728475206002404581347015)
      ·
        refine ⟨50592712809003606872020523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33728475206002404581347015 50592712809003606872020523)
        ·
          refine ⟨75889069213505410308030785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50592712809003606872020523 75889069213505410308030785)
          ·
            refine ⟨56916801910129057731023089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75889069213505410308030785 56916801910129057731023089)
            ·
              refine ⟨42687601432596793298267317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56916801910129057731023089 42687601432596793298267317)
              ·
                refine ⟨4001962634305949371712561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42687601432596793298267317 4001962634305949371712561)
                ·
                  refine ⟨3001471975729462028784421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4001962634305949371712561 3001471975729462028784421)
                  ·
                    refine ⟨562775995449274130397079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3001471975729462028784421 562775995449274130397079)
                    ·
                      rfl

theorem cell23_3288007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_3288007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288007 prefixEnd_3288007 := by exact prefixLift 3288007
  have htrace : WordTrace (prefixWord ++ tailWord_3288007) baseStart_3288007 baseEnd_3288007 := by
    simpa [prefixWord, tailWord_3288007, baseEnd_3288007] using wordTrace_append hprefix tailTrace_3288007
  have hstable : (prefixWord ++ tailWord_3288007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288007).length < 2 ^ (prefixWord ++ tailWord_3288007).sum := by decide
  have hdescent : baseEnd_3288007 < baseStart_3288007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288014 : List Nat := [4, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4]
def baseStart_3288014 : Nat := 118140960795 + 3288014 * 2 ^ 59
def prefixEnd_3288014 : Nat := 4983230072969 + 3 ^ 40 * 3288014 * 2
def baseEnd_3288014 : Nat := 1688331580712403863803705

theorem tailTrace_3288014 : CollatzResearch.WordTrace tailWord_3288014 prefixEnd_3288014 1688331580712403863803705 := by
  unfold tailWord_3288014
  simp only [CollatzResearch.WordTrace]
  refine ⟨14990465338761787616147887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79949148473396200619455397 14990465338761787616147887)
  ·
    refine ⟨22485698008142681424221831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14990465338761787616147887 22485698008142681424221831)
    ·
      refine ⟨33728547012214022136332747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22485698008142681424221831 33728547012214022136332747)
      ·
        refine ⟨50592820518321033204499121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33728547012214022136332747 50592820518321033204499121)
        ·
          refine ⟨37944615388740774903374341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50592820518321033204499121 37944615388740774903374341)
          ·
            refine ⟨7114615385388895294382689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37944615388740774903374341 7114615385388895294382689)
            ·
              refine ⟨5335961539041671470787017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7114615385388895294382689 5335961539041671470787017)
              ·
                refine ⟨4001971154281253603090263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5335961539041671470787017 4001971154281253603090263)
                ·
                  refine ⟨6002956731421880404635395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4001971154281253603090263 6002956731421880404635395)
                  ·
                    refine ⟨9004435097132820606953093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6002956731421880404635395 9004435097132820606953093)
                    ·
                      refine ⟨1688331580712403863803705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9004435097132820606953093 1688331580712403863803705)
                      ·
                        rfl

theorem cell23_3288014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_3288014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288014 prefixEnd_3288014 := by exact prefixLift 3288014
  have htrace : WordTrace (prefixWord ++ tailWord_3288014) baseStart_3288014 baseEnd_3288014 := by
    simpa [prefixWord, tailWord_3288014, baseEnd_3288014] using wordTrace_append hprefix tailTrace_3288014
  have hstable : (prefixWord ++ tailWord_3288014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288014).length < 2 ^ (prefixWord ++ tailWord_3288014).sum := by decide
  have hdescent : baseEnd_3288014 < baseStart_3288014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288034 : List Nat := [3, 3, 3, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_3288034 : Nat := 118140960795 + 3288034 * 2 ^ 59
def prefixEnd_3288034 : Nat := 4983230072969 + 3 ^ 40 * 3288034 * 2
def baseEnd_3288034 : Nat := 1688341850325493785553613

theorem tailTrace_3288034 : CollatzResearch.WordTrace tailWord_3288034 prefixEnd_3288034 1688341850325493785553613 := by
  unfold tailWord_3288034
  simp only [CollatzResearch.WordTrace]
  refine ⟨29981113042505461086227789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79949634780014562896607437 29981113042505461086227789)
  ·
    refine ⟨11242917390939547907335421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29981113042505461086227789 11242917390939547907335421)
    ·
      refine ⟨4216094021602330465250783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11242917390939547907335421 4216094021602330465250783)
      ·
        refine ⟨6324141032403495697876175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4216094021602330465250783 6324141032403495697876175)
        ·
          refine ⟨9486211548605243546814263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6324141032403495697876175 9486211548605243546814263)
          ·
            refine ⟨14229317322907865320221395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9486211548605243546814263 14229317322907865320221395)
            ·
              refine ⟨21343975984361797980332093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14229317322907865320221395 21343975984361797980332093)
              ·
                refine ⟨8003990994135674242624535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21343975984361797980332093 8003990994135674242624535)
                ·
                  refine ⟨12005986491203511363936803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8003990994135674242624535 12005986491203511363936803)
                  ·
                    refine ⟨18008979736805267045905205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12005986491203511363936803 18008979736805267045905205)
                    ·
                      refine ⟨1688341850325493785553613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18008979736805267045905205 1688341850325493785553613)
                      ·
                        rfl

theorem cell23_3288034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_3288034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288034 prefixEnd_3288034 := by exact prefixLift 3288034
  have htrace : WordTrace (prefixWord ++ tailWord_3288034) baseStart_3288034 baseEnd_3288034 := by
    simpa [prefixWord, tailWord_3288034, baseEnd_3288034] using wordTrace_append hprefix tailTrace_3288034
  have hstable : (prefixWord ++ tailWord_3288034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288034).length < 2 ^ (prefixWord ++ tailWord_3288034).sum := by decide
  have hdescent : baseEnd_3288034 < baseStart_3288034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288121 : List Nat := [1, 2, 1, 5, 2, 2, 2, 1, 1, 4, 2]
def baseStart_3288121 : Nat := 118140960795 + 3288121 * 2 ^ 59
def prefixEnd_3288121 : Nat := 4983230072969 + 3 ^ 40 * 3288121 * 2
def baseEnd_3288121 : Nat := 1688386523142434945165713

theorem tailTrace_3288121 : CollatzResearch.WordTrace tailWord_3288121 prefixEnd_3288121 1688386523142434945165713 := by
  unfold tailWord_3288121
  simp only [CollatzResearch.WordTrace]
  refine ⟨119927625320706658203328217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79951750213804438802218811 119927625320706658203328217)
  ·
    refine ⟨89945718990529993652496163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119927625320706658203328217 89945718990529993652496163)
    ·
      refine ⟨134918578485794990478744245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89945718990529993652496163 134918578485794990478744245)
      ·
        refine ⟨12648616733043280357382273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134918578485794990478744245 12648616733043280357382273)
        ·
          refine ⟨9486462549782460268036705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12648616733043280357382273 9486462549782460268036705)
          ·
            refine ⟨7114846912336845201027529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9486462549782460268036705 7114846912336845201027529)
            ·
              refine ⟨5336135184252633900770647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7114846912336845201027529 5336135184252633900770647)
              ·
                refine ⟨8004202776378950851155971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5336135184252633900770647 8004202776378950851155971)
                ·
                  refine ⟨12006304164568426276733957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8004202776378950851155971 12006304164568426276733957)
                  ·
                    refine ⟨2251182030856579926887617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12006304164568426276733957 2251182030856579926887617)
                    ·
                      refine ⟨1688386523142434945165713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2251182030856579926887617 1688386523142434945165713)
                      ·
                        rfl

theorem cell23_3288121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_3288121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288121 prefixEnd_3288121 := by exact prefixLift 3288121
  have htrace : WordTrace (prefixWord ++ tailWord_3288121) baseStart_3288121 baseEnd_3288121 := by
    simpa [prefixWord, tailWord_3288121, baseEnd_3288121] using wordTrace_append hprefix tailTrace_3288121
  have hstable : (prefixWord ++ tailWord_3288121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288121).length < 2 ^ (prefixWord ++ tailWord_3288121).sum := by decide
  have hdescent : baseEnd_3288121 < baseStart_3288121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288177 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 6, 1, 4]
def baseStart_3288177 : Nat := 118140960795 + 3288177 * 2 ^ 59
def prefixEnd_3288177 : Nat := 4983230072969 + 3 ^ 40 * 3288177 * 2
def baseEnd_3288177 : Nat := 1688415278059086726065455

theorem tailTrace_3288177 : CollatzResearch.WordTrace tailWord_3288177 prefixEnd_3288177 1688415278059086726065455 := by
  unfold tailWord_3288177
  simp only [CollatzResearch.WordTrace]
  refine ⟨119929667808503779767366785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79953111872335853178244523 119929667808503779767366785)
  ·
    refine ⟨89947250856377834825525089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119929667808503779767366785 89947250856377834825525089)
    ·
      refine ⟨67460438142283376119143817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89947250856377834825525089 67460438142283376119143817)
      ·
        refine ⟨50595328606712532089357863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67460438142283376119143817 50595328606712532089357863)
        ·
          refine ⟨75892992910068798134036795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50595328606712532089357863 75892992910068798134036795)
          ·
            refine ⟨113839489365103197201055193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75892992910068798134036795 113839489365103197201055193)
            ·
              refine ⟨85379617023827397900791395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113839489365103197201055193 85379617023827397900791395)
              ·
                refine ⟨128069425535741096851187093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85379617023827397900791395 128069425535741096851187093)
                ·
                  refine ⟨6003254321987863914899395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128069425535741096851187093 6003254321987863914899395)
                  ·
                    refine ⟨9004881482981795872349093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6003254321987863914899395 9004881482981795872349093)
                    ·
                      refine ⟨1688415278059086726065455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9004881482981795872349093 1688415278059086726065455)
                      ·
                        rfl

theorem cell23_3288177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_3288177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288177 prefixEnd_3288177 := by exact prefixLift 3288177
  have htrace : WordTrace (prefixWord ++ tailWord_3288177) baseStart_3288177 baseEnd_3288177 := by
    simpa [prefixWord, tailWord_3288177, baseEnd_3288177] using wordTrace_append hprefix tailTrace_3288177
  have hstable : (prefixWord ++ tailWord_3288177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288177).length < 2 ^ (prefixWord ++ tailWord_3288177).sum := by decide
  have hdescent : baseEnd_3288177 < baseStart_3288177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288264 : List Nat := [2, 1, 3, 1, 2, 1, 2, 5, 1, 5]
def baseStart_3288264 : Nat := 118140960795 + 3288264 * 2 ^ 59
def prefixEnd_3288264 : Nat := 4983230072969 + 3 ^ 40 * 3288264 * 2
def baseEnd_3288264 : Nat := 562819983625342628559185

theorem tailTrace_3288264 : CollatzResearch.WordTrace tailWord_3288264 prefixEnd_3288264 562819983625342628559185 := by
  unfold tailWord_3288264
  simp only [CollatzResearch.WordTrace]
  refine ⟨59966420479594296812891923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79955227306125729083855897 59966420479594296812891923)
  ·
    refine ⟨89949630719391445219337885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59966420479594296812891923 89949630719391445219337885)
    ·
      refine ⟨33731111519771791957251707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89949630719391445219337885 33731111519771791957251707)
      ·
        refine ⟨50596667279657687935877561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33731111519771791957251707 50596667279657687935877561)
        ·
          refine ⟨37947500459743265951908171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50596667279657687935877561 37947500459743265951908171)
          ·
            refine ⟨56921250689614898927862257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37947500459743265951908171 56921250689614898927862257)
            ·
              refine ⟨42690938017211174195896693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56921250689614898927862257 42690938017211174195896693)
              ·
                refine ⟨4002275439113547580865315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42690938017211174195896693 4002275439113547580865315)
                ·
                  refine ⟨6003413158670321371297973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4002275439113547580865315 6003413158670321371297973)
                  ·
                    refine ⟨562819983625342628559185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6003413158670321371297973 562819983625342628559185)
                    ·
                      rfl

theorem cell23_3288264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_3288264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288264 prefixEnd_3288264 := by exact prefixLift 3288264
  have htrace : WordTrace (prefixWord ++ tailWord_3288264) baseStart_3288264 baseEnd_3288264 := by
    simpa [prefixWord, tailWord_3288264, baseEnd_3288264] using wordTrace_append hprefix tailTrace_3288264
  have hstable : (prefixWord ++ tailWord_3288264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288264).length < 2 ^ (prefixWord ++ tailWord_3288264).sum := by decide
  have hdescent : baseEnd_3288264 < baseStart_3288264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288301 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_3288301 : Nat := 118140960795 + 3288301 * 2 ^ 59
def prefixEnd_3288301 : Nat := 4983230072969 + 3 ^ 40 * 3288301 * 2
def baseEnd_3288301 : Nat := 1688478949660244240914885

theorem tailTrace_3288301 : CollatzResearch.WordTrace tailWord_3288301 prefixEnd_3288301 1688478949660244240914885 := by
  unfold tailWord_3288301
  simp only [CollatzResearch.WordTrace]
  refine ⟨119934190460054548944880757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79956126973369699296587171 119934190460054548944880757)
  ·
    refine ⟨11243830355630113963582571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119934190460054548944880757 11243830355630113963582571)
    ·
      refine ⟨16865745533445170945373857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11243830355630113963582571 16865745533445170945373857)
      ·
        refine ⟨12649309150083878209030393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16865745533445170945373857 12649309150083878209030393)
        ·
          refine ⟨9486981862562908656772795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12649309150083878209030393 9486981862562908656772795)
          ·
            refine ⟨14230472793844362985159193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9486981862562908656772795 14230472793844362985159193)
            ·
              refine ⟨10672854595383272238869395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14230472793844362985159193 10672854595383272238869395)
              ·
                refine ⟨16009281893074908358304093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10672854595383272238869395 16009281893074908358304093)
                ·
                  refine ⟨6003480709903090634364035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16009281893074908358304093 6003480709903090634364035)
                  ·
                    refine ⟨9005221064854635951546053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6003480709903090634364035 9005221064854635951546053)
                    ·
                      refine ⟨1688478949660244240914885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9005221064854635951546053 1688478949660244240914885)
                      ·
                        rfl

theorem cell23_3288301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_3288301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288301 prefixEnd_3288301 := by exact prefixLift 3288301
  have htrace : WordTrace (prefixWord ++ tailWord_3288301) baseStart_3288301 baseEnd_3288301 := by
    simpa [prefixWord, tailWord_3288301, baseEnd_3288301] using wordTrace_append hprefix tailTrace_3288301
  have hstable : (prefixWord ++ tailWord_3288301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288301).length < 2 ^ (prefixWord ++ tailWord_3288301).sum := by decide
  have hdescent : baseEnd_3288301 < baseStart_3288301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288314 : List Nat := [3, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4]
def baseStart_3288314 : Nat := 118140960795 + 3288314 * 2 ^ 59
def prefixEnd_3288314 : Nat := 4983230072969 + 3 ^ 40 * 3288314 * 2
def baseEnd_3288314 : Nat := 1688485624908752690052325

theorem tailTrace_3288314 : CollatzResearch.WordTrace tailWord_3288314 prefixEnd_3288314 1688485624908752690052325 := by
  unfold tailWord_3288314
  simp only [CollatzResearch.WordTrace]
  refine ⟨29983666152251863041275999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79956443072671634776735997 29983666152251863041275999)
  ·
    refine ⟨44975499228377794561913999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29983666152251863041275999 44975499228377794561913999)
    ·
      refine ⟨67463248842566691842870999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44975499228377794561913999 67463248842566691842870999)
      ·
        refine ⟨101194873263850037764306499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67463248842566691842870999 101194873263850037764306499)
        ·
          refine ⟨151792309895775056646459749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101194873263850037764306499 151792309895775056646459749)
          ·
            refine ⟨28461058105457823121211203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151792309895775056646459749 28461058105457823121211203)
            ·
              refine ⟨42691587158186734681816805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28461058105457823121211203 42691587158186734681816805)
              ·
                refine ⟨8004672592160012752840651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42691587158186734681816805 8004672592160012752840651)
                ·
                  refine ⟨12007008888240019129260977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8004672592160012752840651 12007008888240019129260977)
                  ·
                    refine ⟨9005256666180014346945733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12007008888240019129260977 9005256666180014346945733)
                    ·
                      refine ⟨1688485624908752690052325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9005256666180014346945733 1688485624908752690052325)
                      ·
                        rfl

theorem cell23_3288314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_3288314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288314 prefixEnd_3288314 := by exact prefixLift 3288314
  have htrace : WordTrace (prefixWord ++ tailWord_3288314) baseStart_3288314 baseEnd_3288314 := by
    simpa [prefixWord, tailWord_3288314, baseEnd_3288314] using wordTrace_append hprefix tailTrace_3288314
  have hstable : (prefixWord ++ tailWord_3288314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288314).length < 2 ^ (prefixWord ++ tailWord_3288314).sum := by decide
  have hdescent : baseEnd_3288314 < baseStart_3288314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288318 : List Nat := [4, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_3288318 : Nat := 118140960795 + 3288318 * 2 ^ 59
def prefixEnd_3288318 : Nat := 4983230072969 + 3 ^ 40 * 3288318 * 2
def baseEnd_3288318 : Nat := 1688487678831370674402307

theorem tailTrace_3288318 : CollatzResearch.WordTrace tailWord_3288318 prefixEnd_3288318 1688487678831370674402307 := by
  unfold tailWord_3288318
  simp only [CollatzResearch.WordTrace]
  refine ⟨14991851312624120106031201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79956540333995307232166405 14991851312624120106031201)
  ·
    refine ⟨11243888484468090079523401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14991851312624120106031201 11243888484468090079523401)
    ·
      refine ⟨8432916363351067559642551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11243888484468090079523401 8432916363351067559642551)
      ·
        refine ⟨12649374545026601339463827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8432916363351067559642551 12649374545026601339463827)
        ·
          refine ⟨18974061817539902009195741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12649374545026601339463827 18974061817539902009195741)
          ·
            refine ⟨7115273181577463253448403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18974061817539902009195741 7115273181577463253448403)
            ·
              refine ⟨10672909772366194880172605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7115273181577463253448403 10672909772366194880172605)
              ·
                refine ⟨4002341164637323080064727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10672909772366194880172605 4002341164637323080064727)
                ·
                  refine ⟨6003511746955984620097091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4002341164637323080064727 6003511746955984620097091)
                  ·
                    refine ⟨9005267620433976930145637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6003511746955984620097091 9005267620433976930145637)
                    ·
                      refine ⟨1688487678831370674402307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9005267620433976930145637 1688487678831370674402307)
                      ·
                        rfl

theorem cell23_3288318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_3288318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288318 prefixEnd_3288318 := by exact prefixLift 3288318
  have htrace : WordTrace (prefixWord ++ tailWord_3288318) baseStart_3288318 baseEnd_3288318 := by
    simpa [prefixWord, tailWord_3288318, baseEnd_3288318] using wordTrace_append hprefix tailTrace_3288318
  have hstable : (prefixWord ++ tailWord_3288318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288318).length < 2 ^ (prefixWord ++ tailWord_3288318).sum := by decide
  have hdescent : baseEnd_3288318 < baseStart_3288318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288324 : List Nat := [2, 3, 2, 2, 2, 2, 10]
def baseStart_3288324 : Nat := 118140960795 + 3288324 * 2 ^ 59
def prefixEnd_3288324 : Nat := 4983230072969 + 3 ^ 40 * 3288324 * 2
def baseEnd_3288324 : Nat := 20845564934756761122559

theorem tailTrace_3288324 : CollatzResearch.WordTrace tailWord_3288324 prefixEnd_3288324 20845564934756761122559 := by
  unfold tailWord_3288324
  simp only [CollatzResearch.WordTrace]
  refine ⟨59967514669485611936484013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79956686225980815915312017 59967514669485611936484013)
  ·
    refine ⟨22487818001057104476181505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59967514669485611936484013 22487818001057104476181505)
    ·
      refine ⟨16865863500792828357136129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22487818001057104476181505 16865863500792828357136129)
      ·
        refine ⟨12649397625594621267852097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16865863500792828357136129 12649397625594621267852097)
        ·
          refine ⟨9487048219195965950889073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12649397625594621267852097 9487048219195965950889073)
          ·
            refine ⟨7115286164396974463166805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9487048219195965950889073 7115286164396974463166805)
            ·
              refine ⟨20845564934756761122559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7115286164396974463166805 20845564934756761122559)
              ·
                rfl

theorem cell23_3288324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 10].length) (baseStart_3288324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288324 prefixEnd_3288324 := by exact prefixLift 3288324
  have htrace : WordTrace (prefixWord ++ tailWord_3288324) baseStart_3288324 baseEnd_3288324 := by
    simpa [prefixWord, tailWord_3288324, baseEnd_3288324] using wordTrace_append hprefix tailTrace_3288324
  have hstable : (prefixWord ++ tailWord_3288324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288324).length < 2 ^ (prefixWord ++ tailWord_3288324).sum := by decide
  have hdescent : baseEnd_3288324 < baseStart_3288324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288378 : List Nat := [3, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2]
def baseStart_3288378 : Nat := 118140960795 + 3288378 * 2 ^ 59
def prefixEnd_3288378 : Nat := 4983230072969 + 3 ^ 40 * 3288378 * 2
def baseEnd_3288378 : Nat := 1688518487670640439652031

theorem tailTrace_3288378 : CollatzResearch.WordTrace tailWord_3288378 prefixEnd_3288378 1688518487670640439652031 := by
  unfold tailWord_3288378
  simp only [CollatzResearch.WordTrace]
  refine ⟨29984249720193897773858447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79957999253850394063622525 29984249720193897773858447)
  ·
    refine ⟨44976374580290846660787671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29984249720193897773858447 44976374580290846660787671)
    ·
      refine ⟨67464561870436269991181507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44976374580290846660787671 67464561870436269991181507)
      ·
        refine ⟨101196842805654404986772261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67464561870436269991181507 101196842805654404986772261)
        ·
          refine ⟨18974408026060200935019799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101196842805654404986772261 18974408026060200935019799)
          ·
            refine ⟨28461612039090301402529699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18974408026060200935019799 28461612039090301402529699)
            ·
              refine ⟨42692418058635452103794549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28461612039090301402529699 42692418058635452103794549)
              ·
                refine ⟨4002414192997073634730739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42692418058635452103794549 4002414192997073634730739)
                ·
                  refine ⟨6003621289495610452096109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4002414192997073634730739 6003621289495610452096109)
                  ·
                    refine ⟨2251357983560853919536041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6003621289495610452096109 2251357983560853919536041)
                    ·
                      refine ⟨1688518487670640439652031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2251357983560853919536041 1688518487670640439652031)
                      ·
                        rfl

theorem cell23_3288378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2].length) (baseStart_3288378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288378 prefixEnd_3288378 := by exact prefixLift 3288378
  have htrace : WordTrace (prefixWord ++ tailWord_3288378) baseStart_3288378 baseEnd_3288378 := by
    simpa [prefixWord, tailWord_3288378, baseEnd_3288378] using wordTrace_append hprefix tailTrace_3288378
  have hstable : (prefixWord ++ tailWord_3288378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288378).length < 2 ^ (prefixWord ++ tailWord_3288378).sum := by decide
  have hdescent : baseEnd_3288378 < baseStart_3288378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288406 : List Nat := [5, 2, 3, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_3288406 : Nat := 118140960795 + 3288406 * 2 ^ 59
def prefixEnd_3288406 : Nat := 4983230072969 + 3 ^ 40 * 3288406 * 2
def baseEnd_3288406 : Nat := 1688532865128966330101903

theorem tailTrace_3288406 : CollatzResearch.WordTrace tailWord_3288406 prefixEnd_3288406 1688532865128966330101903 := by
  unfold tailWord_3288406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7496126257792134492340817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79958680083116101251635381 7496126257792134492340817)
  ·
    refine ⟨5622094693344100869255613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7496126257792134492340817 5622094693344100869255613)
    ·
      refine ⟨2108285510004037825970855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5622094693344100869255613 2108285510004037825970855)
      ·
        refine ⟨3162428265006056738956283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2108285510004037825970855 3162428265006056738956283)
        ·
          refine ⟨4743642397509085108434425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3162428265006056738956283 4743642397509085108434425)
          ·
            refine ⟨3557731798131813831325819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4743642397509085108434425 3557731798131813831325819)
            ·
              refine ⟨5336597697197720746988729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3557731798131813831325819 5336597697197720746988729)
              ·
                refine ⟨4002448272898290560241547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5336597697197720746988729 4002448272898290560241547)
                ·
                  refine ⟨6003672409347435840362321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4002448272898290560241547 6003672409347435840362321)
                  ·
                    refine ⟨4502754307010576880271741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6003672409347435840362321 4502754307010576880271741)
                    ·
                      refine ⟨1688532865128966330101903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4502754307010576880271741 1688532865128966330101903)
                      ·
                        rfl

theorem cell23_3288406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_3288406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288406 prefixEnd_3288406 := by exact prefixLift 3288406
  have htrace : WordTrace (prefixWord ++ tailWord_3288406) baseStart_3288406 baseEnd_3288406 := by
    simpa [prefixWord, tailWord_3288406, baseEnd_3288406] using wordTrace_append hprefix tailTrace_3288406
  have hstable : (prefixWord ++ tailWord_3288406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288406).length < 2 ^ (prefixWord ++ tailWord_3288406).sum := by decide
  have hdescent : baseEnd_3288406 < baseStart_3288406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288431 : List Nat := [1, 1, 2, 1, 3, 1, 4, 5, 5]
def baseStart_3288431 : Nat := 118140960795 + 3288431 * 2 ^ 59
def prefixEnd_3288431 : Nat := 4983230072969 + 3 ^ 40 * 3288431 * 2
def baseEnd_3288431 : Nat := 187616189127258748032143

theorem tailTrace_3288431 : CollatzResearch.WordTrace tailWord_3288431 prefixEnd_3288431 187616189127258748032143 := by
  unfold tailWord_3288431
  simp only [CollatzResearch.WordTrace]
  refine ⟨119938931949583581147113147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79959287966389054098075431 119938931949583581147113147)
  ·
    refine ⟨179908397924375371720669721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119938931949583581147113147 179908397924375371720669721)
    ·
      refine ⟨134931298443281528790502291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179908397924375371720669721 134931298443281528790502291)
      ·
        refine ⟨202396947664922293185753437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134931298443281528790502291 202396947664922293185753437)
        ·
          refine ⟨75898855374345859944657539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202396947664922293185753437 75898855374345859944657539)
          ·
            refine ⟨113848283061518789916986309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75898855374345859944657539 113848283061518789916986309)
            ·
              refine ⟨21346553074034773109434933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113848283061518789916986309 21346553074034773109434933)
              ·
                refine ⟨2001239350690759979009525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21346553074034773109434933 2001239350690759979009525)
                ·
                  refine ⟨187616189127258748032143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2001239350690759979009525 187616189127258748032143)
                  ·
                    rfl

theorem cell23_3288431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 5].length) (baseStart_3288431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288431 prefixEnd_3288431 := by exact prefixLift 3288431
  have htrace : WordTrace (prefixWord ++ tailWord_3288431) baseStart_3288431 baseEnd_3288431 := by
    simpa [prefixWord, tailWord_3288431, baseEnd_3288431] using wordTrace_append hprefix tailTrace_3288431
  have hstable : (prefixWord ++ tailWord_3288431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288431).length < 2 ^ (prefixWord ++ tailWord_3288431).sum := by decide
  have hdescent : baseEnd_3288431 < baseStart_3288431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288548 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 5, 1, 3]
def baseStart_3288548 : Nat := 118140960795 + 3288548 * 2 ^ 59
def prefixEnd_3288548 : Nat := 4983230072969 + 3 ^ 40 * 3288548 * 2
def baseEnd_3288548 : Nat := 1688605779381904774526249

theorem tailTrace_3288548 : CollatzResearch.WordTrace tailWord_3288548 prefixEnd_3288548 1688605779381904774526249 := by
  unfold tailWord_3288548
  simp only [CollatzResearch.WordTrace]
  refine ⟨59971599645079855064561149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79962132860106473419414865 59971599645079855064561149)
  ·
    refine ⟨22489349866904945649210431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59971599645079855064561149 22489349866904945649210431)
    ·
      refine ⟨33734024800357418473815647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22489349866904945649210431 33734024800357418473815647)
      ·
        refine ⟨50601037200536127710723471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33734024800357418473815647 50601037200536127710723471)
        ·
          refine ⟨75901555800804191566085207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50601037200536127710723471 75901555800804191566085207)
          ·
            refine ⟨113852333701206287349127811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75901555800804191566085207 113852333701206287349127811)
            ·
              refine ⟨170778500551809431023691717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113852333701206287349127811 170778500551809431023691717)
              ·
                refine ⟨32020968853464268316942197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170778500551809431023691717 32020968853464268316942197)
                ·
                  refine ⟨3001965830012275154713331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32020968853464268316942197 3001965830012275154713331)
                  ·
                    refine ⟨4502948745018412732069997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3001965830012275154713331 4502948745018412732069997)
                    ·
                      refine ⟨1688605779381904774526249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4502948745018412732069997 1688605779381904774526249)
                      ·
                        rfl

theorem cell23_3288548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_3288548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288548 prefixEnd_3288548 := by exact prefixLift 3288548
  have htrace : WordTrace (prefixWord ++ tailWord_3288548) baseStart_3288548 baseEnd_3288548 := by
    simpa [prefixWord, tailWord_3288548, baseEnd_3288548] using wordTrace_append hprefix tailTrace_3288548
  have hstable : (prefixWord ++ tailWord_3288548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288548).length < 2 ^ (prefixWord ++ tailWord_3288548).sum := by decide
  have hdescent : baseEnd_3288548 < baseStart_3288548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288571 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 4]
def baseStart_3288571 : Nat := 118140960795 + 3288571 * 2 ^ 59
def prefixEnd_3288571 : Nat := 4983230072969 + 3 ^ 40 * 3288571 * 2
def baseEnd_3288571 : Nat := 1688617589436958184538643

theorem tailTrace_3288571 : CollatzResearch.WordTrace tailWord_3288571 prefixEnd_3288571 1688617589436958184538643 := by
  unfold tailWord_3288571
  simp only [CollatzResearch.WordTrace]
  refine ⟨119944038169076385057209567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79962692112717590038139711 119944038169076385057209567)
  ·
    refine ⟨179916057253614577585814351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119944038169076385057209567 179916057253614577585814351)
    ·
      refine ⟨269874085880421866378721527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179916057253614577585814351 269874085880421866378721527)
      ·
        refine ⟨404811128820632799568082291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269874085880421866378721527 404811128820632799568082291)
        ·
          refine ⟨607216693230949199352123437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404811128820632799568082291 607216693230949199352123437)
          ·
            refine ⟨227706259961605949757046289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 607216693230949199352123437 227706259961605949757046289)
            ·
              refine ⟨170779694971204462317784717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227706259961605949757046289 170779694971204462317784717)
              ·
                refine ⟨64042385614201673369169269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170779694971204462317784717 64042385614201673369169269)
                ·
                  refine ⟨6003973651331406878359619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64042385614201673369169269 6003973651331406878359619)
                  ·
                    refine ⟨9005960476997110317539429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6003973651331406878359619 9005960476997110317539429)
                    ·
                      refine ⟨1688617589436958184538643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9005960476997110317539429 1688617589436958184538643)
                      ·
                        rfl

theorem cell23_3288571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 4].length) (baseStart_3288571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288571 prefixEnd_3288571 := by exact prefixLift 3288571
  have htrace : WordTrace (prefixWord ++ tailWord_3288571) baseStart_3288571 baseEnd_3288571 := by
    simpa [prefixWord, tailWord_3288571, baseEnd_3288571] using wordTrace_append hprefix tailTrace_3288571
  have hstable : (prefixWord ++ tailWord_3288571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288571).length < 2 ^ (prefixWord ++ tailWord_3288571).sum := by decide
  have hdescent : baseEnd_3288571 < baseStart_3288571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288581 : List Nat := [1, 3, 1, 1, 2, 2, 1, 5, 1, 6]
def baseStart_3288581 : Nat := 118140960795 + 3288581 * 2 ^ 59
def prefixEnd_3288581 : Nat := 4983230072969 + 3 ^ 40 * 3288581 * 2
def baseEnd_3288581 : Nat := 562874241414501048471199

theorem tailTrace_3288581 : CollatzResearch.WordTrace tailWord_3288581 prefixEnd_3288581 562874241414501048471199 := by
  unfold tailWord_3288581
  simp only [CollatzResearch.WordTrace]
  refine ⟨119944402899040156765073597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79962935266026771176715731 119944402899040156765073597)
  ·
    refine ⟨44979151087140058786902599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119944402899040156765073597 44979151087140058786902599)
    ·
      refine ⟨67468726630710088180353899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44979151087140058786902599 67468726630710088180353899)
      ·
        refine ⟨101203089946065132270530849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67468726630710088180353899 101203089946065132270530849)
        ·
          refine ⟨75902317459548849202898137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101203089946065132270530849 75902317459548849202898137)
          ·
            refine ⟨56926738094661636902173603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75902317459548849202898137 56926738094661636902173603)
            ·
              refine ⟨85390107141992455353260405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56926738094661636902173603 85390107141992455353260405)
              ·
                refine ⟨8005322544561792689368163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85390107141992455353260405 8005322544561792689368163)
                ·
                  refine ⟨12007983816842689034052245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8005322544561792689368163 12007983816842689034052245)
                  ·
                    refine ⟨562874241414501048471199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12007983816842689034052245 562874241414501048471199)
                    ·
                      rfl

theorem cell23_3288581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_3288581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288581 prefixEnd_3288581 := by exact prefixLift 3288581
  have htrace : WordTrace (prefixWord ++ tailWord_3288581) baseStart_3288581 baseEnd_3288581 := by
    simpa [prefixWord, tailWord_3288581, baseEnd_3288581] using wordTrace_append hprefix tailTrace_3288581
  have hstable : (prefixWord ++ tailWord_3288581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288581).length < 2 ^ (prefixWord ++ tailWord_3288581).sum := by decide
  have hdescent : baseEnd_3288581 < baseStart_3288581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288611 : List Nat := [1, 1, 1, 4, 5, 11]
def baseStart_3288611 : Nat := 118140960795 + 3288611 * 2 ^ 59
def prefixEnd_3288611 : Nat := 4983230072969 + 3 ^ 40 * 3288611 * 2
def baseEnd_3288611 : Nat := 6949128101494395177113

theorem tailTrace_3288611 : CollatzResearch.WordTrace tailWord_3288611 prefixEnd_3288611 6949128101494395177113 := by
  unfold tailWord_3288611
  simp only [CollatzResearch.WordTrace]
  refine ⟨119945497088931471888665687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79963664725954314592443791 119945497088931471888665687)
  ·
    refine ⟨179918245633397207832998531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119945497088931471888665687 179918245633397207832998531)
    ·
      refine ⟨269877368450095811749497797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179918245633397207832998531 269877368450095811749497797)
      ·
        refine ⟨50602006584392964703030837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269877368450095811749497797 50602006584392964703030837)
        ·
          refine ⟨4743938117286840440909141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50602006584392964703030837 4743938117286840440909141)
          ·
            refine ⟨6949128101494395177113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4743938117286840440909141 6949128101494395177113)
            ·
              rfl

theorem cell23_3288611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 11].length) (baseStart_3288611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288611 prefixEnd_3288611 := by exact prefixLift 3288611
  have htrace : WordTrace (prefixWord ++ tailWord_3288611) baseStart_3288611 baseEnd_3288611 := by
    simpa [prefixWord, tailWord_3288611, baseEnd_3288611] using wordTrace_append hprefix tailTrace_3288611
  have hstable : (prefixWord ++ tailWord_3288611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288611).length < 2 ^ (prefixWord ++ tailWord_3288611).sum := by decide
  have hdescent : baseEnd_3288611 < baseStart_3288611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288618 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_3288618 : Nat := 118140960795 + 3288618 * 2 ^ 59
def prefixEnd_3288618 : Nat := 4983230072969 + 3 ^ 40 * 3288618 * 2
def baseEnd_3288618 : Nat := 1688641723027719500650927

theorem tailTrace_3288618 : CollatzResearch.WordTrace tailWord_3288618 prefixEnd_3288618 1688641723027719500650927 := by
  unfold tailWord_3288618
  simp only [CollatzResearch.WordTrace]
  refine ⟨29986438099976528021042627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79963834933270741389447005 29986438099976528021042627)
  ·
    refine ⟨44979657149964792031563941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29986438099976528021042627 44979657149964792031563941)
    ·
      refine ⟨8433685715618398505918239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44979657149964792031563941 8433685715618398505918239)
      ·
        refine ⟨12650528573427597758877359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8433685715618398505918239 12650528573427597758877359)
        ·
          refine ⟨18975792860141396638316039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12650528573427597758877359 18975792860141396638316039)
          ·
            refine ⟨28463689290212094957474059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18975792860141396638316039 28463689290212094957474059)
            ·
              refine ⟨42695533935318142436211089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28463689290212094957474059 42695533935318142436211089)
              ·
                refine ⟨32021650451488606827158317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42695533935318142436211089 32021650451488606827158317)
                ·
                  refine ⟨12008118919308227560184369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32021650451488606827158317 12008118919308227560184369)
                  ·
                    refine ⟨9006089189481170670138277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12008118919308227560184369 9006089189481170670138277)
                    ·
                      refine ⟨1688641723027719500650927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9006089189481170670138277 1688641723027719500650927)
                      ·
                        rfl

theorem cell23_3288618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_3288618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288618 prefixEnd_3288618 := by exact prefixLift 3288618
  have htrace : WordTrace (prefixWord ++ tailWord_3288618) baseStart_3288618 baseEnd_3288618 := by
    simpa [prefixWord, tailWord_3288618, baseEnd_3288618] using wordTrace_append hprefix tailTrace_3288618
  have hstable : (prefixWord ++ tailWord_3288618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288618).length < 2 ^ (prefixWord ++ tailWord_3288618).sum := by decide
  have hdescent : baseEnd_3288618 < baseStart_3288618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288651 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 5]
def baseStart_3288651 : Nat := 118140960795 + 3288651 * 2 ^ 59
def prefixEnd_3288651 : Nat := 4983230072969 + 3 ^ 40 * 3288651 * 2
def baseEnd_3288651 : Nat := 1688658667889317871538275

theorem tailTrace_3288651 : CollatzResearch.WordTrace tailWord_3288651 prefixEnd_3288651 1688658667889317871538275 := by
  unfold tailWord_3288651
  simp only [CollatzResearch.WordTrace]
  refine ⟨119946956008786558720121807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79964637339191039146747871 119946956008786558720121807)
  ·
    refine ⟨179920434013179838080182711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119946956008786558720121807 179920434013179838080182711)
    ·
      refine ⟨269880651019769757120274067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179920434013179838080182711 269880651019769757120274067)
      ·
        refine ⟨404820976529654635680411101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269880651019769757120274067 404820976529654635680411101)
        ·
          refine ⟨151807866198620488380154163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 404820976529654635680411101 151807866198620488380154163)
          ·
            refine ⟨227711799297930732570231245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151807866198620488380154163 227711799297930732570231245)
            ·
              refine ⟨85391924736724024713836717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227711799297930732570231245 85391924736724024713836717)
              ·
                refine ⟨32021971776271509267688769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85391924736724024713836717 32021971776271509267688769)
                ·
                  refine ⟨24016478832203631950766577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32021971776271509267688769 24016478832203631950766577)
                  ·
                    refine ⟨18012359124152723963074933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24016478832203631950766577 18012359124152723963074933)
                    ·
                      refine ⟨1688658667889317871538275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18012359124152723963074933 1688658667889317871538275)
                      ·
                        rfl

theorem cell23_3288651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 5].length) (baseStart_3288651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288651 prefixEnd_3288651 := by exact prefixLift 3288651
  have htrace : WordTrace (prefixWord ++ tailWord_3288651) baseStart_3288651 baseEnd_3288651 := by
    simpa [prefixWord, tailWord_3288651, baseEnd_3288651] using wordTrace_append hprefix tailTrace_3288651
  have hstable : (prefixWord ++ tailWord_3288651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288651).length < 2 ^ (prefixWord ++ tailWord_3288651).sum := by decide
  have hdescent : baseEnd_3288651 < baseStart_3288651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288662 : List Nat := [5, 2, 2, 2, 1, 1, 10]
def baseStart_3288662 : Nat := 118140960795 + 3288662 * 2 ^ 59
def prefixEnd_3288662 : Nat := 4983230072969 + 3 ^ 40 * 3288662 * 2
def baseEnd_3288662 : Nat := 20847707607117497882725

theorem tailTrace_3288662 : CollatzResearch.WordTrace tailWord_3288662 prefixEnd_3288662 20847707607117497882725 := by
  unfold tailWord_3288662
  simp only [CollatzResearch.WordTrace]
  refine ⟨7496709825734169224923265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79964904807831138399181493 7496709825734169224923265)
  ·
    refine ⟨5622532369300626918692449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7496709825734169224923265 5622532369300626918692449)
    ·
      refine ⟨4216899276975470189019337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5622532369300626918692449 4216899276975470189019337)
      ·
        refine ⟨3162674457731602641764503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4216899276975470189019337 3162674457731602641764503)
        ·
          refine ⟨4744011686597403962646755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3162674457731602641764503 4744011686597403962646755)
          ·
            refine ⟨7116017529896105943970133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4744011686597403962646755 7116017529896105943970133)
            ·
              refine ⟨20847707607117497882725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7116017529896105943970133 20847707607117497882725)
              ·
                rfl

theorem cell23_3288662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 10].length) (baseStart_3288662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288662 prefixEnd_3288662 := by exact prefixLift 3288662
  have htrace : WordTrace (prefixWord ++ tailWord_3288662) baseStart_3288662 baseEnd_3288662 := by
    simpa [prefixWord, tailWord_3288662, baseEnd_3288662] using wordTrace_append hprefix tailTrace_3288662
  have hstable : (prefixWord ++ tailWord_3288662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288662).length < 2 ^ (prefixWord ++ tailWord_3288662).sum := by decide
  have hdescent : baseEnd_3288662 < baseStart_3288662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288688 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 2, 6]
def baseStart_3288688 : Nat := 118140960795 + 3288688 * 2 ^ 59
def prefixEnd_3288688 : Nat := 4983230072969 + 3 ^ 40 * 3288688 * 2
def baseEnd_3288688 : Nat := 562892555557844742258535

theorem tailTrace_3288688 : CollatzResearch.WordTrace tailWord_3288688 prefixEnd_3288688 562892555557844742258535 := by
  unfold tailWord_3288688
  simp only [CollatzResearch.WordTrace]
  refine ⟨59974152754826257019609359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79965537006435009359479145 59974152754826257019609359)
  ·
    refine ⟨89961229132239385529414039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59974152754826257019609359 89961229132239385529414039)
    ·
      refine ⟨134941843698359078294121059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89961229132239385529414039 134941843698359078294121059)
      ·
        refine ⟨202412765547538617441181589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134941843698359078294121059 202412765547538617441181589)
        ·
          refine ⟨9488098385040872692555387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 202412765547538617441181589 9488098385040872692555387)
          ·
            refine ⟨14232147577561309038833081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9488098385040872692555387 14232147577561309038833081)
            ·
              refine ⟨10674110683170981779124811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14232147577561309038833081 10674110683170981779124811)
              ·
                refine ⟨16011166024756472668687217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10674110683170981779124811 16011166024756472668687217)
                ·
                  refine ⟨12008374518567354501515413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16011166024756472668687217 12008374518567354501515413)
                  ·
                    refine ⟨562892555557844742258535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12008374518567354501515413 562892555557844742258535)
                    ·
                      rfl

theorem cell23_3288688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 2, 6].length) (baseStart_3288688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288688 prefixEnd_3288688 := by exact prefixLift 3288688
  have htrace : WordTrace (prefixWord ++ tailWord_3288688) baseStart_3288688 baseEnd_3288688 := by
    simpa [prefixWord, tailWord_3288688, baseEnd_3288688] using wordTrace_append hprefix tailTrace_3288688
  have hstable : (prefixWord ++ tailWord_3288688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288688).length < 2 ^ (prefixWord ++ tailWord_3288688).sum := by decide
  have hdescent : baseEnd_3288688 < baseStart_3288688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288765 : List Nat := [1, 4, 1, 2, 1, 2, 4, 1, 2, 5]
def baseStart_3288765 : Nat := 118140960795 + 3288765 * 2 ^ 59
def prefixEnd_3288765 : Nat := 4983230072969 + 3 ^ 40 * 3288765 * 2
def baseEnd_3288765 : Nat := 562905734894643475170917

theorem tailTrace_3288765 : CollatzResearch.WordTrace tailWord_3288765 prefixEnd_3288765 562905734894643475170917 := by
  unfold tailWord_3288765
  simp only [CollatzResearch.WordTrace]
  refine ⟨119951113930373556189771749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79967409286915704126514499 119951113930373556189771749)
  ·
    refine ⟨22490833861945041785582203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119951113930373556189771749 22490833861945041785582203)
    ·
      refine ⟨33736250792917562678373305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22490833861945041785582203 33736250792917562678373305)
      ·
        refine ⟨25302188094688172008779979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33736250792917562678373305 25302188094688172008779979)
        ·
          refine ⟨37953282142032258013169969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25302188094688172008779979 37953282142032258013169969)
          ·
            refine ⟨28464961606524193509877477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37953282142032258013169969 28464961606524193509877477)
            ·
              refine ⟨5337180301223286283102027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28464961606524193509877477 5337180301223286283102027)
              ·
                refine ⟨8005770451834929424653041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5337180301223286283102027 8005770451834929424653041)
                ·
                  refine ⟨6004327838876197068489781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8005770451834929424653041 6004327838876197068489781)
                  ·
                    refine ⟨562905734894643475170917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6004327838876197068489781 562905734894643475170917)
                    ·
                      rfl

theorem cell23_3288765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_3288765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288765 prefixEnd_3288765 := by exact prefixLift 3288765
  have htrace : WordTrace (prefixWord ++ tailWord_3288765) baseStart_3288765 baseEnd_3288765 := by
    simpa [prefixWord, tailWord_3288765, baseEnd_3288765] using wordTrace_append hprefix tailTrace_3288765
  have hstable : (prefixWord ++ tailWord_3288765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288765).length < 2 ^ (prefixWord ++ tailWord_3288765).sum := by decide
  have hdescent : baseEnd_3288765 < baseStart_3288765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288785 : List Nat := [1, 2, 2, 1, 2, 4, 2, 2, 2, 1, 4]
def baseStart_3288785 : Nat := 118140960795 + 3288785 * 2 ^ 59
def prefixEnd_3288785 : Nat := 4983230072969 + 3 ^ 40 * 3288785 * 2
def baseEnd_3288785 : Nat := 1688727474297020347262659

theorem tailTrace_3288785 : CollatzResearch.WordTrace tailWord_3288785 prefixEnd_3288785 1688727474297020347262659 := by
  unfold tailWord_3288785
  simp only [CollatzResearch.WordTrace]
  refine ⟨119951843390301099605499809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79967895593534066403666539 119951843390301099605499809)
  ·
    refine ⟨89963882542725824704124857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119951843390301099605499809 89963882542725824704124857)
    ·
      refine ⟨67472911907044368528093643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89963882542725824704124857 67472911907044368528093643)
      ·
        refine ⟨101209367860566552792140465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67472911907044368528093643 101209367860566552792140465)
        ·
          refine ⟨75907025895424914594105349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101209367860566552792140465 75907025895424914594105349)
          ·
            refine ⟨14232567355392171486394753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75907025895424914594105349 14232567355392171486394753)
            ·
              refine ⟨10674425516544128614796065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14232567355392171486394753 10674425516544128614796065)
              ·
                refine ⟨8005819137408096461097049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10674425516544128614796065 8005819137408096461097049)
                ·
                  refine ⟨6004364353056072345822787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8005819137408096461097049 6004364353056072345822787)
                  ·
                    refine ⟨9006546529584108518734181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6004364353056072345822787 9006546529584108518734181)
                    ·
                      refine ⟨1688727474297020347262659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9006546529584108518734181 1688727474297020347262659)
                      ·
                        rfl

theorem cell23_3288785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_3288785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288785 prefixEnd_3288785 := by exact prefixLift 3288785
  have htrace : WordTrace (prefixWord ++ tailWord_3288785) baseStart_3288785 baseEnd_3288785 := by
    simpa [prefixWord, tailWord_3288785, baseEnd_3288785] using wordTrace_append hprefix tailTrace_3288785
  have hstable : (prefixWord ++ tailWord_3288785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288785).length < 2 ^ (prefixWord ++ tailWord_3288785).sum := by decide
  have hdescent : baseEnd_3288785 < baseStart_3288785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288805 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 1, 4, 3]
def baseStart_3288805 : Nat := 118140960795 + 3288805 * 2 ^ 59
def prefixEnd_3288805 : Nat := 4983230072969 + 3 ^ 40 * 3288805 * 2
def baseEnd_3288805 : Nat := 1688737743910110269012567

theorem tailTrace_3288805 : CollatzResearch.WordTrace tailWord_3288805 prefixEnd_3288805 1688737743910110269012567 := by
  unfold tailWord_3288805
  simp only [CollatzResearch.WordTrace]
  refine ⟨119952572850228643021227869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79968381900152428680818579 119952572850228643021227869)
  ·
    refine ⟨44982214818835741132960451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119952572850228643021227869 44982214818835741132960451)
    ·
      refine ⟨67473322228253611699440677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44982214818835741132960451 67473322228253611699440677)
      ·
        refine ⟨12651247917797552193645127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67473322228253611699440677 12651247917797552193645127)
        ·
          refine ⟨18976871876696328290467691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12651247917797552193645127 18976871876696328290467691)
          ·
            refine ⟨28465307815044492435701537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18976871876696328290467691 28465307815044492435701537)
            ·
              refine ⟨21348980861283369326776153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28465307815044492435701537 21348980861283369326776153)
              ·
                refine ⟨16011735645962526995082115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21348980861283369326776153 16011735645962526995082115)
                ·
                  refine ⟨24017603468943790492623173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16011735645962526995082115 24017603468943790492623173)
                  ·
                    refine ⟨4503300650426960717366845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24017603468943790492623173 4503300650426960717366845)
                    ·
                      refine ⟨1688737743910110269012567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4503300650426960717366845 1688737743910110269012567)
                      ·
                        rfl

theorem cell23_3288805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_3288805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288805 prefixEnd_3288805 := by exact prefixLift 3288805
  have htrace : WordTrace (prefixWord ++ tailWord_3288805) baseStart_3288805 baseEnd_3288805 := by
    simpa [prefixWord, tailWord_3288805, baseEnd_3288805] using wordTrace_append hprefix tailTrace_3288805
  have hstable : (prefixWord ++ tailWord_3288805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288805).length < 2 ^ (prefixWord ++ tailWord_3288805).sum := by decide
  have hdescent : baseEnd_3288805 < baseStart_3288805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288822 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_3288822 : Nat := 118140960795 + 3288822 * 2 ^ 59
def prefixEnd_3288822 : Nat := 4983230072969 + 3 ^ 40 * 3288822 * 2
def baseEnd_3288822 : Nat := 1688746473081236702499989

theorem tailTrace_3288822 : CollatzResearch.WordTrace tailWord_3288822 prefixEnd_3288822 1688746473081236702499989 := by
  unfold tailWord_3288822
  simp only [CollatzResearch.WordTrace]
  refine ⟨7497074555697940932787295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79968795260778036616397813 7497074555697940932787295)
  ·
    refine ⟨11245611833546911399180943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7497074555697940932787295 11245611833546911399180943)
    ·
      refine ⟨16868417750320367098771415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11245611833546911399180943 16868417750320367098771415)
      ·
        refine ⟨25302626625480550648157123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16868417750320367098771415 25302626625480550648157123)
        ·
          refine ⟨37953939938220825972235685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25302626625480550648157123 37953939938220825972235685)
          ·
            refine ⟨7116363738416404869794191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37953939938220825972235685 7116363738416404869794191)
            ·
              refine ⟨10674545607624607304691287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7116363738416404869794191 10674545607624607304691287)
              ·
                refine ⟨16011818411436910957036931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10674545607624607304691287 16011818411436910957036931)
                ·
                  refine ⟨24017727617155366435555397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16011818411436910957036931 24017727617155366435555397)
                  ·
                    refine ⟨4503323928216631206666637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24017727617155366435555397 4503323928216631206666637)
                    ·
                      refine ⟨1688746473081236702499989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4503323928216631206666637 1688746473081236702499989)
                      ·
                        rfl

theorem cell23_3288822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_3288822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288822 prefixEnd_3288822 := by exact prefixLift 3288822
  have htrace : WordTrace (prefixWord ++ tailWord_3288822) baseStart_3288822 baseEnd_3288822 := by
    simpa [prefixWord, tailWord_3288822, baseEnd_3288822] using wordTrace_append hprefix tailTrace_3288822
  have hstable : (prefixWord ++ tailWord_3288822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288822).length < 2 ^ (prefixWord ++ tailWord_3288822).sum := by decide
  have hdescent : baseEnd_3288822 < baseStart_3288822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288842 : List Nat := [3, 1, 2, 2, 1, 5, 1, 2, 6]
def baseStart_3288842 : Nat := 118140960795 + 3288842 * 2 ^ 59
def prefixEnd_3288842 : Nat := 4983230072969 + 3 ^ 40 * 3288842 * 2
def baseEnd_3288842 : Nat := 187639638077147402694433

theorem tailTrace_3288842 : CollatzResearch.WordTrace tailWord_3288842 prefixEnd_3288842 187639638077147402694433 := by
  unfold tailWord_3288842
  simp only [CollatzResearch.WordTrace]
  refine ⟨29988480587773649585081195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79969281567396398893549853 29988480587773649585081195)
  ·
    refine ⟨44982720881660474377621793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29988480587773649585081195 44982720881660474377621793)
    ·
      refine ⟨33737040661245355783216345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44982720881660474377621793 33737040661245355783216345)
      ·
        refine ⟨25302780495934016837412259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33737040661245355783216345 25302780495934016837412259)
        ·
          refine ⟨37954170743901025256118389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25302780495934016837412259 37954170743901025256118389)
          ·
            refine ⟨3558203507240721117761099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37954170743901025256118389 3558203507240721117761099)
            ·
              refine ⟨5337305260861081676641649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3558203507240721117761099 5337305260861081676641649)
              ·
                refine ⟨4002978945645811257481237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5337305260861081676641649 4002978945645811257481237)
                ·
                  refine ⟨187639638077147402694433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4002978945645811257481237 187639638077147402694433)
                  ·
                    rfl

theorem cell23_3288842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 6].length) (baseStart_3288842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288842 prefixEnd_3288842 := by exact prefixLift 3288842
  have htrace : WordTrace (prefixWord ++ tailWord_3288842) baseStart_3288842 baseEnd_3288842 := by
    simpa [prefixWord, tailWord_3288842, baseEnd_3288842] using wordTrace_append hprefix tailTrace_3288842
  have hstable : (prefixWord ++ tailWord_3288842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288842).length < 2 ^ (prefixWord ++ tailWord_3288842).sum := by decide
  have hdescent : baseEnd_3288842 < baseStart_3288842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288872 : List Nat := [2, 1, 5, 1, 1, 2, 1, 4, 1, 5]
def baseStart_3288872 : Nat := 118140960795 + 3288872 * 2 ^ 59
def prefixEnd_3288872 : Nat := 4983230072969 + 3 ^ 40 * 3288872 * 2
def baseEnd_3288872 : Nat := 562924049037987168958253

theorem tailTrace_3288872 : CollatzResearch.WordTrace tailWord_3288872 prefixEnd_3288872 562924049037987168958253 := by
  unfold tailWord_3288872
  simp only [CollatzResearch.WordTrace]
  refine ⟨59977508270492956731958435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79970011027323942309277913 59977508270492956731958435)
  ·
    refine ⟨89966262405739435097937653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59977508270492956731958435 89966262405739435097937653)
    ·
      refine ⟨8434337100538072040431655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89966262405739435097937653 8434337100538072040431655)
      ·
        refine ⟨12651505650807108060647483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8434337100538072040431655 12651505650807108060647483)
        ·
          refine ⟨18977258476210662090971225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12651505650807108060647483 18977258476210662090971225)
          ·
            refine ⟨14232943857157996568228419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18977258476210662090971225 14232943857157996568228419)
            ·
              refine ⟨21349415785736994852342629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14232943857157996568228419 21349415785736994852342629)
              ·
                refine ⟨4003015459825686534814243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21349415785736994852342629 4003015459825686534814243)
                ·
                  refine ⟨6004523189738529802221365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4003015459825686534814243 6004523189738529802221365)
                  ·
                    refine ⟨562924049037987168958253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6004523189738529802221365 562924049037987168958253)
                    ·
                      rfl

theorem cell23_3288872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_3288872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288872 prefixEnd_3288872 := by exact prefixLift 3288872
  have htrace : WordTrace (prefixWord ++ tailWord_3288872) baseStart_3288872 baseEnd_3288872 := by
    simpa [prefixWord, tailWord_3288872, baseEnd_3288872] using wordTrace_append hprefix tailTrace_3288872
  have hstable : (prefixWord ++ tailWord_3288872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288872).length < 2 ^ (prefixWord ++ tailWord_3288872).sum := by decide
  have hdescent : baseEnd_3288872 < baseStart_3288872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288892 : List Nat := [2, 2, 2, 2, 1, 1, 4, 3, 1, 1, 4]
def baseStart_3288892 : Nat := 118140960795 + 3288892 * 2 ^ 59
def prefixEnd_3288892 : Nat := 4983230072969 + 3 ^ 40 * 3288892 * 2
def baseEnd_3288892 : Nat := 1688782416727051428624667

theorem tailTrace_3288892 : CollatzResearch.WordTrace tailWord_3288892 prefixEnd_3288892 1688782416727051428624667 := by
  unfold tailWord_3288892
  simp only [CollatzResearch.WordTrace]
  refine ⟨59977873000456728439822465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79970497333942304586429953 59977873000456728439822465)
  ·
    refine ⟨44983404750342546329866849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59977873000456728439822465 44983404750342546329866849)
    ·
      refine ⟨33737553562756909747400137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44983404750342546329866849 33737553562756909747400137)
      ·
        refine ⟨25303165172067682310550103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33737553562756909747400137 25303165172067682310550103)
        ·
          refine ⟨37954747758101523465825155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25303165172067682310550103 37954747758101523465825155)
          ·
            refine ⟨56932121637152285198737733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37954747758101523465825155 56932121637152285198737733)
            ·
              refine ⟨10674772806966053474763325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56932121637152285198737733 10674772806966053474763325)
              ·
                refine ⟨4003039802612270053036247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10674772806966053474763325 4003039802612270053036247)
                ·
                  refine ⟨6004559703918405079554371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4003039802612270053036247 6004559703918405079554371)
                  ·
                    refine ⟨9006839555877607619331557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6004559703918405079554371 9006839555877607619331557)
                    ·
                      refine ⟨1688782416727051428624667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9006839555877607619331557 1688782416727051428624667)
                      ·
                        rfl

theorem cell23_3288892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_3288892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288892 prefixEnd_3288892 := by exact prefixLift 3288892
  have htrace : WordTrace (prefixWord ++ tailWord_3288892) baseStart_3288892 baseEnd_3288892 := by
    simpa [prefixWord, tailWord_3288892, baseEnd_3288892] using wordTrace_append hprefix tailTrace_3288892
  have hstable : (prefixWord ++ tailWord_3288892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288892).length < 2 ^ (prefixWord ++ tailWord_3288892).sum := by decide
  have hdescent : baseEnd_3288892 < baseStart_3288892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288919 : List Nat := [1, 1, 3, 2, 5, 1, 1, 3, 2, 4]
def baseStart_3288919 : Nat := 118140960795 + 3288919 * 2 ^ 59
def prefixEnd_3288919 : Nat := 4983230072969 + 3 ^ 40 * 3288919 * 2
def baseEnd_3288919 : Nat := 562932093568240940995681

theorem tailTrace_3288919 : CollatzResearch.WordTrace tailWord_3288919 prefixEnd_3288919 562932093568240940995681 := by
  unfold tailWord_3288919
  simp only [CollatzResearch.WordTrace]
  refine ⟨119956730771815640490877811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79971153847877093660585207 119956730771815640490877811)
  ·
    refine ⟨179935096157723460736316717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119956730771815640490877811 179935096157723460736316717)
    ·
      refine ⟨67475661059146297776118769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179935096157723460736316717 67475661059146297776118769)
      ·
        refine ⟨50606745794359723332089077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67475661059146297776118769 50606745794359723332089077)
        ·
          refine ⟨4744382418221224062383351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50606745794359723332089077 4744382418221224062383351)
          ·
            refine ⟨7116573627331836093575027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4744382418221224062383351 7116573627331836093575027)
            ·
              refine ⟨10674860440997754140362541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7116573627331836093575027 10674860440997754140362541)
              ·
                refine ⟨4003072665374157802635953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10674860440997754140362541 4003072665374157802635953)
                ·
                  refine ⟨3002304499030618351976965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4003072665374157802635953 3002304499030618351976965)
                  ·
                    refine ⟨562932093568240940995681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3002304499030618351976965 562932093568240940995681)
                    ·
                      rfl

theorem cell23_3288919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_3288919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288919 prefixEnd_3288919 := by exact prefixLift 3288919
  have htrace : WordTrace (prefixWord ++ tailWord_3288919) baseStart_3288919 baseEnd_3288919 := by
    simpa [prefixWord, tailWord_3288919, baseEnd_3288919] using wordTrace_append hprefix tailTrace_3288919
  have hstable : (prefixWord ++ tailWord_3288919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288919).length < 2 ^ (prefixWord ++ tailWord_3288919).sum := by decide
  have hdescent : baseEnd_3288919 < baseStart_3288919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288965 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 1, 5, 4]
def baseStart_3288965 : Nat := 118140960795 + 3288965 * 2 ^ 59
def prefixEnd_3288965 : Nat := 4983230072969 + 3 ^ 40 * 3288965 * 2
def baseEnd_3288965 : Nat := 1688819900814829643011831

theorem tailTrace_3288965 : CollatzResearch.WordTrace tailWord_3288965 prefixEnd_3288965 1688819900814829643011831 := by
  unfold tailWord_3288965
  simp only [CollatzResearch.WordTrace]
  refine ⟨119958408529648990347052349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79972272353099326898034899 119958408529648990347052349)
  ·
    refine ⟨44984403198618371380144631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119958408529648990347052349 44984403198618371380144631)
    ·
      refine ⟨67476604797927557070216947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44984403198618371380144631 67476604797927557070216947)
      ·
        refine ⟨101214907196891335605325421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67476604797927557070216947 101214907196891335605325421)
        ·
          refine ⟨37955590198834250851997033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101214907196891335605325421 37955590198834250851997033)
          ·
            refine ⟨28466692649125688138997775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37955590198834250851997033 28466692649125688138997775)
            ·
              refine ⟨42700038973688532208496663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28466692649125688138997775 42700038973688532208496663)
              ·
                refine ⟨64050058460532798312744995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42700038973688532208496663 64050058460532798312744995)
                ·
                  refine ⟨96075087690799197469117493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64050058460532798312744995 96075087690799197469117493)
                  ·
                    refine ⟨9007039471012424762729765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96075087690799197469117493 9007039471012424762729765)
                    ·
                      refine ⟨1688819900814829643011831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9007039471012424762729765 1688819900814829643011831)
                      ·
                        rfl

theorem cell23_3288965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_3288965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288965 prefixEnd_3288965 := by exact prefixLift 3288965
  have htrace : WordTrace (prefixWord ++ tailWord_3288965) baseStart_3288965 baseEnd_3288965 := by
    simpa [prefixWord, tailWord_3288965, baseEnd_3288965] using wordTrace_append hprefix tailTrace_3288965
  have hstable : (prefixWord ++ tailWord_3288965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288965).length < 2 ^ (prefixWord ++ tailWord_3288965).sum := by decide
  have hdescent : baseEnd_3288965 < baseStart_3288965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288985 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 4, 1, 5]
def baseStart_3288985 : Nat := 118140960795 + 3288985 * 2 ^ 59
def prefixEnd_3288985 : Nat := 4983230072969 + 3 ^ 40 * 3288985 * 2
def baseEnd_3288985 : Nat := 1688830170427919564761739

theorem tailTrace_3288985 : CollatzResearch.WordTrace tailWord_3288985 prefixEnd_3288985 1688830170427919564761739 := by
  unfold tailWord_3288985
  simp only [CollatzResearch.WordTrace]
  refine ⟨119959137989576533762780409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79972758659717689175186939 119959137989576533762780409)
  ·
    refine ⟨89969353492182400322085307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119959137989576533762780409 89969353492182400322085307)
    ·
      refine ⟨134954030238273600483127961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89969353492182400322085307 134954030238273600483127961)
      ·
        refine ⟨101215522678705200362345971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134954030238273600483127961 101215522678705200362345971)
        ·
          refine ⟨151823284018057800543518957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101215522678705200362345971 151823284018057800543518957)
          ·
            refine ⟨56933731506771675203819609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151823284018057800543518957 56933731506771675203819609)
            ·
              refine ⟨42700298630078756402864707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56933731506771675203819609 42700298630078756402864707)
              ·
                refine ⟨64050447945118134604297061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42700298630078756402864707 64050447945118134604297061)
                ·
                  refine ⟨12009458989709650238305699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64050447945118134604297061 12009458989709650238305699)
                  ·
                    refine ⟨18014188484564475357458549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12009458989709650238305699 18014188484564475357458549)
                    ·
                      refine ⟨1688830170427919564761739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18014188484564475357458549 1688830170427919564761739)
                      ·
                        rfl

theorem cell23_3288985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_3288985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288985 prefixEnd_3288985 := by exact prefixLift 3288985
  have htrace : WordTrace (prefixWord ++ tailWord_3288985) baseStart_3288985 baseEnd_3288985 := by
    simpa [prefixWord, tailWord_3288985, baseEnd_3288985] using wordTrace_append hprefix tailTrace_3288985
  have hstable : (prefixWord ++ tailWord_3288985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288985).length < 2 ^ (prefixWord ++ tailWord_3288985).sum := by decide
  have hdescent : baseEnd_3288985 < baseStart_3288985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288995 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 4]
def baseStart_3288995 : Nat := 118140960795 + 3288995 * 2 ^ 59
def prefixEnd_3288995 : Nat := 4983230072969 + 3 ^ 40 * 3288995 * 2
def baseEnd_3288995 : Nat := 1688835305234464525636693

theorem tailTrace_3288995 : CollatzResearch.WordTrace tailWord_3288995 prefixEnd_3288995 1688835305234464525636693 := by
  unfold tailWord_3288995
  simp only [CollatzResearch.WordTrace]
  refine ⟨119959502719540305470644439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79973001813026870313762959 119959502719540305470644439)
  ·
    refine ⟨179939254079310458205966659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119959502719540305470644439 179939254079310458205966659)
    ·
      refine ⟨269908881118965687308949989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179939254079310458205966659 269908881118965687308949989)
      ·
        refine ⟨50607915209806066370428123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269908881118965687308949989 50607915209806066370428123)
        ·
          refine ⟨75911872814709099555642185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50607915209806066370428123 75911872814709099555642185)
          ·
            refine ⟨56933904611031824666731639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75911872814709099555642185 56933904611031824666731639)
            ·
              refine ⟨85400856916547737000097459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56933904611031824666731639 85400856916547737000097459)
              ·
                refine ⟨128101285374821605500146189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85400856916547737000097459 128101285374821605500146189)
                ·
                  refine ⟨48037982015558102062554821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128101285374821605500146189 48037982015558102062554821)
                  ·
                    refine ⟨9007121627917144136729029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48037982015558102062554821 9007121627917144136729029)
                    ·
                      refine ⟨1688835305234464525636693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9007121627917144136729029 1688835305234464525636693)
                      ·
                        rfl

theorem cell23_3288995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_3288995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3288995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3288995 prefixEnd_3288995 := by exact prefixLift 3288995
  have htrace : WordTrace (prefixWord ++ tailWord_3288995) baseStart_3288995 baseEnd_3288995 := by
    simpa [prefixWord, tailWord_3288995, baseEnd_3288995] using wordTrace_append hprefix tailTrace_3288995
  have hstable : (prefixWord ++ tailWord_3288995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288995).length < 2 ^ (prefixWord ++ tailWord_3288995).sum := by decide
  have hdescent : baseEnd_3288995 < baseStart_3288995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289022 : List Nat := [4, 2, 1, 1, 1, 3, 1, 3, 7]
def baseStart_3289022 : Nat := 118140960795 + 3289022 * 2 ^ 59
def prefixEnd_3289022 : Nat := 4983230072969 + 3 ^ 40 * 3289022 * 2
def baseEnd_3289022 : Nat := 187649907690237324444341

theorem tailTrace_3289022 : CollatzResearch.WordTrace tailWord_3289022 prefixEnd_3289022 187649907690237324444341 := by
  unfold tailWord_3289022
  simp only [CollatzResearch.WordTrace]
  refine ⟨14995060936305311135234665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79973658326961659387918213 14995060936305311135234665)
  ·
    refine ⟨11246295702228983351425999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14995060936305311135234665 11246295702228983351425999)
    ·
      refine ⟨16869443553343475027138999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11246295702228983351425999 16869443553343475027138999)
      ·
        refine ⟨25304165330015212540708499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16869443553343475027138999 25304165330015212540708499)
        ·
          refine ⟨37956247995022818811062749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25304165330015212540708499 37956247995022818811062749)
          ·
            refine ⟨14233592998133557054148531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37956247995022818811062749 14233592998133557054148531)
            ·
              refine ⟨21350389497200335581222797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14233592998133557054148531 21350389497200335581222797)
              ·
                refine ⟨8006396061450125842958549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21350389497200335581222797 8006396061450125842958549)
                ·
                  refine ⟨187649907690237324444341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8006396061450125842958549 187649907690237324444341)
                  ·
                    rfl

theorem cell23_3289022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_3289022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289022 prefixEnd_3289022 := by exact prefixLift 3289022
  have htrace : WordTrace (prefixWord ++ tailWord_3289022) baseStart_3289022 baseEnd_3289022 := by
    simpa [prefixWord, tailWord_3289022, baseEnd_3289022] using wordTrace_append hprefix tailTrace_3289022
  have hstable : (prefixWord ++ tailWord_3289022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289022).length < 2 ^ (prefixWord ++ tailWord_3289022).sum := by decide
  have hdescent : baseEnd_3289022 < baseStart_3289022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289035 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 3, 7]
def baseStart_3289035 : Nat := 118140960795 + 3289035 * 2 ^ 59
def prefixEnd_3289035 : Nat := 4983230072969 + 3 ^ 40 * 3289035 * 2
def baseEnd_3289035 : Nat := 562951948153548123045503

theorem tailTrace_3289035 : CollatzResearch.WordTrace tailWord_3289035 prefixEnd_3289035 562951948153548123045503 := by
  unfold tailWord_3289035
  simp only [CollatzResearch.WordTrace]
  refine ⟨119960961639395392302100559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79973974426263594868067039 119960961639395392302100559)
  ·
    refine ⟨179941442459093088453150839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119960961639395392302100559 179941442459093088453150839)
    ·
      refine ⟨269912163688639632679726259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179941442459093088453150839 269912163688639632679726259)
      ·
        refine ⟨404868245532959449019589389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269912163688639632679726259 404868245532959449019589389)
        ·
          refine ⟨151825592074859793382346021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 404868245532959449019589389 151825592074859793382346021)
          ·
            refine ⟨28467298514036211259189879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151825592074859793382346021 28467298514036211259189879)
            ·
              refine ⟨42700947771054316888784819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28467298514036211259189879 42700947771054316888784819)
              ·
                refine ⟨64051421656581475333177229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42700947771054316888784819 64051421656581475333177229)
                ·
                  refine ⟨24019283121218053249941461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64051421656581475333177229 24019283121218053249941461)
                  ·
                    refine ⟨562951948153548123045503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24019283121218053249941461 562951948153548123045503)
                    ·
                      rfl

theorem cell23_3289035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 7].length) (baseStart_3289035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289035 prefixEnd_3289035 := by exact prefixLift 3289035
  have htrace : WordTrace (prefixWord ++ tailWord_3289035) baseStart_3289035 baseEnd_3289035 := by
    simpa [prefixWord, tailWord_3289035, baseEnd_3289035] using wordTrace_append hprefix tailTrace_3289035
  have hstable : (prefixWord ++ tailWord_3289035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289035).length < 2 ^ (prefixWord ++ tailWord_3289035).sum := by decide
  have hdescent : baseEnd_3289035 < baseStart_3289035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289072 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 4]
def baseStart_3289072 : Nat := 118140960795 + 3289072 * 2 ^ 59
def prefixEnd_3289072 : Nat := 4983230072969 + 3 ^ 40 * 3289072 * 2
def baseEnd_3289072 : Nat := 1688874843244860724373839

theorem tailTrace_3289072 : CollatzResearch.WordTrace tailWord_3289072 prefixEnd_3289072 1688874843244860724373839 := by
  unfold tailWord_3289072
  simp only [CollatzResearch.WordTrace]
  refine ⟨59981155570130673810598735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79974874093507565080798313 59981155570130673810598735)
  ·
    refine ⟨89971733355196010715898103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59981155570130673810598735 89971733355196010715898103)
    ·
      refine ⟨134957600032794016073847155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89971733355196010715898103 134957600032794016073847155)
      ·
        refine ⟨202436400049191024110770733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134957600032794016073847155 202436400049191024110770733)
        ·
          refine ⟨75913650018446634041539025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202436400049191024110770733 75913650018446634041539025)
          ·
            refine ⟨56935237513834975531154269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75913650018446634041539025 56935237513834975531154269)
            ·
              refine ⟨21350714067688115824182851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56935237513834975531154269 21350714067688115824182851)
              ·
                refine ⟨32026071101532173736274277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21350714067688115824182851 32026071101532173736274277)
                ·
                  refine ⟨6004888331537282575551427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32026071101532173736274277 6004888331537282575551427)
                  ·
                    refine ⟨9007332497305923863327141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6004888331537282575551427 9007332497305923863327141)
                    ·
                      refine ⟨1688874843244860724373839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9007332497305923863327141 1688874843244860724373839)
                      ·
                        rfl

theorem cell23_3289072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 4].length) (baseStart_3289072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289072 prefixEnd_3289072 := by exact prefixLift 3289072
  have htrace : WordTrace (prefixWord ++ tailWord_3289072) baseStart_3289072 baseEnd_3289072 := by
    simpa [prefixWord, tailWord_3289072, baseEnd_3289072] using wordTrace_append hprefix tailTrace_3289072
  have hstable : (prefixWord ++ tailWord_3289072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289072).length < 2 ^ (prefixWord ++ tailWord_3289072).sum := by decide
  have hdescent : baseEnd_3289072 < baseStart_3289072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289089 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 1, 6, 2]
def baseStart_3289089 : Nat := 118140960795 + 3289089 * 2 ^ 59
def prefixEnd_3289089 : Nat := 4983230072969 + 3 ^ 40 * 3289089 * 2
def baseEnd_3289089 : Nat := 1688883572415987157861261

theorem tailTrace_3289089 : CollatzResearch.WordTrace tailWord_3289089 prefixEnd_3289089 1688883572415987157861261 := by
  unfold tailWord_3289089
  simp only [CollatzResearch.WordTrace]
  refine ⟨119962931181199759524566321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79975287454133173016377547 119962931181199759524566321)
  ·
    refine ⟨89972198385899819643424741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119962931181199759524566321 89972198385899819643424741)
    ·
      refine ⟨16869787197356216183142139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89972198385899819643424741 16869787197356216183142139)
      ·
        refine ⟨25304680796034324274713209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16869787197356216183142139 25304680796034324274713209)
        ·
          refine ⟨18978510597025743206034907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25304680796034324274713209 18978510597025743206034907)
          ·
            refine ⟨28467765895538614809052361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18978510597025743206034907 28467765895538614809052361)
            ·
              refine ⟨21350824421653961106789271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28467765895538614809052361 21350824421653961106789271)
              ·
                refine ⟨32026236632480941660183907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21350824421653961106789271 32026236632480941660183907)
                ·
                  refine ⟨48039354948721412490275861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32026236632480941660183907 48039354948721412490275861)
                  ·
                    refine ⟨2251844763221316210481681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48039354948721412490275861 2251844763221316210481681)
                    ·
                      refine ⟨1688883572415987157861261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2251844763221316210481681 1688883572415987157861261)
                      ·
                        rfl

theorem cell23_3289089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_3289089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289089 prefixEnd_3289089 := by exact prefixLift 3289089
  have htrace : WordTrace (prefixWord ++ tailWord_3289089) baseStart_3289089 baseEnd_3289089 := by
    simpa [prefixWord, tailWord_3289089, baseEnd_3289089] using wordTrace_append hprefix tailTrace_3289089
  have hstable : (prefixWord ++ tailWord_3289089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289089).length < 2 ^ (prefixWord ++ tailWord_3289089).sum := by decide
  have hdescent : baseEnd_3289089 < baseStart_3289089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289159 : List Nat := [1, 1, 4, 1, 3, 1, 2, 4, 1, 5]
def baseStart_3289159 : Nat := 118140960795 + 3289159 * 2 ^ 59
def prefixEnd_3289159 : Nat := 4983230072969 + 3 ^ 40 * 3289159 * 2
def baseEnd_3289159 : Nat := 562973172020600627995313

theorem tailTrace_3289159 : CollatzResearch.WordTrace tailWord_3289159 prefixEnd_3289159 562973172020600627995313 := by
  unfold tailWord_3289159
  simp only [CollatzResearch.WordTrace]
  refine ⟨119965484290946161479614531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79976989527297440986409687 119965484290946161479614531)
  ·
    refine ⟨179948226436419242219421797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119965484290946161479614531 179948226436419242219421797)
    ·
      refine ⟨33740292456828607916141587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179948226436419242219421797 33740292456828607916141587)
      ·
        refine ⟨50610438685242911874212381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33740292456828607916141587 50610438685242911874212381)
        ·
          refine ⟨18978914506966091952829643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50610438685242911874212381 18978914506966091952829643)
          ·
            refine ⟨28468371760449137929244465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18978914506966091952829643 28468371760449137929244465)
            ·
              refine ⟨21351278820336853446933349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28468371760449137929244465 21351278820336853446933349)
              ·
                refine ⟨4003364778813160021300003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21351278820336853446933349 4003364778813160021300003)
                ·
                  refine ⟨6005047168219740031950005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4003364778813160021300003 6005047168219740031950005)
                  ·
                    refine ⟨562973172020600627995313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6005047168219740031950005 562973172020600627995313)
                    ·
                      rfl

theorem cell23_3289159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_3289159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289159 prefixEnd_3289159 := by exact prefixLift 3289159
  have htrace : WordTrace (prefixWord ++ tailWord_3289159) baseStart_3289159 baseEnd_3289159 := by
    simpa [prefixWord, tailWord_3289159, baseEnd_3289159] using wordTrace_append hprefix tailTrace_3289159
  have hstable : (prefixWord ++ tailWord_3289159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289159).length < 2 ^ (prefixWord ++ tailWord_3289159).sum := by decide
  have hdescent : baseEnd_3289159 < baseStart_3289159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289166 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2]
def baseStart_3289166 : Nat := 118140960795 + 3289166 * 2 ^ 59
def prefixEnd_3289166 : Nat := 4983230072969 + 3 ^ 40 * 3289166 * 2
def baseEnd_3289166 : Nat := 1688923110426383356598407

theorem tailTrace_3289166 : CollatzResearch.WordTrace tailWord_3289166 prefixEnd_3289166 1688923110426383356598407 := by
  unfold tailWord_3289166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14995717450240100209389919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79977159734613867783412901 14995717450240100209389919)
  ·
    refine ⟨22493576175360150314084879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14995717450240100209389919 22493576175360150314084879)
    ·
      refine ⟨33740364263040225471127319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22493576175360150314084879 33740364263040225471127319)
      ·
        refine ⟨50610546394560338206690979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33740364263040225471127319 50610546394560338206690979)
        ·
          refine ⟨75915819591840507310036469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50610546394560338206690979 75915819591840507310036469)
          ·
            refine ⟨7117108086735047560315919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75915819591840507310036469 7117108086735047560315919)
            ·
              refine ⟨10675662130102571340473879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7117108086735047560315919 10675662130102571340473879)
              ·
                refine ⟨16013493195153857010710819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10675662130102571340473879 16013493195153857010710819)
                ·
                  refine ⟨24020239792730785516066229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16013493195153857010710819 24020239792730785516066229)
                  ·
                    refine ⟨2251897480568511142131209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24020239792730785516066229 2251897480568511142131209)
                    ·
                      refine ⟨1688923110426383356598407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2251897480568511142131209 1688923110426383356598407)
                      ·
                        rfl

theorem cell23_3289166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_3289166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289166 prefixEnd_3289166 := by exact prefixLift 3289166
  have htrace : WordTrace (prefixWord ++ tailWord_3289166) baseStart_3289166 baseEnd_3289166 := by
    simpa [prefixWord, tailWord_3289166, baseEnd_3289166] using wordTrace_append hprefix tailTrace_3289166
  have hstable : (prefixWord ++ tailWord_3289166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289166).length < 2 ^ (prefixWord ++ tailWord_3289166).sum := by decide
  have hdescent : baseEnd_3289166 < baseStart_3289166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289173 : List Nat := [1, 3, 2, 2, 1, 3, 1, 5, 1, 1, 3]
def baseStart_3289173 : Nat := 118140960795 + 3289173 * 2 ^ 59
def prefixEnd_3289173 : Nat := 4983230072969 + 3 ^ 40 * 3289173 * 2
def baseEnd_3289173 : Nat := 1688926704790964829210875

theorem tailTrace_3289173 : CollatzResearch.WordTrace tailWord_3289173 prefixEnd_3289173 1688926704790964829210875 := by
  unfold tailWord_3289173
  simp only [CollatzResearch.WordTrace]
  refine ⟨119965994912895441870624173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79977329941930294580416115 119965994912895441870624173)
  ·
    refine ⟨44987248092335790701484065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119965994912895441870624173 44987248092335790701484065)
    ·
      refine ⟨33740436069251843026113049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44987248092335790701484065 33740436069251843026113049)
      ·
        refine ⟨25305327051938882269584787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33740436069251843026113049 25305327051938882269584787)
        ·
          refine ⟨37957990577908323404377181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25305327051938882269584787 37957990577908323404377181)
          ·
            refine ⟨14234246466715621276641443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37957990577908323404377181 14234246466715621276641443)
            ·
              refine ⟨21351369700073431914962165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14234246466715621276641443 21351369700073431914962165)
              ·
                refine ⟨2001690909381884242027703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21351369700073431914962165 2001690909381884242027703)
                ·
                  refine ⟨3002536364072826363041555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2001690909381884242027703 3002536364072826363041555)
                  ·
                    refine ⟨4503804546109239544562333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3002536364072826363041555 4503804546109239544562333)
                    ·
                      refine ⟨1688926704790964829210875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4503804546109239544562333 1688926704790964829210875)
                      ·
                        rfl

theorem cell23_3289173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_3289173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289173 prefixEnd_3289173 := by exact prefixLift 3289173
  have htrace : WordTrace (prefixWord ++ tailWord_3289173) baseStart_3289173 baseEnd_3289173 := by
    simpa [prefixWord, tailWord_3289173, baseEnd_3289173] using wordTrace_append hprefix tailTrace_3289173
  have hstable : (prefixWord ++ tailWord_3289173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289173).length < 2 ^ (prefixWord ++ tailWord_3289173).sum := by decide
  have hdescent : baseEnd_3289173 < baseStart_3289173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289176 : List Nat := [2, 1, 2, 2, 1, 4, 4, 1, 1, 5]
def baseStart_3289176 : Nat := 118140960795 + 3289176 * 2 ^ 59
def prefixEnd_3289176 : Nat := 4983230072969 + 3 ^ 40 * 3289176 * 2
def baseEnd_3289176 : Nat := 562976081744309439157787

theorem tailTrace_3289176 : CollatzResearch.WordTrace tailWord_3289176 prefixEnd_3289176 562976081744309439157787 := by
  unfold tailWord_3289176
  simp only [CollatzResearch.WordTrace]
  refine ⟨59983052165942286691491691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79977402887923048921988921 59983052165942286691491691)
  ·
    refine ⟨89974578248913430037237537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59983052165942286691491691 89974578248913430037237537)
    ·
      refine ⟨67480933686685072527928153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89974578248913430037237537 67480933686685072527928153)
      ·
        refine ⟨50610700265013804395946115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67480933686685072527928153 50610700265013804395946115)
        ·
          refine ⟨75916050397520706593919173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50610700265013804395946115 75916050397520706593919173)
          ·
            refine ⟨14234259449535132486359845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75916050397520706593919173 14234259449535132486359845)
            ·
              refine ⟨2668923646787837341192471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14234259449535132486359845 2668923646787837341192471)
              ·
                refine ⟨4003385470181756011788707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2668923646787837341192471 4003385470181756011788707)
                ·
                  refine ⟨6005078205272634017683061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4003385470181756011788707 6005078205272634017683061)
                  ·
                    refine ⟨562976081744309439157787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6005078205272634017683061 562976081744309439157787)
                    ·
                      rfl

theorem cell23_3289176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 1, 5].length) (baseStart_3289176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289176 prefixEnd_3289176 := by exact prefixLift 3289176
  have htrace : WordTrace (prefixWord ++ tailWord_3289176) baseStart_3289176 baseEnd_3289176 := by
    simpa [prefixWord, tailWord_3289176, baseEnd_3289176] using wordTrace_append hprefix tailTrace_3289176
  have hstable : (prefixWord ++ tailWord_3289176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289176).length < 2 ^ (prefixWord ++ tailWord_3289176).sum := by decide
  have hdescent : baseEnd_3289176 < baseStart_3289176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289199 : List Nat := [1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 5]
def baseStart_3289199 : Nat := 118140960795 + 3289199 * 2 ^ 59
def prefixEnd_3289199 : Nat := 4983230072969 + 3 ^ 40 * 3289199 * 2
def baseEnd_3289199 : Nat := 1688940055287981727485755

theorem tailTrace_3289199 : CollatzResearch.WordTrace tailWord_3289199 prefixEnd_3289199 1688940055287981727485755 := by
  unfold tailWord_3289199
  simp only [CollatzResearch.WordTrace]
  refine ⟨119966943210801248311070651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79977962140534165540713767 119966943210801248311070651)
  ·
    refine ⟨179950414816201872466605977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119966943210801248311070651 179950414816201872466605977)
    ·
      refine ⟨134962811112151404349954483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179950414816201872466605977 134962811112151404349954483)
      ·
        refine ⟨202444216668227106524931725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134962811112151404349954483 202444216668227106524931725)
        ·
          refine ⟨75916581250585164946849397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202444216668227106524931725 75916581250585164946849397)
          ·
            refine ⟨7117179492242359213767131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75916581250585164946849397 7117179492242359213767131)
            ·
              refine ⟨10675769238363538820650697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7117179492242359213767131 10675769238363538820650697)
              ·
                refine ⟨8006826928772654115488023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10675769238363538820650697 8006826928772654115488023)
                ·
                  refine ⟨12010240393158981173232035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8006826928772654115488023 12010240393158981173232035)
                  ·
                    refine ⟨18015360589738471759848053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12010240393158981173232035 18015360589738471759848053)
                    ·
                      refine ⟨1688940055287981727485755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18015360589738471759848053 1688940055287981727485755)
                      ·
                        rfl

theorem cell23_3289199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 5].length) (baseStart_3289199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289199 prefixEnd_3289199 := by exact prefixLift 3289199
  have htrace : WordTrace (prefixWord ++ tailWord_3289199) baseStart_3289199 baseEnd_3289199 := by
    simpa [prefixWord, tailWord_3289199, baseEnd_3289199] using wordTrace_append hprefix tailTrace_3289199
  have hstable : (prefixWord ++ tailWord_3289199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289199).length < 2 ^ (prefixWord ++ tailWord_3289199).sum := by decide
  have hdescent : baseEnd_3289199 < baseStart_3289199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289206 : List Nat := [5, 1, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_3289206 : Nat := 118140960795 + 3289206 * 2 ^ 59
def prefixEnd_3289206 : Nat := 4983230072969 + 3 ^ 40 * 3289206 * 2
def baseEnd_3289206 : Nat := 562981216550854400032741

theorem tailTrace_3289206 : CollatzResearch.WordTrace tailWord_3289206 prefixEnd_3289206 562981216550854400032741 := by
  unfold tailWord_3289206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7497949907610993031660967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79978132347850592337716981 7497949907610993031660967)
  ·
    refine ⟨11246924861416489547491451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7497949907610993031660967 11246924861416489547491451)
    ·
      refine ⟨16870387292124734321237177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11246924861416489547491451 16870387292124734321237177)
      ·
        refine ⟨12652790469093550740927883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16870387292124734321237177 12652790469093550740927883)
        ·
          refine ⟨18979185703640326111391825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12652790469093550740927883 18979185703640326111391825)
          ·
            refine ⟨14234389277730244583543869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18979185703640326111391825 14234389277730244583543869)
            ·
              refine ⟨5337895979148841718828951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14234389277730244583543869 5337895979148841718828951)
              ·
                refine ⟨8006843968723262578243427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5337895979148841718828951 8006843968723262578243427)
                ·
                  refine ⟨12010265953084893867365141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8006843968723262578243427 12010265953084893867365141)
                  ·
                    refine ⟨562981216550854400032741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12010265953084893867365141 562981216550854400032741)
                    ·
                      rfl

theorem cell23_3289206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_3289206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289206 prefixEnd_3289206 := by exact prefixLift 3289206
  have htrace : WordTrace (prefixWord ++ tailWord_3289206) baseStart_3289206 baseEnd_3289206 := by
    simpa [prefixWord, tailWord_3289206, baseEnd_3289206] using wordTrace_append hprefix tailTrace_3289206
  have hstable : (prefixWord ++ tailWord_3289206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289206).length < 2 ^ (prefixWord ++ tailWord_3289206).sum := by decide
  have hdescent : baseEnd_3289206 < baseStart_3289206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289209 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 1, 1, 6]
def baseStart_3289209 : Nat := 118140960795 + 3289209 * 2 ^ 59
def prefixEnd_3289209 : Nat := 4983230072969 + 3 ^ 40 * 3289209 * 2
def baseEnd_3289209 : Nat := 1688945190094526688360709

theorem tailTrace_3289209 : CollatzResearch.WordTrace tailWord_3289209 prefixEnd_3289209 1688945190094526688360709 := by
  unfold tailWord_3289209
  simp only [CollatzResearch.WordTrace]
  refine ⟨119967307940765020018934681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79978205293843346679289787 119967307940765020018934681)
  ·
    refine ⟨89975480955573765014201011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119967307940765020018934681 89975480955573765014201011)
    ·
      refine ⟨134963221433360647521301517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89975480955573765014201011 134963221433360647521301517)
      ·
        refine ⟨50611208037510242820488069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134963221433360647521301517 50611208037510242820488069)
        ·
          refine ⟨9489601507033170528841513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50611208037510242820488069 9489601507033170528841513)
          ·
            refine ⟨7117201130274877896631135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9489601507033170528841513 7117201130274877896631135)
            ·
              refine ⟨10675801695412316844946703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7117201130274877896631135 10675801695412316844946703)
              ·
                refine ⟨16013702543118475267420055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10675801695412316844946703 16013702543118475267420055)
                ·
                  refine ⟨24020553814677712901130083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16013702543118475267420055 24020553814677712901130083)
                  ·
                    refine ⟨36030830722016569351695125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24020553814677712901130083 36030830722016569351695125)
                    ·
                      refine ⟨1688945190094526688360709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36030830722016569351695125 1688945190094526688360709)
                      ·
                        rfl

theorem cell23_3289209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_3289209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289209 prefixEnd_3289209 := by exact prefixLift 3289209
  have htrace : WordTrace (prefixWord ++ tailWord_3289209) baseStart_3289209 baseEnd_3289209 := by
    simpa [prefixWord, tailWord_3289209, baseEnd_3289209] using wordTrace_append hprefix tailTrace_3289209
  have hstable : (prefixWord ++ tailWord_3289209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289209).length < 2 ^ (prefixWord ++ tailWord_3289209).sum := by decide
  have hdescent : baseEnd_3289209 < baseStart_3289209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289213 : List Nat := [1, 4, 1, 1, 3, 2, 2, 2, 3, 2, 2]
def baseStart_3289213 : Nat := 118140960795 + 3289213 * 2 ^ 59
def prefixEnd_3289213 : Nat := 4983230072969 + 3 ^ 40 * 3289213 * 2
def baseEnd_3289213 : Nat := 1688947244017144672710691

theorem tailTrace_3289213 : CollatzResearch.WordTrace tailWord_3289213 prefixEnd_3289213 1688947244017144672710691 := by
  unfold tailWord_3289213
  simp only [CollatzResearch.WordTrace]
  refine ⟨119967453832750528702080293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79978302555167019134720195 119967453832750528702080293)
  ·
    refine ⟨22493897593640724131640055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119967453832750528702080293 22493897593640724131640055)
    ·
      refine ⟨33740846390461086197460083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22493897593640724131640055 33740846390461086197460083)
      ·
        refine ⟨50611269585691629296190125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33740846390461086197460083 50611269585691629296190125)
        ·
          refine ⟨18979226094634360986071297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50611269585691629296190125 18979226094634360986071297)
          ·
            refine ⟨14234419570975770739553473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18979226094634360986071297 14234419570975770739553473)
            ·
              refine ⟨10675814678231828054665105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14234419570975770739553473 10675814678231828054665105)
              ·
                refine ⟨8006861008673871040998829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10675814678231828054665105 8006861008673871040998829)
                ·
                  refine ⟨3002572878252701640374561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8006861008673871040998829 3002572878252701640374561)
                  ·
                    refine ⟨2251929658689526230280921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3002572878252701640374561 2251929658689526230280921)
                    ·
                      refine ⟨1688947244017144672710691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2251929658689526230280921 1688947244017144672710691)
                      ·
                        rfl

theorem cell23_3289213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_3289213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289213 prefixEnd_3289213 := by exact prefixLift 3289213
  have htrace : WordTrace (prefixWord ++ tailWord_3289213) baseStart_3289213 baseEnd_3289213 := by
    simpa [prefixWord, tailWord_3289213, baseEnd_3289213] using wordTrace_append hprefix tailTrace_3289213
  have hstable : (prefixWord ++ tailWord_3289213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289213).length < 2 ^ (prefixWord ++ tailWord_3289213).sum := by decide
  have hdescent : baseEnd_3289213 < baseStart_3289213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289219 : List Nat := [1, 1, 1, 3, 3, 3, 4, 7]
def baseStart_3289219 : Nat := 118140960795 + 3289219 * 2 ^ 59
def prefixEnd_3289219 : Nat := 4983230072969 + 3 ^ 40 * 3289219 * 2
def baseEnd_3289219 : Nat := 62553715737076727749469

theorem tailTrace_3289219 : CollatzResearch.WordTrace tailWord_3289219 prefixEnd_3289219 62553715737076727749469 := by
  unfold tailWord_3289219
  simp only [CollatzResearch.WordTrace]
  refine ⟨119967672670728791726798711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79978448447152527817865807 119967672670728791726798711)
  ·
    refine ⟨179951509006093187590198067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119967672670728791726798711 179951509006093187590198067)
    ·
      refine ⟨269927263509139781385297101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179951509006093187590198067 269927263509139781385297101)
      ·
        refine ⟨101222723815927418019486413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269927263509139781385297101 101222723815927418019486413)
        ·
          refine ⟨37958521430972781757307405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101222723815927418019486413 37958521430972781757307405)
          ·
            refine ⟨14234445536614793158990277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37958521430972781757307405 14234445536614793158990277)
            ·
              refine ⟨2668958538115273717310677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14234445536614793158990277 2668958538115273717310677)
              ·
                refine ⟨62553715737076727749469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2668958538115273717310677 62553715737076727749469)
                ·
                  rfl

theorem cell23_3289219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 7].length) (baseStart_3289219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289219 prefixEnd_3289219 := by exact prefixLift 3289219
  have htrace : WordTrace (prefixWord ++ tailWord_3289219) baseStart_3289219 baseEnd_3289219 := by
    simpa [prefixWord, tailWord_3289219, baseEnd_3289219] using wordTrace_append hprefix tailTrace_3289219
  have hstable : (prefixWord ++ tailWord_3289219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289219).length < 2 ^ (prefixWord ++ tailWord_3289219).sum := by decide
  have hdescent : baseEnd_3289219 < baseStart_3289219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289290 : List Nat := [3, 1, 2, 1, 3, 1, 5, 1, 1, 3, 2]
def baseStart_3289290 : Nat := 118140960795 + 3289290 * 2 ^ 59
def prefixEnd_3289290 : Nat := 4983230072969 + 3 ^ 40 * 3289290 * 2
def baseEnd_3289290 : Nat := 1688986782027540871447837

theorem tailTrace_3289290 : CollatzResearch.WordTrace tailWord_3289290 prefixEnd_3289290 1688986782027540871447837 := by
  unfold tailWord_3289290
  simp only [CollatzResearch.WordTrace]
  refine ⟨29992565563367892713158331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79980174835647713901755549 29992565563367892713158331)
  ·
    refine ⟨44988848345051839069737497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29992565563367892713158331 44988848345051839069737497)
    ·
      refine ⟨33741636258788879302303123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44988848345051839069737497 33741636258788879302303123)
      ·
        refine ⟨50612454388183318953454685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33741636258788879302303123 50612454388183318953454685)
        ·
          refine ⟨18979670395568744607545507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50612454388183318953454685 18979670395568744607545507)
          ·
            refine ⟨28469505593353116911318261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18979670395568744607545507 28469505593353116911318261)
            ·
              refine ⟨2669016149376854710436087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28469505593353116911318261 2669016149376854710436087)
              ·
                refine ⟨4003524224065282065654131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2669016149376854710436087 4003524224065282065654131)
                ·
                  refine ⟨6005286336097923098481197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4003524224065282065654131 6005286336097923098481197)
                  ·
                    refine ⟨2251982376036721161930449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6005286336097923098481197 2251982376036721161930449)
                    ·
                      refine ⟨1688986782027540871447837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2251982376036721161930449 1688986782027540871447837)
                      ·
                        rfl

theorem cell23_3289290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_3289290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289290 prefixEnd_3289290 := by exact prefixLift 3289290
  have htrace : WordTrace (prefixWord ++ tailWord_3289290) baseStart_3289290 baseEnd_3289290 := by
    simpa [prefixWord, tailWord_3289290, baseEnd_3289290] using wordTrace_append hprefix tailTrace_3289290
  have hstable : (prefixWord ++ tailWord_3289290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289290).length < 2 ^ (prefixWord ++ tailWord_3289290).sum := by decide
  have hdescent : baseEnd_3289290 < baseStart_3289290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289320 : List Nat := [2, 1, 4, 1, 2, 2, 2, 3, 2, 2, 2]
def baseStart_3289320 : Nat := 118140960795 + 3289320 * 2 ^ 59
def prefixEnd_3289320 : Nat := 4983230072969 + 3 ^ 40 * 3289320 * 2
def baseEnd_3289320 : Nat := 1689002186447175754072699

theorem tailTrace_3289320 : CollatzResearch.WordTrace tailWord_3289320 prefixEnd_3289320 1689002186447175754072699 := by
  unfold tailWord_3289320
  simp only [CollatzResearch.WordTrace]
  refine ⟨59985678221681442988112707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79980904295575257317483609 59985678221681442988112707)
  ·
    refine ⟨89978517332522164482169061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59985678221681442988112707 89978517332522164482169061)
    ·
      refine ⟨16870971999847905840406699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89978517332522164482169061 16870971999847905840406699)
      ·
        refine ⟨25306457999771858760610049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16870971999847905840406699 25306457999771858760610049)
        ·
          refine ⟨18979843499828894070457537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25306457999771858760610049 18979843499828894070457537)
          ·
            refine ⟨14234882624871670552843153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18979843499828894070457537 14234882624871670552843153)
            ·
              refine ⟨10676161968653752914632365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14234882624871670552843153 10676161968653752914632365)
              ·
                refine ⟨4003560738245157342987137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10676161968653752914632365 4003560738245157342987137)
                ·
                  refine ⟨3002670553683868007240353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4003560738245157342987137 3002670553683868007240353)
                  ·
                    refine ⟨2252002915262901005430265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3002670553683868007240353 2252002915262901005430265)
                    ·
                      refine ⟨1689002186447175754072699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2252002915262901005430265 1689002186447175754072699)
                      ·
                        rfl

theorem cell23_3289320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_3289320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289320 prefixEnd_3289320 := by exact prefixLift 3289320
  have htrace : WordTrace (prefixWord ++ tailWord_3289320) baseStart_3289320 baseEnd_3289320 := by
    simpa [prefixWord, tailWord_3289320, baseEnd_3289320] using wordTrace_append hprefix tailTrace_3289320
  have hstable : (prefixWord ++ tailWord_3289320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289320).length < 2 ^ (prefixWord ++ tailWord_3289320).sum := by decide
  have hdescent : baseEnd_3289320 < baseStart_3289320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289349 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 1, 2, 5]
def baseStart_3289349 : Nat := 118140960795 + 3289349 * 2 ^ 59
def prefixEnd_3289349 : Nat := 4983230072969 + 3 ^ 40 * 3289349 * 2
def baseEnd_3289349 : Nat := 1689017077386156140610065

theorem tailTrace_3289349 : CollatzResearch.WordTrace tailWord_3289349 prefixEnd_3289349 1689017077386156140610065 := by
  unfold tailWord_3289349
  simp only [CollatzResearch.WordTrace]
  refine ⟨119972414160257823929031101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79981609440171882619354067 119972414160257823929031101)
  ·
    refine ⟨44989655310096683973386663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119972414160257823929031101 44989655310096683973386663)
    ·
      refine ⟨67484482965145025960079995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44989655310096683973386663 67484482965145025960079995)
      ·
        refine ⟨101226724447717538940119993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67484482965145025960079995 101226724447717538940119993)
        ·
          refine ⟨75920043335788154205089995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101226724447717538940119993 75920043335788154205089995)
          ·
            refine ⟨113880065003682231307634993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75920043335788154205089995 113880065003682231307634993)
            ·
              refine ⟨85410048752761673480726245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113880065003682231307634993 85410048752761673480726245)
              ·
                refine ⟨16014384141142813777636171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85410048752761673480726245 16014384141142813777636171)
                ·
                  refine ⟨24021576211714220666454257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16014384141142813777636171 24021576211714220666454257)
                  ·
                    refine ⟨18016182158785665499840693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24021576211714220666454257 18016182158785665499840693)
                    ·
                      refine ⟨1689017077386156140610065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18016182158785665499840693 1689017077386156140610065)
                      ·
                        rfl

theorem cell23_3289349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_3289349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289349 prefixEnd_3289349 := by exact prefixLift 3289349
  have htrace : WordTrace (prefixWord ++ tailWord_3289349) baseStart_3289349 baseEnd_3289349 := by
    simpa [prefixWord, tailWord_3289349, baseEnd_3289349] using wordTrace_append hprefix tailTrace_3289349
  have hstable : (prefixWord ++ tailWord_3289349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289349).length < 2 ^ (prefixWord ++ tailWord_3289349).sum := by decide
  have hdescent : baseEnd_3289349 < baseStart_3289349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289376 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 4]
def baseStart_3289376 : Nat := 118140960795 + 3289376 * 2 ^ 59
def prefixEnd_3289376 : Nat := 4983230072969 + 3 ^ 40 * 3289376 * 2
def baseEnd_3289376 : Nat := 1689030941363827534972441

theorem tailTrace_3289376 : CollatzResearch.WordTrace tailWord_3289376 prefixEnd_3289376 1689030941363827534972441 := by
  unfold tailWord_3289376
  simp only [CollatzResearch.WordTrace]
  refine ⟨59986699465580003770131991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79982265954106671693509321 59986699465580003770131991)
  ·
    refine ⟨89980049198370005655197987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59986699465580003770131991 89980049198370005655197987)
    ·
      refine ⟨134970073797555008482796981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89980049198370005655197987 134970073797555008482796981)
      ·
        refine ⟨12653444418520782045262217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134970073797555008482796981 12653444418520782045262217)
        ·
          refine ⟨9490083313890586533946663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12653444418520782045262217 9490083313890586533946663)
          ·
            refine ⟨14235124970835879800919995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9490083313890586533946663 14235124970835879800919995)
            ·
              refine ⟨21352687456253819701379993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14235124970835879800919995 21352687456253819701379993)
              ·
                refine ⟨16014515592190364776034995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21352687456253819701379993 16014515592190364776034995)
                ·
                  refine ⟨24021773388285547164052493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16014515592190364776034995 24021773388285547164052493)
                  ·
                    refine ⟨9008165020607080186519685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24021773388285547164052493 9008165020607080186519685)
                    ·
                      refine ⟨1689030941363827534972441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9008165020607080186519685 1689030941363827534972441)
                      ·
                        rfl

theorem cell23_3289376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_3289376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289376 prefixEnd_3289376 := by exact prefixLift 3289376
  have htrace : WordTrace (prefixWord ++ tailWord_3289376) baseStart_3289376 baseEnd_3289376 := by
    simpa [prefixWord, tailWord_3289376, baseEnd_3289376] using wordTrace_append hprefix tailTrace_3289376
  have hstable : (prefixWord ++ tailWord_3289376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289376).length < 2 ^ (prefixWord ++ tailWord_3289376).sum := by decide
  have hdescent : baseEnd_3289376 < baseStart_3289376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289419 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 6]
def baseStart_3289419 : Nat := 118140960795 + 3289419 * 2 ^ 59
def prefixEnd_3289419 : Nat := 4983230072969 + 3 ^ 40 * 3289419 * 2
def baseEnd_3289419 : Nat := 1689053021031970866734743

theorem tailTrace_3289419 : CollatzResearch.WordTrace tailWord_3289419 prefixEnd_3289419 1689053021031970866734743 := by
  unfold tailWord_3289419
  simp only [CollatzResearch.WordTrace]
  refine ⟨119974967270004225884079311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79983311513336150589386207 119974967270004225884079311)
  ·
    refine ⟨179962450905006338826118967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119974967270004225884079311 179962450905006338826118967)
    ·
      refine ⟨269943676357509508239178451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179962450905006338826118967 269943676357509508239178451)
      ·
        refine ⟨404915514536264262358767677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269943676357509508239178451 404915514536264262358767677)
        ·
          refine ⟨151843317951099098384537879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 404915514536264262358767677 151843317951099098384537879)
          ·
            refine ⟨227764976926648647576806819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151843317951099098384537879 227764976926648647576806819)
            ·
              refine ⟨341647465389972971365210229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227764976926648647576806819 341647465389972971365210229)
              ·
                refine ⟨32029449880309966065488459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 341647465389972971365210229 32029449880309966065488459)
                ·
                  refine ⟨48044174820464949098232689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32029449880309966065488459 48044174820464949098232689)
                  ·
                    refine ⟨36033131115348711823674517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48044174820464949098232689 36033131115348711823674517)
                    ·
                      refine ⟨1689053021031970866734743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36033131115348711823674517 1689053021031970866734743)
                      ·
                        rfl

theorem cell23_3289419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 6].length) (baseStart_3289419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289419 prefixEnd_3289419 := by exact prefixLift 3289419
  have htrace : WordTrace (prefixWord ++ tailWord_3289419) baseStart_3289419 baseEnd_3289419 := by
    simpa [prefixWord, tailWord_3289419, baseEnd_3289419] using wordTrace_append hprefix tailTrace_3289419
  have hstable : (prefixWord ++ tailWord_3289419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289419).length < 2 ^ (prefixWord ++ tailWord_3289419).sum := by decide
  have hdescent : baseEnd_3289419 < baseStart_3289419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289443 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 5, 1, 3]
def baseStart_3289443 : Nat := 118140960795 + 3289443 * 2 ^ 59
def prefixEnd_3289443 : Nat := 4983230072969 + 3 ^ 40 * 3289443 * 2
def baseEnd_3289443 : Nat := 1689065344567678772834633

theorem tailTrace_3289443 : CollatzResearch.WordTrace tailWord_3289443 prefixEnd_3289443 1689065344567678772834633 := by
  unfold tailWord_3289443
  simp only [CollatzResearch.WordTrace]
  refine ⟨119975842621917277982952983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79983895081278185321968655 119975842621917277982952983)
  ·
    refine ⟨179963763932875916974429475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119975842621917277982952983 179963763932875916974429475)
    ·
      refine ⟨269945645899313875461644213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179963763932875916974429475 269945645899313875461644213)
      ·
        refine ⟨25307404303060675824529145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 269945645899313875461644213 25307404303060675824529145)
        ·
          refine ⟨18980553227295506868396859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25307404303060675824529145 18980553227295506868396859)
          ·
            refine ⟨28470829840943260302595289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18980553227295506868396859 28470829840943260302595289)
            ·
              refine ⟨21353122380707445226946467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28470829840943260302595289 21353122380707445226946467)
              ·
                refine ⟨32029683571061167840419701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21353122380707445226946467 32029683571061167840419701)
                ·
                  refine ⟨3002782834786984485039347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32029683571061167840419701 3002782834786984485039347)
                  ·
                    refine ⟨4504174252180476727559021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3002782834786984485039347 4504174252180476727559021)
                    ·
                      refine ⟨1689065344567678772834633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4504174252180476727559021 1689065344567678772834633)
                      ·
                        rfl

theorem cell23_3289443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_3289443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289443 prefixEnd_3289443 := by exact prefixLift 3289443
  have htrace : WordTrace (prefixWord ++ tailWord_3289443) baseStart_3289443 baseEnd_3289443 := by
    simpa [prefixWord, tailWord_3289443, baseEnd_3289443] using wordTrace_append hprefix tailTrace_3289443
  have hstable : (prefixWord ++ tailWord_3289443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289443).length < 2 ^ (prefixWord ++ tailWord_3289443).sum := by decide
  have hdescent : baseEnd_3289443 < baseStart_3289443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289466 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4]
def baseStart_3289466 : Nat := 118140960795 + 3289466 * 2 ^ 59
def prefixEnd_3289466 : Nat := 4983230072969 + 3 ^ 40 * 3289466 * 2
def baseEnd_3289466 : Nat := 1689077154622732182847027

theorem tailTrace_3289466 : CollatzResearch.WordTrace tailWord_3289466 prefixEnd_3289466 1689077154622732182847027 := by
  unfold tailWord_3289466
  simp only [CollatzResearch.WordTrace]
  refine ⟨29994170375208488227760063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79984454333889301940693501 29994170375208488227760063)
  ·
    refine ⟨44991255562812732341640095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29994170375208488227760063 44991255562812732341640095)
    ·
      refine ⟨67486883344219098512460143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44991255562812732341640095 67486883344219098512460143)
      ·
        refine ⟨101230325016328647768690215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67486883344219098512460143 101230325016328647768690215)
        ·
          refine ⟨151845487524492971653035323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101230325016328647768690215 151845487524492971653035323)
          ·
            refine ⟨227768231286739457479552985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151845487524492971653035323 227768231286739457479552985)
            ·
              refine ⟨170826173465054593109664739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227768231286739457479552985 170826173465054593109664739)
              ·
                refine ⟨256239260197581889664497109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170826173465054593109664739 256239260197581889664497109)
                ·
                  refine ⟨6005607660880825539011651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 256239260197581889664497109 6005607660880825539011651)
                  ·
                    refine ⟨9008411491321238308517477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6005607660880825539011651 9008411491321238308517477)
                    ·
                      refine ⟨1689077154622732182847027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9008411491321238308517477 1689077154622732182847027)
                      ·
                        rfl

theorem cell23_3289466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_3289466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289466 prefixEnd_3289466 := by exact prefixLift 3289466
  have htrace : WordTrace (prefixWord ++ tailWord_3289466) baseStart_3289466 baseEnd_3289466 := by
    simpa [prefixWord, tailWord_3289466, baseEnd_3289466] using wordTrace_append hprefix tailTrace_3289466
  have hstable : (prefixWord ++ tailWord_3289466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289466).length < 2 ^ (prefixWord ++ tailWord_3289466).sum := by decide
  have hdescent : baseEnd_3289466 < baseStart_3289466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289476 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 3, 6]
def baseStart_3289476 : Nat := 118140960795 + 3289476 * 2 ^ 59
def prefixEnd_3289476 : Nat := 4983230072969 + 3 ^ 40 * 3289476 * 2
def baseEnd_3289476 : Nat := 563027429809759047907327

theorem tailTrace_3289476 : CollatzResearch.WordTrace tailWord_3289476 prefixEnd_3289476 563027429809759047907327 := by
  unfold tailWord_3289476
  simp only [CollatzResearch.WordTrace]
  refine ⟨59988523115398862309452141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79984697487198483079269521 59988523115398862309452141)
  ·
    refine ⟨22495696168274573366044553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59988523115398862309452141 22495696168274573366044553)
    ·
      refine ⟨16871772126205930024533415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22495696168274573366044553 16871772126205930024533415)
      ·
        refine ⟨25307658189308895036800123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16871772126205930024533415 25307658189308895036800123)
        ·
          refine ⟨37961487283963342555200185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25307658189308895036800123 37961487283963342555200185)
          ·
            refine ⟨28471115462972506916400139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37961487283963342555200185 28471115462972506916400139)
            ·
              refine ⟨42706673194458760374600209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28471115462972506916400139 42706673194458760374600209)
              ·
                refine ⟨32030004895844070280950157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42706673194458760374600209 32030004895844070280950157)
                ·
                  refine ⟨12011251835941526355356309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32030004895844070280950157 12011251835941526355356309)
                  ·
                    refine ⟨563027429809759047907327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12011251835941526355356309 563027429809759047907327)
                    ·
                      rfl

theorem cell23_3289476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_3289476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289476 prefixEnd_3289476 := by exact prefixLift 3289476
  have htrace : WordTrace (prefixWord ++ tailWord_3289476) baseStart_3289476 baseEnd_3289476 := by
    simpa [prefixWord, tailWord_3289476, baseEnd_3289476] using wordTrace_append hprefix tailTrace_3289476
  have hstable : (prefixWord ++ tailWord_3289476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289476).length < 2 ^ (prefixWord ++ tailWord_3289476).sum := by decide
  have hdescent : baseEnd_3289476 < baseStart_3289476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289503 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 3]
def baseStart_3289503 : Nat := 118140960795 + 3289503 * 2 ^ 59
def prefixEnd_3289503 : Nat := 4983230072969 + 3 ^ 40 * 3289503 * 2
def baseEnd_3289503 : Nat := 1689096153406948538084357

theorem tailTrace_3289503 : CollatzResearch.WordTrace tailWord_3289503 prefixEnd_3289503 1689096153406948538084357 := by
  unfold tailWord_3289503
  simp only [CollatzResearch.WordTrace]
  refine ⟨119978031001699908230137163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79985354001133272153424775 119978031001699908230137163)
  ·
    refine ⟨179967046502549862345205745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119978031001699908230137163 179967046502549862345205745)
    ·
      refine ⟨134975284876912396758904309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179967046502549862345205745 134975284876912396758904309)
      ·
        refine ⟨12653932957210537196147279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134975284876912396758904309 12653932957210537196147279)
        ·
          refine ⟨18980899435815805794220919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12653932957210537196147279 18980899435815805794220919)
          ·
            refine ⟨28471349153723708691331379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18980899435815805794220919 28471349153723708691331379)
            ·
              refine ⟨42707023730585563036997069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28471349153723708691331379 42707023730585563036997069)
              ·
                refine ⟨16015133898969586138873901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42707023730585563036997069 16015133898969586138873901)
                ·
                  refine ⟨6005675212113594802077713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16015133898969586138873901 6005675212113594802077713)
                  ·
                    refine ⟨4504256409085196101558285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6005675212113594802077713 4504256409085196101558285)
                    ·
                      refine ⟨1689096153406948538084357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4504256409085196101558285 1689096153406948538084357)
                      ·
                        rfl

theorem cell23_3289503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_3289503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289503 prefixEnd_3289503 := by exact prefixLift 3289503
  have htrace : WordTrace (prefixWord ++ tailWord_3289503) baseStart_3289503 baseEnd_3289503 := by
    simpa [prefixWord, tailWord_3289503, baseEnd_3289503] using wordTrace_append hprefix tailTrace_3289503
  have hstable : (prefixWord ++ tailWord_3289503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289503).length < 2 ^ (prefixWord ++ tailWord_3289503).sum := by decide
  have hdescent : baseEnd_3289503 < baseStart_3289503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289514 : List Nat := [3, 1, 6, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3289514 : Nat := 118140960795 + 3289514 * 2 ^ 59
def prefixEnd_3289514 : Nat := 4983230072969 + 3 ^ 40 * 3289514 * 2
def baseEnd_3289514 : Nat := 563033933898049331682269

theorem tailTrace_3289514 : CollatzResearch.WordTrace tailWord_3289514 prefixEnd_3289514 563033933898049331682269 := by
  unfold tailWord_3289514
  simp only [CollatzResearch.WordTrace]
  refine ⟨29994608051165014277196899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79985621469773371405858397 29994608051165014277196899)
  ·
    refine ⟨44991912076747521415795349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29994608051165014277196899 44991912076747521415795349)
    ·
      refine ⟨2108995878597540066365407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44991912076747521415795349 2108995878597540066365407)
      ·
        refine ⟨3163493817896310099548111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2108995878597540066365407 3163493817896310099548111)
        ·
          refine ⟨4745240726844465149322167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3163493817896310099548111 4745240726844465149322167)
          ·
            refine ⟨7117861090266697723983251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4745240726844465149322167 7117861090266697723983251)
            ·
              refine ⟨10676791635400046585974877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7117861090266697723983251 10676791635400046585974877)
              ·
                refine ⟨4003796863275017469740579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10676791635400046585974877 4003796863275017469740579)
                ·
                  refine ⟨6005695294912526204610869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4003796863275017469740579 6005695294912526204610869)
                  ·
                    refine ⟨563033933898049331682269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6005695294912526204610869 563033933898049331682269)
                    ·
                      rfl

theorem cell23_3289514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3289514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289514 prefixEnd_3289514 := by exact prefixLift 3289514
  have htrace : WordTrace (prefixWord ++ tailWord_3289514) baseStart_3289514 baseEnd_3289514 := by
    simpa [prefixWord, tailWord_3289514, baseEnd_3289514] using wordTrace_append hprefix tailTrace_3289514
  have hstable : (prefixWord ++ tailWord_3289514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289514).length < 2 ^ (prefixWord ++ tailWord_3289514).sum := by decide
  have hdescent : baseEnd_3289514 < baseStart_3289514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289517 : List Nat := [1, 5, 2, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_3289517 : Nat := 118140960795 + 3289517 * 2 ^ 59
def prefixEnd_3289517 : Nat := 4983230072969 + 3 ^ 40 * 3289517 * 2
def baseEnd_3289517 : Nat := 1689103342136111483309293

theorem tailTrace_3289517 : CollatzResearch.WordTrace tailWord_3289517 prefixEnd_3289517 1689103342136111483309293 := by
  unfold tailWord_3289517
  simp only [CollatzResearch.WordTrace]
  refine ⟨119978541623649188621146805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79985694415766125747431203 119978541623649188621146805)
  ·
    refine ⟨11247988277217111433232513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119978541623649188621146805 11247988277217111433232513)
    ·
      refine ⟨8435991207912833574924385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11247988277217111433232513 8435991207912833574924385)
      ·
        refine ⟨6326993405934625181193289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8435991207912833574924385 6326993405934625181193289)
        ·
          refine ⟨4745245054450968885894967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6326993405934625181193289 4745245054450968885894967)
          ·
            refine ⟨7117867581676453328842451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4745245054450968885894967 7117867581676453328842451)
            ·
              refine ⟨10676801372514679993263677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7117867581676453328842451 10676801372514679993263677)
              ·
                refine ⟨4003800514693004997473879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10676801372514679993263677 4003800514693004997473879)
                ·
                  refine ⟨6005700772039507496210819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4003800514693004997473879 6005700772039507496210819)
                  ·
                    refine ⟨9008551158059261244316229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6005700772039507496210819 9008551158059261244316229)
                    ·
                      refine ⟨1689103342136111483309293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9008551158059261244316229 1689103342136111483309293)
                      ·
                        rfl

theorem cell23_3289517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_3289517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289517 prefixEnd_3289517 := by exact prefixLift 3289517
  have htrace : WordTrace (prefixWord ++ tailWord_3289517) baseStart_3289517 baseEnd_3289517 := by
    simpa [prefixWord, tailWord_3289517, baseEnd_3289517] using wordTrace_append hprefix tailTrace_3289517
  have hstable : (prefixWord ++ tailWord_3289517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289517).length < 2 ^ (prefixWord ++ tailWord_3289517).sum := by decide
  have hdescent : baseEnd_3289517 < baseStart_3289517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289534 : List Nat := [4, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2]
def baseStart_3289534 : Nat := 118140960795 + 3289534 * 2 ^ 59
def prefixEnd_3289534 : Nat := 4983230072969 + 3 ^ 40 * 3289534 * 2
def baseEnd_3289534 : Nat := 1689112071307237916796715

theorem tailTrace_3289534 : CollatzResearch.WordTrace tailWord_3289534 prefixEnd_3289534 1689112071307237916796715 := by
  unfold tailWord_3289534
  simp only [CollatzResearch.WordTrace]
  refine ⟨14997395208073450065564457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79986107776391733683010437 14997395208073450065564457)
  ·
    refine ⟨11248046406055087549173343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14997395208073450065564457 11248046406055087549173343)
    ·
      refine ⟨16872069609082631323760015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11248046406055087549173343 16872069609082631323760015)
      ·
        refine ⟨25308104413623946985640023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16872069609082631323760015 25308104413623946985640023)
        ·
          refine ⟨37962156620435920478460035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25308104413623946985640023 37962156620435920478460035)
          ·
            refine ⟨56943234930653880717690053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37962156620435920478460035 56943234930653880717690053)
            ·
              refine ⟨10676856549497602634566885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56943234930653880717690053 10676856549497602634566885)
              ·
                refine ⟨2001910603030800493981291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10676856549497602634566885 2001910603030800493981291)
                ·
                  refine ⟨3002865904546200740971937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2001910603030800493981291 3002865904546200740971937)
                  ·
                    refine ⟨2252149428409650555728953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3002865904546200740971937 2252149428409650555728953)
                    ·
                      refine ⟨1689112071307237916796715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2252149428409650555728953 1689112071307237916796715)
                      ·
                        rfl

theorem cell23_3289534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_3289534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289534 prefixEnd_3289534 := by exact prefixLift 3289534
  have htrace : WordTrace (prefixWord ++ tailWord_3289534) baseStart_3289534 baseEnd_3289534 := by
    simpa [prefixWord, tailWord_3289534, baseEnd_3289534] using wordTrace_append hprefix tailTrace_3289534
  have hstable : (prefixWord ++ tailWord_3289534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289534).length < 2 ^ (prefixWord ++ tailWord_3289534).sum := by decide
  have hdescent : baseEnd_3289534 < baseStart_3289534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289554 : List Nat := [3, 2, 2, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_3289554 : Nat := 118140960795 + 3289554 * 2 ^ 59
def prefixEnd_3289554 : Nat := 4983230072969 + 3 ^ 40 * 3289554 * 2
def baseEnd_3289554 : Nat := 1689122340920327838546623

theorem tailTrace_3289554 : CollatzResearch.WordTrace tailWord_3289554 prefixEnd_3289554 1689122340920327838546623 := by
  unfold tailWord_3289554
  simp only [CollatzResearch.WordTrace]
  refine ⟨29994972781128785985060929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79986594083010095960162477 29994972781128785985060929)
  ·
    refine ⟨22496229585846589488795697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29994972781128785985060929 22496229585846589488795697)
    ·
      refine ⟨16872172189384942116596773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22496229585846589488795697 16872172189384942116596773)
      ·
        refine ⟨3163532285509676646861895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16872172189384942116596773 3163532285509676646861895)
        ·
          refine ⟨4745298428264514970292843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3163532285509676646861895 4745298428264514970292843)
          ·
            refine ⟨7117947642396772455439265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4745298428264514970292843 7117947642396772455439265)
            ·
              refine ⟨5338460731797579341579449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7117947642396772455439265 5338460731797579341579449)
              ·
                refine ⟨4003845548848184506184587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5338460731797579341579449 4003845548848184506184587)
                ·
                  refine ⟨6005768323272276759276881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4003845548848184506184587 6005768323272276759276881)
                  ·
                    refine ⟨4504326242454207569457661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6005768323272276759276881 4504326242454207569457661)
                    ·
                      refine ⟨1689122340920327838546623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4504326242454207569457661 1689122340920327838546623)
                      ·
                        rfl

theorem cell23_3289554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_3289554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289554 prefixEnd_3289554 := by exact prefixLift 3289554
  have htrace : WordTrace (prefixWord ++ tailWord_3289554) baseStart_3289554 baseEnd_3289554 := by
    simpa [prefixWord, tailWord_3289554, baseEnd_3289554] using wordTrace_append hprefix tailTrace_3289554
  have hstable : (prefixWord ++ tailWord_3289554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289554).length < 2 ^ (prefixWord ++ tailWord_3289554).sum := by decide
  have hdescent : baseEnd_3289554 < baseStart_3289554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289650 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2]
def baseStart_3289650 : Nat := 118140960795 + 3289650 * 2 ^ 59
def prefixEnd_3289650 : Nat := 4983230072969 + 3 ^ 40 * 3289650 * 2
def baseEnd_3289650 : Nat := 1689171635063159462946181

theorem tailTrace_3289650 : CollatzResearch.WordTrace tailWord_3289650 prefixEnd_3289650 1689171635063159462946181 := by
  unfold tailWord_3289650
  simp only [CollatzResearch.WordTrace]
  refine ⟨29995848133041838083934601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79988928354778234890492269 29995848133041838083934601)
  ·
    refine ⟨22496886099781378562950951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29995848133041838083934601 22496886099781378562950951)
    ·
      refine ⟨33745329149672067844426427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22496886099781378562950951 33745329149672067844426427)
      ·
        refine ⟨50617993724508101766639641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33745329149672067844426427 50617993724508101766639641)
        ·
          refine ⟨37963495293381076324979731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50617993724508101766639641 37963495293381076324979731)
          ·
            refine ⟨56945242940071614487469597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37963495293381076324979731 56945242940071614487469597)
            ·
              refine ⟨21354466102526855432801099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56945242940071614487469597 21354466102526855432801099)
              ·
                refine ⟨32031699153790283149201649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21354466102526855432801099 32031699153790283149201649)
                ·
                  refine ⟨24023774365342712361901237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32031699153790283149201649 24023774365342712361901237)
                  ·
                    refine ⟨2252228846750879283928241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24023774365342712361901237 2252228846750879283928241)
                    ·
                      refine ⟨1689171635063159462946181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2252228846750879283928241 1689171635063159462946181)
                      ·
                        rfl

theorem cell23_3289650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_3289650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289650 prefixEnd_3289650 := by exact prefixLift 3289650
  have htrace : WordTrace (prefixWord ++ tailWord_3289650) baseStart_3289650 baseEnd_3289650 := by
    simpa [prefixWord, tailWord_3289650, baseEnd_3289650] using wordTrace_append hprefix tailTrace_3289650
  have hstable : (prefixWord ++ tailWord_3289650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289650).length < 2 ^ (prefixWord ++ tailWord_3289650).sum := by decide
  have hdescent : baseEnd_3289650 < baseStart_3289650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289653 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_3289653 : Nat := 118140960795 + 3289653 * 2 ^ 59
def prefixEnd_3289653 : Nat := 4983230072969 + 3 ^ 40 * 3289653 * 2
def baseEnd_3289653 : Nat := 1689173175505122951208667

theorem tailTrace_3289653 : CollatzResearch.WordTrace tailWord_3289653 prefixEnd_3289653 1689173175505122951208667 := by
  unfold tailWord_3289653
  simp only [CollatzResearch.WordTrace]
  refine ⟨119983501951156483848097613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79989001300770989232065075 119983501951156483848097613)
  ·
    refine ⟨44993813231683681443036605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119983501951156483848097613 44993813231683681443036605)
    ·
      refine ⟨16872679961881380541138727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44993813231683681443036605 16872679961881380541138727)
      ·
        refine ⟨25309019942822070811708091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16872679961881380541138727 25309019942822070811708091)
        ·
          refine ⟨37963529914233106217562137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25309019942822070811708091 37963529914233106217562137)
          ·
            refine ⟨28472647435674829663171603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37963529914233106217562137 28472647435674829663171603)
            ·
              refine ⟨42708971153512244494757405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28472647435674829663171603 42708971153512244494757405)
              ·
                refine ⟨16015864182567091685534027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42708971153512244494757405 16015864182567091685534027)
                ·
                  refine ⟨24023796273850637528301041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16015864182567091685534027 24023796273850637528301041)
                  ·
                    refine ⟨18017847205387978146225781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24023796273850637528301041 18017847205387978146225781)
                    ·
                      refine ⟨1689173175505122951208667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18017847205387978146225781 1689173175505122951208667)
                      ·
                        rfl

theorem cell23_3289653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_3289653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289653 prefixEnd_3289653 := by exact prefixLift 3289653
  have htrace : WordTrace (prefixWord ++ tailWord_3289653) baseStart_3289653 baseEnd_3289653 := by
    simpa [prefixWord, tailWord_3289653, baseEnd_3289653] using wordTrace_append hprefix tailTrace_3289653
  have hstable : (prefixWord ++ tailWord_3289653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289653).length < 2 ^ (prefixWord ++ tailWord_3289653).sum := by decide
  have hdescent : baseEnd_3289653 < baseStart_3289653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289663 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 4]
def baseStart_3289663 : Nat := 118140960795 + 3289663 * 2 ^ 59
def prefixEnd_3289663 : Nat := 4983230072969 + 3 ^ 40 * 3289663 * 2
def baseEnd_3289663 : Nat := 1689178310311667912083621

theorem tailTrace_3289663 : CollatzResearch.WordTrace tailWord_3289663 prefixEnd_3289663 1689178310311667912083621 := by
  unfold tailWord_3289663
  simp only [CollatzResearch.WordTrace]
  refine ⟨119983866681120255555961643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79989244454080170370641095 119983866681120255555961643)
  ·
    refine ⟨179975800021680383333942465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119983866681120255555961643 179975800021680383333942465)
    ·
      refine ⟨134981850016260287500456849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179975800021680383333942465 134981850016260287500456849)
      ·
        refine ⟨101236387512195215625342637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134981850016260287500456849 101236387512195215625342637)
        ·
          refine ⟨37963645317073205859503489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101236387512195215625342637 37963645317073205859503489)
          ·
            refine ⟨28472733987804904394627617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37963645317073205859503489 28472733987804904394627617)
            ·
              refine ⟨21354550490853678295970713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28472733987804904394627617 21354550490853678295970713)
              ·
                refine ⟨16015912868140258721978035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21354550490853678295970713 16015912868140258721978035)
                ·
                  refine ⟨24023869302210388082967053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16015912868140258721978035 24023869302210388082967053)
                  ·
                    refine ⟨9008950988328895531112645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24023869302210388082967053 9008950988328895531112645)
                    ·
                      refine ⟨1689178310311667912083621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9008950988328895531112645 1689178310311667912083621)
                      ·
                        rfl

theorem cell23_3289663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_3289663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289663 prefixEnd_3289663 := by exact prefixLift 3289663
  have htrace : WordTrace (prefixWord ++ tailWord_3289663) baseStart_3289663 baseEnd_3289663 := by
    simpa [prefixWord, tailWord_3289663, baseEnd_3289663] using wordTrace_append hprefix tailTrace_3289663
  have hstable : (prefixWord ++ tailWord_3289663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289663).length < 2 ^ (prefixWord ++ tailWord_3289663).sum := by decide
  have hdescent : baseEnd_3289663 < baseStart_3289663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289677 : List Nat := [1, 6, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_3289677 : Nat := 118140960795 + 3289677 * 2 ^ 59
def prefixEnd_3289677 : Nat := 4983230072969 + 3 ^ 40 * 3289677 * 2
def baseEnd_3289677 : Nat := 563061833013610285769519

theorem tailTrace_3289677 : CollatzResearch.WordTrace tailWord_3289677 prefixEnd_3289677 563061833013610285769519 := by
  unfold tailWord_3289677
  simp only [CollatzResearch.WordTrace]
  refine ⟨119984377303069535946971285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79989584868713023964647523 119984377303069535946971285)
  ·
    refine ⟨5624267686081384497514279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 119984377303069535946971285 5624267686081384497514279)
    ·
      refine ⟨8436401529122076746271419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5624267686081384497514279 8436401529122076746271419)
      ·
        refine ⟨12654602293683115119407129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8436401529122076746271419 12654602293683115119407129)
        ·
          refine ⟨9490951720262336339555347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12654602293683115119407129 9490951720262336339555347)
          ·
            refine ⟨14236427580393504509333021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9490951720262336339555347 14236427580393504509333021)
            ·
              refine ⟨5338660342647564190999883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14236427580393504509333021 5338660342647564190999883)
              ·
                refine ⟨8007990513971346286499825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5338660342647564190999883 8007990513971346286499825)
                ·
                  refine ⟨6005992885478509714874869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8007990513971346286499825 6005992885478509714874869)
                  ·
                    refine ⟨563061833013610285769519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6005992885478509714874869 563061833013610285769519)
                    ·
                      rfl

theorem cell23_3289677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_3289677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289677 prefixEnd_3289677 := by exact prefixLift 3289677
  have htrace : WordTrace (prefixWord ++ tailWord_3289677) baseStart_3289677 baseEnd_3289677 := by
    simpa [prefixWord, tailWord_3289677, baseEnd_3289677] using wordTrace_append hprefix tailTrace_3289677
  have hstable : (prefixWord ++ tailWord_3289677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289677).length < 2 ^ (prefixWord ++ tailWord_3289677).sum := by decide
  have hdescent : baseEnd_3289677 < baseStart_3289677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289700 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 4, 2, 3]
def baseStart_3289700 : Nat := 118140960795 + 3289700 * 2 ^ 59
def prefixEnd_3289700 : Nat := 4983230072969 + 3 ^ 40 * 3289700 * 2
def baseEnd_3289700 : Nat := 1689197309095884267320951

theorem tailTrace_3289700 : CollatzResearch.WordTrace tailWord_3289700 prefixEnd_3289700 1689197309095884267320951 := by
  unfold tailWord_3289700
  simp only [CollatzResearch.WordTrace]
  refine ⟨59992608090993105437529277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79990144121324140583372369 59992608090993105437529277)
  ·
    refine ⟨22497228034122414539073479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59992608090993105437529277 22497228034122414539073479)
    ·
      refine ⟨33745842051183621808610219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22497228034122414539073479 33745842051183621808610219)
      ·
        refine ⟨50618763076775432712915329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33745842051183621808610219 50618763076775432712915329)
        ·
          refine ⟨37964072307581574534686497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50618763076775432712915329 37964072307581574534686497)
          ·
            refine ⟨28473054230686180901014873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37964072307581574534686497 28473054230686180901014873)
            ·
              refine ⟨21354790673014635675761155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28473054230686180901014873 21354790673014635675761155)
              ·
                refine ⟨32032186009521953513641733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21354790673014635675761155 32032186009521953513641733)
                ·
                  refine ⟨6006034876785366283807825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32032186009521953513641733 6006034876785366283807825)
                  ·
                    refine ⟨4504526157589024712855869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6006034876785366283807825 4504526157589024712855869)
                    ·
                      refine ⟨1689197309095884267320951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4504526157589024712855869 1689197309095884267320951)
                      ·
                        rfl

theorem cell23_3289700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_3289700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289700 prefixEnd_3289700 := by exact prefixLift 3289700
  have htrace : WordTrace (prefixWord ++ tailWord_3289700) baseStart_3289700 baseEnd_3289700 := by
    simpa [prefixWord, tailWord_3289700, baseEnd_3289700] using wordTrace_append hprefix tailTrace_3289700
  have hstable : (prefixWord ++ tailWord_3289700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289700).length < 2 ^ (prefixWord ++ tailWord_3289700).sum := by decide
  have hdescent : baseEnd_3289700 < baseStart_3289700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289757 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 4, 3, 2]
def baseStart_3289757 : Nat := 118140960795 + 3289757 * 2 ^ 59
def prefixEnd_3289757 : Nat := 4983230072969 + 3 ^ 40 * 3289757 * 2
def baseEnd_3289757 : Nat := 1689226577493190544308189

theorem tailTrace_3289757 : CollatzResearch.WordTrace tailWord_3289757 prefixEnd_3289757 1689226577493190544308189 := by
  unfold tailWord_3289757
  simp only [CollatzResearch.WordTrace]
  refine ⟨119987295142779709609883525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79991530095186473073255683 119987295142779709609883525)
  ·
    refine ⟨22497617839271195551853161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119987295142779709609883525 22497617839271195551853161)
    ·
      refine ⟨16873213379453396663889871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22497617839271195551853161 16873213379453396663889871)
      ·
        refine ⟨25309820069180094995834807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16873213379453396663889871 25309820069180094995834807)
        ·
          refine ⟨37964730103770142493752211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25309820069180094995834807 37964730103770142493752211)
          ·
            refine ⟨56947095155655213740628317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37964730103770142493752211 56947095155655213740628317)
            ·
              refine ⟨21355160683370705152735619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56947095155655213740628317 21355160683370705152735619)
              ·
                refine ⟨32032741025056057729103429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21355160683370705152735619 32032741025056057729103429)
                ·
                  refine ⟨6006138942198010824206893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32032741025056057729103429 6006138942198010824206893)
                  ·
                    refine ⟨2252302103324254059077585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6006138942198010824206893 2252302103324254059077585)
                    ·
                      refine ⟨1689226577493190544308189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2252302103324254059077585 1689226577493190544308189)
                      ·
                        rfl

theorem cell23_3289757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_3289757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289757 prefixEnd_3289757 := by exact prefixLift 3289757
  have htrace : WordTrace (prefixWord ++ tailWord_3289757) baseStart_3289757 baseEnd_3289757 := by
    simpa [prefixWord, tailWord_3289757, baseEnd_3289757] using wordTrace_append hprefix tailTrace_3289757
  have hstable : (prefixWord ++ tailWord_3289757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289757).length < 2 ^ (prefixWord ++ tailWord_3289757).sum := by decide
  have hdescent : baseEnd_3289757 < baseStart_3289757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289763 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 5, 6]
def baseStart_3289763 : Nat := 118140960795 + 3289763 * 2 ^ 59
def prefixEnd_3289763 : Nat := 4983230072969 + 3 ^ 40 * 3289763 * 2
def baseEnd_3289763 : Nat := 563076552792372506944387

theorem tailTrace_3289763 : CollatzResearch.WordTrace tailWord_3289763 prefixEnd_3289763 563076552792372506944387 := by
  unfold tailWord_3289763
  simp only [CollatzResearch.WordTrace]
  refine ⟨119987513980757972634601943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79991675987171981756401295 119987513980757972634601943)
  ·
    refine ⟨179981270971136958951902915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119987513980757972634601943 179981270971136958951902915)
    ·
      refine ⟨269971906456705438427854373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179981270971136958951902915 269971906456705438427854373)
      ·
        refine ⟨50619732460632269705222695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269971906456705438427854373 50619732460632269705222695)
        ·
          refine ⟨75929598690948404557834043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50619732460632269705222695 75929598690948404557834043)
          ·
            refine ⟨113894398036422606836751065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75929598690948404557834043 113894398036422606836751065)
            ·
              refine ⟨85420798527316955127563299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113894398036422606836751065 85420798527316955127563299)
              ·
                refine ⟨128131197790975432691344949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85420798527316955127563299 128131197790975432691344949)
                ·
                  refine ⟨12012299792903946814813589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128131197790975432691344949 12012299792903946814813589)
                  ·
                    refine ⟨563076552792372506944387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12012299792903946814813589 563076552792372506944387)
                    ·
                      rfl

theorem cell23_3289763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 6].length) (baseStart_3289763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289763 prefixEnd_3289763 := by exact prefixLift 3289763
  have htrace : WordTrace (prefixWord ++ tailWord_3289763) baseStart_3289763 baseEnd_3289763 := by
    simpa [prefixWord, tailWord_3289763, baseEnd_3289763] using wordTrace_append hprefix tailTrace_3289763
  have hstable : (prefixWord ++ tailWord_3289763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289763).length < 2 ^ (prefixWord ++ tailWord_3289763).sum := by decide
  have hdescent : baseEnd_3289763 < baseStart_3289763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289800 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_3289800 : Nat := 118140960795 + 3289800 * 2 ^ 59
def prefixEnd_3289800 : Nat := 4983230072969 + 3 ^ 40 * 3289800 * 2
def baseEnd_3289800 : Nat := 1689248657161333876070491

theorem tailTrace_3289800 : CollatzResearch.WordTrace tailWord_3289800 prefixEnd_3289800 1689248657161333876070491 := by
  unfold tailWord_3289800
  simp only [CollatzResearch.WordTrace]
  refine ⟨59994431740811963976849427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79992575654415951969132569 59994431740811963976849427)
  ·
    refine ⟨89991647611217945965274141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59994431740811963976849427 89991647611217945965274141)
    ·
      refine ⟨33746867854206729736977803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89991647611217945965274141 33746867854206729736977803)
      ·
        refine ⟨50620301781310094605466705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33746867854206729736977803 50620301781310094605466705)
        ·
          refine ⟨37965226335982570954100029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50620301781310094605466705 37965226335982570954100029)
          ·
            refine ⟨14236959875993464107787511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37965226335982570954100029 14236959875993464107787511)
            ·
              refine ⟨21355439813990196161681267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14236959875993464107787511 21355439813990196161681267)
              ·
                refine ⟨32033159720985294242521901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21355439813990196161681267 32033159720985294242521901)
                ·
                  refine ⟨12012434895369485340945713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32033159720985294242521901 12012434895369485340945713)
                  ·
                    refine ⟨9009326171527114005709285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12012434895369485340945713 9009326171527114005709285)
                    ·
                      refine ⟨1689248657161333876070491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9009326171527114005709285 1689248657161333876070491)
                      ·
                        rfl

theorem cell23_3289800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_3289800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289800 prefixEnd_3289800 := by exact prefixLift 3289800
  have htrace : WordTrace (prefixWord ++ tailWord_3289800) baseStart_3289800 baseEnd_3289800 := by
    simpa [prefixWord, tailWord_3289800, baseEnd_3289800] using wordTrace_append hprefix tailTrace_3289800
  have hstable : (prefixWord ++ tailWord_3289800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289800).length < 2 ^ (prefixWord ++ tailWord_3289800).sum := by decide
  have hdescent : baseEnd_3289800 < baseStart_3289800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289810 : List Nat := [3, 2, 2, 2, 3, 11]
def baseStart_3289810 : Nat := 118140960795 + 3289810 * 2 ^ 59
def prefixEnd_3289810 : Nat := 4983230072969 + 3 ^ 40 * 3289810 * 2
def baseEnd_3289810 : Nat := 6951661695341065172615

theorem tailTrace_3289810 : CollatzResearch.WordTrace tailWord_3289810 prefixEnd_3289810 6951661695341065172615 := by
  unfold tailWord_3289810
  simp only [CollatzResearch.WordTrace]
  refine ⟨29997307052896924915390721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79992818807725133107708589 29997307052896924915390721)
  ·
    refine ⟨22497980289672693686543041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29997307052896924915390721 22497980289672693686543041)
    ·
      refine ⟨16873485217254520264907281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22497980289672693686543041 16873485217254520264907281)
      ·
        refine ⟨12655113912940890198680461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16873485217254520264907281 12655113912940890198680461)
        ·
          refine ⟨4745667717352833824505173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12655113912940890198680461 4745667717352833824505173)
          ·
            refine ⟨6951661695341065172615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4745667717352833824505173 6951661695341065172615)
            ·
              rfl

theorem cell23_3289810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 11].length) (baseStart_3289810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289810 prefixEnd_3289810 := by exact prefixLift 3289810
  have htrace : WordTrace (prefixWord ++ tailWord_3289810) baseStart_3289810 baseEnd_3289810 := by
    simpa [prefixWord, tailWord_3289810, baseEnd_3289810] using wordTrace_append hprefix tailTrace_3289810
  have hstable : (prefixWord ++ tailWord_3289810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289810).length < 2 ^ (prefixWord ++ tailWord_3289810).sum := by decide
  have hdescent : baseEnd_3289810 < baseStart_3289810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289827 : List Nat := [1, 1, 1, 7, 1, 3, 1, 8]
def baseStart_3289827 : Nat := 118140960795 + 3289827 * 2 ^ 59
def prefixEnd_3289827 : Nat := 4983230072969 + 3 ^ 40 * 3289827 * 2
def baseEnd_3289827 : Nat := 62565278560703898904921

theorem tailTrace_3289827 : CollatzResearch.WordTrace tailWord_3289827 prefixEnd_3289827 62565278560703898904921 := by
  unfold tailWord_3289827
  simp only [CollatzResearch.WordTrace]
  refine ⟨119989848252526111564931735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79993232168350741043287823 119989848252526111564931735)
  ·
    refine ⟨179984772378789167347397603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119989848252526111564931735 179984772378789167347397603)
    ·
      refine ⟨269977158568183751021096405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179984772378789167347397603 269977158568183751021096405)
      ·
        refine ⟨6327589653941806664556947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 269977158568183751021096405 6327589653941806664556947)
        ·
          refine ⟨9491384480912709996835421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6327589653941806664556947 9491384480912709996835421)
          ·
            refine ⟨3559269180342266248813283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9491384480912709996835421 3559269180342266248813283)
            ·
              refine ⟨5338903770513399373219925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3559269180342266248813283 5338903770513399373219925)
              ·
                refine ⟨62565278560703898904921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5338903770513399373219925 62565278560703898904921)
                ·
                  rfl

theorem cell23_3289827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 8].length) (baseStart_3289827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289827 prefixEnd_3289827 := by exact prefixLift 3289827
  have htrace : WordTrace (prefixWord ++ tailWord_3289827) baseStart_3289827 baseEnd_3289827 := by
    simpa [prefixWord, tailWord_3289827, baseEnd_3289827] using wordTrace_append hprefix tailTrace_3289827
  have hstable : (prefixWord ++ tailWord_3289827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289827).length < 2 ^ (prefixWord ++ tailWord_3289827).sum := by decide
  have hdescent : baseEnd_3289827 < baseStart_3289827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289854 : List Nat := [4, 2, 2, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_3289854 : Nat := 118140960795 + 3289854 * 2 ^ 59
def prefixEnd_3289854 : Nat := 4983230072969 + 3 ^ 40 * 3289854 * 2
def baseEnd_3289854 : Nat := 1689276385116676664795243

theorem tailTrace_3289854 : CollatzResearch.WordTrace tailWord_3289854 prefixEnd_3289854 1689276385116676664795243 := by
  unfold tailWord_3289854
  simp only [CollatzResearch.WordTrace]
  refine ⟨14998854127928536897020577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79993888682285530117443077 14998854127928536897020577)
  ·
    refine ⟨11249140595946402672765433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14998854127928536897020577 11249140595946402672765433)
    ·
      refine ⟨8436855446959802004574075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11249140595946402672765433 8436855446959802004574075)
      ·
        refine ⟨12655283170439703006861113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8436855446959802004574075 12655283170439703006861113)
        ·
          refine ⟨9491462377829777255145835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12655283170439703006861113 9491462377829777255145835)
          ·
            refine ⟨14237193566744665882718753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9491462377829777255145835 14237193566744665882718753)
            ·
              refine ⟨10677895175058499412039065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14237193566744665882718753 10677895175058499412039065)
              ·
                refine ⟨8008421381293874559029299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10677895175058499412039065 8008421381293874559029299)
                ·
                  refine ⟨12012632071940811838543949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8008421381293874559029299 12012632071940811838543949)
                  ·
                    refine ⟨4504737026977804439453981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12012632071940811838543949 4504737026977804439453981)
                    ·
                      refine ⟨1689276385116676664795243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4504737026977804439453981 1689276385116676664795243)
                      ·
                        rfl

theorem cell23_3289854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_3289854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289854 prefixEnd_3289854 := by exact prefixLift 3289854
  have htrace : WordTrace (prefixWord ++ tailWord_3289854) baseStart_3289854 baseEnd_3289854 := by
    simpa [prefixWord, tailWord_3289854, baseEnd_3289854] using wordTrace_append hprefix tailTrace_3289854
  have hstable : (prefixWord ++ tailWord_3289854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289854).length < 2 ^ (prefixWord ++ tailWord_3289854).sum := by decide
  have hdescent : baseEnd_3289854 < baseStart_3289854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289858 : List Nat := [3, 4, 1, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_3289858 : Nat := 118140960795 + 3289858 * 2 ^ 59
def prefixEnd_3289858 : Nat := 4983230072969 + 3 ^ 40 * 3289858 * 2
def baseEnd_3289858 : Nat := 1689278439039294649145225

theorem tailTrace_3289858 : CollatzResearch.WordTrace tailWord_3289858 prefixEnd_3289858 1689278439039294649145225 := by
  unfold tailWord_3289858
  simp only [CollatzResearch.WordTrace]
  refine ⟨29997744728853450964827557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79993985943609202572873485 29997744728853450964827557)
  ·
    refine ⟨5624577136660022055905167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29997744728853450964827557 5624577136660022055905167)
    ·
      refine ⟨8436865704990033083857751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5624577136660022055905167 8436865704990033083857751)
      ·
        refine ⟨12655298557485049625786627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8436865704990033083857751 12655298557485049625786627)
        ·
          refine ⟨18982947836227574438679941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12655298557485049625786627 18982947836227574438679941)
          ·
            refine ⟨3559302719292670207252489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18982947836227574438679941 3559302719292670207252489)
            ·
              refine ⟨2669477039469502655439367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3559302719292670207252489 2669477039469502655439367)
              ·
                refine ⟨4004215559204253983159051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2669477039469502655439367 4004215559204253983159051)
                ·
                  refine ⟨6006323338806380974738577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4004215559204253983159051 6006323338806380974738577)
                  ·
                    refine ⟨4504742504104785731053933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6006323338806380974738577 4504742504104785731053933)
                    ·
                      refine ⟨1689278439039294649145225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4504742504104785731053933 1689278439039294649145225)
                      ·
                        rfl

theorem cell23_3289858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_3289858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289858 prefixEnd_3289858 := by exact prefixLift 3289858
  have htrace : WordTrace (prefixWord ++ tailWord_3289858) baseStart_3289858 baseEnd_3289858 := by
    simpa [prefixWord, tailWord_3289858, baseEnd_3289858] using wordTrace_append hprefix tailTrace_3289858
  have hstable : (prefixWord ++ tailWord_3289858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289858).length < 2 ^ (prefixWord ++ tailWord_3289858).sum := by decide
  have hdescent : baseEnd_3289858 < baseStart_3289858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289880 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 4, 1, 5]
def baseStart_3289880 : Nat := 118140960795 + 3289880 * 2 ^ 59
def prefixEnd_3289880 : Nat := 4983230072969 + 3 ^ 40 * 3289880 * 2
def baseEnd_3289880 : Nat := 1689289735613693563070123

theorem tailTrace_3289880 : CollatzResearch.WordTrace tailWord_3289880 prefixEnd_3289880 1689289735613693563070123 := by
  unfold tailWord_3289880
  simp only [CollatzResearch.WordTrace]
  refine ⟨59995890660667050808305547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79994520880889401077740729 59995890660667050808305547)
  ·
    refine ⟨89993835991000576212458321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59995890660667050808305547 89993835991000576212458321)
    ·
      refine ⟨67495376993250432159343741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89993835991000576212458321 67495376993250432159343741)
      ·
        refine ⟨25310766372468912059753903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67495376993250432159343741 25310766372468912059753903)
        ·
          refine ⟨37966149558703368089630855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25310766372468912059753903 37966149558703368089630855)
          ·
            refine ⟨56949224338055052134446283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37966149558703368089630855 56949224338055052134446283)
            ·
              refine ⟨85423836507082578201669425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56949224338055052134446283 85423836507082578201669425)
              ·
                refine ⟨64067877380311933651252069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85423836507082578201669425 64067877380311933651252069)
                ·
                  refine ⟨12012727008808487559609763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64067877380311933651252069 12012727008808487559609763)
                  ·
                    refine ⟨18019090513212731339414645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12012727008808487559609763 18019090513212731339414645)
                    ·
                      refine ⟨1689289735613693563070123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18019090513212731339414645 1689289735613693563070123)
                      ·
                        rfl

theorem cell23_3289880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_3289880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289880 prefixEnd_3289880 := by exact prefixLift 3289880
  have htrace : WordTrace (prefixWord ++ tailWord_3289880) baseStart_3289880 baseEnd_3289880 := by
    simpa [prefixWord, tailWord_3289880, baseEnd_3289880] using wordTrace_append hprefix tailTrace_3289880
  have hstable : (prefixWord ++ tailWord_3289880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289880).length < 2 ^ (prefixWord ++ tailWord_3289880).sum := by decide
  have hdescent : baseEnd_3289880 < baseStart_3289880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289900 : List Nat := [2, 2, 1, 1, 1, 4, 1, 4, 7]
def baseStart_3289900 : Nat := 118140960795 + 3289900 * 2 ^ 59
def prefixEnd_3289900 : Nat := 4983230072969 + 3 ^ 40 * 3289900 * 2
def baseEnd_3289900 : Nat := 187700000580753720535559

theorem tailTrace_3289900 : CollatzResearch.WordTrace tailWord_3289900 prefixEnd_3289900 187700000580753720535559 := by
  unfold tailWord_3289900
  simp only [CollatzResearch.WordTrace]
  refine ⟨59996255390630822516169577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79995007187507763354892769 59996255390630822516169577)
  ·
    refine ⟨44997191542973116887127183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59996255390630822516169577 44997191542973116887127183)
    ·
      refine ⟨67495787314459675330690775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44997191542973116887127183 67495787314459675330690775)
      ·
        refine ⟨101243680971689512996036163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67495787314459675330690775 101243680971689512996036163)
        ·
          refine ⟨151865521457534269494054245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101243680971689512996036163 151865521457534269494054245)
          ·
            refine ⟨28474785273287675530135171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151865521457534269494054245 28474785273287675530135171)
            ·
              refine ⟨42712177909931513295202757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28474785273287675530135171 42712177909931513295202757)
              ·
                refine ⟨8008533358112158742850517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42712177909931513295202757 8008533358112158742850517)
                ·
                  refine ⟨187700000580753720535559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8008533358112158742850517 187700000580753720535559)
                  ·
                    rfl

theorem cell23_3289900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 7].length) (baseStart_3289900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289900 prefixEnd_3289900 := by exact prefixLift 3289900
  have htrace : WordTrace (prefixWord ++ tailWord_3289900) baseStart_3289900 baseEnd_3289900 := by
    simpa [prefixWord, tailWord_3289900, baseEnd_3289900] using wordTrace_append hprefix tailTrace_3289900
  have hstable : (prefixWord ++ tailWord_3289900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289900).length < 2 ^ (prefixWord ++ tailWord_3289900).sum := by decide
  have hdescent : baseEnd_3289900 < baseStart_3289900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289930 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 3, 7]
def baseStart_3289930 : Nat := 118140960795 + 3289930 * 2 ^ 59
def prefixEnd_3289930 : Nat := 4983230072969 + 3 ^ 40 * 3289930 * 2
def baseEnd_3289930 : Nat := 563105136548806122481631

theorem tailTrace_3289930 : CollatzResearch.WordTrace tailWord_3289930 prefixEnd_3289930 563105136548806122481631 := by
  unfold tailWord_3289930
  simp only [CollatzResearch.WordTrace]
  refine ⟨29998401242788240038982811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79995736647435306770620829 29998401242788240038982811)
  ·
    refine ⟨44997601864182360058474217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29998401242788240038982811 44997601864182360058474217)
    ·
      refine ⟨33748201398136770043855663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44997601864182360058474217 33748201398136770043855663)
      ·
        refine ⟨50622302097205155065783495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33748201398136770043855663 50622302097205155065783495)
        ·
          refine ⟨75933453145807732598675243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50622302097205155065783495 75933453145807732598675243)
          ·
            refine ⟨113900179718711598898012865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75933453145807732598675243 113900179718711598898012865)
            ·
              refine ⟨85425134789033699173509649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113900179718711598898012865 85425134789033699173509649)
              ·
                refine ⟨64068851091775274380132237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85425134789033699173509649 64068851091775274380132237)
                ·
                  refine ⟨24025819159415727892549589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64068851091775274380132237 24025819159415727892549589)
                  ·
                    refine ⟨563105136548806122481631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24025819159415727892549589 563105136548806122481631)
                    ·
                      rfl

theorem cell23_3289930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_3289930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289930 prefixEnd_3289930 := by exact prefixLift 3289930
  have htrace : WordTrace (prefixWord ++ tailWord_3289930) baseStart_3289930 baseEnd_3289930 := by
    simpa [prefixWord, tailWord_3289930, baseEnd_3289930] using wordTrace_append hprefix tailTrace_3289930
  have hstable : (prefixWord ++ tailWord_3289930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289930).length < 2 ^ (prefixWord ++ tailWord_3289930).sum := by decide
  have hdescent : baseEnd_3289930 < baseStart_3289930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289974 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3289974 : Nat := 118140960795 + 3289974 * 2 ^ 59
def prefixEnd_3289974 : Nat := 4983230072969 + 3 ^ 40 * 3289974 * 2
def baseEnd_3289974 : Nat := 1689338002795216195294691

theorem tailTrace_3289974 : CollatzResearch.WordTrace tailWord_3289974 prefixEnd_3289974 1689338002795216195294691 := by
  unfold tailWord_3289974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7499700611437097229408311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79996806521995703780355317 7499700611437097229408311)
  ·
    refine ⟨11249550917155645844112467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7499700611437097229408311 11249550917155645844112467)
    ·
      refine ⟨16874326375733468766168701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11249550917155645844112467 16874326375733468766168701)
      ·
        refine ⟨6327872390900050787313263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16874326375733468766168701 6327872390900050787313263)
        ·
          refine ⟨9491808586350076180969895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6327872390900050787313263 9491808586350076180969895)
          ·
            refine ⟨14237712879525114271454843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9491808586350076180969895 14237712879525114271454843)
            ·
              refine ⟨21356569319287671407182265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14237712879525114271454843 21356569319287671407182265)
              ·
                refine ⟨16017426989465753555386699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21356569319287671407182265 16017426989465753555386699)
                ·
                  refine ⟨24026140484198630333080049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16017426989465753555386699 24026140484198630333080049)
                  ·
                    refine ⟨18019605363148972749810037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24026140484198630333080049 18019605363148972749810037)
                    ·
                      refine ⟨1689338002795216195294691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18019605363148972749810037 1689338002795216195294691)
                      ·
                        rfl

theorem cell23_3289974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3289974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3289974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3289974 prefixEnd_3289974 := by exact prefixLift 3289974
  have htrace : WordTrace (prefixWord ++ tailWord_3289974) baseStart_3289974 baseEnd_3289974 := by
    simpa [prefixWord, tailWord_3289974, baseEnd_3289974] using wordTrace_append hprefix tailTrace_3289974
  have hstable : (prefixWord ++ tailWord_3289974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289974).length < 2 ^ (prefixWord ++ tailWord_3289974).sum := by decide
  have hdescent : baseEnd_3289974 < baseStart_3289974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290000 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 9]
def baseStart_3290000 : Nat := 118140960795 + 3290000 * 2 ^ 59
def prefixEnd_3290000 : Nat := 4983230072969 + 3 ^ 40 * 3290000 * 2
def baseEnd_3290000 : Nat := 1689351353292233093569571

theorem tailTrace_3290000 : CollatzResearch.WordTrace tailWord_3290000 prefixEnd_3290000 1689351353292233093569571 := by
  unfold tailWord_3290000
  simp only [CollatzResearch.WordTrace]
  refine ⟨59998079040449681055489727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79997438720599574740652969 59998079040449681055489727)
  ·
    refine ⟨89997118560674521583234591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59998079040449681055489727 89997118560674521583234591)
    ·
      refine ⟨134995677841011782374851887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89997118560674521583234591 134995677841011782374851887)
      ·
        refine ⟨202493516761517673562277831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134995677841011782374851887 202493516761517673562277831)
        ·
          refine ⟨303740275142276510343416747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202493516761517673562277831 303740275142276510343416747)
          ·
            refine ⟨455610412713414765515125121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303740275142276510343416747 455610412713414765515125121)
            ·
              refine ⟨341707809535061074136343841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455610412713414765515125121 341707809535061074136343841)
              ·
                refine ⟨256280857151295805602257881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 341707809535061074136343841 256280857151295805602257881)
                ·
                  refine ⟨192210642863471854201693411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256280857151295805602257881 192210642863471854201693411)
                  ·
                    refine ⟨288315964295207781302540117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 192210642863471854201693411 288315964295207781302540117)
                    ·
                      refine ⟨1689351353292233093569571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 288315964295207781302540117 1689351353292233093569571)
                      ·
                        rfl

theorem cell23_3290000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_3290000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290000 prefixEnd_3290000 := by exact prefixLift 3290000
  have htrace : WordTrace (prefixWord ++ tailWord_3290000) baseStart_3290000 baseEnd_3290000 := by
    simpa [prefixWord, tailWord_3290000, baseEnd_3290000] using wordTrace_append hprefix tailTrace_3290000
  have hstable : (prefixWord ++ tailWord_3290000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290000).length < 2 ^ (prefixWord ++ tailWord_3290000).sum := by decide
  have hdescent : baseEnd_3290000 < baseStart_3290000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290004 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_3290004 : Nat := 118140960795 + 3290004 * 2 ^ 59
def prefixEnd_3290004 : Nat := 4983230072969 + 3 ^ 40 * 3290004 * 2
def baseEnd_3290004 : Nat := 1689353407214851077919553

theorem tailTrace_3290004 : CollatzResearch.WordTrace tailWord_3290004 prefixEnd_3290004 1689353407214851077919553 := by
  unfold tailWord_3290004
  simp only [CollatzResearch.WordTrace]
  refine ⟨59998151986442435397062533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79997535981923247196083377 59998151986442435397062533)
  ·
    refine ⟨11249653497457956636949225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59998151986442435397062533 11249653497457956636949225)
    ·
      refine ⟨8437240123093467477711919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11249653497457956636949225 8437240123093467477711919)
      ·
        refine ⟨12655860184640201216567879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8437240123093467477711919 12655860184640201216567879)
        ·
          refine ⟨18983790276960301824851819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12655860184640201216567879 18983790276960301824851819)
          ·
            refine ⟨28475685415440452737277729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18983790276960301824851819 28475685415440452737277729)
            ·
              refine ⟨21356764061580339552958297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28475685415440452737277729 21356764061580339552958297)
              ·
                refine ⟨16017573046185254664718723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21356764061580339552958297 16017573046185254664718723)
                ·
                  refine ⟨24026359569277881997078085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16017573046185254664718723 24026359569277881997078085)
                  ·
                    refine ⟨4504942419239602874452141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24026359569277881997078085 4504942419239602874452141)
                    ·
                      refine ⟨1689353407214851077919553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4504942419239602874452141 1689353407214851077919553)
                      ·
                        rfl

theorem cell23_3290004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_3290004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290004 prefixEnd_3290004 := by exact prefixLift 3290004
  have htrace : WordTrace (prefixWord ++ tailWord_3290004) baseStart_3290004 baseEnd_3290004 := by
    simpa [prefixWord, tailWord_3290004, baseEnd_3290004] using wordTrace_append hprefix tailTrace_3290004
  have hstable : (prefixWord ++ tailWord_3290004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290004).length < 2 ^ (prefixWord ++ tailWord_3290004).sum := by decide
  have hdescent : baseEnd_3290004 < baseStart_3290004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290007 : List Nat := [1, 1, 3, 3, 1, 2, 1, 5, 6]
def baseStart_3290007 : Nat := 118140960795 + 3290007 * 2 ^ 59
def prefixEnd_3290007 : Nat := 4983230072969 + 3 ^ 40 * 3290007 * 2
def baseEnd_3290007 : Nat := 187706105295201618464671

theorem tailTrace_3290007 : CollatzResearch.WordTrace tailWord_3290007 prefixEnd_3290007 187706105295201618464671 := by
  unfold tailWord_3290007
  simp only [CollatzResearch.WordTrace]
  refine ⟨119996413391874002306484275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79997608927916001537656183 119996413391874002306484275)
  ·
    refine ⟨179994620087811003459726413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119996413391874002306484275 179994620087811003459726413)
    ·
      refine ⟨67497982532929126297397405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179994620087811003459726413 67497982532929126297397405)
      ·
        refine ⟨25311743449848422361524027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67497982532929126297397405 25311743449848422361524027)
        ·
          refine ⟨37967615174772633542286041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25311743449848422361524027 37967615174772633542286041)
          ·
            refine ⟨28475711381079475156714531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37967615174772633542286041 28475711381079475156714531)
            ·
              refine ⟨42713567071619212735071797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28475711381079475156714531 42713567071619212735071797)
              ·
                refine ⟨4004396912964301193912981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42713567071619212735071797 4004396912964301193912981)
                ·
                  refine ⟨187706105295201618464671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4004396912964301193912981 187706105295201618464671)
                  ·
                    rfl

theorem cell23_3290007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 6].length) (baseStart_3290007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290007 prefixEnd_3290007 := by exact prefixLift 3290007
  have htrace : WordTrace (prefixWord ++ tailWord_3290007) baseStart_3290007 baseEnd_3290007 := by
    simpa [prefixWord, tailWord_3290007, baseEnd_3290007] using wordTrace_append hprefix tailTrace_3290007
  have hstable : (prefixWord ++ tailWord_3290007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290007).length < 2 ^ (prefixWord ++ tailWord_3290007).sum := by decide
  have hdescent : baseEnd_3290007 < baseStart_3290007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290097 : List Nat := [1, 2, 2, 2, 4, 1, 11]
def baseStart_3290097 : Nat := 118140960795 + 3290097 * 2 ^ 59
def prefixEnd_3290097 : Nat := 4983230072969 + 3 ^ 40 * 3290097 * 2
def baseEnd_3290097 : Nat := 20856804455749619926625

theorem tailTrace_3290097 : CollatzResearch.WordTrace tailWord_3290097 prefixEnd_3290097 20856804455749619926625 := by
  unfold tailWord_3290097
  simp only [CollatzResearch.WordTrace]
  refine ⟨119999695961547947677260545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79999797307698631784840363 119999695961547947677260545)
  ·
    refine ⟨89999771971160960757945409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119999695961547947677260545 89999771971160960757945409)
    ·
      refine ⟨67499828978370720568459057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89999771971160960757945409 67499828978370720568459057)
      ·
        refine ⟨50624871733778040426344293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67499828978370720568459057 50624871733778040426344293)
        ·
          refine ⟨9492163450083382579939555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50624871733778040426344293 9492163450083382579939555)
          ·
            refine ⟨14238245175125073869909333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9492163450083382579939555 14238245175125073869909333)
            ·
              refine ⟨20856804455749619926625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14238245175125073869909333 20856804455749619926625)
              ·
                rfl

theorem cell23_3290097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 11].length) (baseStart_3290097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290097 prefixEnd_3290097 := by exact prefixLift 3290097
  have htrace : WordTrace (prefixWord ++ tailWord_3290097) baseStart_3290097 baseEnd_3290097 := by
    simpa [prefixWord, tailWord_3290097, baseEnd_3290097] using wordTrace_append hprefix tailTrace_3290097
  have hstable : (prefixWord ++ tailWord_3290097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290097).length < 2 ^ (prefixWord ++ tailWord_3290097).sum := by decide
  have hdescent : baseEnd_3290097 < baseStart_3290097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290102 : List Nat := [5, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3]
def baseStart_3290102 : Nat := 118140960795 + 3290102 * 2 ^ 59
def prefixEnd_3290102 : Nat := 4983230072969 + 3 ^ 40 * 3290102 * 2
def baseEnd_3290102 : Nat := 1689403728318991694494103

theorem tailTrace_3290102 : CollatzResearch.WordTrace tailWord_3290102 prefixEnd_3290102 1689403728318991694494103 := by
  unfold tailWord_3290102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7499992395408114595699535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79999918884353222354128373 7499992395408114595699535)
  ·
    refine ⟨11249988593112171893549303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7499992395408114595699535 11249988593112171893549303)
    ·
      refine ⟨16874982889668257840323955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11249988593112171893549303 16874982889668257840323955)
      ·
        refine ⟨25312474334502386760485933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16874982889668257840323955 25312474334502386760485933)
        ·
          refine ⟨9492177875438395035182225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25312474334502386760485933 9492177875438395035182225)
          ·
            refine ⟨7119133406578796276386669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9492177875438395035182225 7119133406578796276386669)
            ·
              refine ⟨2669675027467048603645001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7119133406578796276386669 2669675027467048603645001)
              ·
                refine ⟨2002256270600286452733751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2669675027467048603645001 2002256270600286452733751)
                ·
                  refine ⟨3003384405900429679100627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2002256270600286452733751 3003384405900429679100627)
                  ·
                    refine ⟨4505076608850644518650941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3003384405900429679100627 4505076608850644518650941)
                    ·
                      refine ⟨1689403728318991694494103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4505076608850644518650941 1689403728318991694494103)
                      ·
                        rfl

theorem cell23_3290102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_3290102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290102 prefixEnd_3290102 := by exact prefixLift 3290102
  have htrace : WordTrace (prefixWord ++ tailWord_3290102) baseStart_3290102 baseEnd_3290102 := by
    simpa [prefixWord, tailWord_3290102, baseEnd_3290102] using wordTrace_append hprefix tailTrace_3290102
  have hstable : (prefixWord ++ tailWord_3290102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290102).length < 2 ^ (prefixWord ++ tailWord_3290102).sum := by decide
  have hdescent : baseEnd_3290102 < baseStart_3290102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290108 : List Nat := [2, 2, 2, 1, 2, 3, 3, 1, 3, 2, 2]
def baseStart_3290108 : Nat := 118140960795 + 3290108 * 2 ^ 59
def prefixEnd_3290108 : Nat := 4983230072969 + 3 ^ 40 * 3290108 * 2
def baseEnd_3290108 : Nat := 1689406809202918671019075

theorem tailTrace_3290108 : CollatzResearch.WordTrace tailWord_3290108 prefixEnd_3290108 1689406809202918671019075 := by
  unfold tailWord_3290108
  simp only [CollatzResearch.WordTrace]
  refine ⟨60000048582254048277955489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80000064776338731037273985 60000048582254048277955489)
  ·
    refine ⟨45000036436690536208466617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60000048582254048277955489 45000036436690536208466617)
    ·
      refine ⟨33750027327517902156349963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45000036436690536208466617 33750027327517902156349963)
      ·
        refine ⟨50625040991276853234524945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33750027327517902156349963 50625040991276853234524945)
        ·
          refine ⟨37968780743457639925893709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50625040991276853234524945 37968780743457639925893709)
          ·
            refine ⟨14238292778796614972210141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37968780743457639925893709 14238292778796614972210141)
            ·
              refine ⟨5339359792048730614578803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14238292778796614972210141 5339359792048730614578803)
              ·
                refine ⟨8009039688073095921868205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5339359792048730614578803 8009039688073095921868205)
                ·
                  refine ⟨3003389883027410970700577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8009039688073095921868205 3003389883027410970700577)
                  ·
                    refine ⟨2252542412270558228025433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3003389883027410970700577 2252542412270558228025433)
                    ·
                      refine ⟨1689406809202918671019075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2252542412270558228025433 1689406809202918671019075)
                      ·
                        rfl

theorem cell23_3290108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_3290108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290108 prefixEnd_3290108 := by exact prefixLift 3290108
  have htrace : WordTrace (prefixWord ++ tailWord_3290108) baseStart_3290108 baseEnd_3290108 := by
    simpa [prefixWord, tailWord_3290108, baseEnd_3290108] using wordTrace_append hprefix tailTrace_3290108
  have hstable : (prefixWord ++ tailWord_3290108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290108).length < 2 ^ (prefixWord ++ tailWord_3290108).sum := by decide
  have hdescent : baseEnd_3290108 < baseStart_3290108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290117 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 2, 2, 6]
def baseStart_3290117 : Nat := 118140960795 + 3290117 * 2 ^ 59
def prefixEnd_3290117 : Nat := 4983230072969 + 3 ^ 40 * 3290117 * 2
def baseEnd_3290117 : Nat := 1689411430528809135806533

theorem tailTrace_3290117 : CollatzResearch.WordTrace tailWord_3290117 prefixEnd_3290117 1689411430528809135806533 := by
  unfold tailWord_3290117
  simp only [CollatzResearch.WordTrace]
  refine ⟨120000425421475491092988605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80000283614316994061992403 120000425421475491092988605)
  ·
    refine ⟨45000159533053309159870727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120000425421475491092988605 45000159533053309159870727)
    ·
      refine ⟨67500239299579963739806091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45000159533053309159870727 67500239299579963739806091)
      ·
        refine ⟨101250358949369945609709137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67500239299579963739806091 101250358949369945609709137)
        ·
          refine ⟨75937769212027459207281853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101250358949369945609709137 75937769212027459207281853)
          ·
            refine ⟨28476663454510297202730695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75937769212027459207281853 28476663454510297202730695)
            ·
              refine ⟨42714995181765445804096043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28476663454510297202730695 42714995181765445804096043)
              ·
                refine ⟨64072492772648168706144065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42714995181765445804096043 64072492772648168706144065)
                ·
                  refine ⟨48054369579486126529608049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64072492772648168706144065 48054369579486126529608049)
                  ·
                    refine ⟨36040777184614594897206037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48054369579486126529608049 36040777184614594897206037)
                    ·
                      refine ⟨1689411430528809135806533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36040777184614594897206037 1689411430528809135806533)
                      ·
                        rfl

theorem cell23_3290117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_3290117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290117 prefixEnd_3290117 := by exact prefixLift 3290117
  have htrace : WordTrace (prefixWord ++ tailWord_3290117) baseStart_3290117 baseEnd_3290117 := by
    simpa [prefixWord, tailWord_3290117, baseEnd_3290117] using wordTrace_append hprefix tailTrace_3290117
  have hstable : (prefixWord ++ tailWord_3290117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290117).length < 2 ^ (prefixWord ++ tailWord_3290117).sum := by decide
  have hdescent : baseEnd_3290117 < baseStart_3290117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290137 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 1, 4, 5]
def baseStart_3290137 : Nat := 118140960795 + 3290137 * 2 ^ 59
def prefixEnd_3290137 : Nat := 4983230072969 + 3 ^ 40 * 3290137 * 2
def baseEnd_3290137 : Nat := 1689421700141899057556441

theorem tailTrace_3290137 : CollatzResearch.WordTrace tailWord_3290137 prefixEnd_3290137 1689421700141899057556441 := by
  unfold tailWord_3290137
  simp only [CollatzResearch.WordTrace]
  refine ⟨120001154881403034508716665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80000769920935356339144443 120001154881403034508716665)
  ·
    refine ⟨90000866161052275881537499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120001154881403034508716665 90000866161052275881537499)
    ·
      refine ⟨135001299241578413822306249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90000866161052275881537499 135001299241578413822306249)
      ·
        refine ⟨101250974431183810366729687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135001299241578413822306249 101250974431183810366729687)
        ·
          refine ⟨151876461646775715550094531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101250974431183810366729687 151876461646775715550094531)
          ·
            refine ⟨227814692470163573325141797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151876461646775715550094531 227814692470163573325141797)
            ·
              refine ⟨42715254838155669998464087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 227814692470163573325141797 42715254838155669998464087)
              ·
                refine ⟨64072882257233504997696131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42715254838155669998464087 64072882257233504997696131)
                ·
                  refine ⟨96109323385850257496544197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64072882257233504997696131 96109323385850257496544197)
                  ·
                    refine ⟨18020498134846923280602037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96109323385850257496544197 18020498134846923280602037)
                    ·
                      refine ⟨1689421700141899057556441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18020498134846923280602037 1689421700141899057556441)
                      ·
                        rfl

theorem cell23_3290137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_3290137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290137 prefixEnd_3290137 := by exact prefixLift 3290137
  have htrace : WordTrace (prefixWord ++ tailWord_3290137) baseStart_3290137 baseEnd_3290137 := by
    simpa [prefixWord, tailWord_3290137, baseEnd_3290137] using wordTrace_append hprefix tailTrace_3290137
  have hstable : (prefixWord ++ tailWord_3290137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290137).length < 2 ^ (prefixWord ++ tailWord_3290137).sum := by decide
  have hdescent : baseEnd_3290137 < baseStart_3290137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290181 : List Nat := [1, 3, 1, 1, 1, 3, 3, 3, 1, 4, 2]
def baseStart_3290181 : Nat := 118140960795 + 3290181 * 2 ^ 59
def prefixEnd_3290181 : Nat := 4983230072969 + 3 ^ 40 * 3290181 * 2
def baseEnd_3290181 : Nat := 1689444293290696885406239

theorem tailTrace_3290181 : CollatzResearch.WordTrace tailWord_3290181 prefixEnd_3290181 1689444293290696885406239 := by
  unfold tailWord_3290181
  simp only [CollatzResearch.WordTrace]
  refine ⟨120002759693243630023318397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80001839795495753348878931 120002759693243630023318397)
  ·
    refine ⟨45001034884966361258744399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120002759693243630023318397 45001034884966361258744399)
    ·
      refine ⟨67501552327449541888116599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45001034884966361258744399 67501552327449541888116599)
      ·
        refine ⟨101252328491174312832174899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67501552327449541888116599 101252328491174312832174899)
        ·
          refine ⟨151878492736761469248262349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101252328491174312832174899 151878492736761469248262349)
          ·
            refine ⟨56954434776285550968098381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151878492736761469248262349 56954434776285550968098381)
            ·
              refine ⟨21357913041107081613036893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56954434776285550968098381 21357913041107081613036893)
              ·
                refine ⟨8009217390415155604888835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21357913041107081613036893 8009217390415155604888835)
                ·
                  refine ⟨12013826085622733407333253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8009217390415155604888835 12013826085622733407333253)
                  ·
                    refine ⟨2252592391054262513874985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12013826085622733407333253 2252592391054262513874985)
                    ·
                      refine ⟨1689444293290696885406239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2252592391054262513874985 1689444293290696885406239)
                      ·
                        rfl

theorem cell23_3290181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 4, 2].length) (baseStart_3290181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290181 prefixEnd_3290181 := by exact prefixLift 3290181
  have htrace : WordTrace (prefixWord ++ tailWord_3290181) baseStart_3290181 baseEnd_3290181 := by
    simpa [prefixWord, tailWord_3290181, baseEnd_3290181] using wordTrace_append hprefix tailTrace_3290181
  have hstable : (prefixWord ++ tailWord_3290181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290181).length < 2 ^ (prefixWord ++ tailWord_3290181).sum := by decide
  have hdescent : baseEnd_3290181 < baseStart_3290181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290184 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 2, 4, 3]
def baseStart_3290184 : Nat := 118140960795 + 3290184 * 2 ^ 59
def prefixEnd_3290184 : Nat := 4983230072969 + 3 ^ 40 * 3290184 * 2
def baseEnd_3290184 : Nat := 1689445833732660373668725

theorem tailTrace_3290184 : CollatzResearch.WordTrace tailWord_3290184 prefixEnd_3290184 1689445833732660373668725 := by
  unfold tailWord_3290184
  simp only [CollatzResearch.WordTrace]
  refine ⟨60001434556116380767838803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80001912741488507690451737 60001434556116380767838803)
  ·
    refine ⟨90002151834174571151758205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60001434556116380767838803 90002151834174571151758205)
    ·
      refine ⟨33750806937815464181909327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90002151834174571151758205 33750806937815464181909327)
      ·
        refine ⟨50626210406723196272863991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33750806937815464181909327 50626210406723196272863991)
        ·
          refine ⟨75939315610084794409295987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50626210406723196272863991 75939315610084794409295987)
          ·
            refine ⟨113908973415127191613943981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75939315610084794409295987 113908973415127191613943981)
            ·
              refine ⟨42715865030672696855228993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113908973415127191613943981 42715865030672696855228993)
              ·
                refine ⟨32036898773004522641421745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42715865030672696855228993 32036898773004522641421745)
                ·
                  refine ⟨24027674079753391981066309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32036898773004522641421745 24027674079753391981066309)
                  ·
                    refine ⟨4505188889953760996449933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24027674079753391981066309 4505188889953760996449933)
                    ·
                      refine ⟨1689445833732660373668725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4505188889953760996449933 1689445833732660373668725)
                      ·
                        rfl

theorem cell23_3290184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_3290184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290184 prefixEnd_3290184 := by exact prefixLift 3290184
  have htrace : WordTrace (prefixWord ++ tailWord_3290184) baseStart_3290184 baseEnd_3290184 := by
    simpa [prefixWord, tailWord_3290184, baseEnd_3290184] using wordTrace_append hprefix tailTrace_3290184
  have hstable : (prefixWord ++ tailWord_3290184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290184).length < 2 ^ (prefixWord ++ tailWord_3290184).sum := by decide
  have hdescent : baseEnd_3290184 < baseStart_3290184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290204 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 9]
def baseStart_3290204 : Nat := 118140960795 + 3290204 * 2 ^ 59
def prefixEnd_3290204 : Nat := 4983230072969 + 3 ^ 40 * 3290204 * 2
def baseEnd_3290204 : Nat := 187717344816194477268737

theorem tailTrace_3290204 : CollatzResearch.WordTrace tailWord_3290204 prefixEnd_3290204 187717344816194477268737 := by
  unfold tailWord_3290204
  simp only [CollatzResearch.WordTrace]
  refine ⟨60001799286080152475702833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80002399048106869967603777 60001799286080152475702833)
  ·
    refine ⟨45001349464560114356777125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60001799286080152475702833 45001349464560114356777125)
    ·
      refine ⟨8437753024605021441895711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45001349464560114356777125 8437753024605021441895711)
      ·
        refine ⟨12656629536907532162843567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8437753024605021441895711 12656629536907532162843567)
        ·
          refine ⟨18984944305361298244265351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12656629536907532162843567 18984944305361298244265351)
          ·
            refine ⟨28477416458041947366398027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18984944305361298244265351 28477416458041947366398027)
            ·
              refine ⟨42716124687062921049597041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28477416458041947366398027 42716124687062921049597041)
              ·
                refine ⟨32037093515297190787197781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42716124687062921049597041 32037093515297190787197781)
                ·
                  refine ⟨187717344816194477268737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32037093515297190787197781 187717344816194477268737)
                  ·
                    rfl

theorem cell23_3290204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 9].length) (baseStart_3290204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290204 prefixEnd_3290204 := by exact prefixLift 3290204
  have htrace : WordTrace (prefixWord ++ tailWord_3290204) baseStart_3290204 baseEnd_3290204 := by
    simpa [prefixWord, tailWord_3290204, baseEnd_3290204] using wordTrace_append hprefix tailTrace_3290204
  have hstable : (prefixWord ++ tailWord_3290204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290204).length < 2 ^ (prefixWord ++ tailWord_3290204).sum := by decide
  have hdescent : baseEnd_3290204 < baseStart_3290204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290215 : List Nat := [1, 1, 5, 1, 1, 3, 3, 2, 2, 2, 2]
def baseStart_3290215 : Nat := 118140960795 + 3290215 * 2 ^ 59
def prefixEnd_3290215 : Nat := 4983230072969 + 3 ^ 40 * 3290215 * 2
def baseEnd_3290215 : Nat := 1689461751632949752381083

theorem tailTrace_3290215 : CollatzResearch.WordTrace tailWord_3290215 prefixEnd_3290215 1689461751632949752381083 := by
  unfold tailWord_3290215
  simp only [CollatzResearch.WordTrace]
  refine ⟨120003999775120453830056099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80002666516746969220037399 120003999775120453830056099)
  ·
    refine ⟨180005999662680680745084149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120003999775120453830056099 180005999662680680745084149)
    ·
      refine ⟨16875562468376313819851639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180005999662680680745084149 16875562468376313819851639)
      ·
        refine ⟨25313343702564470729777459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16875562468376313819851639 25313343702564470729777459)
        ·
          refine ⟨37970015553846706094666189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25313343702564470729777459 37970015553846706094666189)
          ·
            refine ⟨14238755832692514785499821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37970015553846706094666189 14238755832692514785499821)
            ·
              refine ⟨5339533437259693044562433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14238755832692514785499821 5339533437259693044562433)
              ·
                refine ⟨4004650077944769783421825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5339533437259693044562433 4004650077944769783421825)
                ·
                  refine ⟨3003487558458577337566369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4004650077944769783421825 3003487558458577337566369)
                  ·
                    refine ⟨2252615668843933003174777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3003487558458577337566369 2252615668843933003174777)
                    ·
                      refine ⟨1689461751632949752381083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2252615668843933003174777 1689461751632949752381083)
                      ·
                        rfl

theorem cell23_3290215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_3290215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290215 prefixEnd_3290215 := by exact prefixLift 3290215
  have htrace : WordTrace (prefixWord ++ tailWord_3290215) baseStart_3290215 baseEnd_3290215 := by
    simpa [prefixWord, tailWord_3290215, baseEnd_3290215] using wordTrace_append hprefix tailTrace_3290215
  have hstable : (prefixWord ++ tailWord_3290215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290215).length < 2 ^ (prefixWord ++ tailWord_3290215).sum := by decide
  have hdescent : baseEnd_3290215 < baseStart_3290215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290221 : List Nat := [1, 5, 1, 1, 2, 3, 2, 1, 7]
def baseStart_3290221 : Nat := 118140960795 + 3290221 * 2 ^ 59
def prefixEnd_3290221 : Nat := 4983230072969 + 3 ^ 40 * 3290221 * 2
def baseEnd_3290221 : Nat := 187718314724097414322895

theorem tailTrace_3290221 : CollatzResearch.WordTrace tailWord_3290221 prefixEnd_3290221 187718314724097414322895 := by
  unfold tailWord_3290221
  simp only [CollatzResearch.WordTrace]
  refine ⟨120004218613098716854774517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80002812408732477903183011 120004218613098716854774517)
  ·
    refine ⟨11250395494978004705135111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120004218613098716854774517 11250395494978004705135111)
    ·
      refine ⟨16875593242467007057702667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11250395494978004705135111 16875593242467007057702667)
      ·
        refine ⟨25313389863700510586554001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16875593242467007057702667 25313389863700510586554001)
        ·
          refine ⟨18985042397775382939915501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25313389863700510586554001 18985042397775382939915501)
          ·
            refine ⟨7119390899165768602468313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18985042397775382939915501 7119390899165768602468313)
            ·
              refine ⟨5339543174374326451851235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7119390899165768602468313 5339543174374326451851235)
              ·
                refine ⟨8009314761561489677776853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5339543174374326451851235 8009314761561489677776853)
                ·
                  refine ⟨187718314724097414322895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8009314761561489677776853 187718314724097414322895)
                  ·
                    rfl

theorem cell23_3290221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_3290221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290221 prefixEnd_3290221 := by exact prefixLift 3290221
  have htrace : WordTrace (prefixWord ++ tailWord_3290221) baseStart_3290221 baseEnd_3290221 := by
    simpa [prefixWord, tailWord_3290221, baseEnd_3290221] using wordTrace_append hprefix tailTrace_3290221
  have hstable : (prefixWord ++ tailWord_3290221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290221).length < 2 ^ (prefixWord ++ tailWord_3290221).sum := by decide
  have hdescent : baseEnd_3290221 < baseStart_3290221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290284 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 4]
def baseStart_3290284 : Nat := 118140960795 + 3290284 * 2 ^ 59
def prefixEnd_3290284 : Nat := 4983230072969 + 3 ^ 40 * 3290284 * 2
def baseEnd_3290284 : Nat := 1689497181798109982418265

theorem tailTrace_3290284 : CollatzResearch.WordTrace tailWord_3290284 prefixEnd_3290284 1689497181798109982418265 := by
  unfold tailWord_3290284
  simp only [CollatzResearch.WordTrace]
  refine ⟨60003258205935239307158953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80004344274580319076211937 60003258205935239307158953)
  ·
    refine ⟨45002443654451429480369215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60003258205935239307158953 45002443654451429480369215)
    ·
      refine ⟨67503665481677144220553823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45002443654451429480369215 67503665481677144220553823)
      ·
        refine ⟨101255498222515716330830735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67503665481677144220553823 101255498222515716330830735)
        ·
          refine ⟨151883247333773574496246103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101255498222515716330830735 151883247333773574496246103)
          ·
            refine ⟨227824871000660361744369155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151883247333773574496246103 227824871000660361744369155)
            ·
              refine ⟨341737306500990542616553733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227824871000660361744369155 341737306500990542616553733)
              ·
                refine ⟨64075744968935726740603825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 341737306500990542616553733 64075744968935726740603825)
                ·
                  refine ⟨48056808726701795055452869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64075744968935726740603825 48056808726701795055452869)
                  ·
                    refine ⟨9010651636256586572897413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48056808726701795055452869 9010651636256586572897413)
                    ·
                      refine ⟨1689497181798109982418265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9010651636256586572897413 1689497181798109982418265)
                      ·
                        rfl

theorem cell23_3290284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_3290284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290284 prefixEnd_3290284 := by exact prefixLift 3290284
  have htrace : WordTrace (prefixWord ++ tailWord_3290284) baseStart_3290284 baseEnd_3290284 := by
    simpa [prefixWord, tailWord_3290284, baseEnd_3290284] using wordTrace_append hprefix tailTrace_3290284
  have hstable : (prefixWord ++ tailWord_3290284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290284).length < 2 ^ (prefixWord ++ tailWord_3290284).sum := by decide
  have hdescent : baseEnd_3290284 < baseStart_3290284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290305 : List Nat := [1, 2, 6, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3290305 : Nat := 118140960795 + 3290305 * 2 ^ 59
def prefixEnd_3290305 : Nat := 4983230072969 + 3 ^ 40 * 3290305 * 2
def baseEnd_3290305 : Nat := 1689507964891854400255669

theorem tailTrace_3290305 : CollatzResearch.WordTrace tailWord_3290305 prefixEnd_3290305 1689507964891854400255669 := by
  unfold tailWord_3290305
  simp only [CollatzResearch.WordTrace]
  refine ⟨120007282344794399200832369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80004854896529599467221579 120007282344794399200832369)
  ·
    refine ⟨90005461758595799400624277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120007282344794399200832369 90005461758595799400624277)
    ·
      refine ⟨4219006019934178096904263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90005461758595799400624277 4219006019934178096904263)
      ·
        refine ⟨6328509029901267145356395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4219006019934178096904263 6328509029901267145356395)
        ·
          refine ⟨9492763544851900718034593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6328509029901267145356395 9492763544851900718034593)
          ·
            refine ⟨7119572658638925538525945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9492763544851900718034593 7119572658638925538525945)
            ·
              refine ⟨5339679493979194153894459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7119572658638925538525945 5339679493979194153894459)
              ·
                refine ⟨8009519240968791230841689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5339679493979194153894459 8009519240968791230841689)
                ·
                  refine ⟨6007139430726593423131267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8009519240968791230841689 6007139430726593423131267)
                  ·
                    refine ⟨9010709146089890134696901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6007139430726593423131267 9010709146089890134696901)
                    ·
                      refine ⟨1689507964891854400255669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9010709146089890134696901 1689507964891854400255669)
                      ·
                        rfl

theorem cell23_3290305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3290305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290305 prefixEnd_3290305 := by exact prefixLift 3290305
  have htrace : WordTrace (prefixWord ++ tailWord_3290305) baseStart_3290305 baseEnd_3290305 := by
    simpa [prefixWord, tailWord_3290305, baseEnd_3290305] using wordTrace_append hprefix tailTrace_3290305
  have hstable : (prefixWord ++ tailWord_3290305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290305).length < 2 ^ (prefixWord ++ tailWord_3290305).sum := by decide
  have hdescent : baseEnd_3290305 < baseStart_3290305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290328 : List Nat := [2, 1, 2, 2, 5, 1, 2, 2, 6]
def baseStart_3290328 : Nat := 118140960795 + 3290328 * 2 ^ 59
def prefixEnd_3290328 : Nat := 4983230072969 + 3 ^ 40 * 3290328 * 2
def baseEnd_3290328 : Nat := 187724419438545312252007

theorem tailTrace_3290328 : CollatzResearch.WordTrace tailWord_3290328 prefixEnd_3290328 187724419438545312252007 := by
  unfold tailWord_3290328
  simp only [CollatzResearch.WordTrace]
  refine ⟨60004060611855537064459819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80005414149140716085946425 60004060611855537064459819)
  ·
    refine ⟨90006090917783305596689729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60004060611855537064459819 90006090917783305596689729)
    ·
      refine ⟨67504568188337479197517297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90006090917783305596689729 67504568188337479197517297)
      ·
        refine ⟨50628426141253109398137973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67504568188337479197517297 50628426141253109398137973)
        ·
          refine ⟨4746414950742479006075435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50628426141253109398137973 4746414950742479006075435)
          ·
            refine ⟨7119622426113718509113153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4746414950742479006075435 7119622426113718509113153)
            ·
              refine ⟨5339716819585288881834865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7119622426113718509113153 5339716819585288881834865)
              ·
                refine ⟨4004787614688966661376149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5339716819585288881834865 4004787614688966661376149)
                ·
                  refine ⟨187724419438545312252007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4004787614688966661376149 187724419438545312252007)
                  ·
                    rfl

theorem cell23_3290328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 6].length) (baseStart_3290328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290328 prefixEnd_3290328 := by exact prefixLift 3290328
  have htrace : WordTrace (prefixWord ++ tailWord_3290328) baseStart_3290328 baseEnd_3290328 := by
    simpa [prefixWord, tailWord_3290328, baseEnd_3290328] using wordTrace_append hprefix tailTrace_3290328
  have hstable : (prefixWord ++ tailWord_3290328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290328).length < 2 ^ (prefixWord ++ tailWord_3290328).sum := by decide
  have hdescent : baseEnd_3290328 < baseStart_3290328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290356 : List Nat := [2, 6, 1, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_3290356 : Nat := 118140960795 + 3290356 * 2 ^ 59
def prefixEnd_3290356 : Nat := 4983230072969 + 3 ^ 40 * 3290356 * 2
def baseEnd_3290356 : Nat := 1689534152405233700717935

theorem tailTrace_3290356 : CollatzResearch.WordTrace tailWord_3290356 prefixEnd_3290356 1689534152405233700717935 := by
  unfold tailWord_3290356
  simp only [CollatzResearch.WordTrace]
  refine ⟨60004571233804817455469461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80006094978406423273959281 60004571233804817455469461)
  ·
    refine ⟨2812714276584600818225131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60004571233804817455469461 2812714276584600818225131)
    ·
      refine ⟨4219071414876901227337697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2812714276584600818225131 4219071414876901227337697)
      ·
        refine ⟨3164303561157675920503273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4219071414876901227337697 3164303561157675920503273)
        ·
          refine ⟨2373227670868256940377455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3164303561157675920503273 2373227670868256940377455)
          ·
            refine ⟨3559841506302385410566183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2373227670868256940377455 3559841506302385410566183)
            ·
              refine ⟨5339762259453578115849275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3559841506302385410566183 5339762259453578115849275)
              ·
                refine ⟨8009643389180367173773913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5339762259453578115849275 8009643389180367173773913)
                ·
                  refine ⟨6007232541885275380330435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8009643389180367173773913 6007232541885275380330435)
                  ·
                    refine ⟨9010848812827913070495653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6007232541885275380330435 9010848812827913070495653)
                    ·
                      refine ⟨1689534152405233700717935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9010848812827913070495653 1689534152405233700717935)
                      ·
                        rfl

theorem cell23_3290356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_3290356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290356 prefixEnd_3290356 := by exact prefixLift 3290356
  have htrace : WordTrace (prefixWord ++ tailWord_3290356) baseStart_3290356 baseEnd_3290356 := by
    simpa [prefixWord, tailWord_3290356, baseEnd_3290356] using wordTrace_append hprefix tailTrace_3290356
  have hstable : (prefixWord ++ tailWord_3290356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290356).length < 2 ^ (prefixWord ++ tailWord_3290356).sum := by decide
  have hdescent : baseEnd_3290356 < baseStart_3290356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290358 : List Nat := [5, 1, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_3290358 : Nat := 118140960795 + 3290358 * 2 ^ 59
def prefixEnd_3290358 : Nat := 4983230072969 + 3 ^ 40 * 3290358 * 2
def baseEnd_3290358 : Nat := 563178393122180897630975

theorem tailTrace_3290358 : CollatzResearch.WordTrace tailWord_3290358 prefixEnd_3290358 563178393122180897630975 := by
  unfold tailWord_3290358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7500575963350149328281983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80006143609068259501674485 7500575963350149328281983)
  ·
    refine ⟨11250863945025223992422975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7500575963350149328281983 11250863945025223992422975)
    ·
      refine ⟨16876295917537835988634463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11250863945025223992422975 16876295917537835988634463)
      ·
        refine ⟨25314443876306753982951695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16876295917537835988634463 25314443876306753982951695)
        ·
          refine ⟨37971665814460130974427543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25314443876306753982951695 37971665814460130974427543)
          ·
            refine ⟨56957498721690196461641315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37971665814460130974427543 56957498721690196461641315)
            ·
              refine ⟨85436248082535294692461973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56957498721690196461641315 85436248082535294692461973)
              ·
                refine ⟨4004824128868841938709155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85436248082535294692461973 4004824128868841938709155)
                ·
                  refine ⟨6007236193303262908063733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4004824128868841938709155 6007236193303262908063733)
                  ·
                    refine ⟨563178393122180897630975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6007236193303262908063733 563178393122180897630975)
                    ·
                      rfl

theorem cell23_3290358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_3290358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290358 prefixEnd_3290358 := by exact prefixLift 3290358
  have htrace : WordTrace (prefixWord ++ tailWord_3290358) baseStart_3290358 baseEnd_3290358 := by
    simpa [prefixWord, tailWord_3290358, baseEnd_3290358] using wordTrace_append hprefix tailTrace_3290358
  have hstable : (prefixWord ++ tailWord_3290358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290358).length < 2 ^ (prefixWord ++ tailWord_3290358).sum := by decide
  have hdescent : baseEnd_3290358 < baseStart_3290358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290361 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 3, 1, 4]
def baseStart_3290361 : Nat := 118140960795 + 3290361 * 2 ^ 59
def prefixEnd_3290361 : Nat := 4983230072969 + 3 ^ 40 * 3290361 * 2
def baseEnd_3290361 : Nat := 1689536719808506181155411

theorem tailTrace_3290361 : CollatzResearch.WordTrace tailWord_3290361 prefixEnd_3290361 1689536719808506181155411 := by
  unfold tailWord_3290361
  simp only [CollatzResearch.WordTrace]
  refine ⟨120009324832591520764870937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80006216555061013843247291 120009324832591520764870937)
  ·
    refine ⟨90006993624443640573653203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120009324832591520764870937 90006993624443640573653203)
    ·
      refine ⟨135010490436665460860479805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90006993624443640573653203 135010490436665460860479805)
      ·
        refine ⟨50628933913749547822679927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135010490436665460860479805 50628933913749547822679927)
        ·
          refine ⟨75943400870624321734019891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50628933913749547822679927 75943400870624321734019891)
          ·
            refine ⟨113915101305936482601029837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75943400870624321734019891 113915101305936482601029837)
            ·
              refine ⟨42718162989726180975386189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113915101305936482601029837 42718162989726180975386189)
              ·
                refine ⟨16019311121147317865769821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42718162989726180975386189 16019311121147317865769821)
                ·
                  refine ⟨6007241670430244199663683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16019311121147317865769821 6007241670430244199663683)
                  ·
                    refine ⟨9010862505645366299495525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6007241670430244199663683 9010862505645366299495525)
                    ·
                      refine ⟨1689536719808506181155411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9010862505645366299495525 1689536719808506181155411)
                      ·
                        rfl

theorem cell23_3290361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_3290361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290361 prefixEnd_3290361 := by exact prefixLift 3290361
  have htrace : WordTrace (prefixWord ++ tailWord_3290361) baseStart_3290361 baseEnd_3290361 := by
    simpa [prefixWord, tailWord_3290361, baseEnd_3290361] using wordTrace_append hprefix tailTrace_3290361
  have hstable : (prefixWord ++ tailWord_3290361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290361).length < 2 ^ (prefixWord ++ tailWord_3290361).sum := by decide
  have hdescent : baseEnd_3290361 < baseStart_3290361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290371 : List Nat := [1, 1, 1, 3, 2, 4, 2, 2, 1, 6]
def baseStart_3290371 : Nat := 118140960795 + 3290371 * 2 ^ 59
def prefixEnd_3290371 : Nat := 4983230072969 + 3 ^ 40 * 3290371 * 2
def baseEnd_3290371 : Nat := 563180618205017047343455

theorem tailTrace_3290371 : CollatzResearch.WordTrace tailWord_3290371 prefixEnd_3290371 563180618205017047343455 := by
  unfold tailWord_3290371
  simp only [CollatzResearch.WordTrace]
  refine ⟨120009689562555292472734967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80006459708370194981823311 120009689562555292472734967)
  ·
    refine ⟨180014534343832938709102451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120009689562555292472734967 180014534343832938709102451)
    ·
      refine ⟨270021801515749408063653677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180014534343832938709102451 270021801515749408063653677)
      ·
        refine ⟨101258175568406028023870129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270021801515749408063653677 101258175568406028023870129)
        ·
          refine ⟨75943631676304521017902597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101258175568406028023870129 75943631676304521017902597)
          ·
            refine ⟨14239430939307097690856737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75943631676304521017902597 14239430939307097690856737)
            ·
              refine ⟨10679573204480323268142553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14239430939307097690856737 10679573204480323268142553)
              ·
                refine ⟨8009679903360242451106915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10679573204480323268142553 8009679903360242451106915)
                ·
                  refine ⟨12014519855040363676660373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8009679903360242451106915 12014519855040363676660373)
                  ·
                    refine ⟨563180618205017047343455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12014519855040363676660373 563180618205017047343455)
                    ·
                      rfl

theorem cell23_3290371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 6].length) (baseStart_3290371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290371 prefixEnd_3290371 := by exact prefixLift 3290371
  have htrace : WordTrace (prefixWord ++ tailWord_3290371) baseStart_3290371 baseEnd_3290371 := by
    simpa [prefixWord, tailWord_3290371, baseEnd_3290371] using wordTrace_append hprefix tailTrace_3290371
  have hstable : (prefixWord ++ tailWord_3290371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290371).length < 2 ^ (prefixWord ++ tailWord_3290371).sum := by decide
  have hdescent : baseEnd_3290371 < baseStart_3290371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290372 : List Nat := [2, 3, 2, 2, 2, 1, 1, 5, 1, 1, 3]
def baseStart_3290372 : Nat := 118140960795 + 3290372 * 2 ^ 59
def prefixEnd_3290372 : Nat := 4983230072969 + 3 ^ 40 * 3290372 * 2
def baseEnd_3290372 : Nat := 1689542368095705638117861

theorem tailTrace_3290372 : CollatzResearch.WordTrace tailWord_3290372 prefixEnd_3290372 1689542368095705638117861 := by
  unfold tailWord_3290372
  simp only [CollatzResearch.WordTrace]
  refine ⟨60004863017775834821760685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80006484023701113095680913 60004863017775834821760685)
  ·
    refine ⟨22501823631665938058160257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60004863017775834821760685 22501823631665938058160257)
    ·
      refine ⟨16876367723749453543620193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22501823631665938058160257 16876367723749453543620193)
      ·
        refine ⟨12657275792812090157715145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16876367723749453543620193 12657275792812090157715145)
        ·
          refine ⟨9492956844609067618286359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12657275792812090157715145 9492956844609067618286359)
          ·
            refine ⟨14239435266913601427429539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9492956844609067618286359 14239435266913601427429539)
            ·
              refine ⟨21359152900370402141144309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14239435266913601427429539 21359152900370402141144309)
              ·
                refine ⟨2002420584409725200732279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21359152900370402141144309 2002420584409725200732279)
                ·
                  refine ⟨3003630876614587801098419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2002420584409725200732279 3003630876614587801098419)
                  ·
                    refine ⟨4505446314921881701647629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3003630876614587801098419 4505446314921881701647629)
                    ·
                      refine ⟨1689542368095705638117861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4505446314921881701647629 1689542368095705638117861)
                      ·
                        rfl

theorem cell23_3290372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_3290372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290372 prefixEnd_3290372 := by exact prefixLift 3290372
  have htrace : WordTrace (prefixWord ++ tailWord_3290372) baseStart_3290372 baseEnd_3290372 := by
    simpa [prefixWord, tailWord_3290372, baseEnd_3290372] using wordTrace_append hprefix tailTrace_3290372
  have hstable : (prefixWord ++ tailWord_3290372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290372).length < 2 ^ (prefixWord ++ tailWord_3290372).sum := by decide
  have hdescent : baseEnd_3290372 < baseStart_3290372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290391 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 6]
def baseStart_3290391 : Nat := 118140960795 + 3290391 * 2 ^ 59
def prefixEnd_3290391 : Nat := 4983230072969 + 3 ^ 40 * 3290391 * 2
def baseEnd_3290391 : Nat := 1689552124228141063780273

theorem tailTrace_3290391 : CollatzResearch.WordTrace tailWord_3290391 prefixEnd_3290391 1689552124228141063780273 := by
  unfold tailWord_3290391
  simp only [CollatzResearch.WordTrace]
  refine ⟨120010419022482835888463027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80006946014988557258975351 120010419022482835888463027)
  ·
    refine ⟨180015628533724253832694541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120010419022482835888463027 180015628533724253832694541)
    ·
      refine ⟨67505860700146595187260453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180015628533724253832694541 67505860700146595187260453)
      ·
        refine ⟨12657348881277486597611335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67505860700146595187260453 12657348881277486597611335)
        ·
          refine ⟨18986023321916229896417003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12657348881277486597611335 18986023321916229896417003)
          ·
            refine ⟨28479034982874344844625505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18986023321916229896417003 28479034982874344844625505)
            ·
              refine ⟨21359276237155758633469129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28479034982874344844625505 21359276237155758633469129)
              ·
                refine ⟨16019457177866818975101847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21359276237155758633469129 16019457177866818975101847)
                ·
                  refine ⟨24029185766800228462652771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16019457177866818975101847 24029185766800228462652771)
                  ·
                    refine ⟨36043778650200342693979157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24029185766800228462652771 36043778650200342693979157)
                    ·
                      refine ⟨1689552124228141063780273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36043778650200342693979157 1689552124228141063780273)
                      ·
                        rfl

theorem cell23_3290391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_3290391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290391 prefixEnd_3290391 := by exact prefixLift 3290391
  have htrace : WordTrace (prefixWord ++ tailWord_3290391) baseStart_3290391 baseEnd_3290391 := by
    simpa [prefixWord, tailWord_3290391, baseEnd_3290391] using wordTrace_append hprefix tailTrace_3290391
  have hstable : (prefixWord ++ tailWord_3290391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290391).length < 2 ^ (prefixWord ++ tailWord_3290391).sum := by decide
  have hdescent : baseEnd_3290391 < baseStart_3290391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290408 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_3290408 : Nat := 118140960795 + 3290408 * 2 ^ 59
def prefixEnd_3290408 : Nat := 4983230072969 + 3 ^ 40 * 3290408 * 2
def baseEnd_3290408 : Nat := 1689560853399267497267695

theorem tailTrace_3290408 : CollatzResearch.WordTrace tailWord_3290408 prefixEnd_3290408 1689560853399267497267695 := by
  unfold tailWord_3290408
  simp only [CollatzResearch.WordTrace]
  refine ⟨60005519531710623895915939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80007359375614165194554585 60005519531710623895915939)
  ·
    refine ⟨90008279297565935843873909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60005519531710623895915939 90008279297565935843873909)
    ·
      refine ⟨8438276184146806485363179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90008279297565935843873909 8438276184146806485363179)
      ·
        refine ⟨12657414276220209728044769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8438276184146806485363179 12657414276220209728044769)
        ·
          refine ⟨9493060707165157296033577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12657414276220209728044769 9493060707165157296033577)
          ·
            refine ⟨7119795530373867972025183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9493060707165157296033577 7119795530373867972025183)
            ·
              refine ⟨10679693295560801958037775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7119795530373867972025183 10679693295560801958037775)
              ·
                refine ⟨16019539943341202937056663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10679693295560801958037775 16019539943341202937056663)
                ·
                  refine ⟨24029309915011804405584995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16019539943341202937056663 24029309915011804405584995)
                  ·
                    refine ⟨36043964872517706608377493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24029309915011804405584995 36043964872517706608377493)
                    ·
                      refine ⟨1689560853399267497267695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36043964872517706608377493 1689560853399267497267695)
                      ·
                        rfl

theorem cell23_3290408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_3290408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290408 prefixEnd_3290408 := by exact prefixLift 3290408
  have htrace : WordTrace (prefixWord ++ tailWord_3290408) baseStart_3290408 baseEnd_3290408 := by
    simpa [prefixWord, tailWord_3290408, baseEnd_3290408] using wordTrace_append hprefix tailTrace_3290408
  have hstable : (prefixWord ++ tailWord_3290408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290408).length < 2 ^ (prefixWord ++ tailWord_3290408).sum := by decide
  have hdescent : baseEnd_3290408 < baseStart_3290408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290411 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 3]
def baseStart_3290411 : Nat := 118140960795 + 3290411 * 2 ^ 59
def prefixEnd_3290411 : Nat := 4983230072969 + 3 ^ 40 * 3290411 * 2
def baseEnd_3290411 : Nat := 1689562393841230985530181

theorem tailTrace_3290411 : CollatzResearch.WordTrace tailWord_3290411 prefixEnd_3290411 1689562393841230985530181 := by
  unfold tailWord_3290411
  simp only [CollatzResearch.WordTrace]
  refine ⟨120011148482410379304191087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80007432321606919536127391 120011148482410379304191087)
  ·
    refine ⟨180016722723615568956286631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120011148482410379304191087 180016722723615568956286631)
    ·
      refine ⟨270025084085423353434429947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180016722723615568956286631 270025084085423353434429947)
      ·
        refine ⟨405037626128135030151644921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270025084085423353434429947 405037626128135030151644921)
        ·
          refine ⟨303778219596101272613733691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405037626128135030151644921 303778219596101272613733691)
          ·
            refine ⟨455667329394151908920600537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303778219596101272613733691 455667329394151908920600537)
            ·
              refine ⟨341750497045613931690450403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455667329394151908920600537 341750497045613931690450403)
              ·
                refine ⟨512625745568420897535675605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341750497045613931690450403 512625745568420897535675605)
                ·
                  refine ⟨12014665911759864785992397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 512625745568420897535675605 12014665911759864785992397)
                  ·
                    refine ⟨4505499716909949294747149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12014665911759864785992397 4505499716909949294747149)
                    ·
                      refine ⟨1689562393841230985530181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4505499716909949294747149 1689562393841230985530181)
                      ·
                        rfl

theorem cell23_3290411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 3].length) (baseStart_3290411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290411 prefixEnd_3290411 := by exact prefixLift 3290411
  have htrace : WordTrace (prefixWord ++ tailWord_3290411) baseStart_3290411 baseEnd_3290411 := by
    simpa [prefixWord, tailWord_3290411, baseEnd_3290411] using wordTrace_append hprefix tailTrace_3290411
  have hstable : (prefixWord ++ tailWord_3290411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290411).length < 2 ^ (prefixWord ++ tailWord_3290411).sum := by decide
  have hdescent : baseEnd_3290411 < baseStart_3290411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290418 : List Nat := [3, 2, 1, 1, 4, 1, 4, 7]
def baseStart_3290418 : Nat := 118140960795 + 3290418 * 2 ^ 59
def prefixEnd_3290418 : Nat := 4983230072969 + 3 ^ 40 * 3290418 * 2
def baseEnd_3290418 : Nat := 62576518081696757708987

theorem tailTrace_3290418 : CollatzResearch.WordTrace tailWord_3290418 prefixEnd_3290418 62576518081696757708987 := by
  unfold tailWord_3290418
  simp only [CollatzResearch.WordTrace]
  refine ⟨30002850948346254874923977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80007602528923346333130605 30002850948346254874923977)
  ·
    refine ⟨22502138211259691156192983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30002850948346254874923977 22502138211259691156192983)
    ·
      refine ⟨33753207316889536734289475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22502138211259691156192983 33753207316889536734289475)
      ·
        refine ⟨50629810975334305101434213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33753207316889536734289475 50629810975334305101434213)
        ·
          refine ⟨9493089557875182206518915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50629810975334305101434213 9493089557875182206518915)
          ·
            refine ⟨14239634336812773309778373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9493089557875182206518915 14239634336812773309778373)
            ·
              refine ⟨2669931438152394995583445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14239634336812773309778373 2669931438152394995583445)
              ·
                refine ⟨62576518081696757708987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2669931438152394995583445 62576518081696757708987)
                ·
                  rfl

theorem cell23_3290418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 7].length) (baseStart_3290418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290418 prefixEnd_3290418 := by exact prefixLift 3290418
  have htrace : WordTrace (prefixWord ++ tailWord_3290418) baseStart_3290418 baseEnd_3290418 := by
    simpa [prefixWord, tailWord_3290418, baseEnd_3290418] using wordTrace_append hprefix tailTrace_3290418
  have hstable : (prefixWord ++ tailWord_3290418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290418).length < 2 ^ (prefixWord ++ tailWord_3290418).sum := by decide
  have hdescent : baseEnd_3290418 < baseStart_3290418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290451 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 4]
def baseStart_3290451 : Nat := 118140960795 + 3290451 * 2 ^ 59
def prefixEnd_3290451 : Nat := 4983230072969 + 3 ^ 40 * 3290451 * 2
def baseEnd_3290451 : Nat := 1689582933067410829029997

theorem tailTrace_3290451 : CollatzResearch.WordTrace tailWord_3290451 prefixEnd_3290451 1689582933067410829029997 := by
  unfold tailWord_3290451
  simp only [CollatzResearch.WordTrace]
  refine ⟨120012607402265466135647207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80008404934843644090431471 120012607402265466135647207)
  ·
    refine ⟨180018911103398199203470811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120012607402265466135647207 180018911103398199203470811)
    ·
      refine ⟨270028366655097298805206217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180018911103398199203470811 270028366655097298805206217)
      ·
        refine ⟨202521274991322974103904663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270028366655097298805206217 202521274991322974103904663)
        ·
          refine ⟨303781912486984461155856995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202521274991322974103904663 303781912486984461155856995)
          ·
            refine ⟨455672868730476691733785493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303781912486984461155856995 455672868730476691733785493)
            ·
              refine ⟨21359665721741094925021195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 455672868730476691733785493 21359665721741094925021195)
              ·
                refine ⟨32039498582611642387531793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21359665721741094925021195 32039498582611642387531793)
                ·
                  refine ⟨24029623936958731790648845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32039498582611642387531793 24029623936958731790648845)
                  ·
                    refine ⟨9011108976359524421493317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24029623936958731790648845 9011108976359524421493317)
                    ·
                      refine ⟨1689582933067410829029997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9011108976359524421493317 1689582933067410829029997)
                      ·
                        rfl

theorem cell23_3290451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_3290451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290451 prefixEnd_3290451 := by exact prefixLift 3290451
  have htrace : WordTrace (prefixWord ++ tailWord_3290451) baseStart_3290451 baseEnd_3290451 := by
    simpa [prefixWord, tailWord_3290451, baseEnd_3290451] using wordTrace_append hprefix tailTrace_3290451
  have hstable : (prefixWord ++ tailWord_3290451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290451).length < 2 ^ (prefixWord ++ tailWord_3290451).sum := by decide
  have hdescent : baseEnd_3290451 < baseStart_3290451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290472 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 3, 3, 2]
def baseStart_3290472 : Nat := 118140960795 + 3290472 * 2 ^ 59
def prefixEnd_3290472 : Nat := 4983230072969 + 3 ^ 40 * 3290472 * 2
def baseEnd_3290472 : Nat := 1689593716161155246867401

theorem tailTrace_3290472 : CollatzResearch.WordTrace tailWord_3290472 prefixEnd_3290472 1689593716161155246867401 := by
  unfold tailWord_3290472
  simp only [CollatzResearch.WordTrace]
  refine ⟨60006686667594693361080835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80008915556792924481441113 60006686667594693361080835)
  ·
    refine ⟨90010030001392040041621253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60006686667594693361080835 90010030001392040041621253)
    ·
      refine ⟨16876880625261007507803985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90010030001392040041621253 16876880625261007507803985)
      ·
        refine ⟨12657660468945755630852989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16876880625261007507803985 12657660468945755630852989)
        ·
          refine ⟨4746622675854658361569871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12657660468945755630852989 4746622675854658361569871)
          ·
            refine ⟨7119934013781987542354807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4746622675854658361569871 7119934013781987542354807)
            ·
              refine ⟨10679901020672981313532211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7119934013781987542354807 10679901020672981313532211)
              ·
                refine ⟨16019851531009471970298317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10679901020672981313532211 16019851531009471970298317)
                ·
                  refine ⟨6007444324128551988861869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16019851531009471970298317 6007444324128551988861869)
                  ·
                    refine ⟨2252791621548206995823201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6007444324128551988861869 2252791621548206995823201)
                    ·
                      refine ⟨1689593716161155246867401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2252791621548206995823201 1689593716161155246867401)
                      ·
                        rfl

theorem cell23_3290472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_3290472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290472 prefixEnd_3290472 := by exact prefixLift 3290472
  have htrace : WordTrace (prefixWord ++ tailWord_3290472) baseStart_3290472 baseEnd_3290472 := by
    simpa [prefixWord, tailWord_3290472, baseEnd_3290472] using wordTrace_append hprefix tailTrace_3290472
  have hstable : (prefixWord ++ tailWord_3290472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290472).length < 2 ^ (prefixWord ++ tailWord_3290472).sum := by decide
  have hdescent : baseEnd_3290472 < baseStart_3290472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290501 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 7]
def baseStart_3290501 : Nat := 118140960795 + 3290501 * 2 ^ 59
def prefixEnd_3290501 : Nat := 4983230072969 + 3 ^ 40 * 3290501 * 2
def baseEnd_3290501 : Nat := 1689608607100135633404767

theorem tailTrace_3290501 : CollatzResearch.WordTrace tailWord_3290501 prefixEnd_3290501 1689608607100135633404767 := by
  unfold tailWord_3290501
  simp only [CollatzResearch.WordTrace]
  refine ⟨120014431052084324674967357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80009620701389549783311571 120014431052084324674967357)
  ·
    refine ⟨45005411644531621753112759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120014431052084324674967357 45005411644531621753112759)
    ·
      refine ⟨67508117466797432629669139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45005411644531621753112759 67508117466797432629669139)
      ·
        refine ⟨101262176200196148944503709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67508117466797432629669139 101262176200196148944503709)
        ·
          refine ⟨37973316075073555854188891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101262176200196148944503709 37973316075073555854188891)
          ·
            refine ⟨56959974112610333781283337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37973316075073555854188891 56959974112610333781283337)
            ·
              refine ⟨42719980584457750335962503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56959974112610333781283337 42719980584457750335962503)
              ·
                refine ⟨64079970876686625503943755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42719980584457750335962503 64079970876686625503943755)
                ·
                  refine ⟨96119956315029938255915633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64079970876686625503943755 96119956315029938255915633)
                  ·
                    refine ⟨72089967236272453691936725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96119956315029938255915633 72089967236272453691936725)
                    ·
                      refine ⟨1689608607100135633404767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72089967236272453691936725 1689608607100135633404767)
                      ·
                        rfl

theorem cell23_3290501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_3290501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290501 prefixEnd_3290501 := by exact prefixLift 3290501
  have htrace : WordTrace (prefixWord ++ tailWord_3290501) baseStart_3290501 baseEnd_3290501 := by
    simpa [prefixWord, tailWord_3290501, baseEnd_3290501] using wordTrace_append hprefix tailTrace_3290501
  have hstable : (prefixWord ++ tailWord_3290501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290501).length < 2 ^ (prefixWord ++ tailWord_3290501).sum := by decide
  have hdescent : baseEnd_3290501 < baseStart_3290501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290575 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 2, 4, 2]
def baseStart_3290575 : Nat := 118140960795 + 3290575 * 2 ^ 59
def prefixEnd_3290575 : Nat := 4983230072969 + 3 ^ 40 * 3290575 * 2
def baseEnd_3290575 : Nat := 1689646604668568343879427

theorem tailTrace_3290575 : CollatzResearch.WordTrace tailWord_3290575 prefixEnd_3290575 1689646604668568343879427 := by
  unfold tailWord_3290575
  simp only [CollatzResearch.WordTrace]
  refine ⟨120017130053816235313161179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80011420035877490208774119 120017130053816235313161179)
  ·
    refine ⟨180025695080724352969741769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120017130053816235313161179 180025695080724352969741769)
    ·
      refine ⟨135019271310543264727306327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180025695080724352969741769 135019271310543264727306327)
      ·
        refine ⟨202528906965814897090959491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135019271310543264727306327 202528906965814897090959491)
        ·
          refine ⟨303793360448722345636439237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202528906965814897090959491 303793360448722345636439237)
          ·
            refine ⟨56961255084135439806832357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 303793360448722345636439237 56961255084135439806832357)
            ·
              refine ⟨10680235328275394963781067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56961255084135439806832357 10680235328275394963781067)
              ·
                refine ⟨16020352992413092445671601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10680235328275394963781067 16020352992413092445671601)
                ·
                  refine ⟨12015264744309819334253701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16020352992413092445671601 12015264744309819334253701)
                  ·
                    refine ⟨2252862139558091125172569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12015264744309819334253701 2252862139558091125172569)
                    ·
                      refine ⟨1689646604668568343879427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2252862139558091125172569 1689646604668568343879427)
                      ·
                        rfl

theorem cell23_3290575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 4, 2].length) (baseStart_3290575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290575 prefixEnd_3290575 := by exact prefixLift 3290575
  have htrace : WordTrace (prefixWord ++ tailWord_3290575) baseStart_3290575 baseEnd_3290575 := by
    simpa [prefixWord, tailWord_3290575, baseEnd_3290575] using wordTrace_append hprefix tailTrace_3290575
  have hstable : (prefixWord ++ tailWord_3290575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290575).length < 2 ^ (prefixWord ++ tailWord_3290575).sum := by decide
  have hdescent : baseEnd_3290575 < baseStart_3290575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290585 : List Nat := [1, 2, 1, 2, 4, 2, 2, 2, 3, 4]
def baseStart_3290585 : Nat := 118140960795 + 3290585 * 2 ^ 59
def prefixEnd_3290585 : Nat := 4983230072969 + 3 ^ 40 * 3290585 * 2
def baseEnd_3290585 : Nat := 563217246491704434918127

theorem tailTrace_3290585 : CollatzResearch.WordTrace tailWord_3290585 prefixEnd_3290585 563217246491704434918127 := by
  unfold tailWord_3290585
  simp only [CollatzResearch.WordTrace]
  refine ⟨120017494783780007021025209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80011663189186671347350139 120017494783780007021025209)
  ·
    refine ⟨90013121087835005265768907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120017494783780007021025209 90013121087835005265768907)
    ·
      refine ⟨135019681631752507898653361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90013121087835005265768907 135019681631752507898653361)
      ·
        refine ⟨101264761223814380923990021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135019681631752507898653361 101264761223814380923990021)
        ·
          refine ⟨18987142729465196423248129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101264761223814380923990021 18987142729465196423248129)
          ·
            refine ⟨14240357047098897317436097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18987142729465196423248129 14240357047098897317436097)
            ·
              refine ⟨10680267785324172988077073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14240357047098897317436097 10680267785324172988077073)
              ·
                refine ⟨8010200838993129741057805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10680267785324172988077073 8010200838993129741057805)
                ·
                  refine ⟨3003825314622423652896677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8010200838993129741057805 3003825314622423652896677)
                  ·
                    refine ⟨563217246491704434918127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3003825314622423652896677 563217246491704434918127)
                    ·
                      rfl

theorem cell23_3290585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 4].length) (baseStart_3290585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290585 prefixEnd_3290585 := by exact prefixLift 3290585
  have htrace : WordTrace (prefixWord ++ tailWord_3290585) baseStart_3290585 baseEnd_3290585 := by
    simpa [prefixWord, tailWord_3290585, baseEnd_3290585] using wordTrace_append hprefix tailTrace_3290585
  have hstable : (prefixWord ++ tailWord_3290585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290585).length < 2 ^ (prefixWord ++ tailWord_3290585).sum := by decide
  have hdescent : baseEnd_3290585 < baseStart_3290585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290595 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 3]
def baseStart_3290595 : Nat := 118140960795 + 3290595 * 2 ^ 59
def prefixEnd_3290595 : Nat := 4983230072969 + 3 ^ 40 * 3290595 * 2
def baseEnd_3290595 : Nat := 1689656874281658265629335

theorem tailTrace_3290595 : CollatzResearch.WordTrace tailWord_3290595 prefixEnd_3290595 1689656874281658265629335 := by
  unfold tailWord_3290595
  simp only [CollatzResearch.WordTrace]
  refine ⟨120017859513743778728889239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80011906342495852485926159 120017859513743778728889239)
  ·
    refine ⟨180026789270615668093333859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120017859513743778728889239 180026789270615668093333859)
    ·
      refine ⟨270040183905923502140000789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180026789270615668093333859 270040183905923502140000789)
      ·
        refine ⟨12658133620590164162812537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 270040183905923502140000789 12658133620590164162812537)
        ·
          refine ⟨9493600215442623122109403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12658133620590164162812537 9493600215442623122109403)
          ·
            refine ⟨14240400323163934683164105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9493600215442623122109403 14240400323163934683164105)
            ·
              refine ⟨10680300242372951012373079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14240400323163934683164105 10680300242372951012373079)
              ·
                refine ⟨16020450363559426518559619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10680300242372951012373079 16020450363559426518559619)
                ·
                  refine ⟨24030675545339139777839429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16020450363559426518559619 24030675545339139777839429)
                  ·
                    refine ⟨4505751664751088708344893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24030675545339139777839429 4505751664751088708344893)
                    ·
                      refine ⟨1689656874281658265629335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4505751664751088708344893 1689656874281658265629335)
                      ·
                        rfl

theorem cell23_3290595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_3290595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290595 prefixEnd_3290595 := by exact prefixLift 3290595
  have htrace : WordTrace (prefixWord ++ tailWord_3290595) baseStart_3290595 baseEnd_3290595 := by
    simpa [prefixWord, tailWord_3290595, baseEnd_3290595] using wordTrace_append hprefix tailTrace_3290595
  have hstable : (prefixWord ++ tailWord_3290595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290595).length < 2 ^ (prefixWord ++ tailWord_3290595).sum := by decide
  have hdescent : baseEnd_3290595 < baseStart_3290595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290645 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 3, 5]
def baseStart_3290645 : Nat := 118140960795 + 3290645 * 2 ^ 59
def prefixEnd_3290645 : Nat := 4983230072969 + 3 ^ 40 * 3290645 * 2
def baseEnd_3290645 : Nat := 563227516104794356668035

theorem tailTrace_3290645 : CollatzResearch.WordTrace tailWord_3290645 prefixEnd_3290645 563227516104794356668035 := by
  unfold tailWord_3290645
  simp only [CollatzResearch.WordTrace]
  refine ⟨120019683163562637268209389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80013122109041758178806259 120019683163562637268209389)
  ·
    refine ⟨45007381186335988975578521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120019683163562637268209389 45007381186335988975578521)
    ·
      refine ⟨33755535889751991731683891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45007381186335988975578521 33755535889751991731683891)
      ·
        refine ⟨50633303834627987597525837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33755535889751991731683891 50633303834627987597525837)
        ·
          refine ⟨18987488937985495349072189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50633303834627987597525837 18987488937985495349072189)
          ·
            refine ⟨7120308351744560755902071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18987488937985495349072189 7120308351744560755902071)
            ·
              refine ⟨10680462527616841133853107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7120308351744560755902071 10680462527616841133853107)
              ·
                refine ⟨16020693791425261700779661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10680462527616841133853107 16020693791425261700779661)
                ·
                  refine ⟨6007760171784473137792373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16020693791425261700779661 6007760171784473137792373)
                  ·
                    refine ⟨563227516104794356668035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6007760171784473137792373 563227516104794356668035)
                    ·
                      rfl

theorem cell23_3290645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_3290645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290645 prefixEnd_3290645 := by exact prefixLift 3290645
  have htrace : WordTrace (prefixWord ++ tailWord_3290645) baseStart_3290645 baseEnd_3290645 := by
    simpa [prefixWord, tailWord_3290645, baseEnd_3290645] using wordTrace_append hprefix tailTrace_3290645
  have hstable : (prefixWord ++ tailWord_3290645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290645).length < 2 ^ (prefixWord ++ tailWord_3290645).sum := by decide
  have hdescent : baseEnd_3290645 < baseStart_3290645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290702 : List Nat := [4, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3]
def baseStart_3290702 : Nat := 118140960795 + 3290702 * 2 ^ 59
def prefixEnd_3290702 : Nat := 4983230072969 + 3 ^ 40 * 3290702 * 2
def baseEnd_3290702 : Nat := 1689711816711689346991343

theorem tailTrace_3290702 : CollatzResearch.WordTrace tailWord_3290702 prefixEnd_3290702 1689711816711689346991343 := by
  unfold tailWord_3290702
  simp only [CollatzResearch.WordTrace]
  refine ⟨15002720265544517000379295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80014508082904090668689573 15002720265544517000379295)
  ·
    refine ⟨22504080398316775500568943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15002720265544517000379295 22504080398316775500568943)
    ·
      refine ⟨33756120597475163250853415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22504080398316775500568943 33756120597475163250853415)
      ·
        refine ⟨50634180896212744876280123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33756120597475163250853415 50634180896212744876280123)
        ·
          refine ⟨75951271344319117314420185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50634180896212744876280123 75951271344319117314420185)
          ·
            refine ⟨56963453508239337985815139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75951271344319117314420185 56963453508239337985815139)
            ·
              refine ⟨85445180262359006978722709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56963453508239337985815139 85445180262359006978722709)
              ·
                refine ⟨4005242824798078452127627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85445180262359006978722709 4005242824798078452127627)
                ·
                  refine ⟨6007864237197117678191441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4005242824798078452127627 6007864237197117678191441)
                  ·
                    refine ⟨4505898177897838258643581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6007864237197117678191441 4505898177897838258643581)
                    ·
                      refine ⟨1689711816711689346991343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4505898177897838258643581 1689711816711689346991343)
                      ·
                        rfl

theorem cell23_3290702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_3290702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290702 prefixEnd_3290702 := by exact prefixLift 3290702
  have htrace : WordTrace (prefixWord ++ tailWord_3290702) baseStart_3290702 baseEnd_3290702 := by
    simpa [prefixWord, tailWord_3290702, baseEnd_3290702] using wordTrace_append hprefix tailTrace_3290702
  have hstable : (prefixWord ++ tailWord_3290702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290702).length < 2 ^ (prefixWord ++ tailWord_3290702).sum := by decide
  have hdescent : baseEnd_3290702 < baseStart_3290702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290705 : List Nat := [1, 2, 2, 1, 3, 2, 5, 7]
def baseStart_3290705 : Nat := 118140960795 + 3290705 * 2 ^ 59
def prefixEnd_3290705 : Nat := 4983230072969 + 3 ^ 40 * 3290705 * 2
def baseEnd_3290705 : Nat := 62581976190876030935327

theorem tailTrace_3290705 : CollatzResearch.WordTrace tailWord_3290705 prefixEnd_3290705 62581976190876030935327 := by
  unfold tailWord_3290705
  simp only [CollatzResearch.WordTrace]
  refine ⟨120021871543345267515393569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80014581028896845010262379 120021871543345267515393569)
  ·
    refine ⟨90016403657508950636545177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120021871543345267515393569 90016403657508950636545177)
    ·
      refine ⟨67512302743131712977408883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90016403657508950636545177 67512302743131712977408883)
      ·
        refine ⟨101268454114697569466113325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67512302743131712977408883 101268454114697569466113325)
        ·
          refine ⟨37975670293011588549792497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101268454114697569466113325 37975670293011588549792497)
          ·
            refine ⟨28481752719758691412344373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37975670293011588549792497 28481752719758691412344373)
            ·
              refine ⟨2670164317477377319907285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28481752719758691412344373 2670164317477377319907285)
              ·
                refine ⟨62581976190876030935327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2670164317477377319907285 62581976190876030935327)
                ·
                  rfl

theorem cell23_3290705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 7].length) (baseStart_3290705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290705 prefixEnd_3290705 := by exact prefixLift 3290705
  have htrace : WordTrace (prefixWord ++ tailWord_3290705) baseStart_3290705 baseEnd_3290705 := by
    simpa [prefixWord, tailWord_3290705, baseEnd_3290705] using wordTrace_append hprefix tailTrace_3290705
  have hstable : (prefixWord ++ tailWord_3290705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290705).length < 2 ^ (prefixWord ++ tailWord_3290705).sum := by decide
  have hdescent : baseEnd_3290705 < baseStart_3290705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290716 : List Nat := [2, 2, 4, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_3290716 : Nat := 118140960795 + 3290716 * 2 ^ 59
def prefixEnd_3290716 : Nat := 4983230072969 + 3 ^ 40 * 3290716 * 2
def baseEnd_3290716 : Nat := 1689719005440852292216279

theorem tailTrace_3290716 : CollatzResearch.WordTrace tailWord_3290716 prefixEnd_3290716 1689719005440852292216279 := by
  unfold tailWord_3290716
  simp only [CollatzResearch.WordTrace]
  refine ⟨60011136373152708197022001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80014848497536944262696001 60011136373152708197022001)
  ·
    refine ⟨45008352279864531147766501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60011136373152708197022001 45008352279864531147766501)
    ·
      refine ⟨8439066052474599590206219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45008352279864531147766501 8439066052474599590206219)
      ·
        refine ⟨12658599078711899385309329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8439066052474599590206219 12658599078711899385309329)
        ·
          refine ⟨9493949309033924538981997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12658599078711899385309329 9493949309033924538981997)
          ·
            refine ⟨3560230990887721702118249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9493949309033924538981997 3560230990887721702118249)
            ·
              refine ⟨2670173243165791276588687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3560230990887721702118249 2670173243165791276588687)
              ·
                refine ⟨4005259864748686914883031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2670173243165791276588687 4005259864748686914883031)
                ·
                  refine ⟨6007889797123030372324547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4005259864748686914883031 6007889797123030372324547)
                  ·
                    refine ⟨9011834695684545558486821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6007889797123030372324547 9011834695684545558486821)
                    ·
                      refine ⟨1689719005440852292216279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9011834695684545558486821 1689719005440852292216279)
                      ·
                        rfl

theorem cell23_3290716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_3290716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290716 prefixEnd_3290716 := by exact prefixLift 3290716
  have htrace : WordTrace (prefixWord ++ tailWord_3290716) baseStart_3290716 baseEnd_3290716 := by
    simpa [prefixWord, tailWord_3290716, baseEnd_3290716] using wordTrace_append hprefix tailTrace_3290716
  have hstable : (prefixWord ++ tailWord_3290716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290716).length < 2 ^ (prefixWord ++ tailWord_3290716).sum := by decide
  have hdescent : baseEnd_3290716 < baseStart_3290716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290749 : List Nat := [1, 4, 1, 1, 4, 3, 1, 1, 1, 3, 3]
def baseStart_3290749 : Nat := 118140960795 + 3290749 * 2 ^ 59
def prefixEnd_3290749 : Nat := 4983230072969 + 3 ^ 40 * 3290749 * 2
def baseEnd_3290749 : Nat := 1689735950302450663103627

theorem tailTrace_3290749 : CollatzResearch.WordTrace tailWord_3290749 prefixEnd_3290749 1689735950302450663103627 := by
  unfold tailWord_3290749
  simp only [CollatzResearch.WordTrace]
  refine ⟨120023476355185863029995301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80015650903457242019996867 120023476355185863029995301)
  ·
    refine ⟨22504401816597349318124119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120023476355185863029995301 22504401816597349318124119)
    ·
      refine ⟨33756602724896023977186179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22504401816597349318124119 33756602724896023977186179)
      ·
        refine ⟨50634904087344035965779269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33756602724896023977186179 50634904087344035965779269)
        ·
          refine ⟨9494044516377006743583613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50634904087344035965779269 9494044516377006743583613)
          ·
            refine ⟨3560266693641377528843855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9494044516377006743583613 3560266693641377528843855)
            ·
              refine ⟨5340400040462066293265783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3560266693641377528843855 5340400040462066293265783)
              ·
                refine ⟨8010600060693099439898675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5340400040462066293265783 8010600060693099439898675)
                ·
                  refine ⟨12015900091039649159848013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8010600060693099439898675 12015900091039649159848013)
                  ·
                    refine ⟨4505962534139868434943005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12015900091039649159848013 4505962534139868434943005)
                    ·
                      refine ⟨1689735950302450663103627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4505962534139868434943005 1689735950302450663103627)
                      ·
                        rfl

theorem cell23_3290749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_3290749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290749 prefixEnd_3290749 := by exact prefixLift 3290749
  have htrace : WordTrace (prefixWord ++ tailWord_3290749) baseStart_3290749 baseEnd_3290749 := by
    simpa [prefixWord, tailWord_3290749, baseEnd_3290749] using wordTrace_append hprefix tailTrace_3290749
  have hstable : (prefixWord ++ tailWord_3290749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290749).length < 2 ^ (prefixWord ++ tailWord_3290749).sum := by decide
  have hdescent : baseEnd_3290749 < baseStart_3290749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290759 : List Nat := [1, 1, 4, 2, 1, 3, 1, 4, 1, 3, 2]
def baseStart_3290759 : Nat := 118140960795 + 3290759 * 2 ^ 59
def prefixEnd_3290759 : Nat := 4983230072969 + 3 ^ 40 * 3290759 * 2
def baseEnd_3290759 : Nat := 1689741085108995623978581

theorem tailTrace_3290759 : CollatzResearch.WordTrace tailWord_3290759 prefixEnd_3290759 1689741085108995623978581 := by
  unfold tailWord_3290759
  simp only [CollatzResearch.WordTrace]
  refine ⟨120023841085149634737859331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80015894056766423158572887 120023841085149634737859331)
  ·
    refine ⟨180035761627724452106788997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120023841085149634737859331 180035761627724452106788997)
    ·
      refine ⟨33756705305198334770022937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180035761627724452106788997 33756705305198334770022937)
      ·
        refine ⟨25317528978898751077517203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33756705305198334770022937 25317528978898751077517203)
        ·
          refine ⟨37976293468348126616275805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25317528978898751077517203 37976293468348126616275805)
          ·
            refine ⟨14241110050630547481103427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37976293468348126616275805 14241110050630547481103427)
            ·
              refine ⟨21361665075945821221655141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14241110050630547481103427 21361665075945821221655141)
              ·
                refine ⟨4005312201739841479060339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21361665075945821221655141 4005312201739841479060339)
                ·
                  refine ⟨6007968302609762218590509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4005312201739841479060339 6007968302609762218590509)
                  ·
                    refine ⟨2252988113478660831971441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6007968302609762218590509 2252988113478660831971441)
                    ·
                      refine ⟨1689741085108995623978581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2252988113478660831971441 1689741085108995623978581)
                      ·
                        rfl

theorem cell23_3290759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_3290759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290759 prefixEnd_3290759 := by exact prefixLift 3290759
  have htrace : WordTrace (prefixWord ++ tailWord_3290759) baseStart_3290759 baseEnd_3290759 := by
    simpa [prefixWord, tailWord_3290759, baseEnd_3290759] using wordTrace_append hprefix tailTrace_3290759
  have hstable : (prefixWord ++ tailWord_3290759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290759).length < 2 ^ (prefixWord ++ tailWord_3290759).sum := by decide
  have hdescent : baseEnd_3290759 < baseStart_3290759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290775 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 5]
def baseStart_3290775 : Nat := 118140960795 + 3290775 * 2 ^ 59
def prefixEnd_3290775 : Nat := 4983230072969 + 3 ^ 40 * 3290775 * 2
def baseEnd_3290775 : Nat := 1689749300799467561378507

theorem tailTrace_3290775 : CollatzResearch.WordTrace tailWord_3290775 prefixEnd_3290775 1689749300799467561378507 := by
  unfold tailWord_3290775
  simp only [CollatzResearch.WordTrace]
  refine ⟨120024424653091669470441779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80016283102061112980294519 120024424653091669470441779)
  ·
    refine ⟨180036636979637504205662669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120024424653091669470441779 180036636979637504205662669)
    ·
      refine ⟨67513738867364064077123501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180036636979637504205662669 67513738867364064077123501)
      ·
        refine ⟨25317652075261524028921313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67513738867364064077123501 25317652075261524028921313)
        ·
          refine ⟨18988239056446143021690985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25317652075261524028921313 18988239056446143021690985)
          ·
            refine ⟨14241179292334607266268239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18988239056446143021690985 14241179292334607266268239)
            ·
              refine ⟨21361768938501910899402359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14241179292334607266268239 21361768938501910899402359)
              ·
                refine ⟨32042653407752866349103539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21361768938501910899402359 32042653407752866349103539)
                ·
                  refine ⟨48063980111629299523655309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32042653407752866349103539 48063980111629299523655309)
                  ·
                    refine ⟨18023992541860987321370741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48063980111629299523655309 18023992541860987321370741)
                    ·
                      refine ⟨1689749300799467561378507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18023992541860987321370741 1689749300799467561378507)
                      ·
                        rfl

theorem cell23_3290775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_3290775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290775 prefixEnd_3290775 := by exact prefixLift 3290775
  have htrace : WordTrace (prefixWord ++ tailWord_3290775) baseStart_3290775 baseEnd_3290775 := by
    simpa [prefixWord, tailWord_3290775, baseEnd_3290775] using wordTrace_append hprefix tailTrace_3290775
  have hstable : (prefixWord ++ tailWord_3290775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290775).length < 2 ^ (prefixWord ++ tailWord_3290775).sum := by decide
  have hdescent : baseEnd_3290775 < baseStart_3290775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290789 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 4, 2, 2]
def baseStart_3290789 : Nat := 118140960795 + 3290789 * 2 ^ 59
def prefixEnd_3290789 : Nat := 4983230072969 + 3 ^ 40 * 3290789 * 2
def baseEnd_3290789 : Nat := 1689756489528630506603443

theorem tailTrace_3290789 : CollatzResearch.WordTrace tailWord_3290789 prefixEnd_3290789 1689756489528630506603443 := by
  unfold tailWord_3290789
  simp only [CollatzResearch.WordTrace]
  refine ⟨120024935275040949861451421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80016623516693966574300947 120024935275040949861451421)
  ·
    refine ⟨45009350728140356198044283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120024935275040949861451421 45009350728140356198044283)
    ·
      refine ⟨67514026092210534297066425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45009350728140356198044283 67514026092210534297066425)
      ·
        refine ⟨50635519569157900722799819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67514026092210534297066425 50635519569157900722799819)
        ·
          refine ⟨75953279353736851084199729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50635519569157900722799819 75953279353736851084199729)
          ·
            refine ⟨56964959515302638313149797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75953279353736851084199729 56964959515302638313149797)
            ·
              refine ⟨10680929909119244683715587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56964959515302638313149797 10680929909119244683715587)
              ·
                refine ⟨16021394863678867025573381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10680929909119244683715587 16021394863678867025573381)
                ·
                  refine ⟨3004011536939787567295009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16021394863678867025573381 3004011536939787567295009)
                  ·
                    refine ⟨2253008652704840675471257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3004011536939787567295009 2253008652704840675471257)
                    ·
                      refine ⟨1689756489528630506603443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2253008652704840675471257 1689756489528630506603443)
                      ·
                        rfl

theorem cell23_3290789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_3290789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290789 prefixEnd_3290789 := by exact prefixLift 3290789
  have htrace : WordTrace (prefixWord ++ tailWord_3290789) baseStart_3290789 baseEnd_3290789 := by
    simpa [prefixWord, tailWord_3290789, baseEnd_3290789] using wordTrace_append hprefix tailTrace_3290789
  have hstable : (prefixWord ++ tailWord_3290789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290789).length < 2 ^ (prefixWord ++ tailWord_3290789).sum := by decide
  have hdescent : baseEnd_3290789 < baseStart_3290789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290842 : List Nat := [3, 1, 1, 2, 2, 3, 2, 2, 2, 5]
def baseStart_3290842 : Nat := 118140960795 + 3290842 * 2 ^ 59
def prefixEnd_3290842 : Nat := 4983230072969 + 3 ^ 40 * 3290842 * 2
def baseEnd_3290842 : Nat := 563261234667772933080233

theorem tailTrace_3290842 : CollatzResearch.WordTrace tailWord_3290842 prefixEnd_3290842 563261234667772933080233 := by
  unfold tailWord_3290842
  simp only [CollatzResearch.WordTrace]
  refine ⟨30006717085962234978282695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80017912229232626608753853 30006717085962234978282695)
  ·
    refine ⟨45010075628943352467424043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30006717085962234978282695 45010075628943352467424043)
    ·
      refine ⟨67515113443415028701136065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45010075628943352467424043 67515113443415028701136065)
      ·
        refine ⟨50636335082561271525852049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67515113443415028701136065 50636335082561271525852049)
        ·
          refine ⟨37977251311920953644389037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50636335082561271525852049 37977251311920953644389037)
          ·
            refine ⟨14241469241970357616645889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37977251311920953644389037 14241469241970357616645889)
            ·
              refine ⟨10681101931477768212484417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14241469241970357616645889 10681101931477768212484417)
              ·
                refine ⟨8010826448608326159363313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10681101931477768212484417 8010826448608326159363313)
                ·
                  refine ⟨6008119836456244619522485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8010826448608326159363313 6008119836456244619522485)
                  ·
                    refine ⟨563261234667772933080233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6008119836456244619522485 563261234667772933080233)
                    ·
                      rfl

theorem cell23_3290842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_3290842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290842 prefixEnd_3290842 := by exact prefixLift 3290842
  have htrace : WordTrace (prefixWord ++ tailWord_3290842) baseStart_3290842 baseEnd_3290842 := by
    simpa [prefixWord, tailWord_3290842, baseEnd_3290842] using wordTrace_append hprefix tailTrace_3290842
  have hstable : (prefixWord ++ tailWord_3290842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290842).length < 2 ^ (prefixWord ++ tailWord_3290842).sum := by decide
  have hdescent : baseEnd_3290842 < baseStart_3290842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290862 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_3290862 : Nat := 118140960795 + 3290862 * 2 ^ 59
def prefixEnd_3290862 : Nat := 4983230072969 + 3 ^ 40 * 3290862 * 2
def baseEnd_3290862 : Nat := 1689793973616408720990607

theorem tailTrace_3290862 : CollatzResearch.WordTrace tailWord_3290862 prefixEnd_3290862 1689793973616408720990607 := by
  unfold tailWord_3290862
  simp only [CollatzResearch.WordTrace]
  refine ⟨15003449725472060416107355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80018398535850988885905893 15003449725472060416107355)
  ·
    refine ⟨22505174588208090624161033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15003449725472060416107355 22505174588208090624161033)
    ·
      refine ⟨16878880941156067968120775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22505174588208090624161033 16878880941156067968120775)
      ·
        refine ⟨25318321411734101952181163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16878880941156067968120775 25318321411734101952181163)
        ·
          refine ⟨37977482117601152928271745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25318321411734101952181163 37977482117601152928271745)
          ·
            refine ⟨28483111588200864696203809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37977482117601152928271745 28483111588200864696203809)
            ·
              refine ⟨21362333691150648522152857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28483111588200864696203809 21362333691150648522152857)
              ·
                refine ⟨16021750268362986391614643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21362333691150648522152857 16021750268362986391614643)
                ·
                  refine ⟨24032625402544479587421965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16021750268362986391614643 24032625402544479587421965)
                  ·
                    refine ⟨9012234525954179845283237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24032625402544479587421965 9012234525954179845283237)
                    ·
                      refine ⟨1689793973616408720990607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9012234525954179845283237 1689793973616408720990607)
                      ·
                        rfl

theorem cell23_3290862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_3290862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290862 prefixEnd_3290862 := by exact prefixLift 3290862
  have htrace : WordTrace (prefixWord ++ tailWord_3290862) baseStart_3290862 baseEnd_3290862 := by
    simpa [prefixWord, tailWord_3290862, baseEnd_3290862] using wordTrace_append hprefix tailTrace_3290862
  have hstable : (prefixWord ++ tailWord_3290862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290862).length < 2 ^ (prefixWord ++ tailWord_3290862).sum := by decide
  have hdescent : baseEnd_3290862 < baseStart_3290862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290875 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 4]
def baseStart_3290875 : Nat := 118140960795 + 3290875 * 2 ^ 59
def prefixEnd_3290875 : Nat := 4983230072969 + 3 ^ 40 * 3290875 * 2
def baseEnd_3290875 : Nat := 1689800648864917170128047

theorem tailTrace_3290875 : CollatzResearch.WordTrace tailWord_3290875 prefixEnd_3290875 1689800648864917170128047 := by
  unfold tailWord_3290875
  simp only [CollatzResearch.WordTrace]
  refine ⟨120028071952729386549082079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80018714635152924366054719 120028071952729386549082079)
  ·
    refine ⟨180042107929094079823623119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120028071952729386549082079 180042107929094079823623119)
    ·
      refine ⟨270063161893641119735434679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180042107929094079823623119 270063161893641119735434679)
      ·
        refine ⟨405094742840461679603152019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270063161893641119735434679 405094742840461679603152019)
        ·
          refine ⟨607642114260692519404728029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405094742840461679603152019 607642114260692519404728029)
          ·
            refine ⟨227865792847759694776773011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 607642114260692519404728029 227865792847759694776773011)
            ·
              refine ⟨341798689271639542165159517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227865792847759694776773011 341798689271639542165159517)
              ·
                refine ⟨128174508476864828311934819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 341798689271639542165159517 128174508476864828311934819)
                ·
                  refine ⟨192261762715297242467902229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128174508476864828311934819 192261762715297242467902229)
                  ·
                    refine ⟨9012270127279558240682917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 192261762715297242467902229 9012270127279558240682917)
                    ·
                      refine ⟨1689800648864917170128047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9012270127279558240682917 1689800648864917170128047)
                      ·
                        rfl

theorem cell23_3290875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 4].length) (baseStart_3290875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290875 prefixEnd_3290875 := by exact prefixLift 3290875
  have htrace : WordTrace (prefixWord ++ tailWord_3290875) baseStart_3290875 baseEnd_3290875 := by
    simpa [prefixWord, tailWord_3290875, baseEnd_3290875] using wordTrace_append hprefix tailTrace_3290875
  have hstable : (prefixWord ++ tailWord_3290875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290875).length < 2 ^ (prefixWord ++ tailWord_3290875).sum := by decide
  have hdescent : baseEnd_3290875 < baseStart_3290875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290906 : List Nat := [3, 1, 1, 3, 2, 2, 2, 4, 1, 4]
def baseStart_3290906 : Nat := 118140960795 + 3290906 * 2 ^ 59
def prefixEnd_3290906 : Nat := 4983230072969 + 3 ^ 40 * 3290906 * 2
def baseEnd_3290906 : Nat := 563272188921735516280135

theorem tailTrace_3290906 : CollatzResearch.WordTrace tailWord_3290906 prefixEnd_3290906 563272188921735516280135 := by
  unfold tailWord_3290906
  simp only [CollatzResearch.WordTrace]
  refine ⟨30007300653904269710865143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80019468410411385895640381 30007300653904269710865143)
  ·
    refine ⟨45010950980856404566297715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30007300653904269710865143 45010950980856404566297715)
    ·
      refine ⟨67516426471284606849446573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45010950980856404566297715 67516426471284606849446573)
      ·
        refine ⟨25318659926731727568542465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67516426471284606849446573 25318659926731727568542465)
        ·
          refine ⟨18988994945048795676406849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25318659926731727568542465 18988994945048795676406849)
          ·
            refine ⟨14241746208786596757305137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18988994945048795676406849 14241746208786596757305137)
            ·
              refine ⟨10681309656589947567978853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14241746208786596757305137 10681309656589947567978853)
              ·
                refine ⟨2002745560610615168996035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10681309656589947567978853 2002745560610615168996035)
                ·
                  refine ⟨3004118340915922753494053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2002745560610615168996035 3004118340915922753494053)
                  ·
                    refine ⟨563272188921735516280135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3004118340915922753494053 563272188921735516280135)
                    ·
                      rfl

theorem cell23_3290906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 1, 4].length) (baseStart_3290906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3290906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3290906 prefixEnd_3290906 := by exact prefixLift 3290906
  have htrace : WordTrace (prefixWord ++ tailWord_3290906) baseStart_3290906 baseEnd_3290906 := by
    simpa [prefixWord, tailWord_3290906, baseEnd_3290906] using wordTrace_append hprefix tailTrace_3290906
  have hstable : (prefixWord ++ tailWord_3290906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290906).length < 2 ^ (prefixWord ++ tailWord_3290906).sum := by decide
  have hdescent : baseEnd_3290906 < baseStart_3290906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291003 : List Nat := [1, 1, 1, 1, 1, 5, 1, 7, 1, 2, 2]
def baseStart_3291003 : Nat := 118140960795 + 3291003 * 2 ^ 59
def prefixEnd_3291003 : Nat := 4983230072969 + 3 ^ 40 * 3291003 * 2
def baseEnd_3291003 : Nat := 1689866374388692669327459

theorem tailTrace_3291003 : CollatzResearch.WordTrace tailWord_3291003 prefixEnd_3291003 1689866374388692669327459 := by
  unfold tailWord_3291003
  simp only [CollatzResearch.WordTrace]
  refine ⟨120032740496265664409741663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80021826997510442939827775 120032740496265664409741663)
  ·
    refine ⟨180049110744398496614612495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120032740496265664409741663 180049110744398496614612495)
    ·
      refine ⟨270073666116597744921918743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180049110744398496614612495 270073666116597744921918743)
      ·
        refine ⟨405110499174896617382878115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270073666116597744921918743 405110499174896617382878115)
        ·
          refine ⟨607665748762344926074317173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405110499174896617382878115 607665748762344926074317173)
          ·
            refine ⟨56968663946469836819467235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 607665748762344926074317173 56968663946469836819467235)
            ·
              refine ⟨85452995919704755229200853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56968663946469836819467235 85452995919704755229200853)
              ·
                refine ⟨2002804591868080200684395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 85452995919704755229200853 2002804591868080200684395)
                ·
                  refine ⟨3004206887802120301026593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2002804591868080200684395 3004206887802120301026593)
                  ·
                    refine ⟨2253155165851590225769945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3004206887802120301026593 2253155165851590225769945)
                    ·
                      refine ⟨1689866374388692669327459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2253155165851590225769945 1689866374388692669327459)
                      ·
                        rfl

theorem cell23_3291003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 1, 2, 2].length) (baseStart_3291003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291003 prefixEnd_3291003 := by exact prefixLift 3291003
  have htrace : WordTrace (prefixWord ++ tailWord_3291003) baseStart_3291003 baseEnd_3291003 := by
    simpa [prefixWord, tailWord_3291003, baseEnd_3291003] using wordTrace_append hprefix tailTrace_3291003
  have hstable : (prefixWord ++ tailWord_3291003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291003).length < 2 ^ (prefixWord ++ tailWord_3291003).sum := by decide
  have hdescent : baseEnd_3291003 < baseStart_3291003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291009 : List Nat := [1, 2, 4, 4, 1, 11]
def baseStart_3291009 : Nat := 118140960795 + 3291009 * 2 ^ 59
def prefixEnd_3291009 : Nat := 4983230072969 + 3 ^ 40 * 3291009 * 2
def baseEnd_3291009 : Nat := 6954195289187735168117

theorem tailTrace_3291009 : CollatzResearch.WordTrace tailWord_3291009 prefixEnd_3291009 6954195289187735168117 := by
  unfold tailWord_3291009
  simp only [CollatzResearch.WordTrace]
  refine ⟨120032959334243927434460081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80021972889495951622973387 120032959334243927434460081)
  ·
    refine ⟨90024719500682945575845061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120032959334243927434460081 90024719500682945575845061)
    ·
      refine ⟨16879634906378052295470949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90024719500682945575845061 16879634906378052295470949)
      ·
        refine ⟨3164931544945884805400803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16879634906378052295470949 3164931544945884805400803)
        ·
          refine ⟨4747397317418827208101205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3164931544945884805400803 4747397317418827208101205)
          ·
            refine ⟨6954195289187735168117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4747397317418827208101205 6954195289187735168117)
            ·
              rfl

theorem cell23_3291009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 11].length) (baseStart_3291009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291009 prefixEnd_3291009 := by exact prefixLift 3291009
  have htrace : WordTrace (prefixWord ++ tailWord_3291009) baseStart_3291009 baseEnd_3291009 := by
    simpa [prefixWord, tailWord_3291009, baseEnd_3291009] using wordTrace_append hprefix tailTrace_3291009
  have hstable : (prefixWord ++ tailWord_3291009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291009).length < 2 ^ (prefixWord ++ tailWord_3291009).sum := by decide
  have hdescent : baseEnd_3291009 < baseStart_3291009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291026 : List Nat := [3, 2, 3, 2, 1, 3, 1, 8]
def baseStart_3291026 : Nat := 118140960795 + 3291026 * 2 ^ 59
def prefixEnd_3291026 : Nat := 4983230072969 + 3 ^ 40 * 3291026 * 2
def baseEnd_3291026 : Nat := 62588080905323928864439

theorem tailTrace_3291026 : CollatzResearch.WordTrace tailWord_3291026 prefixEnd_3291026 62588080905323928864439 := by
  unfold tailWord_3291026
  simp only [CollatzResearch.WordTrace]
  refine ⟨30008394843795584834457233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80022386250121559558552621 30008394843795584834457233)
  ·
    refine ⟨22506296132846688625842925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30008394843795584834457233 22506296132846688625842925)
    ·
      refine ⟨8439861049817508234691097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22506296132846688625842925 8439861049817508234691097)
      ·
        refine ⟨6329895787363131176018323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8439861049817508234691097 6329895787363131176018323)
        ·
          refine ⟨9494843681044696764027485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6329895787363131176018323 9494843681044696764027485)
          ·
            refine ⟨3560566380391761286510307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9494843681044696764027485 3560566380391761286510307)
            ·
              refine ⟨5340849570587641929765461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3560566380391761286510307 5340849570587641929765461)
              ·
                refine ⟨62588080905323928864439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5340849570587641929765461 62588080905323928864439)
                ·
                  rfl

theorem cell23_3291026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 8].length) (baseStart_3291026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291026 prefixEnd_3291026 := by exact prefixLift 3291026
  have htrace : WordTrace (prefixWord ++ tailWord_3291026) baseStart_3291026 baseEnd_3291026 := by
    simpa [prefixWord, tailWord_3291026, baseEnd_3291026] using wordTrace_append hprefix tailTrace_3291026
  have hstable : (prefixWord ++ tailWord_3291026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291026).length < 2 ^ (prefixWord ++ tailWord_3291026).sum := by decide
  have hdescent : baseEnd_3291026 < baseStart_3291026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291030 : List Nat := [5, 3, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_3291030 : Nat := 118140960795 + 3291030 * 2 ^ 59
def prefixEnd_3291030 : Nat := 4983230072969 + 3 ^ 40 * 3291030 * 2
def baseEnd_3291030 : Nat := 563293412788788021229945

theorem tailTrace_3291030 : CollatzResearch.WordTrace tailWord_3291030 prefixEnd_3291030 563293412788788021229945 := by
  unfold tailWord_3291030
  simp only [CollatzResearch.WordTrace]
  refine ⟨7502107829197990501310909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80022483511445232013983029 7502107829197990501310909)
  ·
    refine ⟨2813290435949246437991591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7502107829197990501310909 2813290435949246437991591)
    ·
      refine ⟨4219935653923869656987387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2813290435949246437991591 4219935653923869656987387)
      ·
        refine ⟨6329903480885804485481081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4219935653923869656987387 6329903480885804485481081)
        ·
          refine ⟨4747427610664353364110811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6329903480885804485481081 4747427610664353364110811)
          ·
            refine ⟨7121141415996530046166217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4747427610664353364110811 7121141415996530046166217)
            ·
              refine ⟨5340856061997397534624663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7121141415996530046166217 5340856061997397534624663)
              ·
                refine ⟨8011284092996096301936995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5340856061997397534624663 8011284092996096301936995)
                ·
                  refine ⟨12016926139494144452905493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8011284092996096301936995 12016926139494144452905493)
                  ·
                    refine ⟨563293412788788021229945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12016926139494144452905493 563293412788788021229945)
                    ·
                      rfl

theorem cell23_3291030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_3291030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291030 prefixEnd_3291030 := by exact prefixLift 3291030
  have htrace : WordTrace (prefixWord ++ tailWord_3291030) baseStart_3291030 baseEnd_3291030 := by
    simpa [prefixWord, tailWord_3291030, baseEnd_3291030] using wordTrace_append hprefix tailTrace_3291030
  have hstable : (prefixWord ++ tailWord_3291030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291030).length < 2 ^ (prefixWord ++ tailWord_3291030).sum := by decide
  have hdescent : baseEnd_3291030 < baseStart_3291030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291036 : List Nat := [2, 2, 3, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_3291036 : Nat := 118140960795 + 3291036 * 2 ^ 59
def prefixEnd_3291036 : Nat := 4983230072969 + 3 ^ 40 * 3291036 * 2
def baseEnd_3291036 : Nat := 1689883319250291040214807

theorem tailTrace_3291036 : CollatzResearch.WordTrace tailWord_3291036 prefixEnd_3291036 1689883319250291040214807 := by
  unfold tailWord_3291036
  simp only [CollatzResearch.WordTrace]
  refine ⟨60016972052573055522846481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80022629403430740697128641 60016972052573055522846481)
  ·
    refine ⟨45012729039429791642134861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60016972052573055522846481 45012729039429791642134861)
    ·
      refine ⟨16879773389786171865800573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45012729039429791642134861 16879773389786171865800573)
      ·
        refine ⟨6329915021169814449675215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16879773389786171865800573 6329915021169814449675215)
        ·
          refine ⟨9494872531754721674512823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6329915021169814449675215 9494872531754721674512823)
          ·
            refine ⟨14242308797632082511769235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9494872531754721674512823 14242308797632082511769235)
            ·
              refine ⟨21363463196448123767653853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14242308797632082511769235 21363463196448123767653853)
              ·
                refine ⟨8011298698668046412870195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21363463196448123767653853 8011298698668046412870195)
                ·
                  refine ⟨12016948048002069619305293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8011298698668046412870195 12016948048002069619305293)
                  ·
                    refine ⟨4506355518000776107239485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12016948048002069619305293 4506355518000776107239485)
                    ·
                      refine ⟨1689883319250291040214807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4506355518000776107239485 1689883319250291040214807)
                      ·
                        rfl

theorem cell23_3291036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_3291036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291036 prefixEnd_3291036 := by exact prefixLift 3291036
  have htrace : WordTrace (prefixWord ++ tailWord_3291036) baseStart_3291036 baseEnd_3291036 := by
    simpa [prefixWord, tailWord_3291036, baseEnd_3291036] using wordTrace_append hprefix tailTrace_3291036
  have hstable : (prefixWord ++ tailWord_3291036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291036).length < 2 ^ (prefixWord ++ tailWord_3291036).sum := by decide
  have hdescent : baseEnd_3291036 < baseStart_3291036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291052 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 6, 6]
def baseStart_3291052 : Nat := 118140960795 + 3291052 * 2 ^ 59
def prefixEnd_3291052 : Nat := 4983230072969 + 3 ^ 40 * 3291052 * 2
def baseEnd_3291052 : Nat := 563297178313587659204911

theorem tailTrace_3291052 : CollatzResearch.WordTrace tailWord_3291052 prefixEnd_3291052 563297178313587659204911 := by
  unfold tailWord_3291052
  simp only [CollatzResearch.WordTrace]
  refine ⟨60017263836544072889137705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80023018448725430518850273 60017263836544072889137705)
  ·
    refine ⟨45012947877408054666853279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60017263836544072889137705 45012947877408054666853279)
    ·
      refine ⟨67519421816112082000279919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45012947877408054666853279 67519421816112082000279919)
      ·
        refine ⟨101279132724168123000419879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67519421816112082000279919 101279132724168123000419879)
        ·
          refine ⟨151918699086252184500629819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101279132724168123000419879 151918699086252184500629819)
          ·
            refine ⟨227878048629378276750944729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151918699086252184500629819 227878048629378276750944729)
            ·
              refine ⟨170908536472033707563208547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227878048629378276750944729 170908536472033707563208547)
              ·
                refine ⟨256362804708050561344812821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170908536472033707563208547 256362804708050561344812821)
                ·
                  refine ⟨12017006470689870063038101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 256362804708050561344812821 12017006470689870063038101)
                  ·
                    refine ⟨563297178313587659204911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12017006470689870063038101 563297178313587659204911)
                    ·
                      rfl

theorem cell23_3291052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_3291052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291052 prefixEnd_3291052 := by exact prefixLift 3291052
  have htrace : WordTrace (prefixWord ++ tailWord_3291052) baseStart_3291052 baseEnd_3291052 := by
    simpa [prefixWord, tailWord_3291052, baseEnd_3291052] using wordTrace_append hprefix tailTrace_3291052
  have hstable : (prefixWord ++ tailWord_3291052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291052).length < 2 ^ (prefixWord ++ tailWord_3291052).sum := by decide
  have hdescent : baseEnd_3291052 < baseStart_3291052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291054 : List Nat := [4, 1, 5, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_3291054 : Nat := 118140960795 + 3291054 * 2 ^ 59
def prefixEnd_3291054 : Nat := 4983230072969 + 3 ^ 40 * 3291054 * 2
def baseEnd_3291054 : Nat := 1689892561902071969789725

theorem tailTrace_3291054 : CollatzResearch.WordTrace tailWord_3291054 prefixEnd_3291054 1689892561902071969789725 := by
  unfold tailWord_3291054
  simp only [CollatzResearch.WordTrace]
  refine ⟨15004325077385112514981027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80023067079387266746565477 15004325077385112514981027)
  ·
    refine ⟨22506487616077668772471541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15004325077385112514981027 22506487616077668772471541)
    ·
      refine ⟨2109983214007281447419207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22506487616077668772471541 2109983214007281447419207)
      ·
        refine ⟨3164974821010922171128811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2109983214007281447419207 3164974821010922171128811)
        ·
          refine ⟨4747462231516383256693217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3164974821010922171128811 4747462231516383256693217)
          ·
            refine ⟨3560596673637287442519913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4747462231516383256693217 3560596673637287442519913)
            ·
              refine ⟨2670447505227965581889935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3560596673637287442519913 2670447505227965581889935)
              ·
                refine ⟨4005671257841948372834903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2670447505227965581889935 4005671257841948372834903)
                ·
                  refine ⟨6008506886762922559252355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4005671257841948372834903 6008506886762922559252355)
                  ·
                    refine ⟨9012760330144383838878533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6008506886762922559252355 9012760330144383838878533)
                    ·
                      refine ⟨1689892561902071969789725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9012760330144383838878533 1689892561902071969789725)
                      ·
                        rfl

theorem cell23_3291054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_3291054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291054 prefixEnd_3291054 := by exact prefixLift 3291054
  have htrace : WordTrace (prefixWord ++ tailWord_3291054) baseStart_3291054 baseEnd_3291054 := by
    simpa [prefixWord, tailWord_3291054, baseEnd_3291054] using wordTrace_append hprefix tailTrace_3291054
  have hstable : (prefixWord ++ tailWord_3291054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291054).length < 2 ^ (prefixWord ++ tailWord_3291054).sum := by decide
  have hdescent : baseEnd_3291054 < baseStart_3291054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291069 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 2, 6]
def baseStart_3291069 : Nat := 118140960795 + 3291069 * 2 ^ 59
def prefixEnd_3291069 : Nat := 4983230072969 + 3 ^ 40 * 3291069 * 2
def baseEnd_3291069 : Nat := 563300088037296470367385

theorem tailTrace_3291069 : CollatzResearch.WordTrace tailWord_3291069 prefixEnd_3291069 563300088037296470367385 := by
  unfold tailWord_3291069
  simp only [CollatzResearch.WordTrace]
  refine ⟨120035147714026557681644261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80023431809351038454429507 120035147714026557681644261)
  ·
    refine ⟨22506590196379979565308299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120035147714026557681644261 22506590196379979565308299)
    ·
      refine ⟨33759885294569969347962449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22506590196379979565308299 33759885294569969347962449)
      ·
        refine ⟨25319913970927477010971837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33759885294569969347962449 25319913970927477010971837)
        ·
          refine ⟨9494967739097803879114439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25319913970927477010971837 9494967739097803879114439)
          ·
            refine ⟨14242451608646705818671659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9494967739097803879114439 14242451608646705818671659)
            ·
              refine ⟨21363677412970058728007489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14242451608646705818671659 21363677412970058728007489)
              ·
                refine ⟨16022758059727544046005617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21363677412970058728007489 16022758059727544046005617)
                ·
                  refine ⟨12017068544795658034504213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16022758059727544046005617 12017068544795658034504213)
                  ·
                    refine ⟨563300088037296470367385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12017068544795658034504213 563300088037296470367385)
                    ·
                      rfl

theorem cell23_3291069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_3291069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291069 prefixEnd_3291069 := by exact prefixLift 3291069
  have htrace : WordTrace (prefixWord ++ tailWord_3291069) baseStart_3291069 baseEnd_3291069 := by
    simpa [prefixWord, tailWord_3291069, baseEnd_3291069] using wordTrace_append hprefix tailTrace_3291069
  have hstable : (prefixWord ++ tailWord_3291069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291069).length < 2 ^ (prefixWord ++ tailWord_3291069).sum := by decide
  have hdescent : baseEnd_3291069 < baseStart_3291069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291070 : List Nat := [4, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_3291070 : Nat := 118140960795 + 3291070 * 2 ^ 59
def prefixEnd_3291070 : Nat := 4983230072969 + 3 ^ 40 * 3291070 * 2
def baseEnd_3291070 : Nat := 1689900777592543907189651

theorem tailTrace_3291070 : CollatzResearch.WordTrace tailWord_3291070 prefixEnd_3291070 1689900777592543907189651 := by
  unfold tailWord_3291070
  simp only [CollatzResearch.WordTrace]
  refine ⟨15004398023377866856553833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80023456124681956568287109 15004398023377866856553833)
  ·
    refine ⟨11253298517533400142415375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15004398023377866856553833 11253298517533400142415375)
    ·
      refine ⟨16879947776300100213623063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11253298517533400142415375 16879947776300100213623063)
      ·
        refine ⟨25319921664450150320434595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16879947776300100213623063 25319921664450150320434595)
        ·
          refine ⟨37979882496675225480651893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25319921664450150320434595 37979882496675225480651893)
          ·
            refine ⟨3560613984063302388811115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37979882496675225480651893 3560613984063302388811115)
            ·
              refine ⟨5340920976094953583216673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3560613984063302388811115 5340920976094953583216673)
              ·
                refine ⟨4005690732071215187412505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5340920976094953583216673 4005690732071215187412505)
                ·
                  refine ⟨3004268049053411390559379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4005690732071215187412505 3004268049053411390559379)
                  ·
                    refine ⟨4506402073580117085839069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3004268049053411390559379 4506402073580117085839069)
                    ·
                      refine ⟨1689900777592543907189651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4506402073580117085839069 1689900777592543907189651)
                      ·
                        rfl

theorem cell23_3291070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_3291070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291070 prefixEnd_3291070 := by exact prefixLift 3291070
  have htrace : WordTrace (prefixWord ++ tailWord_3291070) baseStart_3291070 baseEnd_3291070 := by
    simpa [prefixWord, tailWord_3291070, baseEnd_3291070] using wordTrace_append hprefix tailTrace_3291070
  have hstable : (prefixWord ++ tailWord_3291070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291070).length < 2 ^ (prefixWord ++ tailWord_3291070).sum := by decide
  have hdescent : baseEnd_3291070 < baseStart_3291070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291093 : List Nat := [1, 3, 2, 3, 2, 1, 3, 1, 1, 4, 2]
def baseStart_3291093 : Nat := 118140960795 + 3291093 * 2 ^ 59
def prefixEnd_3291093 : Nat := 4983230072969 + 3 ^ 40 * 3291093 * 2
def baseEnd_3291093 : Nat := 1689912587647597317202045

theorem tailTrace_3291093 : CollatzResearch.WordTrace tailWord_3291093 prefixEnd_3291093 1689912587647597317202045 := by
  unfold tailWord_3291093
  simp only [CollatzResearch.WordTrace]
  refine ⟨120036023065939609780517933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80024015377293073187011955 120036023065939609780517933)
  ·
    refine ⟨45013508649727353667694225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120036023065939609780517933 45013508649727353667694225)
    ·
      refine ⟨33760131487295515250770669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45013508649727353667694225 33760131487295515250770669)
      ·
        refine ⟨12660049307735818219039001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33760131487295515250770669 12660049307735818219039001)
        ·
          refine ⟨9495036980801863664279251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12660049307735818219039001 9495036980801863664279251)
          ·
            refine ⟨14242555471202795496418877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9495036980801863664279251 14242555471202795496418877)
            ·
              refine ⟨5340958301701048311157079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14242555471202795496418877 5340958301701048311157079)
              ·
                refine ⟨8011437452551572466735619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5340958301701048311157079 8011437452551572466735619)
                ·
                  refine ⟨12017156178827358700103429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8011437452551572466735619 12017156178827358700103429)
                  ·
                    refine ⟨2253216783530129756269393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12017156178827358700103429 2253216783530129756269393)
                    ·
                      refine ⟨1689912587647597317202045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2253216783530129756269393 1689912587647597317202045)
                      ·
                        rfl

theorem cell23_3291093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_3291093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291093 prefixEnd_3291093 := by exact prefixLift 3291093
  have htrace : WordTrace (prefixWord ++ tailWord_3291093) baseStart_3291093 baseEnd_3291093 := by
    simpa [prefixWord, tailWord_3291093, baseEnd_3291093] using wordTrace_append hprefix tailTrace_3291093
  have hstable : (prefixWord ++ tailWord_3291093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291093).length < 2 ^ (prefixWord ++ tailWord_3291093).sum := by decide
  have hdescent : baseEnd_3291093 < baseStart_3291093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291129 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 4, 5]
def baseStart_3291129 : Nat := 118140960795 + 3291129 * 2 ^ 59
def prefixEnd_3291129 : Nat := 4983230072969 + 3 ^ 40 * 3291129 * 2
def baseEnd_3291129 : Nat := 563310357650386392117293

theorem tailTrace_3291129 : CollatzResearch.WordTrace tailWord_3291129 prefixEnd_3291129 563310357650386392117293 := by
  unfold tailWord_3291129
  simp only [CollatzResearch.WordTrace]
  refine ⟨120037336093809187928828441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80024890729206125285885627 120037336093809187928828441)
  ·
    refine ⟨90028002070356890946621331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120037336093809187928828441 90028002070356890946621331)
    ·
      refine ⟨135042003105535336419931997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90028002070356890946621331 135042003105535336419931997)
      ·
        refine ⟨50640751164575751157474499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135042003105535336419931997 50640751164575751157474499)
        ·
          refine ⟨75961126746863626736211749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50640751164575751157474499 75961126746863626736211749)
          ·
            refine ⟨14242711265036930013039703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75961126746863626736211749 14242711265036930013039703)
            ·
              refine ⟨21364066897555395019559555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14242711265036930013039703 21364066897555395019559555)
              ·
                refine ⟨32046100346333092529339333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21364066897555395019559555 32046100346333092529339333)
                ·
                  refine ⟨6008643814937454849251125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32046100346333092529339333 6008643814937454849251125)
                  ·
                    refine ⟨563310357650386392117293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6008643814937454849251125 563310357650386392117293)
                    ·
                      rfl

theorem cell23_3291129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 5].length) (baseStart_3291129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291129 prefixEnd_3291129 := by exact prefixLift 3291129
  have htrace : WordTrace (prefixWord ++ tailWord_3291129) baseStart_3291129 baseEnd_3291129 := by
    simpa [prefixWord, tailWord_3291129, baseEnd_3291129] using wordTrace_append hprefix tailTrace_3291129
  have hstable : (prefixWord ++ tailWord_3291129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291129).length < 2 ^ (prefixWord ++ tailWord_3291129).sum := by decide
  have hdescent : baseEnd_3291129 < baseStart_3291129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291189 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 8]
def baseStart_3291189 : Nat := 118140960795 + 3291189 * 2 ^ 59
def prefixEnd_3291189 : Nat := 4983230072969 + 3 ^ 40 * 3291189 * 2
def baseEnd_3291189 : Nat := 187773542421158771289067

theorem tailTrace_3291189 : CollatzResearch.WordTrace tailWord_3291189 prefixEnd_3291189 187773542421158771289067 := by
  unfold tailWord_3291189
  simp only [CollatzResearch.WordTrace]
  refine ⟨120039524473591818176012621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80026349649061212117341747 120039524473591818176012621)
  ·
    refine ⟨45014821677596931816004733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120039524473591818176012621 45014821677596931816004733)
    ·
      refine ⟨16880558129098849431001775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45014821677596931816004733 16880558129098849431001775)
      ·
        refine ⟨25320837193648274146502663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16880558129098849431001775 25320837193648274146502663)
        ·
          refine ⟨37981255790472411219753995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25320837193648274146502663 37981255790472411219753995)
          ·
            refine ⟨56971883685708616829630993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37981255790472411219753995 56971883685708616829630993)
            ·
              refine ⟨42728912764281462622223245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56971883685708616829630993 42728912764281462622223245)
              ·
                refine ⟨16023342286605548483333717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42728912764281462622223245 16023342286605548483333717)
                ·
                  refine ⟨187773542421158771289067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16023342286605548483333717 187773542421158771289067)
                  ·
                    rfl

theorem cell23_3291189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 8].length) (baseStart_3291189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291189 prefixEnd_3291189 := by exact prefixLift 3291189
  have htrace : WordTrace (prefixWord ++ tailWord_3291189) baseStart_3291189 baseEnd_3291189 := by
    simpa [prefixWord, tailWord_3291189, baseEnd_3291189] using wordTrace_append hprefix tailTrace_3291189
  have hstable : (prefixWord ++ tailWord_3291189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291189).length < 2 ^ (prefixWord ++ tailWord_3291189).sum := by decide
  have hdescent : baseEnd_3291189 < baseStart_3291189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291219 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 7, 5]
def baseStart_3291219 : Nat := 118140960795 + 3291219 * 2 ^ 59
def prefixEnd_3291219 : Nat := 4983230072969 + 3 ^ 40 * 3291219 * 2
def baseEnd_3291219 : Nat := 563325762070021274742155

theorem tailTrace_3291219 : CollatzResearch.WordTrace tailWord_3291219 prefixEnd_3291219 563325762070021274742155 := by
  unfold tailWord_3291219
  simp only [CollatzResearch.WordTrace]
  refine ⟨120040618663483133299604711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80027079108988755533069807 120040618663483133299604711)
  ·
    refine ⟨180060927995224699949407067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120040618663483133299604711 180060927995224699949407067)
    ·
      refine ⟨270091391992837049924110601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180060927995224699949407067 270091391992837049924110601)
      ·
        refine ⟨202568543994627787443082951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270091391992837049924110601 202568543994627787443082951)
        ·
          refine ⟨303852815991941681164624427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202568543994627787443082951 303852815991941681164624427)
          ·
            refine ⟨455779223987912521746936641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303852815991941681164624427 455779223987912521746936641)
            ·
              refine ⟨341834417990934391310202481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455779223987912521746936641 341834417990934391310202481)
              ·
                refine ⟨256375813493200793482651861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 341834417990934391310202481 256375813493200793482651861)
                ·
                  refine ⟨6008808128746893597249653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 256375813493200793482651861 6008808128746893597249653)
                  ·
                    refine ⟨563325762070021274742155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6008808128746893597249653 563325762070021274742155)
                    ·
                      rfl

theorem cell23_3291219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 5].length) (baseStart_3291219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291219 prefixEnd_3291219 := by exact prefixLift 3291219
  have htrace : WordTrace (prefixWord ++ tailWord_3291219) baseStart_3291219 baseEnd_3291219 := by
    simpa [prefixWord, tailWord_3291219, baseEnd_3291219] using wordTrace_append hprefix tailTrace_3291219
  have hstable : (prefixWord ++ tailWord_3291219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291219).length < 2 ^ (prefixWord ++ tailWord_3291219).sum := by decide
  have hdescent : baseEnd_3291219 < baseStart_3291219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291250 : List Nat := [3, 2, 1, 2, 2, 3, 2, 1, 3, 1, 3]
def baseStart_3291250 : Nat := 118140960795 + 3291250 * 2 ^ 59
def prefixEnd_3291250 : Nat := 4983230072969 + 3 ^ 40 * 3291250 * 2
def baseEnd_3291250 : Nat := 1689993204110353202938823

theorem tailTrace_3291250 : CollatzResearch.WordTrace tailWord_3291250 prefixEnd_3291250 1689993204110353202938823 := by
  unfold tailWord_3291250
  simp only [CollatzResearch.WordTrace]
  refine ⟨30010437331592706398495801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80027832884247217062655469 30010437331592706398495801)
  ·
    refine ⟨22507827998694529798871851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30010437331592706398495801 22507827998694529798871851)
    ·
      refine ⟨33761741998041794698307777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22507827998694529798871851 33761741998041794698307777)
      ·
        refine ⟨25321306498531346023730833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33761741998041794698307777 25321306498531346023730833)
        ·
          refine ⟨18990979873898509517798125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25321306498531346023730833 18990979873898509517798125)
          ·
            refine ⟨7121617452711941069174297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18990979873898509517798125 7121617452711941069174297)
            ·
              refine ⟨5341213089533955801880723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7121617452711941069174297 5341213089533955801880723)
              ·
                refine ⟨8011819634300933702821085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5341213089533955801880723 8011819634300933702821085)
                ·
                  refine ⟨3004432362862850138557907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8011819634300933702821085 3004432362862850138557907)
                  ·
                    refine ⟨4506648544294275207836861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3004432362862850138557907 4506648544294275207836861)
                    ·
                      refine ⟨1689993204110353202938823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4506648544294275207836861 1689993204110353202938823)
                      ·
                        rfl

theorem cell23_3291250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_3291250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291250 prefixEnd_3291250 := by exact prefixLift 3291250
  have htrace : WordTrace (prefixWord ++ tailWord_3291250) baseStart_3291250 baseEnd_3291250 := by
    simpa [prefixWord, tailWord_3291250, baseEnd_3291250] using wordTrace_append hprefix tailTrace_3291250
  have hstable : (prefixWord ++ tailWord_3291250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291250).length < 2 ^ (prefixWord ++ tailWord_3291250).sum := by decide
  have hdescent : baseEnd_3291250 < baseStart_3291250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291273 : List Nat := [1, 2, 1, 1, 4, 2, 4, 2, 1, 1, 4]
def baseStart_3291273 : Nat := 118140960795 + 3291273 * 2 ^ 59
def prefixEnd_3291273 : Nat := 4983230072969 + 3 ^ 40 * 3291273 * 2
def baseEnd_3291273 : Nat := 1690005014165406612951217

theorem tailTrace_3291273 : CollatzResearch.WordTrace tailWord_3291273 prefixEnd_3291273 1690005014165406612951217 := by
  unfold tailWord_3291273
  simp only [CollatzResearch.WordTrace]
  refine ⟨120042588205287500522070473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80028392136858333681380315 120042588205287500522070473)
  ·
    refine ⟨90031941153965625391552855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120042588205287500522070473 90031941153965625391552855)
    ·
      refine ⟨135047911730948438087329283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90031941153965625391552855 135047911730948438087329283)
      ·
        refine ⟨202571867596422657130993925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135047911730948438087329283 202571867596422657130993925)
        ·
          refine ⟨37982225174329248212061361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202571867596422657130993925 37982225174329248212061361)
          ·
            refine ⟨28486668880746936159046021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37982225174329248212061361 28486668880746936159046021)
            ·
              refine ⟨5341250415140050529821129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28486668880746936159046021 5341250415140050529821129)
              ·
                refine ⟨4005937811355037897365847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5341250415140050529821129 4005937811355037897365847)
                ·
                  refine ⟨6008906717032556846048771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4005937811355037897365847 6008906717032556846048771)
                  ·
                    refine ⟨9013360075548835269073157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6008906717032556846048771 9013360075548835269073157)
                    ·
                      refine ⟨1690005014165406612951217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9013360075548835269073157 1690005014165406612951217)
                      ·
                        rfl

theorem cell23_3291273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 1, 4].length) (baseStart_3291273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291273 prefixEnd_3291273 := by exact prefixLift 3291273
  have htrace : WordTrace (prefixWord ++ tailWord_3291273) baseStart_3291273 baseEnd_3291273 := by
    simpa [prefixWord, tailWord_3291273, baseEnd_3291273] using wordTrace_append hprefix tailTrace_3291273
  have hstable : (prefixWord ++ tailWord_3291273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291273).length < 2 ^ (prefixWord ++ tailWord_3291273).sum := by decide
  have hdescent : baseEnd_3291273 < baseStart_3291273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291293 : List Nat := [1, 4, 2, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_3291293 : Nat := 118140960795 + 3291293 * 2 ^ 59
def prefixEnd_3291293 : Nat := 4983230072969 + 3 ^ 40 * 3291293 * 2
def baseEnd_3291293 : Nat := 1690015283778496534701125

theorem tailTrace_3291293 : CollatzResearch.WordTrace tailWord_3291293 prefixEnd_3291293 1690015283778496534701125 := by
  unfold tailWord_3291293
  simp only [CollatzResearch.WordTrace]
  refine ⟨120043317665215043937798533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80028878443476695958532355 120043317665215043937798533)
  ·
    refine ⟨22508122062227820738337225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120043317665215043937798533 22508122062227820738337225)
    ·
      refine ⟨16881091546670865553752919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22508122062227820738337225 16881091546670865553752919)
      ·
        refine ⟨25321637320006298330629379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16881091546670865553752919 25321637320006298330629379)
        ·
          refine ⟨37982455980009447495944069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25321637320006298330629379 37982455980009447495944069)
          ·
            refine ⟨7121710496251771405489513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37982455980009447495944069 7121710496251771405489513)
            ·
              refine ⟨5341282872188828554117135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7121710496251771405489513 5341282872188828554117135)
              ·
                refine ⟨8011924308283242831175703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5341282872188828554117135 8011924308283242831175703)
                ·
                  refine ⟨12017886462424864246763555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8011924308283242831175703 12017886462424864246763555)
                  ·
                    refine ⟨18026829693637296370145333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12017886462424864246763555 18026829693637296370145333)
                    ·
                      refine ⟨1690015283778496534701125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18026829693637296370145333 1690015283778496534701125)
                      ·
                        rfl

theorem cell23_3291293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_3291293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291293 prefixEnd_3291293 := by exact prefixLift 3291293
  have htrace : WordTrace (prefixWord ++ tailWord_3291293) baseStart_3291293 baseEnd_3291293 := by
    simpa [prefixWord, tailWord_3291293, baseEnd_3291293] using wordTrace_append hprefix tailTrace_3291293
  have hstable : (prefixWord ++ tailWord_3291293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291293).length < 2 ^ (prefixWord ++ tailWord_3291293).sum := by decide
  have hdescent : baseEnd_3291293 < baseStart_3291293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291296 : List Nat := [2, 1, 1, 4, 2, 4, 9]
def baseStart_3291296 : Nat := 118140960795 + 3291296 * 2 ^ 59
def prefixEnd_3291296 : Nat := 4983230072969 + 3 ^ 40 * 3291296 * 2
def baseEnd_3291296 : Nat := 20864405237289629913131

theorem tailTrace_3291296 : CollatzResearch.WordTrace tailWord_3291296 prefixEnd_3291296 20864405237289629913131 := by
  unfold tailWord_3291296
  simp only [CollatzResearch.WordTrace]
  refine ⟨60021713542102087725078871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80028951389469450300105161 60021713542102087725078871)
  ·
    refine ⟨90032570313153131587618307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60021713542102087725078871 90032570313153131587618307)
    ·
      refine ⟨135048855469729697381427461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90032570313153131587618307 135048855469729697381427461)
      ·
        refine ⟨25321660400574318259017649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135048855469729697381427461 25321660400574318259017649)
        ·
          refine ⟨18991245300430738694263237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25321660400574318259017649 18991245300430738694263237)
          ·
            refine ⟨3560858493830763505174357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18991245300430738694263237 3560858493830763505174357)
            ·
              refine ⟨20864405237289629913131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3560858493830763505174357 20864405237289629913131)
              ·
                rfl

theorem cell23_3291296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 9].length) (baseStart_3291296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291296 prefixEnd_3291296 := by exact prefixLift 3291296
  have htrace : WordTrace (prefixWord ++ tailWord_3291296) baseStart_3291296 baseEnd_3291296 := by
    simpa [prefixWord, tailWord_3291296, baseEnd_3291296] using wordTrace_append hprefix tailTrace_3291296
  have hstable : (prefixWord ++ tailWord_3291296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291296).length < 2 ^ (prefixWord ++ tailWord_3291296).sum := by decide
  have hdescent : baseEnd_3291296 < baseStart_3291296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291313 : List Nat := [1, 2, 2, 5, 2, 1, 2, 8]
def baseStart_3291313 : Nat := 118140960795 + 3291313 * 2 ^ 59
def prefixEnd_3291313 : Nat := 4983230072969 + 3 ^ 40 * 3291313 * 2
def baseEnd_3291313 : Nat := 62593539014503202090779

theorem tailTrace_3291313 : CollatzResearch.WordTrace tailWord_3291313 prefixEnd_3291313 62593539014503202090779 := by
  unfold tailWord_3291313
  simp only [CollatzResearch.WordTrace]
  refine ⟨120044047125142587353526593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80029364750095058235684395 120044047125142587353526593)
  ·
    refine ⟨90033035343856940515144945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120044047125142587353526593 90033035343856940515144945)
    ·
      refine ⟨67524776507892705386358709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90033035343856940515144945 67524776507892705386358709)
      ·
        refine ⟨6330447797614941129971129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67524776507892705386358709 6330447797614941129971129)
        ·
          refine ⟨4747835848211205847478347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6330447797614941129971129 4747835848211205847478347)
          ·
            refine ⟨7121753772316808771217521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4747835848211205847478347 7121753772316808771217521)
            ·
              refine ⟨5341315329237606578413141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7121753772316808771217521 5341315329237606578413141)
              ·
                refine ⟨62593539014503202090779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5341315329237606578413141 62593539014503202090779)
                ·
                  rfl

theorem cell23_3291313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 8].length) (baseStart_3291313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291313 prefixEnd_3291313 := by exact prefixLift 3291313
  have htrace : WordTrace (prefixWord ++ tailWord_3291313) baseStart_3291313 baseEnd_3291313 := by
    simpa [prefixWord, tailWord_3291313, baseEnd_3291313] using wordTrace_append hprefix tailTrace_3291313
  have hstable : (prefixWord ++ tailWord_3291313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291313).length < 2 ^ (prefixWord ++ tailWord_3291313).sum := by decide
  have hdescent : baseEnd_3291313 < baseStart_3291313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291317 : List Nat := [1, 3, 3, 4, 1, 1, 1, 3, 2, 4]
def baseStart_3291317 : Nat := 118140960795 + 3291317 * 2 ^ 59
def prefixEnd_3291317 : Nat := 4983230072969 + 3 ^ 40 * 3291317 * 2
def baseEnd_3291317 : Nat := 563342535771401480267005

theorem tailTrace_3291317 : CollatzResearch.WordTrace tailWord_3291317 prefixEnd_3291317 563342535771401480267005 := by
  unfold tailWord_3291317
  simp only [CollatzResearch.WordTrace]
  refine ⟨120044193017128096036672205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80029462011418730691114803 120044193017128096036672205)
  ·
    refine ⟨45016572381423036013752077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120044193017128096036672205 45016572381423036013752077)
    ·
      refine ⟨16881214643033638505157029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45016572381423036013752077 16881214643033638505157029)
      ·
        refine ⟨3165227745568807219716943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16881214643033638505157029 3165227745568807219716943)
        ·
          refine ⟨4747841618353210829575415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3165227745568807219716943 4747841618353210829575415)
          ·
            refine ⟨7121762427529816244363123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4747841618353210829575415 7121762427529816244363123)
            ·
              refine ⟨10682643641294724366544685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7121762427529816244363123 10682643641294724366544685)
              ·
                refine ⟨4005991365485521637454257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10682643641294724366544685 4005991365485521637454257)
                ·
                  refine ⟨3004493524114141228090693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4005991365485521637454257 3004493524114141228090693)
                  ·
                    refine ⟨563342535771401480267005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3004493524114141228090693 563342535771401480267005)
                    ·
                      rfl

theorem cell23_3291317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_3291317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291317 prefixEnd_3291317 := by exact prefixLift 3291317
  have htrace : WordTrace (prefixWord ++ tailWord_3291317) baseStart_3291317 baseEnd_3291317 := by
    simpa [prefixWord, tailWord_3291317, baseEnd_3291317] using wordTrace_append hprefix tailTrace_3291317
  have hstable : (prefixWord ++ tailWord_3291317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291317).length < 2 ^ (prefixWord ++ tailWord_3291317).sum := by decide
  have hdescent : baseEnd_3291317 < baseStart_3291317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291330 : List Nat := [3, 5, 1, 1, 1, 1, 2, 9]
def baseStart_3291330 : Nat := 118140960795 + 3291330 * 2 ^ 59
def prefixEnd_3291330 : Nat := 4983230072969 + 3 ^ 40 * 3291330 * 2
def baseEnd_3291330 : Nat := 62593862317137514442165

theorem tailTrace_3291330 : CollatzResearch.WordTrace tailWord_3291330 prefixEnd_3291330 62593862317137514442165 := by
  unfold tailWord_3291330
  simp only [CollatzResearch.WordTrace]
  refine ⟨30011166791520249814223861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80029778110720666171263629 30011166791520249814223861)
  ·
    refine ⟨2813546886705023420083487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30011166791520249814223861 2813546886705023420083487)
    ·
      refine ⟨4220320330057535130125231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2813546886705023420083487 4220320330057535130125231)
      ·
        refine ⟨6330480495086302695187847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4220320330057535130125231 6330480495086302695187847)
        ·
          refine ⟨9495720742629454042781771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6330480495086302695187847 9495720742629454042781771)
          ·
            refine ⟨14243581113944181064172657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9495720742629454042781771 14243581113944181064172657)
            ·
              refine ⟨10682685835458135798129493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14243581113944181064172657 10682685835458135798129493)
              ·
                refine ⟨62593862317137514442165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10682685835458135798129493 62593862317137514442165)
                ·
                  rfl

theorem cell23_3291330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 9].length) (baseStart_3291330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291330 prefixEnd_3291330 := by exact prefixLift 3291330
  have htrace : WordTrace (prefixWord ++ tailWord_3291330) baseStart_3291330 baseEnd_3291330 := by
    simpa [prefixWord, tailWord_3291330, baseEnd_3291330] using wordTrace_append hprefix tailTrace_3291330
  have hstable : (prefixWord ++ tailWord_3291330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291330).length < 2 ^ (prefixWord ++ tailWord_3291330).sum := by decide
  have hdescent : baseEnd_3291330 < baseStart_3291330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291357 : List Nat := [1, 4, 3, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_3291357 : Nat := 118140960795 + 3291357 * 2 ^ 59
def prefixEnd_3291357 : Nat := 4983230072969 + 3 ^ 40 * 3291357 * 2
def baseEnd_3291357 : Nat := 1690048146540384284300831

theorem tailTrace_3291357 : CollatzResearch.WordTrace tailWord_3291357 prefixEnd_3291357 1690048146540384284300831 := by
  unfold tailWord_3291357
  simp only [CollatzResearch.WordTrace]
  refine ⟨120045651936983182868128325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80030434624655455245418883 120045651936983182868128325)
  ·
    refine ⟨22508559738184346787774061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120045651936983182868128325 22508559738184346787774061)
    ·
      refine ⟨8440709901819130045415273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22508559738184346787774061 8440709901819130045415273)
      ·
        refine ⟨6330532426364347534061455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8440709901819130045415273 6330532426364347534061455)
        ·
          refine ⟨9495798639546521301092183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6330532426364347534061455 9495798639546521301092183)
          ·
            refine ⟨14243697959319781951638275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9495798639546521301092183 14243697959319781951638275)
            ·
              refine ⟨21365546938979672927457413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14243697959319781951638275 21365546938979672927457413)
              ·
                refine ⟨4006040051058688673898265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21365546938979672927457413 4006040051058688673898265)
                ·
                  refine ⟨3004530038294016505423699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4006040051058688673898265 3004530038294016505423699)
                  ·
                    refine ⟨4506795057441024758135549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3004530038294016505423699 4506795057441024758135549)
                    ·
                      refine ⟨1690048146540384284300831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4506795057441024758135549 1690048146540384284300831)
                      ·
                        rfl

theorem cell23_3291357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_3291357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291357 prefixEnd_3291357 := by exact prefixLift 3291357
  have htrace : WordTrace (prefixWord ++ tailWord_3291357) baseStart_3291357 baseEnd_3291357 := by
    simpa [prefixWord, tailWord_3291357, baseEnd_3291357] using wordTrace_append hprefix tailTrace_3291357
  have hstable : (prefixWord ++ tailWord_3291357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291357).length < 2 ^ (prefixWord ++ tailWord_3291357).sum := by decide
  have hdescent : baseEnd_3291357 < baseStart_3291357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291386 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 9]
def baseStart_3291386 : Nat := 118140960795 + 3291386 * 2 ^ 59
def prefixEnd_3291386 : Nat := 4983230072969 + 3 ^ 40 * 3291386 * 2
def baseEnd_3291386 : Nat := 187784781942151630093133

theorem tailTrace_3291386 : CollatzResearch.WordTrace tailWord_3291386 prefixEnd_3291386 187784781942151630093133 := by
  unfold tailWord_3291386
  simp only [CollatzResearch.WordTrace]
  refine ⟨30011677413469530205233503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80031139769252080547289341 30011677413469530205233503)
  ·
    refine ⟨45017516120204295307850255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30011677413469530205233503 45017516120204295307850255)
    ·
      refine ⟨67526274180306442961775383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45017516120204295307850255 67526274180306442961775383)
      ·
        refine ⟨101289411270459664442663075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67526274180306442961775383 101289411270459664442663075)
        ·
          refine ⟨151934116905689496663994613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101289411270459664442663075 151934116905689496663994613)
          ·
            refine ⟨14243823459908390312249495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151934116905689496663994613 14243823459908390312249495)
            ·
              refine ⟨21365735189862585468374243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14243823459908390312249495 21365735189862585468374243)
              ·
                refine ⟨32048602784793878202561365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21365735189862585468374243 32048602784793878202561365)
                ·
                  refine ⟨187784781942151630093133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32048602784793878202561365 187784781942151630093133)
                  ·
                    rfl

theorem cell23_3291386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 9].length) (baseStart_3291386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291386 prefixEnd_3291386 := by exact prefixLift 3291386
  have htrace : WordTrace (prefixWord ++ tailWord_3291386) baseStart_3291386 baseEnd_3291386 := by
    simpa [prefixWord, tailWord_3291386, baseEnd_3291386] using wordTrace_append hprefix tailTrace_3291386
  have hstable : (prefixWord ++ tailWord_3291386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291386).length < 2 ^ (prefixWord ++ tailWord_3291386).sum := by decide
  have hdescent : baseEnd_3291386 < baseStart_3291386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291413 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 2, 3, 3]
def baseStart_3291413 : Nat := 118140960795 + 3291413 * 2 ^ 59
def prefixEnd_3291413 : Nat := 4983230072969 + 3 ^ 40 * 3291413 * 2
def baseEnd_3291413 : Nat := 1690076901457036065200573

theorem tailTrace_3291413 : CollatzResearch.WordTrace tailWord_3291413 prefixEnd_3291413 1690076901457036065200573 := by
  unfold tailWord_3291413
  simp only [CollatzResearch.WordTrace]
  refine ⟨120047694424780304432166893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80031796283186869621444595 120047694424780304432166893)
  ·
    refine ⟨45017885409292614162062585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120047694424780304432166893 45017885409292614162062585)
    ·
      refine ⟨33763414056969460621546939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45017885409292614162062585 33763414056969460621546939)
      ·
        refine ⟨50645121085454190932320409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33763414056969460621546939 50645121085454190932320409)
        ·
          refine ⟨37983840814090643199240307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50645121085454190932320409 37983840814090643199240307)
          ·
            refine ⟨56975761221135964798860461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37983840814090643199240307 56975761221135964798860461)
            ·
              refine ⟨21365910457925986799572673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56975761221135964798860461 21365910457925986799572673)
              ·
                refine ⟨16024432843444490099679505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21365910457925986799572673 16024432843444490099679505)
                ·
                  refine ⟨12018324632583367574759629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16024432843444490099679505 12018324632583367574759629)
                  ·
                    refine ⟨4506871737218762840534861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12018324632583367574759629 4506871737218762840534861)
                    ·
                      refine ⟨1690076901457036065200573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4506871737218762840534861 1690076901457036065200573)
                      ·
                        rfl

theorem cell23_3291413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_3291413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291413 prefixEnd_3291413 := by exact prefixLift 3291413
  have htrace : WordTrace (prefixWord ++ tailWord_3291413) baseStart_3291413 baseEnd_3291413 := by
    simpa [prefixWord, tailWord_3291413, baseEnd_3291413] using wordTrace_append hprefix tailTrace_3291413
  have hstable : (prefixWord ++ tailWord_3291413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291413).length < 2 ^ (prefixWord ++ tailWord_3291413).sum := by decide
  have hdescent : baseEnd_3291413 < baseStart_3291413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291470 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2]
def baseStart_3291470 : Nat := 118140960795 + 3291470 * 2 ^ 59
def prefixEnd_3291470 : Nat := 4983230072969 + 3 ^ 40 * 3291470 * 2
def baseEnd_3291470 : Nat := 1690106169854342342187811

theorem tailTrace_3291470 : CollatzResearch.WordTrace tailWord_3291470 prefixEnd_3291470 1690106169854342342187811 := by
  unfold tailWord_3291470
  simp only [CollatzResearch.WordTrace]
  refine ⟨15006221673196725395873983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80033182257049202111327909 15006221673196725395873983)
  ·
    refine ⟨22509332509795088093810975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15006221673196725395873983 22509332509795088093810975)
    ·
      refine ⟨33763998764692632140716463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22509332509795088093810975 33763998764692632140716463)
      ·
        refine ⟨50645998147038948211074695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33763998764692632140716463 50645998147038948211074695)
        ·
          refine ⟨75968997220558422316612043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50645998147038948211074695 75968997220558422316612043)
          ·
            refine ⟨113953495830837633474918065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75968997220558422316612043 113953495830837633474918065)
            ·
              refine ⟨85465121873128225106188549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113953495830837633474918065 85465121873128225106188549)
              ·
                refine ⟨16024710351211542207410353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85465121873128225106188549 16024710351211542207410353)
                ·
                  refine ⟨12018532763408656655557765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16024710351211542207410353 12018532763408656655557765)
                  ·
                    refine ⟨2253474893139123122917081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12018532763408656655557765 2253474893139123122917081)
                    ·
                      refine ⟨1690106169854342342187811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2253474893139123122917081 1690106169854342342187811)
                      ·
                        rfl

theorem cell23_3291470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_3291470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291470 prefixEnd_3291470 := by exact prefixLift 3291470
  have htrace : WordTrace (prefixWord ++ tailWord_3291470) baseStart_3291470 baseEnd_3291470 := by
    simpa [prefixWord, tailWord_3291470, baseEnd_3291470] using wordTrace_append hprefix tailTrace_3291470
  have hstable : (prefixWord ++ tailWord_3291470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291470).length < 2 ^ (prefixWord ++ tailWord_3291470).sum := by decide
  have hdescent : baseEnd_3291470 < baseStart_3291470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291570 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 4, 4]
def baseStart_3291570 : Nat := 118140960795 + 3291570 * 2 ^ 59
def prefixEnd_3291570 : Nat := 4983230072969 + 3 ^ 40 * 3291570 * 2
def baseEnd_3291570 : Nat := 563385839306597316979117

theorem tailTrace_3291570 : CollatzResearch.WordTrace tailWord_3291570 prefixEnd_3291570 563385839306597316979117 := by
  unfold tailWord_3291570
  simp only [CollatzResearch.WordTrace]
  refine ⟨30013355171302880061408041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80035613790141013497088109 30013355171302880061408041)
  ·
    refine ⟨22510016378477160046056031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30013355171302880061408041 22510016378477160046056031)
    ·
      refine ⟨33765024567715740069084047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22510016378477160046056031 33765024567715740069084047)
      ·
        refine ⟨50647536851573610103626071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33765024567715740069084047 50647536851573610103626071)
        ·
          refine ⟨75971305277360415155439107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50647536851573610103626071 75971305277360415155439107)
          ·
            refine ⟨113956957916040622733158661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75971305277360415155439107 113956957916040622733158661)
            ·
              refine ⟨21366929609257616762467249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113956957916040622733158661 21366929609257616762467249)
              ·
                refine ⟨16025197206943212571850437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21366929609257616762467249 16025197206943212571850437)
                ·
                  refine ⟨3004724476301852357221957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16025197206943212571850437 3004724476301852357221957)
                  ·
                    refine ⟨563385839306597316979117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3004724476301852357221957 563385839306597316979117)
                    ·
                      rfl

theorem cell23_3291570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_3291570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291570 prefixEnd_3291570 := by exact prefixLift 3291570
  have htrace : WordTrace (prefixWord ++ tailWord_3291570) baseStart_3291570 baseEnd_3291570 := by
    simpa [prefixWord, tailWord_3291570, baseEnd_3291570] using wordTrace_append hprefix tailTrace_3291570
  have hstable : (prefixWord ++ tailWord_3291570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291570).length < 2 ^ (prefixWord ++ tailWord_3291570).sum := by decide
  have hdescent : baseEnd_3291570 < baseStart_3291570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291577 : List Nat := [1, 2, 1, 4, 3, 2, 1, 3, 1, 1, 4]
def baseStart_3291577 : Nat := 118140960795 + 3291577 * 2 ^ 59
def prefixEnd_3291577 : Nat := 4983230072969 + 3 ^ 40 * 3291577 * 2
def baseEnd_3291577 : Nat := 1690161112284373423549819

theorem tailTrace_3291577 : CollatzResearch.WordTrace tailWord_3291577 prefixEnd_3291577 1690161112284373423549819 := by
  unfold tailWord_3291577
  simp only [CollatzResearch.WordTrace]
  refine ⟨120053675996186160441136985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80035783997457440294091323 120053675996186160441136985)
  ·
    refine ⟨90040256997139620330852739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120053675996186160441136985 90040256997139620330852739)
    ·
      refine ⟨135060385495709430496279109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90040256997139620330852739 135060385495709430496279109)
      ·
        refine ⟨25323822280445518218052333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135060385495709430496279109 25323822280445518218052333)
        ·
          refine ⟨9496433355167069331769625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25323822280445518218052333 9496433355167069331769625)
          ·
            refine ⟨7122325016375301998827219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9496433355167069331769625 7122325016375301998827219)
            ·
              refine ⟨10683487524562952998240829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7122325016375301998827219 10683487524562952998240829)
              ·
                refine ⟨4006307821711107374340311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10683487524562952998240829 4006307821711107374340311)
                ·
                  refine ⟨6009461732566661061510467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4006307821711107374340311 6009461732566661061510467)
                  ·
                    refine ⟨9014192598849991592265701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6009461732566661061510467 9014192598849991592265701)
                    ·
                      refine ⟨1690161112284373423549819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9014192598849991592265701 1690161112284373423549819)
                      ·
                        rfl

theorem cell23_3291577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_3291577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291577 prefixEnd_3291577 := by exact prefixLift 3291577
  have htrace : WordTrace (prefixWord ++ tailWord_3291577) baseStart_3291577 baseEnd_3291577 := by
    simpa [prefixWord, tailWord_3291577, baseEnd_3291577] using wordTrace_append hprefix tailTrace_3291577
  have hstable : (prefixWord ++ tailWord_3291577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291577).length < 2 ^ (prefixWord ++ tailWord_3291577).sum := by decide
  have hdescent : baseEnd_3291577 < baseStart_3291577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291594 : List Nat := [3, 1, 2, 1, 2, 2, 4, 1, 3, 2, 2]
def baseStart_3291594 : Nat := 118140960795 + 3291594 * 2 ^ 59
def prefixEnd_3291594 : Nat := 4983230072969 + 3 ^ 40 * 3291594 * 2
def baseEnd_3291594 : Nat := 1690169841455499857037241

theorem tailTrace_3291594 : CollatzResearch.WordTrace tailWord_3291594 prefixEnd_3291594 1690169841455499857037241 := by
  unfold tailWord_3291594
  simp only [CollatzResearch.WordTrace]
  refine ⟨30013574009281143086126459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80036197358083048229670557 30013574009281143086126459)
  ·
    refine ⟨45020361013921714629189689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30013574009281143086126459 45020361013921714629189689)
    ·
      refine ⟨33765270760441285971892267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45020361013921714629189689 33765270760441285971892267)
      ·
        refine ⟨50647906140661928957838401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33765270760441285971892267 50647906140661928957838401)
        ·
          refine ⟨37985929605496446718378801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50647906140661928957838401 37985929605496446718378801)
          ·
            refine ⟨28489447204122335038784101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37985929605496446718378801 28489447204122335038784101)
            ·
              refine ⟨5341771350772937819772019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28489447204122335038784101 5341771350772937819772019)
              ·
                refine ⟨8012657026159406729658029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5341771350772937819772019 8012657026159406729658029)
                ·
                  refine ⟨3004746384809777523621761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8012657026159406729658029 3004746384809777523621761)
                  ·
                    refine ⟨2253559788607333142716321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3004746384809777523621761 2253559788607333142716321)
                    ·
                      refine ⟨1690169841455499857037241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2253559788607333142716321 1690169841455499857037241)
                      ·
                        rfl

theorem cell23_3291594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_3291594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291594 prefixEnd_3291594 := by exact prefixLift 3291594
  have htrace : WordTrace (prefixWord ++ tailWord_3291594) baseStart_3291594 baseEnd_3291594 := by
    simpa [prefixWord, tailWord_3291594, baseEnd_3291594] using wordTrace_append hprefix tailTrace_3291594
  have hstable : (prefixWord ++ tailWord_3291594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291594).length < 2 ^ (prefixWord ++ tailWord_3291594).sum := by decide
  have hdescent : baseEnd_3291594 < baseStart_3291594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291667 : List Nat := [1, 1, 1, 2, 1, 5, 2, 3, 1, 4, 2]
def baseStart_3291667 : Nat := 118140960795 + 3291667 * 2 ^ 59
def prefixEnd_3291667 : Nat := 4983230072969 + 3 ^ 40 * 3291667 * 2
def baseEnd_3291667 : Nat := 1690207325543278071424405

theorem tailTrace_3291667 : CollatzResearch.WordTrace tailWord_3291667 prefixEnd_3291667 1690207325543278071424405 := by
  unfold tailWord_3291667
  simp only [CollatzResearch.WordTrace]
  refine ⟨120056958565860105811913255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80037972377240070541275503 120056958565860105811913255)
  ·
    refine ⟨180085437848790158717869883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120056958565860105811913255 180085437848790158717869883)
    ·
      refine ⟨270128156773185238076804825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180085437848790158717869883 270128156773185238076804825)
      ·
        refine ⟨202596117579888928557603619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270128156773185238076804825 202596117579888928557603619)
        ·
          refine ⟨303894176369833392836405429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202596117579888928557603619 303894176369833392836405429)
          ·
            refine ⟨28490079034671880578413009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 303894176369833392836405429 28490079034671880578413009)
            ·
              refine ⟨21367559276003910433809757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28490079034671880578413009 21367559276003910433809757)
              ·
                refine ⟨8012834728501466412678659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21367559276003910433809757 8012834728501466412678659)
                ·
                  refine ⟨12019252092752199619017989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8012834728501466412678659 12019252092752199619017989)
                  ·
                    refine ⟨2253609767391037428565873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12019252092752199619017989 2253609767391037428565873)
                    ·
                      refine ⟨1690207325543278071424405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2253609767391037428565873 1690207325543278071424405)
                      ·
                        rfl

theorem cell23_3291667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 4, 2].length) (baseStart_3291667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291667 prefixEnd_3291667 := by exact prefixLift 3291667
  have htrace : WordTrace (prefixWord ++ tailWord_3291667) baseStart_3291667 baseEnd_3291667 := by
    simpa [prefixWord, tailWord_3291667, baseEnd_3291667] using wordTrace_append hprefix tailTrace_3291667
  have hstable : (prefixWord ++ tailWord_3291667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291667).length < 2 ^ (prefixWord ++ tailWord_3291667).sum := by decide
  have hdescent : baseEnd_3291667 < baseStart_3291667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291671 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 3, 3, 2]
def baseStart_3291671 : Nat := 118140960795 + 3291671 * 2 ^ 59
def prefixEnd_3291671 : Nat := 4983230072969 + 3 ^ 40 * 3291671 * 2
def baseEnd_3291671 : Nat := 1690209379465896055774387

theorem tailTrace_3291671 : CollatzResearch.WordTrace tailWord_3291671 prefixEnd_3291671 1690209379465896055774387 := by
  unfold tailWord_3291671
  simp only [CollatzResearch.WordTrace]
  refine ⟨120057104457845614495058867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80038069638563742996705911 120057104457845614495058867)
  ·
    refine ⟨180085656686768421742588301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120057104457845614495058867 180085656686768421742588301)
    ·
      refine ⟨67532121257538158153470613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180085656686768421742588301 67532121257538158153470613)
      ·
        refine ⟨3165568183947101163443935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67532121257538158153470613 3165568183947101163443935)
        ·
          refine ⟨4748352275920651745165903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3165568183947101163443935 4748352275920651745165903)
          ·
            refine ⟨7122528413880977617748855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4748352275920651745165903 7122528413880977617748855)
            ·
              refine ⟨10683792620821466426623283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7122528413880977617748855 10683792620821466426623283)
              ·
                refine ⟨16025688931232199639934925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10683792620821466426623283 16025688931232199639934925)
                ·
                  refine ⟨6009633349212074864975597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16025688931232199639934925 6009633349212074864975597)
                  ·
                    refine ⟨2253612505954528074365849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6009633349212074864975597 2253612505954528074365849)
                    ·
                      refine ⟨1690209379465896055774387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2253612505954528074365849 1690209379465896055774387)
                      ·
                        rfl

theorem cell23_3291671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_3291671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291671 prefixEnd_3291671 := by exact prefixLift 3291671
  have htrace : WordTrace (prefixWord ++ tailWord_3291671) baseStart_3291671 baseEnd_3291671 := by
    simpa [prefixWord, tailWord_3291671, baseEnd_3291671] using wordTrace_append hprefix tailTrace_3291671
  have hstable : (prefixWord ++ tailWord_3291671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291671).length < 2 ^ (prefixWord ++ tailWord_3291671).sum := by decide
  have hdescent : baseEnd_3291671 < baseStart_3291671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291688 : List Nat := [2, 1, 5, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_3291688 : Nat := 118140960795 + 3291688 * 2 ^ 59
def prefixEnd_3291688 : Nat := 4983230072969 + 3 ^ 40 * 3291688 * 2
def baseEnd_3291688 : Nat := 1690218108637022489261809

theorem tailTrace_3291688 : CollatzResearch.WordTrace tailWord_3291688 prefixEnd_3291688 1690218108637022489261809 := by
  unfold tailWord_3291688
  simp only [CollatzResearch.WordTrace]
  refine ⟨60028862249392013199213859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80038482999189350932285145 60028862249392013199213859)
  ·
    refine ⟨90043293374088019798820789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60028862249392013199213859 90043293374088019798820789)
    ·
      refine ⟨8441558753820751856139449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90043293374088019798820789 8441558753820751856139449)
      ·
        refine ⟨6331169065365563892104587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8441558753820751856139449 6331169065365563892104587)
        ·
          refine ⟨9496753598048345838156881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6331169065365563892104587 9496753598048345838156881)
          ·
            refine ⟨7122565198536259378617661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9496753598048345838156881 7122565198536259378617661)
            ·
              refine ⟨2670961949451097266981623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7122565198536259378617661 2670961949451097266981623)
              ·
                refine ⟨4006442924176645900472435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2670961949451097266981623 4006442924176645900472435)
                ·
                  refine ⟨6009664386264968850708653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4006442924176645900472435 6009664386264968850708653)
                  ·
                    refine ⟨2253624144849363319015745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6009664386264968850708653 2253624144849363319015745)
                    ·
                      refine ⟨1690218108637022489261809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2253624144849363319015745 1690218108637022489261809)
                      ·
                        rfl

theorem cell23_3291688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_3291688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291688 prefixEnd_3291688 := by exact prefixLift 3291688
  have htrace : WordTrace (prefixWord ++ tailWord_3291688) baseStart_3291688 baseEnd_3291688 := by
    simpa [prefixWord, tailWord_3291688, baseEnd_3291688] using wordTrace_append hprefix tailTrace_3291688
  have hstable : (prefixWord ++ tailWord_3291688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291688).length < 2 ^ (prefixWord ++ tailWord_3291688).sum := by decide
  have hdescent : baseEnd_3291688 < baseStart_3291688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291701 : List Nat := [1, 3, 3, 1, 1, 2, 4, 2, 2, 2, 2]
def baseStart_3291701 : Nat := 118140960795 + 3291701 * 2 ^ 59
def prefixEnd_3291701 : Nat := 4983230072969 + 3 ^ 40 * 3291701 * 2
def baseEnd_3291701 : Nat := 1690224783885530938399249

theorem tailTrace_3291701 : CollatzResearch.WordTrace tailWord_3291701 prefixEnd_3291701 1690224783885530938399249 := by
  unfold tailWord_3291701
  simp only [CollatzResearch.WordTrace]
  refine ⟨120058198647736929618650957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80038799098491286412433971 120058198647736929618650957)
  ·
    refine ⟨45021824492901348606994109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120058198647736929618650957 45021824492901348606994109)
    ·
      refine ⟨16883184184838005727622791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45021824492901348606994109 16883184184838005727622791)
      ·
        refine ⟨25324776277257008591434187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16883184184838005727622791 25324776277257008591434187)
        ·
          refine ⟨37987164415885512887151281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25324776277257008591434187 37987164415885512887151281)
          ·
            refine ⟨28490373311914134665363461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37987164415885512887151281 28490373311914134665363461)
            ·
              refine ⟨5341944995983900249755649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28490373311914134665363461 5341944995983900249755649)
              ·
                refine ⟨4006458746987925187316737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5341944995983900249755649 4006458746987925187316737)
                ·
                  refine ⟨3004844060240943890487553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4006458746987925187316737 3004844060240943890487553)
                  ·
                    refine ⟨2253633045180707917865665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3004844060240943890487553 2253633045180707917865665)
                    ·
                      refine ⟨1690224783885530938399249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2253633045180707917865665 1690224783885530938399249)
                      ·
                        rfl

theorem cell23_3291701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_3291701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291701 prefixEnd_3291701 := by exact prefixLift 3291701
  have htrace : WordTrace (prefixWord ++ tailWord_3291701) baseStart_3291701 baseEnd_3291701 := by
    simpa [prefixWord, tailWord_3291701, baseEnd_3291701] using wordTrace_append hprefix tailTrace_3291701
  have hstable : (prefixWord ++ tailWord_3291701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291701).length < 2 ^ (prefixWord ++ tailWord_3291701).sum := by decide
  have hdescent : baseEnd_3291701 < baseStart_3291701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291717 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 2, 3, 3]
def baseStart_3291717 : Nat := 118140960795 + 3291717 * 2 ^ 59
def prefixEnd_3291717 : Nat := 4983230072969 + 3 ^ 40 * 3291717 * 2
def baseEnd_3291717 : Nat := 1690232999576002875799175

theorem tailTrace_3291717 : CollatzResearch.WordTrace tailWord_3291717 prefixEnd_3291717 1690232999576002875799175 := by
  unfold tailWord_3291717
  simp only [CollatzResearch.WordTrace]
  refine ⟨120058782215678964351233405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80039188143785976234155603 120058782215678964351233405)
  ·
    refine ⟨45022043330879611631712527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120058782215678964351233405 45022043330879611631712527)
    ·
      refine ⟨67533064996319417447568791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45022043330879611631712527 67533064996319417447568791)
      ·
        refine ⟨101299597494479126171353187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67533064996319417447568791 101299597494479126171353187)
        ·
          refine ⟨151949396241718689257029781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101299597494479126171353187 151949396241718689257029781)
          ·
            refine ⟨7122627948830563558923271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 151949396241718689257029781 7122627948830563558923271)
            ·
              refine ⟨10683941923245845338384907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7122627948830563558923271 10683941923245845338384907)
              ·
                refine ⟨16025912884868768007577361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10683941923245845338384907 16025912884868768007577361)
                ·
                  refine ⟨12019434663651576005683021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16025912884868768007577361 12019434663651576005683021)
                  ·
                    refine ⟨4507287998869341002131133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12019434663651576005683021 4507287998869341002131133)
                    ·
                      refine ⟨1690232999576002875799175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4507287998869341002131133 1690232999576002875799175)
                      ·
                        rfl

theorem cell23_3291717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_3291717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291717 prefixEnd_3291717 := by exact prefixLift 3291717
  have htrace : WordTrace (prefixWord ++ tailWord_3291717) baseStart_3291717 baseEnd_3291717 := by
    simpa [prefixWord, tailWord_3291717, baseEnd_3291717] using wordTrace_append hprefix tailTrace_3291717
  have hstable : (prefixWord ++ tailWord_3291717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291717).length < 2 ^ (prefixWord ++ tailWord_3291717).sum := by decide
  have hdescent : baseEnd_3291717 < baseStart_3291717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291718 : List Nat := [6, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_3291718 : Nat := 118140960795 + 3291718 * 2 ^ 59
def prefixEnd_3291718 : Nat := 4983230072969 + 3 ^ 40 * 3291718 * 2
def baseEnd_3291718 : Nat := 1690233513056657371886671

theorem tailTrace_3291718 : CollatzResearch.WordTrace tailWord_3291718 prefixEnd_3291718 1690233513056657371886671 := by
  unfold tailWord_3291718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3751838084021104422563119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80039212459116894348013205 3751838084021104422563119)
  ·
    refine ⟨5627757126031656633844679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3751838084021104422563119 5627757126031656633844679)
    ·
      refine ⟨8441635689047484950767019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5627757126031656633844679 8441635689047484950767019)
      ·
        refine ⟨12662453533571227426150529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8441635689047484950767019 12662453533571227426150529)
        ·
          refine ⟨9496840150178420569612897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12662453533571227426150529 9496840150178420569612897)
          ·
            refine ⟨7122630112633815427209673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9496840150178420569612897 7122630112633815427209673)
            ·
              refine ⟨5341972584475361570407255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7122630112633815427209673 5341972584475361570407255)
              ·
                refine ⟨8012958876713042355610883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5341972584475361570407255 8012958876713042355610883)
                ·
                  refine ⟨12019438315069563533416325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8012958876713042355610883 12019438315069563533416325)
                  ·
                    refine ⟨2253644684075543162515561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12019438315069563533416325 2253644684075543162515561)
                    ·
                      refine ⟨1690233513056657371886671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2253644684075543162515561 1690233513056657371886671)
                      ·
                        rfl

theorem cell23_3291718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_3291718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291718 prefixEnd_3291718 := by exact prefixLift 3291718
  have htrace : WordTrace (prefixWord ++ tailWord_3291718) baseStart_3291718 baseEnd_3291718 := by
    simpa [prefixWord, tailWord_3291718, baseEnd_3291718] using wordTrace_append hprefix tailTrace_3291718
  have hstable : (prefixWord ++ tailWord_3291718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291718).length < 2 ^ (prefixWord ++ tailWord_3291718).sum := by decide
  have hdescent : baseEnd_3291718 < baseStart_3291718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291720 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 4, 5]
def baseStart_3291720 : Nat := 118140960795 + 3291720 * 2 ^ 59
def prefixEnd_3291720 : Nat := 4983230072969 + 3 ^ 40 * 3291720 * 2
def baseEnd_3291720 : Nat := 563411513339322121353887

theorem tailTrace_3291720 : CollatzResearch.WordTrace tailWord_3291720 prefixEnd_3291720 563411513339322121353887 := by
  unfold tailWord_3291720
  simp only [CollatzResearch.WordTrace]
  refine ⟨60029445817334047931796307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80039261089778730575728409 60029445817334047931796307)
  ·
    refine ⟨90044168726001071897694461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60029445817334047931796307 90044168726001071897694461)
    ·
      refine ⟨33766563272250401961635423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90044168726001071897694461 33766563272250401961635423)
      ·
        refine ⟨50649844908375602942453135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33766563272250401961635423 50649844908375602942453135)
        ·
          refine ⟨75974767362563404413679703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50649844908375602942453135 75974767362563404413679703)
          ·
            refine ⟨113962151043845106620519555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75974767362563404413679703 113962151043845106620519555)
            ·
              refine ⟨170943226565767659930779333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113962151043845106620519555 170943226565767659930779333)
              ·
                refine ⟨32051854981081436237021125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170943226565767659930779333 32051854981081436237021125)
                ·
                  refine ⟨6009722808952769294441461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32051854981081436237021125 6009722808952769294441461)
                  ·
                    refine ⟨563411513339322121353887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6009722808952769294441461 563411513339322121353887)
                    ·
                      rfl

theorem cell23_3291720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_3291720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291720 prefixEnd_3291720 := by exact prefixLift 3291720
  have htrace : WordTrace (prefixWord ++ tailWord_3291720) baseStart_3291720 baseEnd_3291720 := by
    simpa [prefixWord, tailWord_3291720, baseEnd_3291720] using wordTrace_append hprefix tailTrace_3291720
  have hstable : (prefixWord ++ tailWord_3291720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291720).length < 2 ^ (prefixWord ++ tailWord_3291720).sum := by decide
  have hdescent : baseEnd_3291720 < baseStart_3291720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291767 : List Nat := [1, 1, 3, 1, 1, 3, 3, 3, 3, 4]
def baseStart_3291767 : Nat := 118140960795 + 3291767 * 2 ^ 59
def prefixEnd_3291767 : Nat := 4983230072969 + 3 ^ 40 * 3291767 * 2
def baseEnd_3291767 : Nat := 563419557869575893391315

theorem tailTrace_3291767 : CollatzResearch.WordTrace tailWord_3291767 prefixEnd_3291767 563419557869575893391315 := by
  unfold tailWord_3291767
  simp only [CollatzResearch.WordTrace]
  refine ⟨120060605865497822890553555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80040403910331881927035703 120060605865497822890553555)
  ·
    refine ⟨180090908798246734335830333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120060605865497822890553555 180090908798246734335830333)
    ·
      refine ⟨67534090799342525375936375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180090908798246734335830333 67534090799342525375936375)
      ·
        refine ⟨101301136199013788063904563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67534090799342525375936375 101301136199013788063904563)
        ·
          refine ⟨151951704298520682095856845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101301136199013788063904563 151951704298520682095856845)
          ·
            refine ⟨56981889111945255785946317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151951704298520682095856845 56981889111945255785946317)
            ·
              refine ⟨21368208416979470919729869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56981889111945255785946317 21368208416979470919729869)
              ·
                refine ⟨8013078156367301594898701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21368208416979470919729869 8013078156367301594898701)
                ·
                  refine ⟨3004904308637738098087013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8013078156367301594898701 3004904308637738098087013)
                  ·
                    refine ⟨563419557869575893391315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3004904308637738098087013 563419557869575893391315)
                    ·
                      rfl

theorem cell23_3291767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_3291767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291767 prefixEnd_3291767 := by exact prefixLift 3291767
  have htrace : WordTrace (prefixWord ++ tailWord_3291767) baseStart_3291767 baseEnd_3291767 := by
    simpa [prefixWord, tailWord_3291767, baseEnd_3291767] using wordTrace_append hprefix tailTrace_3291767
  have hstable : (prefixWord ++ tailWord_3291767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291767).length < 2 ^ (prefixWord ++ tailWord_3291767).sum := by decide
  have hdescent : baseEnd_3291767 < baseStart_3291767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291777 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_3291777 : Nat := 118140960795 + 3291777 * 2 ^ 59
def prefixEnd_3291777 : Nat := 4983230072969 + 3 ^ 40 * 3291777 * 2
def baseEnd_3291777 : Nat := 1690263808415272641048899

theorem tailTrace_3291777 : CollatzResearch.WordTrace tailWord_3291777 prefixEnd_3291777 1690263808415272641048899 := by
  unfold tailWord_3291777
  simp only [CollatzResearch.WordTrace]
  refine ⟨120060970595461594598417585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80040647063641063065611723 120060970595461594598417585)
  ·
    refine ⟨90045727946596195948813189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120060970595461594598417585 90045727946596195948813189)
    ·
      refine ⟨16883573989986786740402473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90045727946596195948813189 16883573989986786740402473)
      ·
        refine ⟨12662680492490090055301855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16883573989986786740402473 12662680492490090055301855)
        ·
          refine ⟨18994020738735135082952783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12662680492490090055301855 18994020738735135082952783)
          ·
            refine ⟨28491031108102702624429175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18994020738735135082952783 28491031108102702624429175)
            ·
              refine ⟨42736546662154053936643763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28491031108102702624429175 42736546662154053936643763)
              ·
                refine ⟨64104819993231080904965645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42736546662154053936643763 64104819993231080904965645)
                ·
                  refine ⟨24039307497461655339362117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64104819993231080904965645 24039307497461655339362117)
                  ·
                    refine ⟨4507370155774060376130397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24039307497461655339362117 4507370155774060376130397)
                    ·
                      refine ⟨1690263808415272641048899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4507370155774060376130397 1690263808415272641048899)
                      ·
                        rfl

theorem cell23_3291777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_3291777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291777 prefixEnd_3291777 := by exact prefixLift 3291777
  have htrace : WordTrace (prefixWord ++ tailWord_3291777) baseStart_3291777 baseEnd_3291777 := by
    simpa [prefixWord, tailWord_3291777, baseEnd_3291777] using wordTrace_append hprefix tailTrace_3291777
  have hstable : (prefixWord ++ tailWord_3291777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291777).length < 2 ^ (prefixWord ++ tailWord_3291777).sum := by decide
  have hdescent : baseEnd_3291777 < baseStart_3291777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291794 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_3291794 : Nat := 118140960795 + 3291794 * 2 ^ 59
def prefixEnd_3291794 : Nat := 4983230072969 + 3 ^ 40 * 3291794 * 2
def baseEnd_3291794 : Nat := 1690272537586399074536321

theorem tailTrace_3291794 : CollatzResearch.WordTrace tailWord_3291794 prefixEnd_3291794 1690272537586399074536321 := by
  unfold tailWord_3291794
  simp only [CollatzResearch.WordTrace]
  refine ⟨30015397659100001625446609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80041060424266671001190957 30015397659100001625446609)
  ·
    refine ⟨22511548244325001219084957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30015397659100001625446609 22511548244325001219084957)
    ·
      refine ⟨8441830591621875457156859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22511548244325001219084957 8441830591621875457156859)
      ·
        refine ⟨12662745887432813185735289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8441830591621875457156859 12662745887432813185735289)
        ·
          refine ⟨9497059415574609889301467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12662745887432813185735289 9497059415574609889301467)
          ·
            refine ⟨14245589123361914833952201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9497059415574609889301467 14245589123361914833952201)
            ·
              refine ⟨10684191842521436125464151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14245589123361914833952201 10684191842521436125464151)
              ·
                refine ⟨16026287763782154188196227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10684191842521436125464151 16026287763782154188196227)
                ·
                  refine ⟨24039431645673231282294341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16026287763782154188196227 24039431645673231282294341)
                  ·
                    refine ⟨4507393433563730865430189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24039431645673231282294341 4507393433563730865430189)
                    ·
                      refine ⟨1690272537586399074536321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4507393433563730865430189 1690272537586399074536321)
                      ·
                        rfl

theorem cell23_3291794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_3291794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291794 prefixEnd_3291794 := by exact prefixLift 3291794
  have htrace : WordTrace (prefixWord ++ tailWord_3291794) baseStart_3291794 baseEnd_3291794 := by
    simpa [prefixWord, tailWord_3291794, baseEnd_3291794] using wordTrace_append hprefix tailTrace_3291794
  have hstable : (prefixWord ++ tailWord_3291794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291794).length < 2 ^ (prefixWord ++ tailWord_3291794).sum := by decide
  have hdescent : baseEnd_3291794 < baseStart_3291794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291831 : List Nat := [1, 1, 3, 1, 6, 2, 2, 1, 6]
def baseStart_3291831 : Nat := 118140960795 + 3291831 * 2 ^ 59
def prefixEnd_3291831 : Nat := 4983230072969 + 3 ^ 40 * 3291831 * 2
def baseEnd_3291831 : Nat := 187810170707846158863739

theorem tailTrace_3291831 : CollatzResearch.WordTrace tailWord_3291831 prefixEnd_3291831 187810170707846158863739 := by
  unfold tailWord_3291831
  simp only [CollatzResearch.WordTrace]
  refine ⟨120062940137265961820883347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80041960091510641213922231 120062940137265961820883347)
  ·
    refine ⟨180094410205898942731325021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120062940137265961820883347 180094410205898942731325021)
    ·
      refine ⟨67535403827212103524246883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180094410205898942731325021 67535403827212103524246883)
      ·
        refine ⟨101303105740818155286370325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67535403827212103524246883 101303105740818155286370325)
        ·
          refine ⟨4748583081600851029048609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101303105740818155286370325 4748583081600851029048609)
          ·
            refine ⟨3561437311200638271786457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4748583081600851029048609 3561437311200638271786457)
            ·
              refine ⟨2671077983400478703839843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3561437311200638271786457 2671077983400478703839843)
              ·
                refine ⟨4006616975100718055759765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2671077983400478703839843 4006616975100718055759765)
                ·
                  refine ⟨187810170707846158863739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4006616975100718055759765 187810170707846158863739)
                  ·
                    rfl

theorem cell23_3291831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 6].length) (baseStart_3291831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291831 prefixEnd_3291831 := by exact prefixLift 3291831
  have htrace : WordTrace (prefixWord ++ tailWord_3291831) baseStart_3291831 baseEnd_3291831 := by
    simpa [prefixWord, tailWord_3291831, baseEnd_3291831] using wordTrace_append hprefix tailTrace_3291831
  have hstable : (prefixWord ++ tailWord_3291831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291831).length < 2 ^ (prefixWord ++ tailWord_3291831).sum := by decide
  have hdescent : baseEnd_3291831 < baseStart_3291831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291834 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2]
def baseStart_3291834 : Nat := 118140960795 + 3291834 * 2 ^ 59
def prefixEnd_3291834 : Nat := 4983230072969 + 3 ^ 40 * 3291834 * 2
def baseEnd_3291834 : Nat := 1690293076812578918036137

theorem tailTrace_3291834 : CollatzResearch.WordTrace tailWord_3291834 prefixEnd_3291834 1690293076812578918036137 := by
  unfold tailWord_3291834
  simp only [CollatzResearch.WordTrace]
  refine ⟨30015762389063773333310639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80042033037503395555495037 30015762389063773333310639)
  ·
    refine ⟨45023643583595659999965959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30015762389063773333310639 45023643583595659999965959)
    ·
      refine ⟨67535465375393489999948939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45023643583595659999965959 67535465375393489999948939)
      ·
        refine ⟨101303198063090234999923409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67535465375393489999948939 101303198063090234999923409)
        ·
          refine ⟨75977398547317676249942557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101303198063090234999923409 75977398547317676249942557)
          ·
            refine ⟨28491524455244128593728459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75977398547317676249942557 28491524455244128593728459)
            ·
              refine ⟨42737286682866192890592689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28491524455244128593728459 42737286682866192890592689)
              ·
                refine ⟨32052965012149644667944517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42737286682866192890592689 32052965012149644667944517)
                ·
                  refine ⟨6009930939778058375239597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32052965012149644667944517 6009930939778058375239597)
                  ·
                    refine ⟨2253724102416771890714849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6009930939778058375239597 2253724102416771890714849)
                    ·
                      refine ⟨1690293076812578918036137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2253724102416771890714849 1690293076812578918036137)
                      ·
                        rfl

theorem cell23_3291834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2].length) (baseStart_3291834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291834 prefixEnd_3291834 := by exact prefixLift 3291834
  have htrace : WordTrace (prefixWord ++ tailWord_3291834) baseStart_3291834 baseEnd_3291834 := by
    simpa [prefixWord, tailWord_3291834, baseEnd_3291834] using wordTrace_append hprefix tailTrace_3291834
  have hstable : (prefixWord ++ tailWord_3291834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291834).length < 2 ^ (prefixWord ++ tailWord_3291834).sum := by decide
  have hdescent : baseEnd_3291834 < baseStart_3291834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291844 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 3, 5]
def baseStart_3291844 : Nat := 118140960795 + 3291844 * 2 ^ 59
def prefixEnd_3291844 : Nat := 4983230072969 + 3 ^ 40 * 3291844 * 2
def baseEnd_3291844 : Nat := 563432737206374626303697

theorem tailTrace_3291844 : CollatzResearch.WordTrace tailWord_3291844 prefixEnd_3291844 563432737206374626303697 := by
  unfold tailWord_3291844
  simp only [CollatzResearch.WordTrace]
  refine ⟨60031707143109432520553293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80042276190812576694071057 60031707143109432520553293)
  ·
    refine ⟨22511890178666037195207485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60031707143109432520553293 22511890178666037195207485)
    ·
      refine ⟨8441958816999763948202807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22511890178666037195207485 8441958816999763948202807)
      ·
        refine ⟨12662938225499645922304211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8441958816999763948202807 12662938225499645922304211)
        ·
          refine ⟨18994407338249468883456317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12662938225499645922304211 18994407338249468883456317)
          ·
            refine ⟨7122902751843550831296119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18994407338249468883456317 7122902751843550831296119)
            ·
              refine ⟨10684354127765326246944179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7122902751843550831296119 10684354127765326246944179)
              ·
                refine ⟨16026531191647989370416269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10684354127765326246944179 16026531191647989370416269)
                ·
                  refine ⟨6009949196867996013906101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16026531191647989370416269 6009949196867996013906101)
                  ·
                    refine ⟨563432737206374626303697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6009949196867996013906101 563432737206374626303697)
                    ·
                      rfl

theorem cell23_3291844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_3291844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291844 prefixEnd_3291844 := by exact prefixLift 3291844
  have htrace : WordTrace (prefixWord ++ tailWord_3291844) baseStart_3291844 baseEnd_3291844 := by
    simpa [prefixWord, tailWord_3291844, baseEnd_3291844] using wordTrace_append hprefix tailTrace_3291844
  have hstable : (prefixWord ++ tailWord_3291844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291844).length < 2 ^ (prefixWord ++ tailWord_3291844).sum := by decide
  have hdescent : baseEnd_3291844 < baseStart_3291844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291857 : List Nat := [1, 2, 2, 1, 2, 3, 3, 2, 1, 6]
def baseStart_3291857 : Nat := 118140960795 + 3291857 * 2 ^ 59
def prefixEnd_3291857 : Nat := 4983230072969 + 3 ^ 40 * 3291857 * 2
def baseEnd_3291857 : Nat := 563434962289210776016177

theorem tailTrace_3291857 : CollatzResearch.WordTrace tailWord_3291857 prefixEnd_3291857 563434962289210776016177 := by
  unfold tailWord_3291857
  simp only [CollatzResearch.WordTrace]
  refine ⟨120063888435171768261329825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80042592290114512174219883 120063888435171768261329825)
  ·
    refine ⟨90047916326378826195997369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120063888435171768261329825 90047916326378826195997369)
    ·
      refine ⟨67535937244784119646998027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90047916326378826195997369 67535937244784119646998027)
      ·
        refine ⟨101303905867176179470497041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67535937244784119646998027 101303905867176179470497041)
        ·
          refine ⟨75977929400382134602872781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101303905867176179470497041 75977929400382134602872781)
          ·
            refine ⟨28491723525143300476077293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75977929400382134602872781 28491723525143300476077293)
            ·
              refine ⟨10684396321928737678528985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28491723525143300476077293 10684396321928737678528985)
              ·
                refine ⟨8013297241446553258896739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10684396321928737678528985 8013297241446553258896739)
                ·
                  refine ⟨12019945862169829888345109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8013297241446553258896739 12019945862169829888345109)
                  ·
                    refine ⟨563434962289210776016177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12019945862169829888345109 563434962289210776016177)
                    ·
                      rfl

theorem cell23_3291857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_3291857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291857 prefixEnd_3291857 := by exact prefixLift 3291857
  have htrace : WordTrace (prefixWord ++ tailWord_3291857) baseStart_3291857 baseEnd_3291857 := by
    simpa [prefixWord, tailWord_3291857, baseEnd_3291857] using wordTrace_append hprefix tailTrace_3291857
  have hstable : (prefixWord ++ tailWord_3291857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291857).length < 2 ^ (prefixWord ++ tailWord_3291857).sum := by decide
  have hdescent : baseEnd_3291857 < baseStart_3291857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291868 : List Nat := [2, 2, 5, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_3291868 : Nat := 118140960795 + 3291868 * 2 ^ 59
def prefixEnd_3291868 : Nat := 4983230072969 + 3 ^ 40 * 3291868 * 2
def baseEnd_3291868 : Nat := 1690310535154831785010981

theorem tailTrace_3291868 : CollatzResearch.WordTrace tailWord_3291868 prefixEnd_3291868 1690310535154831785010981 := by
  unfold tailWord_3291868
  simp only [CollatzResearch.WordTrace]
  refine ⟨60032144819065958569990129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80042859758754611426653505 60032144819065958569990129)
  ·
    refine ⟨45024108614299468927492597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60032144819065958569990129 45024108614299468927492597)
    ·
      refine ⟨4221010182590575211952431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45024108614299468927492597 4221010182590575211952431)
      ·
        refine ⟨6331515273885862817928647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4221010182590575211952431 6331515273885862817928647)
        ·
          refine ⟨9497272910828794226892971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6331515273885862817928647 9497272910828794226892971)
          ·
            refine ⟨14245909366243191340339457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9497272910828794226892971 14245909366243191340339457)
            ·
              refine ⟨10684432024682393505254593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14245909366243191340339457 10684432024682393505254593)
              ·
                refine ⟨8013324018511795128940945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10684432024682393505254593 8013324018511795128940945)
                ·
                  refine ⟨6009993013883846346705709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8013324018511795128940945 6009993013883846346705709)
                  ·
                    refine ⟨2253747380206442380014641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6009993013883846346705709 2253747380206442380014641)
                    ·
                      refine ⟨1690310535154831785010981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2253747380206442380014641 1690310535154831785010981)
                      ·
                        rfl

theorem cell23_3291868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_3291868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291868 prefixEnd_3291868 := by exact prefixLift 3291868
  have htrace : WordTrace (prefixWord ++ tailWord_3291868) baseStart_3291868 baseEnd_3291868 := by
    simpa [prefixWord, tailWord_3291868, baseEnd_3291868] using wordTrace_append hprefix tailTrace_3291868
  have hstable : (prefixWord ++ tailWord_3291868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291868).length < 2 ^ (prefixWord ++ tailWord_3291868).sum := by decide
  have hdescent : baseEnd_3291868 < baseStart_3291868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291875 : List Nat := [1, 1, 1, 7, 1, 1, 4, 2, 1, 1, 3]
def baseStart_3291875 : Nat := 118140960795 + 3291875 * 2 ^ 59
def prefixEnd_3291875 : Nat := 4983230072969 + 3 ^ 40 * 3291875 * 2
def baseEnd_3291875 : Nat := 1690314129519413257623449

theorem tailTrace_3291875 : CollatzResearch.WordTrace tailWord_3291875 prefixEnd_3291875 1690314129519413257623449 := by
  unfold tailWord_3291875
  simp only [CollatzResearch.WordTrace]
  refine ⟨120064544949106557335485079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80043029966071038223656719 120064544949106557335485079)
  ·
    refine ⟨180096817423659836003227619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120064544949106557335485079 180096817423659836003227619)
    ·
      refine ⟨270145226135489754004841429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180096817423659836003227619 270145226135489754004841429)
      ·
        refine ⟨6331528737550541109488471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 270145226135489754004841429 6331528737550541109488471)
        ·
          refine ⟨9497293106325811664232707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6331528737550541109488471 9497293106325811664232707)
          ·
            refine ⟨14245939659488717496349061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9497293106325811664232707 14245939659488717496349061)
            ·
              refine ⟨2671113686154134530565449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14245939659488717496349061 2671113686154134530565449)
              ·
                refine ⟨2003335264615600897924087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2671113686154134530565449 2003335264615600897924087)
                ·
                  refine ⟨3005002896923401346886131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2003335264615600897924087 3005002896923401346886131)
                  ·
                    refine ⟨4507504345385102020329197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3005002896923401346886131 4507504345385102020329197)
                    ·
                      refine ⟨1690314129519413257623449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4507504345385102020329197 1690314129519413257623449)
                      ·
                        rfl

theorem cell23_3291875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_3291875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291875 prefixEnd_3291875 := by exact prefixLift 3291875
  have htrace : WordTrace (prefixWord ++ tailWord_3291875) baseStart_3291875 baseEnd_3291875 := by
    simpa [prefixWord, tailWord_3291875, baseEnd_3291875] using wordTrace_append hprefix tailTrace_3291875
  have hstable : (prefixWord ++ tailWord_3291875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291875).length < 2 ^ (prefixWord ++ tailWord_3291875).sum := by decide
  have hdescent : baseEnd_3291875 < baseStart_3291875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291887 : List Nat := [1, 1, 2, 1, 5, 2, 3, 8]
def baseStart_3291887 : Nat := 118140960795 + 3291887 * 2 ^ 59
def prefixEnd_3291887 : Nat := 4983230072969 + 3 ^ 40 * 3291887 * 2
def baseEnd_3291887 : Nat := 62604455232861748543459

theorem tailTrace_3291887 : CollatzResearch.WordTrace tailWord_3291887 prefixEnd_3291887 62604455232861748543459 := by
  unfold tailWord_3291887
  simp only [CollatzResearch.WordTrace]
  refine ⟨120064982625063083384921915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80043321750042055589947943 120064982625063083384921915)
  ·
    refine ⟨180097473937594625077382873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120064982625063083384921915 180097473937594625077382873)
    ·
      refine ⟨135073105453195968808037155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180097473937594625077382873 135073105453195968808037155)
      ·
        refine ⟨202609658179793953212055733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135073105453195968808037155 202609658179793953212055733)
        ·
          refine ⟨18994655454355683113630225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 202609658179793953212055733 18994655454355683113630225)
          ·
            refine ⟨14245991590766762335222669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18994655454355683113630225 14245991590766762335222669)
            ·
              refine ⟨5342246846537535875708501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14245991590766762335222669 5342246846537535875708501)
              ·
                refine ⟨62604455232861748543459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5342246846537535875708501 62604455232861748543459)
                ·
                  rfl

theorem cell23_3291887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 8].length) (baseStart_3291887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291887 prefixEnd_3291887 := by exact prefixLift 3291887
  have htrace : WordTrace (prefixWord ++ tailWord_3291887) baseStart_3291887 baseEnd_3291887 := by
    simpa [prefixWord, tailWord_3291887, baseEnd_3291887] using wordTrace_append hprefix tailTrace_3291887
  have hstable : (prefixWord ++ tailWord_3291887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291887).length < 2 ^ (prefixWord ++ tailWord_3291887).sum := by decide
  have hdescent : baseEnd_3291887 < baseStart_3291887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291914 : List Nat := [3, 1, 2, 2, 1, 2, 1, 4, 1, 3, 3]
def baseStart_3291914 : Nat := 118140960795 + 3291914 * 2 ^ 59
def prefixEnd_3291914 : Nat := 4983230072969 + 3 ^ 40 * 3291914 * 2
def baseEnd_3291914 : Nat := 1690334155264938605035769

theorem tailTrace_3291914 : CollatzResearch.WordTrace tailWord_3291914 prefixEnd_3291914 1690334155264938605035769 := by
  unfold tailWord_3291914
  simp only [CollatzResearch.WordTrace]
  refine ⟨30016491848991316749038699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80043978263976844664103197 30016491848991316749038699)
  ·
    refine ⟨45024737773486975123558049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30016491848991316749038699 45024737773486975123558049)
    ·
      refine ⟨33768553330115231342668537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45024737773486975123558049 33768553330115231342668537)
      ·
        refine ⟨25326414997586423507001403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33768553330115231342668537 25326414997586423507001403)
        ·
          refine ⟨37989622496379635260502105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25326414997586423507001403 37989622496379635260502105)
          ·
            refine ⟨28492216872284726445376579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37989622496379635260502105 28492216872284726445376579)
            ·
              refine ⟨42738325308427089668064869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28492216872284726445376579 42738325308427089668064869)
              ·
                refine ⟨8013435995330079312762163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42738325308427089668064869 8013435995330079312762163)
                ·
                  refine ⟨12020153992995118969143245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8013435995330079312762163 12020153992995118969143245)
                  ·
                    refine ⟨4507557747373169613428717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12020153992995118969143245 4507557747373169613428717)
                    ·
                      refine ⟨1690334155264938605035769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4507557747373169613428717 1690334155264938605035769)
                      ·
                        rfl

theorem cell23_3291914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_3291914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291914 prefixEnd_3291914 := by exact prefixLift 3291914
  have htrace : WordTrace (prefixWord ++ tailWord_3291914) baseStart_3291914 baseEnd_3291914 := by
    simpa [prefixWord, tailWord_3291914, baseEnd_3291914] using wordTrace_append hprefix tailTrace_3291914
  have hstable : (prefixWord ++ tailWord_3291914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291914).length < 2 ^ (prefixWord ++ tailWord_3291914).sum := by decide
  have hdescent : baseEnd_3291914 < baseStart_3291914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291948 : List Nat := [2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 3]
def baseStart_3291948 : Nat := 118140960795 + 3291948 * 2 ^ 59
def prefixEnd_3291948 : Nat := 4983230072969 + 3 ^ 40 * 3291948 * 2
def baseEnd_3291948 : Nat := 1690351613607191472010613

theorem tailTrace_3291948 : CollatzResearch.WordTrace tailWord_3291948 prefixEnd_3291948 1690351613607191472010613 := by
  unfold tailWord_3291948
  simp only [CollatzResearch.WordTrace]
  refine ⟨60033603738921045401446249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80044804985228060535261665 60033603738921045401446249)
  ·
    refine ⟨45025202804190784051084687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60033603738921045401446249 45025202804190784051084687)
    ·
      refine ⟨67537804206286176076627031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45025202804190784051084687 67537804206286176076627031)
      ·
        refine ⟨101306706309429264114940547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67537804206286176076627031 101306706309429264114940547)
        ·
          refine ⟨151960059464143896172410821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101306706309429264114940547 151960059464143896172410821)
          ·
            refine ⟨28492511149526980532327029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151960059464143896172410821 28492511149526980532327029)
            ·
              refine ⟨2671172920268154424905659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28492511149526980532327029 2671172920268154424905659)
              ·
                refine ⟨4006759380402231637358489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2671172920268154424905659 4006759380402231637358489)
                ·
                  refine ⟨3005069535301673728018867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4006759380402231637358489 3005069535301673728018867)
                  ·
                    refine ⟨4507604302952510592028301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3005069535301673728018867 4507604302952510592028301)
                    ·
                      refine ⟨1690351613607191472010613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4507604302952510592028301 1690351613607191472010613)
                      ·
                        rfl

theorem cell23_3291948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 3].length) (baseStart_3291948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291948 prefixEnd_3291948 := by exact prefixLift 3291948
  have htrace : WordTrace (prefixWord ++ tailWord_3291948) baseStart_3291948 baseEnd_3291948 := by
    simpa [prefixWord, tailWord_3291948, baseEnd_3291948] using wordTrace_append hprefix tailTrace_3291948
  have hstable : (prefixWord ++ tailWord_3291948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291948).length < 2 ^ (prefixWord ++ tailWord_3291948).sum := by decide
  have hdescent : baseEnd_3291948 < baseStart_3291948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291971 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 6, 2, 2]
def baseStart_3291971 : Nat := 118140960795 + 3291971 * 2 ^ 59
def prefixEnd_3291971 : Nat := 4983230072969 + 3 ^ 40 * 3291971 * 2
def baseEnd_3291971 : Nat := 1690363423662244882023007

theorem tailTrace_3291971 : CollatzResearch.WordTrace tailWord_3291971 prefixEnd_3291971 1690363423662244882023007 := by
  unfold tailWord_3291971
  simp only [CollatzResearch.WordTrace]
  refine ⟨120068046356758765730979767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80045364237839177153986511 120068046356758765730979767)
  ·
    refine ⟨180102069535138148596469651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120068046356758765730979767 180102069535138148596469651)
    ·
      refine ⟨270153104302707222894704477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180102069535138148596469651 270153104302707222894704477)
      ·
        refine ⟨101307414113515208585514179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270153104302707222894704477 101307414113515208585514179)
        ·
          refine ⟨151961121170272812878271269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101307414113515208585514179 151961121170272812878271269)
          ·
            refine ⟨28492710219426152414675863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151961121170272812878271269 28492710219426152414675863)
            ·
              refine ⟨42739065329139228622013795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28492710219426152414675863 42739065329139228622013795)
              ·
                refine ⟨64108597993708842933020693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42739065329139228622013795 64108597993708842933020693)
                ·
                  refine ⟨3005090530955102012485345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64108597993708842933020693 3005090530955102012485345)
                  ·
                    refine ⟨2253817898216326509364009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3005090530955102012485345 2253817898216326509364009)
                    ·
                      refine ⟨1690363423662244882023007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2253817898216326509364009 1690363423662244882023007)
                      ·
                        rfl

theorem cell23_3291971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 2, 2].length) (baseStart_3291971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291971 prefixEnd_3291971 := by exact prefixLift 3291971
  have htrace : WordTrace (prefixWord ++ tailWord_3291971) baseStart_3291971 baseEnd_3291971 := by
    simpa [prefixWord, tailWord_3291971, baseEnd_3291971] using wordTrace_append hprefix tailTrace_3291971
  have hstable : (prefixWord ++ tailWord_3291971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291971).length < 2 ^ (prefixWord ++ tailWord_3291971).sum := by decide
  have hdescent : baseEnd_3291971 < baseStart_3291971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
