import V185TrunkScan23Chunk0580

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3436108 : List Nat := [2, 2, 1, 3, 1, 4, 1, 3, 1, 1, 4]
def baseStart_3436108 : Nat := 118140960795 + 3436108 * 2 ^ 59
def prefixEnd_3436108 : Nat := 4983230072969 + 3 ^ 40 * 3436108 * 2
def baseEnd_3436108 : Nat := 1764374984759347445347633

theorem tailTrace_3436108 : CollatzResearch.WordTrace tailWord_3436108 prefixEnd_3436108 1764374984759347445347633 := by
  unfold tailWord_3436108
  simp only [CollatzResearch.WordTrace]
  refine ⟨62662577317787515685374489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83550103090383354247165985 62662577317787515685374489)
  ·
    refine ⟨46996932988340636764030867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62662577317787515685374489 46996932988340636764030867)
    ·
      refine ⟨70495399482510955146046301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46996932988340636764030867 70495399482510955146046301)
      ·
        refine ⟨26435774805941608179767363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70495399482510955146046301 26435774805941608179767363)
        ·
          refine ⟨39653662208912412269651045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26435774805941608179767363 39653662208912412269651045)
          ·
            refine ⟨7435061664171077300559571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39653662208912412269651045 7435061664171077300559571)
            ·
              refine ⟨11152592496256615950839357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7435061664171077300559571 11152592496256615950839357)
              ·
                refine ⟨4182222186096230981564759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11152592496256615950839357 4182222186096230981564759)
                ·
                  refine ⟨6273333279144346472347139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4182222186096230981564759 6273333279144346472347139)
                  ·
                    refine ⟨9409999918716519708520709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6273333279144346472347139 9409999918716519708520709)
                    ·
                      refine ⟨1764374984759347445347633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9409999918716519708520709 1764374984759347445347633)
                      ·
                        rfl

theorem cell23_3436108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_3436108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436108 prefixEnd_3436108 := by exact prefixLift 3436108
  have htrace : WordTrace (prefixWord ++ tailWord_3436108) baseStart_3436108 baseEnd_3436108 := by
    simpa [prefixWord, tailWord_3436108, baseEnd_3436108] using wordTrace_append hprefix tailTrace_3436108
  have hstable : (prefixWord ++ tailWord_3436108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436108).length < 2 ^ (prefixWord ++ tailWord_3436108).sum := by decide
  have hdescent : baseEnd_3436108 < baseStart_3436108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436138 : List Nat := [3, 1, 3, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_3436138 : Nat := 118140960795 + 3436138 * 2 ^ 59
def prefixEnd_3436138 : Nat := 4983230072969 + 3 ^ 40 * 3436138 * 2
def baseEnd_3436138 : Nat := 1764390389178982327972495

theorem tailTrace_3436138 : CollatzResearch.WordTrace tailWord_3436138 prefixEnd_3436138 1764390389178982327972495 := by
  unfold tailWord_3436138
  simp only [CollatzResearch.WordTrace]
  refine ⟨31331562206366586623585267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83550832550310897662894045 31331562206366586623585267)
  ·
    refine ⟨46997343309549879935377901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31331562206366586623585267 46997343309549879935377901)
    ·
      refine ⟨17624003741081204975766713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46997343309549879935377901 17624003741081204975766713)
      ·
        refine ⟨13218002805810903731825035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17624003741081204975766713 13218002805810903731825035)
        ·
          refine ⟨19827004208716355597737553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13218002805810903731825035 19827004208716355597737553)
          ·
            refine ⟨14870253156537266698303165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19827004208716355597737553 14870253156537266698303165)
            ·
              refine ⟨5576344933701475011863687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14870253156537266698303165 5576344933701475011863687)
              ·
                refine ⟨8364517400552212517795531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5576344933701475011863687 8364517400552212517795531)
                ·
                  refine ⟨12546776100828318776693297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8364517400552212517795531 12546776100828318776693297)
                  ·
                    refine ⟨9410082075621239082519973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12546776100828318776693297 9410082075621239082519973)
                    ·
                      refine ⟨1764390389178982327972495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9410082075621239082519973 1764390389178982327972495)
                      ·
                        rfl

theorem cell23_3436138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_3436138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436138 prefixEnd_3436138 := by exact prefixLift 3436138
  have htrace : WordTrace (prefixWord ++ tailWord_3436138) baseStart_3436138 baseEnd_3436138 := by
    simpa [prefixWord, tailWord_3436138, baseEnd_3436138] using wordTrace_append hprefix tailTrace_3436138
  have hstable : (prefixWord ++ tailWord_3436138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436138).length < 2 ^ (prefixWord ++ tailWord_3436138).sum := by decide
  have hdescent : baseEnd_3436138 < baseStart_3436138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436192 : List Nat := [2, 1, 1, 4, 3, 1, 4, 1, 2, 1, 3]
def baseStart_3436192 : Nat := 118140960795 + 3436192 * 2 ^ 59
def prefixEnd_3436192 : Nat := 4983230072969 + 3 ^ 40 * 3436192 * 2
def baseEnd_3436192 : Nat := 1764418117134325116697247

theorem tailTrace_3436192 : CollatzResearch.WordTrace tailWord_3436192 prefixEnd_3436192 1764418117134325116697247 := by
  unfold tailWord_3436192
  simp only [CollatzResearch.WordTrace]
  refine ⟨62664109183635356858403415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83552145578180475811204553 62664109183635356858403415)
  ·
    refine ⟨93996163775453035287605123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62664109183635356858403415 93996163775453035287605123)
    ·
      refine ⟨140994245663179552931407685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93996163775453035287605123 140994245663179552931407685)
      ·
        refine ⟨26436421061846166174638941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140994245663179552931407685 26436421061846166174638941)
        ·
          refine ⟨9913657898192312315489603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26436421061846166174638941 9913657898192312315489603)
          ·
            refine ⟨14870486847288468473234405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9913657898192312315489603 14870486847288468473234405)
            ·
              refine ⟨2788216283866587838731451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14870486847288468473234405 2788216283866587838731451)
              ·
                refine ⟨4182324425799881758097177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2788216283866587838731451 4182324425799881758097177)
                ·
                  refine ⟨3136743319349911318572883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4182324425799881758097177 3136743319349911318572883)
                  ·
                    refine ⟨4705114979024866977859325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3136743319349911318572883 4705114979024866977859325)
                    ·
                      refine ⟨1764418117134325116697247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4705114979024866977859325 1764418117134325116697247)
                      ·
                        rfl

theorem cell23_3436192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_3436192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436192 prefixEnd_3436192 := by exact prefixLift 3436192
  have htrace : WordTrace (prefixWord ++ tailWord_3436192) baseStart_3436192 baseEnd_3436192 := by
    simpa [prefixWord, tailWord_3436192, baseEnd_3436192] using wordTrace_append hprefix tailTrace_3436192
  have hstable : (prefixWord ++ tailWord_3436192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436192).length < 2 ^ (prefixWord ++ tailWord_3436192).sum := by decide
  have hdescent : baseEnd_3436192 < baseStart_3436192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436215 : List Nat := [1, 1, 3, 1, 5, 2, 1, 2, 1, 4, 2]
def baseStart_3436215 : Nat := 118140960795 + 3436215 * 2 ^ 59
def prefixEnd_3436215 : Nat := 4983230072969 + 3 ^ 40 * 3436215 * 2
def baseEnd_3436215 : Nat := 1764429927189378526709641

theorem tailTrace_3436215 : CollatzResearch.WordTrace tailWord_3436215 prefixEnd_3436215 1764429927189378526709641 := by
  unfold tailWord_3436215
  simp only [CollatzResearch.WordTrace]
  refine ⟨125329057246187388644894099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83552704830791592429929399 125329057246187388644894099)
  ·
    refine ⟨187993585869281082967341149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125329057246187388644894099 187993585869281082967341149)
    ·
      refine ⟨70497594700980406112752931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187993585869281082967341149 70497594700980406112752931)
      ·
        refine ⟨105746392051470609169129397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70497594700980406112752931 105746392051470609169129397)
        ·
          refine ⟨9913724254825369609605881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105746392051470609169129397 9913724254825369609605881)
          ·
            refine ⟨7435293191119027207204411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9913724254825369609605881 7435293191119027207204411)
            ·
              refine ⟨11152939786678540810806617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7435293191119027207204411 11152939786678540810806617)
              ·
                refine ⟨8364704840008905608104963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11152939786678540810806617 8364704840008905608104963)
                ·
                  refine ⟨12547057260013358412157445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8364704840008905608104963 12547057260013358412157445)
                  ·
                    refine ⟨2352573236252504702279521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12547057260013358412157445 2352573236252504702279521)
                    ·
                      refine ⟨1764429927189378526709641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2352573236252504702279521 1764429927189378526709641)
                      ·
                        rfl

theorem cell23_3436215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 4, 2].length) (baseStart_3436215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436215 prefixEnd_3436215 := by exact prefixLift 3436215
  have htrace : WordTrace (prefixWord ++ tailWord_3436215) baseStart_3436215 baseEnd_3436215 := by
    simpa [prefixWord, tailWord_3436215, baseEnd_3436215] using wordTrace_append hprefix tailTrace_3436215
  have hstable : (prefixWord ++ tailWord_3436215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436215).length < 2 ^ (prefixWord ++ tailWord_3436215).sum := by decide
  have hdescent : baseEnd_3436215 < baseStart_3436215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436228 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_3436228 : Nat := 118140960795 + 3436228 * 2 ^ 59
def prefixEnd_3436228 : Nat := 4983230072969 + 3 ^ 40 * 3436228 * 2
def baseEnd_3436228 : Nat := 1764436602437886975847081

theorem tailTrace_3436228 : CollatzResearch.WordTrace tailWord_3436228 prefixEnd_3436228 1764436602437886975847081 := by
  unfold tailWord_3436228
  simp only [CollatzResearch.WordTrace]
  refine ⟨62664765697570145932558669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83553020930093527910078225 62664765697570145932558669)
  ·
    refine ⟨23499287136588804724709501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62664765697570145932558669 23499287136588804724709501)
    ·
      refine ⟨8812232676220801771766063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23499287136588804724709501 8812232676220801771766063)
      ·
        refine ⟨13218349014331202657649095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8812232676220801771766063 13218349014331202657649095)
        ·
          refine ⟨19827523521496803986473643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13218349014331202657649095 19827523521496803986473643)
          ·
            refine ⟨29741285282245205979710465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19827523521496803986473643 29741285282245205979710465)
            ·
              refine ⟨22305963961683904484782849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29741285282245205979710465 22305963961683904484782849)
              ·
                refine ⟨16729472971262928363587137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22305963961683904484782849 16729472971262928363587137)
                ·
                  refine ⟨12547104728447196272690353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16729472971262928363587137 12547104728447196272690353)
                  ·
                    refine ⟨9410328546335397204517765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12547104728447196272690353 9410328546335397204517765)
                    ·
                      refine ⟨1764436602437886975847081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9410328546335397204517765 1764436602437886975847081)
                      ·
                        rfl

theorem cell23_3436228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_3436228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436228 prefixEnd_3436228 := by exact prefixLift 3436228
  have htrace : WordTrace (prefixWord ++ tailWord_3436228) baseStart_3436228 baseEnd_3436228 := by
    simpa [prefixWord, tailWord_3436228, baseEnd_3436228] using wordTrace_append hprefix tailTrace_3436228
  have hstable : (prefixWord ++ tailWord_3436228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436228).length < 2 ^ (prefixWord ++ tailWord_3436228).sum := by decide
  have hdescent : baseEnd_3436228 < baseStart_3436228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436232 : List Nat := [2, 1, 3, 1, 2, 2, 4, 2, 2, 2, 2]
def baseStart_3436232 : Nat := 118140960795 + 3436232 * 2 ^ 59
def prefixEnd_3436232 : Nat := 4983230072969 + 3 ^ 40 * 3436232 * 2
def baseEnd_3436232 : Nat := 1764438656360504960197063

theorem tailTrace_3436232 : CollatzResearch.WordTrace tailWord_3436232 prefixEnd_3436232 1764438656360504960197063 := by
  unfold tailWord_3436232
  simp only [CollatzResearch.WordTrace]
  refine ⟨62664838643562900274131475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83553118191417200365508633 62664838643562900274131475)
  ·
    refine ⟨93997257965344350411197213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62664838643562900274131475 93997257965344350411197213)
    ·
      refine ⟨35248971737004131404198955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93997257965344350411197213 35248971737004131404198955)
      ·
        refine ⟨52873457605506197106298433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35248971737004131404198955 52873457605506197106298433)
        ·
          refine ⟨39655093204129647829723825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52873457605506197106298433 39655093204129647829723825)
          ·
            refine ⟨29741319903097235872292869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39655093204129647829723825 29741319903097235872292869)
            ·
              refine ⟨5576497481830731726054913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29741319903097235872292869 5576497481830731726054913)
              ·
                refine ⟨4182373111373048794541185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5576497481830731726054913 4182373111373048794541185)
                ·
                  refine ⟨3136779833529786595905889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4182373111373048794541185 3136779833529786595905889)
                  ·
                    refine ⟨2352584875147339946929417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3136779833529786595905889 2352584875147339946929417)
                    ·
                      refine ⟨1764438656360504960197063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2352584875147339946929417 1764438656360504960197063)
                      ·
                        rfl

theorem cell23_3436232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_3436232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436232 prefixEnd_3436232 := by exact prefixLift 3436232
  have htrace : WordTrace (prefixWord ++ tailWord_3436232) baseStart_3436232 baseEnd_3436232 := by
    simpa [prefixWord, tailWord_3436232, baseEnd_3436232] using wordTrace_append hprefix tailTrace_3436232
  have hstable : (prefixWord ++ tailWord_3436232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436232).length < 2 ^ (prefixWord ++ tailWord_3436232).sum := by decide
  have hdescent : baseEnd_3436232 < baseStart_3436232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436248 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 2, 3, 3]
def baseStart_3436248 : Nat := 118140960795 + 3436248 * 2 ^ 59
def prefixEnd_3436248 : Nat := 4983230072969 + 3 ^ 40 * 3436248 * 2
def baseEnd_3436248 : Nat := 1764446872050976897596989

theorem tailTrace_3436248 : CollatzResearch.WordTrace tailWord_3436248 prefixEnd_3436248 1764446872050976897596989 := by
  unfold tailWord_3436248
  simp only [CollatzResearch.WordTrace]
  refine ⟨62665130427533917640422699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83553507236711890187230265 62665130427533917640422699)
  ·
    refine ⟨93997695641300876460634049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62665130427533917640422699 93997695641300876460634049)
    ·
      refine ⟨70498271730975657345475537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93997695641300876460634049 70498271730975657345475537)
      ·
        refine ⟨52873703798231743009106653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70498271730975657345475537 52873703798231743009106653)
        ·
          refine ⟨19827638924336903628414995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52873703798231743009106653 19827638924336903628414995)
          ·
            refine ⟨29741458386505355442622493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19827638924336903628414995 29741458386505355442622493)
            ·
              refine ⟨11153046894939508290983435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29741458386505355442622493 11153046894939508290983435)
              ·
                refine ⟨16729570342409262436475153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11153046894939508290983435 16729570342409262436475153)
                ·
                  refine ⟨12547177756806946827356365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16729570342409262436475153 12547177756806946827356365)
                  ·
                    refine ⟨4705191658802605060258637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12547177756806946827356365 4705191658802605060258637)
                    ·
                      refine ⟨1764446872050976897596989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4705191658802605060258637 1764446872050976897596989)
                      ·
                        rfl

theorem cell23_3436248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_3436248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436248 prefixEnd_3436248 := by exact prefixLift 3436248
  have htrace : WordTrace (prefixWord ++ tailWord_3436248) baseStart_3436248 baseEnd_3436248 := by
    simpa [prefixWord, tailWord_3436248, baseEnd_3436248] using wordTrace_append hprefix tailTrace_3436248
  have hstable : (prefixWord ++ tailWord_3436248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436248).length < 2 ^ (prefixWord ++ tailWord_3436248).sum := by decide
  have hdescent : baseEnd_3436248 < baseStart_3436248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436268 : List Nat := [2, 2, 1, 1, 2, 2, 5, 1, 2, 5]
def baseStart_3436268 : Nat := 118140960795 + 3436268 * 2 ^ 59
def prefixEnd_3436268 : Nat := 4983230072969 + 3 ^ 40 * 3436268 * 2
def baseEnd_3436268 : Nat := 588152380554688939782299

theorem tailTrace_3436268 : CollatzResearch.WordTrace tailWord_3436268 prefixEnd_3436268 588152380554688939782299 := by
  unfold tailWord_3436268
  simp only [CollatzResearch.WordTrace]
  refine ⟨62665495157497689348286729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83553993543330252464382305 62665495157497689348286729)
  ·
    refine ⟨46999121368123267011215047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62665495157497689348286729 46999121368123267011215047)
    ·
      refine ⟨70498682052184900516822571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46999121368123267011215047 70498682052184900516822571)
      ·
        refine ⟨105748023078277350775233857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70498682052184900516822571 105748023078277350775233857)
        ·
          refine ⟨79311017308708013081425393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105748023078277350775233857 79311017308708013081425393)
          ·
            refine ⟨59483262981531009811069045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79311017308708013081425393 59483262981531009811069045)
            ·
              refine ⟨5576555904518532169787723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59483262981531009811069045 5576555904518532169787723)
              ·
                refine ⟨8364833856777798254681585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5576555904518532169787723 8364833856777798254681585)
                ·
                  refine ⟨6273625392583348691011189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8364833856777798254681585 6273625392583348691011189)
                  ·
                    refine ⟨588152380554688939782299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6273625392583348691011189 588152380554688939782299)
                    ·
                      rfl

theorem cell23_3436268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_3436268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436268 prefixEnd_3436268 := by exact prefixLift 3436268
  have htrace : WordTrace (prefixWord ++ tailWord_3436268) baseStart_3436268 baseEnd_3436268 := by
    simpa [prefixWord, tailWord_3436268, baseEnd_3436268] using wordTrace_append hprefix tailTrace_3436268
  have hstable : (prefixWord ++ tailWord_3436268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436268).length < 2 ^ (prefixWord ++ tailWord_3436268).sum := by decide
  have hdescent : baseEnd_3436268 < baseStart_3436268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436288 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 3, 6, 2]
def baseStart_3436288 : Nat := 118140960795 + 3436288 * 2 ^ 59
def prefixEnd_3436288 : Nat := 4983230072969 + 3 ^ 40 * 3436288 * 2
def baseEnd_3436288 : Nat := 1764467411277156741096805

theorem tailTrace_3436288 : CollatzResearch.WordTrace tailWord_3436288 prefixEnd_3436288 1764467411277156741096805 := by
  unfold tailWord_3436288
  simp only [CollatzResearch.WordTrace]
  refine ⟨62665859887461461056150759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83554479849948614741534345 62665859887461461056150759)
  ·
    refine ⟨93998789831192191584226139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62665859887461461056150759 93998789831192191584226139)
    ·
      refine ⟨140998184746788287376339209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93998789831192191584226139 140998184746788287376339209)
      ·
        refine ⟨105748638560091215532254407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140998184746788287376339209 105748638560091215532254407)
        ·
          refine ⟨158622957840136823298381611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105748638560091215532254407 158622957840136823298381611)
          ·
            refine ⟨237934436760205234947572417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158622957840136823298381611 237934436760205234947572417)
            ·
              refine ⟨178450827570153926210679313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237934436760205234947572417 178450827570153926210679313)
              ·
                refine ⟨133838120677615444658009485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178450827570153926210679313 133838120677615444658009485)
                ·
                  refine ⟨50189295254105791746753557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133838120677615444658009485 50189295254105791746753557)
                  ·
                    refine ⟨2352623215036208988129073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50189295254105791746753557 2352623215036208988129073)
                    ·
                      refine ⟨1764467411277156741096805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2352623215036208988129073 1764467411277156741096805)
                      ·
                        rfl

theorem cell23_3436288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 6, 2].length) (baseStart_3436288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436288 prefixEnd_3436288 := by exact prefixLift 3436288
  have htrace : WordTrace (prefixWord ++ tailWord_3436288) baseStart_3436288 baseEnd_3436288 := by
    simpa [prefixWord, tailWord_3436288, baseEnd_3436288] using wordTrace_append hprefix tailTrace_3436288
  have hstable : (prefixWord ++ tailWord_3436288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436288).length < 2 ^ (prefixWord ++ tailWord_3436288).sum := by decide
  have hdescent : baseEnd_3436288 < baseStart_3436288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436291 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 5]
def baseStart_3436291 : Nat := 118140960795 + 3436291 * 2 ^ 59
def prefixEnd_3436291 : Nat := 4983230072969 + 3 ^ 40 * 3436291 * 2
def baseEnd_3436291 : Nat := 1764468951719120229359291

theorem tailTrace_3436291 : CollatzResearch.WordTrace tailWord_3436291 prefixEnd_3436291 1764468951719120229359291 := by
  unfold tailWord_3436291
  simp only [CollatzResearch.WordTrace]
  refine ⟨125331829193912053624660727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83554552795941369083107151 125331829193912053624660727)
  ·
    refine ⟨187997743790868080436991091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125331829193912053624660727 187997743790868080436991091)
    ·
      refine ⟨281996615686302120655486637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187997743790868080436991091 281996615686302120655486637)
      ·
        refine ⟨105748730882363295245807489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281996615686302120655486637 105748730882363295245807489)
        ·
          refine ⟨79311548161772471434355617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105748730882363295245807489 79311548161772471434355617)
          ·
            refine ⟨59483661121329353575766713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79311548161772471434355617 59483661121329353575766713)
            ·
              refine ⟨44612745840997015181825035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59483661121329353575766713 44612745840997015181825035)
              ·
                refine ⟨66919118761495522772737553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44612745840997015181825035 66919118761495522772737553)
                ·
                  refine ⟨50189339071121642079553165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66919118761495522772737553 50189339071121642079553165)
                  ·
                    refine ⟨18821002151670615779832437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50189339071121642079553165 18821002151670615779832437)
                    ·
                      refine ⟨1764468951719120229359291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18821002151670615779832437 1764468951719120229359291)
                      ·
                        rfl

theorem cell23_3436291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_3436291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436291 prefixEnd_3436291 := by exact prefixLift 3436291
  have htrace : WordTrace (prefixWord ++ tailWord_3436291) baseStart_3436291 baseEnd_3436291 := by
    simpa [prefixWord, tailWord_3436291, baseEnd_3436291] using wordTrace_append hprefix tailTrace_3436291
  have hstable : (prefixWord ++ tailWord_3436291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436291).length < 2 ^ (prefixWord ++ tailWord_3436291).sum := by decide
  have hdescent : baseEnd_3436291 < baseStart_3436291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436328 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 8]
def baseStart_3436328 : Nat := 118140960795 + 3436328 * 2 ^ 59
def prefixEnd_3436328 : Nat := 4983230072969 + 3 ^ 40 * 3436328 * 2
def baseEnd_3436328 : Nat := 196054216722592953844069

theorem tailTrace_3436328 : CollatzResearch.WordTrace tailWord_3436328 prefixEnd_3436328 196054216722592953844069 := by
  unfold tailWord_3436328
  simp only [CollatzResearch.WordTrace]
  refine ⟨62666589347389004471878819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83555452463185339295838425 62666589347389004471878819)
  ·
    refine ⟨93999884021083506707818229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62666589347389004471878819 93999884021083506707818229)
    ·
      refine ⟨8812489126976578753857959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93999884021083506707818229 8812489126976578753857959)
      ·
        refine ⟨13218733690464868130786939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8812489126976578753857959 13218733690464868130786939)
        ·
          refine ⟨19828100535697302196180409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13218733690464868130786939 19828100535697302196180409)
          ·
            refine ⟨14871075401772976647135307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19828100535697302196180409 14871075401772976647135307)
            ·
              refine ⟨22306613102659464970702961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14871075401772976647135307 22306613102659464970702961)
              ·
                refine ⟨16729959826994598728027221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22306613102659464970702961 16729959826994598728027221)
                ·
                  refine ⟨196054216722592953844069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16729959826994598728027221 196054216722592953844069)
                  ·
                    rfl

theorem cell23_3436328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 8].length) (baseStart_3436328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436328 prefixEnd_3436328 := by exact prefixLift 3436328
  have htrace : WordTrace (prefixWord ++ tailWord_3436328) baseStart_3436328 baseEnd_3436328 := by
    simpa [prefixWord, tailWord_3436328, baseEnd_3436328] using wordTrace_append hprefix tailTrace_3436328
  have hstable : (prefixWord ++ tailWord_3436328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436328).length < 2 ^ (prefixWord ++ tailWord_3436328).sum := by decide
  have hdescent : baseEnd_3436328 < baseStart_3436328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436332 : List Nat := [2, 2, 1, 1, 1, 5, 3, 3, 1, 4]
def baseStart_3436332 : Nat := 118140960795 + 3436332 * 2 ^ 59
def prefixEnd_3436332 : Nat := 4983230072969 + 3 ^ 40 * 3436332 * 2
def baseEnd_3436332 : Nat := 588163334808651522982201

theorem tailTrace_3436332 : CollatzResearch.WordTrace tailWord_3436332 prefixEnd_3436332 588163334808651522982201 := by
  unfold tailWord_3436332
  simp only [CollatzResearch.WordTrace]
  refine ⟨62666662293381758813451625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83555549724509011751268833 62666662293381758813451625)
  ·
    refine ⟨46999996720036319110088719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62666662293381758813451625 46999996720036319110088719)
    ·
      refine ⟨70499995080054478665133079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46999996720036319110088719 70499995080054478665133079)
      ·
        refine ⟨105749992620081717997699619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70499995080054478665133079 105749992620081717997699619)
        ·
          refine ⟨158624988930122576996549429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105749992620081717997699619 158624988930122576996549429)
          ·
            refine ⟨14871092712198991593426509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158624988930122576996549429 14871092712198991593426509)
            ·
              refine ⟨5576659767074621847534941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14871092712198991593426509 5576659767074621847534941)
              ·
                refine ⟨2091247412652983192825603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5576659767074621847534941 2091247412652983192825603)
                ·
                  refine ⟨3136871118979474789238405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2091247412652983192825603 3136871118979474789238405)
                  ·
                    refine ⟨588163334808651522982201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3136871118979474789238405 588163334808651522982201)
                    ·
                      rfl

theorem cell23_3436332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 1, 4].length) (baseStart_3436332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436332 prefixEnd_3436332 := by exact prefixLift 3436332
  have htrace : WordTrace (prefixWord ++ tailWord_3436332) baseStart_3436332 baseEnd_3436332 := by
    simpa [prefixWord, tailWord_3436332, baseEnd_3436332] using wordTrace_append hprefix tailTrace_3436332
  have hstable : (prefixWord ++ tailWord_3436332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436332).length < 2 ^ (prefixWord ++ tailWord_3436332).sum := by decide
  have hdescent : baseEnd_3436332 < baseStart_3436332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436342 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_3436342 : Nat := 118140960795 + 3436342 * 2 ^ 59
def prefixEnd_3436342 : Nat := 4983230072969 + 3 ^ 40 * 3436342 * 2
def baseEnd_3436342 : Nat := 1764495139232499529821557

theorem tailTrace_3436342 : CollatzResearch.WordTrace tailWord_3436342 prefixEnd_3436342 1764495139232499529821557 := by
  unfold tailWord_3436342
  simp only [CollatzResearch.WordTrace]
  refine ⟨7833355582295455583422955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83555792877818192889844853 7833355582295455583422955)
  ·
    refine ⟨11750033373443183375134433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7833355582295455583422955 11750033373443183375134433)
    ·
      refine ⟨8812525030082387531350825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11750033373443183375134433 8812525030082387531350825)
      ·
        refine ⟨6609393772561790648513119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8812525030082387531350825 6609393772561790648513119)
        ·
          refine ⟨9914090658842685972769679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6609393772561790648513119 9914090658842685972769679)
          ·
            refine ⟨14871135988264028959154519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9914090658842685972769679 14871135988264028959154519)
            ·
              refine ⟨22306703982396043438731779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14871135988264028959154519 22306703982396043438731779)
              ·
                refine ⟨33460055973594065158097669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22306703982396043438731779 33460055973594065158097669)
                ·
                  refine ⟨6273760495048887217143313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33460055973594065158097669 6273760495048887217143313)
                  ·
                    refine ⟨4705320371286665412857485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6273760495048887217143313 4705320371286665412857485)
                    ·
                      refine ⟨1764495139232499529821557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4705320371286665412857485 1764495139232499529821557)
                      ·
                        rfl

theorem cell23_3436342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_3436342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436342 prefixEnd_3436342 := by exact prefixLift 3436342
  have htrace : WordTrace (prefixWord ++ tailWord_3436342) baseStart_3436342 baseEnd_3436342 := by
    simpa [prefixWord, tailWord_3436342, baseEnd_3436342] using wordTrace_append hprefix tailTrace_3436342
  have hstable : (prefixWord ++ tailWord_3436342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436342).length < 2 ^ (prefixWord ++ tailWord_3436342).sum := by decide
  have hdescent : baseEnd_3436342 < baseStart_3436342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436375 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 3, 5]
def baseStart_3436375 : Nat := 118140960795 + 3436375 * 2 ^ 59
def prefixEnd_3436375 : Nat := 4983230072969 + 3 ^ 40 * 3436375 * 2
def baseEnd_3436375 : Nat := 588170694698032633569635

theorem tailTrace_3436375 : CollatzResearch.WordTrace tailWord_3436375 prefixEnd_3436375 588170694698032633569635 := by
  unfold tailWord_3436375
  simp only [CollatzResearch.WordTrace]
  refine ⟨125334892925607735970718579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83556595283738490647145719 125334892925607735970718579)
  ·
    refine ⟨188002339388411603956077869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125334892925607735970718579 188002339388411603956077869)
    ·
      refine ⟨70500877270654351483529201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188002339388411603956077869 70500877270654351483529201)
      ·
        refine ⟨52875657952990763612646901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70500877270654351483529201 52875657952990763612646901)
        ·
          refine ⟨4957092933092884088685647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52875657952990763612646901 4957092933092884088685647)
          ·
            refine ⟨7435639399639326133028471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4957092933092884088685647 7435639399639326133028471)
            ·
              refine ⟨11153459099458989199542707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7435639399639326133028471 11153459099458989199542707)
              ·
                refine ⟨16730188649188483799314061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11153459099458989199542707 16730188649188483799314061)
                ·
                  refine ⟨6273820743445681424742773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16730188649188483799314061 6273820743445681424742773)
                  ·
                    refine ⟨588170694698032633569635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6273820743445681424742773 588170694698032633569635)
                    ·
                      rfl

theorem cell23_3436375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_3436375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436375 prefixEnd_3436375 := by exact prefixLift 3436375
  have htrace : WordTrace (prefixWord ++ tailWord_3436375) baseStart_3436375 baseEnd_3436375 := by
    simpa [prefixWord, tailWord_3436375, baseEnd_3436375] using wordTrace_append hprefix tailTrace_3436375
  have hstable : (prefixWord ++ tailWord_3436375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436375).length < 2 ^ (prefixWord ++ tailWord_3436375).sum := by decide
  have hdescent : baseEnd_3436375 < baseStart_3436375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436392 : List Nat := [2, 1, 4, 2, 1, 1, 5, 1, 1, 5]
def baseStart_3436392 : Nat := 118140960795 + 3436392 * 2 ^ 59
def prefixEnd_3436392 : Nat := 4983230072969 + 3 ^ 40 * 3436392 * 2
def baseEnd_3436392 : Nat := 588173604421741444732109

theorem tailTrace_3436392 : CollatzResearch.WordTrace tailWord_3436392 prefixEnd_3436392 588173604421741444732109 := by
  unfold tailWord_3436392
  simp only [CollatzResearch.WordTrace]
  refine ⟨62667756483273073937043715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83557008644364098582724953 62667756483273073937043715)
  ·
    refine ⟨94001634724909610905565573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62667756483273073937043715 94001634724909610905565573)
    ·
      refine ⟨17625306510920552044793545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94001634724909610905565573 17625306510920552044793545)
      ·
        refine ⟨13218979883190414033595159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17625306510920552044793545 13218979883190414033595159)
        ·
          refine ⟨19828469824785621050392739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13218979883190414033595159 19828469824785621050392739)
          ·
            refine ⟨29742704737178431575589109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19828469824785621050392739 29742704737178431575589109)
            ·
              refine ⟨2788378569110477960211479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29742704737178431575589109 2788378569110477960211479)
              ·
                refine ⟨4182567853665716940317219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2788378569110477960211479 4182567853665716940317219)
                ·
                  refine ⟨6273851780498575410475829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4182567853665716940317219 6273851780498575410475829)
                  ·
                    refine ⟨588173604421741444732109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6273851780498575410475829 588173604421741444732109)
                    ·
                      rfl

theorem cell23_3436392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_3436392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436392 prefixEnd_3436392 := by exact prefixLift 3436392
  have htrace : WordTrace (prefixWord ++ tailWord_3436392) baseStart_3436392 baseEnd_3436392 := by
    simpa [prefixWord, tailWord_3436392, baseEnd_3436392] using wordTrace_append hprefix tailTrace_3436392
  have hstable : (prefixWord ++ tailWord_3436392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436392).length < 2 ^ (prefixWord ++ tailWord_3436392).sum := by decide
  have hdescent : baseEnd_3436392 < baseStart_3436392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436425 : List Nat := [1, 2, 1, 1, 5, 1, 4, 1, 1, 2, 4]
def baseStart_3436425 : Nat := 118140960795 + 3436425 * 2 ^ 59
def prefixEnd_3436425 : Nat := 4983230072969 + 3 ^ 40 * 3436425 * 2
def baseEnd_3436425 : Nat := 1764537758126822705083675

theorem tailTrace_3436425 : CollatzResearch.WordTrace tailWord_3436425 prefixEnd_3436425 1764537758126822705083675 := by
  unfold tailWord_3436425
  simp only [CollatzResearch.WordTrace]
  refine ⟨125336716575426594510038729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83557811050284396340025819 125336716575426594510038729)
  ·
    refine ⟨94002537431569945882529047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125336716575426594510038729 94002537431569945882529047)
    ·
      refine ⟨141003806147354918823793571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94002537431569945882529047 141003806147354918823793571)
      ·
        refine ⟨211505709221032378235690357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141003806147354918823793571 211505709221032378235690357)
        ·
          refine ⟨19828660239471785459595971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 211505709221032378235690357 19828660239471785459595971)
          ·
            refine ⟨29742990359207678189393957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19828660239471785459595971 29742990359207678189393957)
            ·
              refine ⟨5576810692351439660511367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29742990359207678189393957 5576810692351439660511367)
              ·
                refine ⟨8365216038527159490767051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5576810692351439660511367 8365216038527159490767051)
                ·
                  refine ⟨12547824057790739236150577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8365216038527159490767051 12547824057790739236150577)
                  ·
                    refine ⟨9410868043343054427112933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12547824057790739236150577 9410868043343054427112933)
                    ·
                      refine ⟨1764537758126822705083675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9410868043343054427112933 1764537758126822705083675)
                      ·
                        rfl

theorem cell23_3436425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 2, 4].length) (baseStart_3436425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436425 prefixEnd_3436425 := by exact prefixLift 3436425
  have htrace : WordTrace (prefixWord ++ tailWord_3436425) baseStart_3436425 baseEnd_3436425 := by
    simpa [prefixWord, tailWord_3436425, baseEnd_3436425] using wordTrace_append hprefix tailTrace_3436425
  have hstable : (prefixWord ++ tailWord_3436425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436425).length < 2 ^ (prefixWord ++ tailWord_3436425).sum := by decide
  have hdescent : baseEnd_3436425 < baseStart_3436425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436446 : List Nat := [4, 3, 1, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3436446 : Nat := 118140960795 + 3436446 * 2 ^ 59
def prefixEnd_3436446 : Nat := 4983230072969 + 3 ^ 40 * 3436446 * 2
def baseEnd_3436446 : Nat := 1764548541220567122921079

theorem tailTrace_3436446 : CollatzResearch.WordTrace tailWord_3436446 prefixEnd_3436446 1764548541220567122921079 := by
  unfold tailWord_3436446
  simp only [CollatzResearch.WordTrace]
  refine ⟨15667185313543814387069149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83558321672233676731035461 15667185313543814387069149)
  ·
    refine ⟨5875194492578930395150931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15667185313543814387069149 5875194492578930395150931)
    ·
      refine ⟨8812791738868395592726397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5875194492578930395150931 8812791738868395592726397)
      ·
        refine ⟨3304796902075648347272399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8812791738868395592726397 3304796902075648347272399)
        ·
          refine ⟨4957195353113472520908599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3304796902075648347272399 4957195353113472520908599)
          ·
            refine ⟨7435793029670208781362899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4957195353113472520908599 7435793029670208781362899)
            ·
              refine ⟨11153689544505313172044349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7435793029670208781362899 11153689544505313172044349)
              ·
                refine ⟨4182633579189492439516631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11153689544505313172044349 4182633579189492439516631)
                ·
                  refine ⟨6273950368784238659274947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4182633579189492439516631 6273950368784238659274947)
                  ·
                    refine ⟨9410925553176357988912421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6273950368784238659274947 9410925553176357988912421)
                    ·
                      refine ⟨1764548541220567122921079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9410925553176357988912421 1764548541220567122921079)
                      ·
                        rfl

theorem cell23_3436446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3436446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436446 prefixEnd_3436446 := by exact prefixLift 3436446
  have htrace : WordTrace (prefixWord ++ tailWord_3436446) baseStart_3436446 baseEnd_3436446 := by
    simpa [prefixWord, tailWord_3436446, baseEnd_3436446] using wordTrace_append hprefix tailTrace_3436446
  have hstable : (prefixWord ++ tailWord_3436446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436446).length < 2 ^ (prefixWord ++ tailWord_3436446).sum := by decide
  have hdescent : baseEnd_3436446 < baseStart_3436446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436449 : List Nat := [1, 2, 3, 4, 2, 1, 1, 3, 1, 2, 3]
def baseStart_3436449 : Nat := 118140960795 + 3436449 * 2 ^ 59
def prefixEnd_3436449 : Nat := 4983230072969 + 3 ^ 40 * 3436449 * 2
def baseEnd_3436449 : Nat := 1764550081662530611183565

theorem tailTrace_3436449 : CollatzResearch.WordTrace tailWord_3436449 prefixEnd_3436449 1764550081662530611183565 := by
  unfold tailWord_3436449
  simp only [CollatzResearch.WordTrace]
  refine ⟨125337591927339646608912401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83558394618226431072608267 125337591927339646608912401)
  ·
    refine ⟨94003193945504734956684301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125337591927339646608912401 94003193945504734956684301)
    ·
      refine ⟨35251197729564275608756613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94003193945504734956684301 35251197729564275608756613)
      ·
        refine ⟨6609599574293301676641865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35251197729564275608756613 6609599574293301676641865)
        ·
          refine ⟨4957199680719976257481399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6609599574293301676641865 4957199680719976257481399)
          ·
            refine ⟨7435799521079964386222099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4957199680719976257481399 7435799521079964386222099)
            ·
              refine ⟨11153699281619946579333149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7435799521079964386222099 11153699281619946579333149)
              ·
                refine ⟨4182637230607479967249931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11153699281619946579333149 4182637230607479967249931)
                ·
                  refine ⟨6273955845911219950874897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4182637230607479967249931 6273955845911219950874897)
                  ·
                    refine ⟨4705466884433414963156173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6273955845911219950874897 4705466884433414963156173)
                    ·
                      refine ⟨1764550081662530611183565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4705466884433414963156173 1764550081662530611183565)
                      ·
                        rfl

theorem cell23_3436449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_3436449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436449 prefixEnd_3436449 := by exact prefixLift 3436449
  have htrace : WordTrace (prefixWord ++ tailWord_3436449) baseStart_3436449 baseEnd_3436449 := by
    simpa [prefixWord, tailWord_3436449, baseEnd_3436449] using wordTrace_append hprefix tailTrace_3436449
  have hstable : (prefixWord ++ tailWord_3436449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436449).length < 2 ^ (prefixWord ++ tailWord_3436449).sum := by decide
  have hdescent : baseEnd_3436449 < baseStart_3436449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436476 : List Nat := [2, 2, 2, 5, 2, 1, 1, 1, 1, 2, 4]
def baseStart_3436476 : Nat := 118140960795 + 3436476 * 2 ^ 59
def prefixEnd_3436476 : Nat := 4983230072969 + 3 ^ 40 * 3436476 * 2
def baseEnd_3436476 : Nat := 1764563945640202005545941

theorem tailTrace_3436476 : CollatzResearch.WordTrace tailWord_3436476 prefixEnd_3436476 1764563945640202005545941 := by
  unfold tailWord_3436476
  simp only [CollatzResearch.WordTrace]
  refine ⟨62669288349120915110072641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83559051132161220146763521 62669288349120915110072641)
  ·
    refine ⟨47001966261840686332554481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62669288349120915110072641 47001966261840686332554481)
    ·
      refine ⟨35251474696380514749415861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47001966261840686332554481 35251474696380514749415861)
      ·
        refine ⟨3304825752785673257757737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35251474696380514749415861 3304825752785673257757737)
        ·
          refine ⟨2478619314589254943318303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3304825752785673257757737 2478619314589254943318303)
          ·
            refine ⟨3717928971883882414977455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2478619314589254943318303 3717928971883882414977455)
            ·
              refine ⟨5576893457825823622466183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3717928971883882414977455 5576893457825823622466183)
              ·
                refine ⟨8365340186738735433699275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5576893457825823622466183 8365340186738735433699275)
                ·
                  refine ⟨12548010280108103150548913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8365340186738735433699275 12548010280108103150548913)
                  ·
                    refine ⟨9411007710081077362911685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12548010280108103150548913 9411007710081077362911685)
                    ·
                      refine ⟨1764563945640202005545941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9411007710081077362911685 1764563945640202005545941)
                      ·
                        rfl

theorem cell23_3436476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_3436476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436476 prefixEnd_3436476 := by exact prefixLift 3436476
  have htrace : WordTrace (prefixWord ++ tailWord_3436476) baseStart_3436476 baseEnd_3436476 := by
    simpa [prefixWord, tailWord_3436476, baseEnd_3436476] using wordTrace_append hprefix tailTrace_3436476
  have hstable : (prefixWord ++ tailWord_3436476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436476).length < 2 ^ (prefixWord ++ tailWord_3436476).sum := by decide
  have hdescent : baseEnd_3436476 < baseStart_3436476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436479 : List Nat := [1, 1, 2, 2, 2, 1, 7, 1, 2, 1, 3]
def baseStart_3436479 : Nat := 118140960795 + 3436479 * 2 ^ 59
def prefixEnd_3436479 : Nat := 4983230072969 + 3 ^ 40 * 3436479 * 2
def baseEnd_3436479 : Nat := 1764565486082165493808427

theorem tailTrace_3436479 : CollatzResearch.WordTrace tailWord_3436479 prefixEnd_3436479 1764565486082165493808427 := by
  unfold tailWord_3436479
  simp only [CollatzResearch.WordTrace]
  refine ⟨125338686117230961732504491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83559124078153974488336327 125338686117230961732504491)
  ·
    refine ⟨188008029175846442598756737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125338686117230961732504491 188008029175846442598756737)
    ·
      refine ⟨141006021881884831949067553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188008029175846442598756737 141006021881884831949067553)
      ·
        refine ⟨105754516411413623961800665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141006021881884831949067553 105754516411413623961800665)
        ·
          refine ⟨79315887308560217971350499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105754516411413623961800665 79315887308560217971350499)
          ·
            refine ⟨118973830962840326957025749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79315887308560217971350499 118973830962840326957025749)
            ·
              refine ⟨2788449163191570163055291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 118973830962840326957025749 2788449163191570163055291)
              ·
                refine ⟨4182673744787355244582937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2788449163191570163055291 4182673744787355244582937)
                ·
                  refine ⟨3137005308590516433437203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4182673744787355244582937 3137005308590516433437203)
                  ·
                    refine ⟨4705507962885774650155805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3137005308590516433437203 4705507962885774650155805)
                    ·
                      refine ⟨1764565486082165493808427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4705507962885774650155805 1764565486082165493808427)
                      ·
                        rfl

theorem cell23_3436479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 2, 1, 3].length) (baseStart_3436479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436479 prefixEnd_3436479 := by exact prefixLift 3436479
  have htrace : WordTrace (prefixWord ++ tailWord_3436479) baseStart_3436479 baseEnd_3436479 := by
    simpa [prefixWord, tailWord_3436479, baseEnd_3436479] using wordTrace_append hprefix tailTrace_3436479
  have hstable : (prefixWord ++ tailWord_3436479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436479).length < 2 ^ (prefixWord ++ tailWord_3436479).sum := by decide
  have hdescent : baseEnd_3436479 < baseStart_3436479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436536 : List Nat := [2, 1, 2, 1, 1, 3, 6, 1, 2, 2, 2]
def baseStart_3436536 : Nat := 118140960795 + 3436536 * 2 ^ 59
def prefixEnd_3436536 : Nat := 4983230072969 + 3 ^ 40 * 3436536 * 2
def baseEnd_3436536 : Nat := 1764594754479471770795665

theorem tailTrace_3436536 : CollatzResearch.WordTrace tailWord_3436536 prefixEnd_3436536 1764594754479471770795665 := by
  unfold tailWord_3436536
  simp only [CollatzResearch.WordTrace]
  refine ⟨62670382539012230233664731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83560510052016306978219641 62670382539012230233664731)
  ·
    refine ⟨94005573808518345350497097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62670382539012230233664731 94005573808518345350497097)
    ·
      refine ⟨70504180356388759012872823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94005573808518345350497097 70504180356388759012872823)
      ·
        refine ⟨105756270534583138519309235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70504180356388759012872823 105756270534583138519309235)
        ·
          refine ⟨158634405801874707778963853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105756270534583138519309235 158634405801874707778963853)
          ·
            refine ⟨59487902175703015417111445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158634405801874707778963853 59487902175703015417111445)
            ·
              refine ⟨2788495414486078847677099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59487902175703015417111445 2788495414486078847677099)
              ·
                refine ⟨4182743121729118271515649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2788495414486078847677099 4182743121729118271515649)
                ·
                  refine ⟨3137057341296838703636737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4182743121729118271515649 3137057341296838703636737)
                  ·
                    refine ⟨2352793005972629027727553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3137057341296838703636737 2352793005972629027727553)
                    ·
                      refine ⟨1764594754479471770795665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2352793005972629027727553 1764594754479471770795665)
                      ·
                        rfl

theorem cell23_3436536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 2, 2, 2].length) (baseStart_3436536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436536 prefixEnd_3436536 := by exact prefixLift 3436536
  have htrace : WordTrace (prefixWord ++ tailWord_3436536) baseStart_3436536 baseEnd_3436536 := by
    simpa [prefixWord, tailWord_3436536, baseEnd_3436536] using wordTrace_append hprefix tailTrace_3436536
  have hstable : (prefixWord ++ tailWord_3436536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436536).length < 2 ^ (prefixWord ++ tailWord_3436536).sum := by decide
  have hdescent : baseEnd_3436536 < baseStart_3436536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436557 : List Nat := [1, 7, 1, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_3436557 : Nat := 118140960795 + 3436557 * 2 ^ 59
def prefixEnd_3436557 : Nat := 4983230072969 + 3 ^ 40 * 3436557 * 2
def baseEnd_3436557 : Nat := 1764605537573216188633069

theorem tailTrace_3436557 : CollatzResearch.WordTrace tailWord_3436557 prefixEnd_3436557 1764605537573216188633069 := by
  unfold tailWord_3436557
  simp only [CollatzResearch.WordTrace]
  refine ⟨125341531010948381053843925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83561020673965587369229283 125341531010948381053843925)
  ·
    refine ⟨2937692133069102680949467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 125341531010948381053843925 2937692133069102680949467)
    ·
      refine ⟨4406538199603654021424201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2937692133069102680949467 4406538199603654021424201)
      ·
        refine ⟨3304903649702740516068151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4406538199603654021424201 3304903649702740516068151)
        ·
          refine ⟨4957355474554110774102227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3304903649702740516068151 4957355474554110774102227)
          ·
            refine ⟨7436033211831166161153341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4957355474554110774102227 7436033211831166161153341)
            ·
              refine ⟨2788512454436687310432503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7436033211831166161153341 2788512454436687310432503)
              ·
                refine ⟨4182768681655030965648755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2788512454436687310432503 4182768681655030965648755)
                ·
                  refine ⟨6274153022482546448473133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4182768681655030965648755 6274153022482546448473133)
                  ·
                    refine ⟨2352807383430954918177425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6274153022482546448473133 2352807383430954918177425)
                    ·
                      refine ⟨1764605537573216188633069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2352807383430954918177425 1764605537573216188633069)
                      ·
                        rfl

theorem cell23_3436557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_3436557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436557 prefixEnd_3436557 := by exact prefixLift 3436557
  have htrace : WordTrace (prefixWord ++ tailWord_3436557) baseStart_3436557 baseEnd_3436557 := by
    simpa [prefixWord, tailWord_3436557, baseEnd_3436557] using wordTrace_append hprefix tailTrace_3436557
  have hstable : (prefixWord ++ tailWord_3436557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436557).length < 2 ^ (prefixWord ++ tailWord_3436557).sum := by decide
  have hdescent : baseEnd_3436557 < baseStart_3436557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436572 : List Nat := [2, 2, 3, 1, 3, 1, 2, 2, 2, 5]
def baseStart_3436572 : Nat := 118140960795 + 3436572 * 2 ^ 59
def prefixEnd_3436572 : Nat := 4983230072969 + 3 ^ 40 * 3436572 * 2
def baseEnd_3436572 : Nat := 588204413261011209981833

theorem tailTrace_3436572 : CollatzResearch.WordTrace tailWord_3436572 prefixEnd_3436572 588204413261011209981833 := by
  unfold tailWord_3436572
  simp only [CollatzResearch.WordTrace]
  refine ⟨62671039052947019307819985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83561385403929359077093313 62671039052947019307819985)
  ·
    refine ⟨47003279289710264480864989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62671039052947019307819985 47003279289710264480864989)
    ·
      refine ⟨17626229733641349180324371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47003279289710264480864989 17626229733641349180324371)
      ·
        refine ⟨26439344600462023770486557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17626229733641349180324371 26439344600462023770486557)
        ·
          refine ⟨9914754225173258913932459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26439344600462023770486557 9914754225173258913932459)
          ·
            refine ⟨14872131337759888370898689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9914754225173258913932459 14872131337759888370898689)
            ·
              refine ⟨11154098503319916278174017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14872131337759888370898689 11154098503319916278174017)
              ·
                refine ⟨8365573877489937208630513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11154098503319916278174017 8365573877489937208630513)
                ·
                  refine ⟨6274180408117452906472885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8365573877489937208630513 6274180408117452906472885)
                  ·
                    refine ⟨588204413261011209981833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6274180408117452906472885 588204413261011209981833)
                    ·
                      rfl

theorem cell23_3436572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_3436572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436572 prefixEnd_3436572 := by exact prefixLift 3436572
  have htrace : WordTrace (prefixWord ++ tailWord_3436572) baseStart_3436572 baseEnd_3436572 := by
    simpa [prefixWord, tailWord_3436572, baseEnd_3436572] using wordTrace_append hprefix tailTrace_3436572
  have hstable : (prefixWord ++ tailWord_3436572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436572).length < 2 ^ (prefixWord ++ tailWord_3436572).sum := by decide
  have hdescent : baseEnd_3436572 < baseStart_3436572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436592 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 1, 6, 2]
def baseStart_3436592 : Nat := 118140960795 + 3436592 * 2 ^ 59
def prefixEnd_3436592 : Nat := 4983230072969 + 3 ^ 40 * 3436592 * 2
def baseEnd_3436592 : Nat := 1764623509396123551695407

theorem tailTrace_3436592 : CollatzResearch.WordTrace tailWord_3436592 prefixEnd_3436592 1764623509396123551695407 := by
  unfold tailWord_3436592
  simp only [CollatzResearch.WordTrace]
  refine ⟨62671403782910791015684015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83561871710547721354245353 62671403782910791015684015)
  ·
    refine ⟨94007105674366186523526023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62671403782910791015684015 94007105674366186523526023)
    ·
      refine ⟨141010658511549279785289035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94007105674366186523526023 141010658511549279785289035)
      ·
        refine ⟨211515987767323919677933553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141010658511549279785289035 211515987767323919677933553)
        ·
          refine ⟨158636990825492939758450165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211515987767323919677933553 158636990825492939758450165)
          ·
            refine ⟨14872217889889963102354703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158636990825492939758450165 14872217889889963102354703)
            ·
              refine ⟨22308326834834944653532055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14872217889889963102354703 22308326834834944653532055)
              ·
                refine ⟨33462490252252416980298083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22308326834834944653532055 33462490252252416980298083)
                ·
                  refine ⟨50193735378378625470447125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33462490252252416980298083 50193735378378625470447125)
                  ·
                    refine ⟨2352831345861498068927209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50193735378378625470447125 2352831345861498068927209)
                    ·
                      refine ⟨1764623509396123551695407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2352831345861498068927209 1764623509396123551695407)
                      ·
                        rfl

theorem cell23_3436592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 1, 6, 2].length) (baseStart_3436592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436592 prefixEnd_3436592 := by exact prefixLift 3436592
  have htrace : WordTrace (prefixWord ++ tailWord_3436592) baseStart_3436592 baseEnd_3436592 := by
    simpa [prefixWord, tailWord_3436592, baseEnd_3436592] using wordTrace_append hprefix tailTrace_3436592
  have hstable : (prefixWord ++ tailWord_3436592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436592).length < 2 ^ (prefixWord ++ tailWord_3436592).sum := by decide
  have hdescent : baseEnd_3436592 < baseStart_3436592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436606 : List Nat := [4, 2, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_3436606 : Nat := 118140960795 + 3436606 * 2 ^ 59
def prefixEnd_3436606 : Nat := 4983230072969 + 3 ^ 40 * 3436606 * 2
def baseEnd_3436606 : Nat := 588210232708428832306781

theorem tailTrace_3436606 : CollatzResearch.WordTrace tailWord_3436606 prefixEnd_3436606 588210232708428832306781 := by
  unfold tailWord_3436606
  simp only [CollatzResearch.WordTrace]
  refine ⟨15667914773471357802797209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83562212125180574948251781 15667914773471357802797209)
  ·
    refine ⟨11750936080103518352097907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15667914773471357802797209 11750936080103518352097907)
    ·
      refine ⟨17626404120155277528146861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11750936080103518352097907 17626404120155277528146861)
      ·
        refine ⟨6609901545058229073055073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17626404120155277528146861 6609901545058229073055073)
        ·
          refine ⟨4957426158793671804791305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6609901545058229073055073 4957426158793671804791305)
          ·
            refine ⟨3718069619095253853593479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4957426158793671804791305 3718069619095253853593479)
            ·
              refine ⟨5577104428642880780390219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3718069619095253853593479 5577104428642880780390219)
              ·
                refine ⟨8365656642964321170585329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5577104428642880780390219 8365656642964321170585329)
                ·
                  refine ⟨6274242482223240877938997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8365656642964321170585329 6274242482223240877938997)
                  ·
                    refine ⟨588210232708428832306781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6274242482223240877938997 588210232708428832306781)
                    ·
                      rfl

theorem cell23_3436606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_3436606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436606 prefixEnd_3436606 := by exact prefixLift 3436606
  have htrace : WordTrace (prefixWord ++ tailWord_3436606) baseStart_3436606 baseEnd_3436606 := by
    simpa [prefixWord, tailWord_3436606, baseEnd_3436606] using wordTrace_append hprefix tailTrace_3436606
  have hstable : (prefixWord ++ tailWord_3436606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436606).length < 2 ^ (prefixWord ++ tailWord_3436606).sum := by decide
  have hdescent : baseEnd_3436606 < baseStart_3436606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436609 : List Nat := [1, 2, 5, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_3436609 : Nat := 118140960795 + 3436609 * 2 ^ 59
def prefixEnd_3436609 : Nat := 4983230072969 + 3 ^ 40 * 3436609 * 2
def baseEnd_3436609 : Nat := 1764632238567249985182829

theorem tailTrace_3436609 : CollatzResearch.WordTrace tailWord_3436609 prefixEnd_3436609 1764632238567249985182829 := by
  unfold tailWord_3436609
  simp only [CollatzResearch.WordTrace]
  refine ⟨125343427606759993934736881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83562285071173329289824587 125343427606759993934736881)
  ·
    refine ⟨94007570705069995451052661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125343427606759993934736881 94007570705069995451052661)
    ·
      refine ⟨8813209753600312073536187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94007570705069995451052661 8813209753600312073536187)
      ·
        refine ⟨13219814630400468110304281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8813209753600312073536187 13219814630400468110304281)
        ·
          refine ⟨9914860972800351082728211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13219814630400468110304281 9914860972800351082728211)
          ·
            refine ⟨14872291459200526624092317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9914860972800351082728211 14872291459200526624092317)
            ·
              refine ⟨5577109297200197484034619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14872291459200526624092317 5577109297200197484034619)
              ·
                refine ⟨8365663945800296226051929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5577109297200197484034619 8365663945800296226051929)
                ·
                  refine ⟨6274247959350222169538947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8365663945800296226051929 6274247959350222169538947)
                  ·
                    refine ⟨9411371939025333254308421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6274247959350222169538947 9411371939025333254308421)
                    ·
                      refine ⟨1764632238567249985182829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9411371939025333254308421 1764632238567249985182829)
                      ·
                        rfl

theorem cell23_3436609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_3436609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436609 prefixEnd_3436609 := by exact prefixLift 3436609
  have htrace : WordTrace (prefixWord ++ tailWord_3436609) baseStart_3436609 baseEnd_3436609 := by
    simpa [prefixWord, tailWord_3436609, baseEnd_3436609] using wordTrace_append hprefix tailTrace_3436609
  have hstable : (prefixWord ++ tailWord_3436609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436609).length < 2 ^ (prefixWord ++ tailWord_3436609).sum := by decide
  have hdescent : baseEnd_3436609 < baseStart_3436609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436615 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 8]
def baseStart_3436615 : Nat := 118140960795 + 3436615 * 2 ^ 59
def prefixEnd_3436615 : Nat := 4983230072969 + 3 ^ 40 * 3436615 * 2
def baseEnd_3436615 : Nat := 196070591050130773523089

theorem tailTrace_3436615 : CollatzResearch.WordTrace tailWord_3436615 prefixEnd_3436615 196070591050130773523089 := by
  unfold tailWord_3436615
  simp only [CollatzResearch.WordTrace]
  refine ⟨125343646444738256959455299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83562430963158837972970199 125343646444738256959455299)
  ·
    refine ⟨188015469667107385439182949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125343646444738256959455299 188015469667107385439182949)
    ·
      refine ⟨35252900562582634769846803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188015469667107385439182949 35252900562582634769846803)
      ·
        refine ⟨52879350843873952154770205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35252900562582634769846803 52879350843873952154770205)
        ·
          refine ⟨19829756566452732058038827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52879350843873952154770205 19829756566452732058038827)
          ·
            refine ⟨29744634849679098087058241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19829756566452732058038827 29744634849679098087058241)
            ·
              refine ⟨22308476137259323565293681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29744634849679098087058241 22308476137259323565293681)
              ·
                refine ⟨16731357102944492673970261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22308476137259323565293681 16731357102944492673970261)
                ·
                  refine ⟨196070591050130773523089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16731357102944492673970261 196070591050130773523089)
                  ·
                    rfl

theorem cell23_3436615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 8].length) (baseStart_3436615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436615 prefixEnd_3436615 := by exact prefixLift 3436615
  have htrace : WordTrace (prefixWord ++ tailWord_3436615) baseStart_3436615 baseEnd_3436615 := by
    simpa [prefixWord, tailWord_3436615, baseEnd_3436615] using wordTrace_append hprefix tailTrace_3436615
  have hstable : (prefixWord ++ tailWord_3436615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436615).length < 2 ^ (prefixWord ++ tailWord_3436615).sum := by decide
  have hdescent : baseEnd_3436615 < baseStart_3436615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436632 : List Nat := [2, 1, 2, 2, 1, 4, 3, 2, 6]
def baseStart_3436632 : Nat := 118140960795 + 3436632 * 2 ^ 59
def prefixEnd_3436632 : Nat := 4983230072969 + 3 ^ 40 * 3436632 * 2
def baseEnd_3436632 : Nat := 196071560958033710577247

theorem tailTrace_3436632 : CollatzResearch.WordTrace tailWord_3436632 prefixEnd_3436632 196071560958033710577247 := by
  unfold tailWord_3436632
  simp only [CollatzResearch.WordTrace]
  refine ⟨62672133242838334431412075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83562844323784445908549433 62672133242838334431412075)
  ·
    refine ⟨94008199864257501647118113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62672133242838334431412075 94008199864257501647118113)
    ·
      refine ⟨70506149898193126235338585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94008199864257501647118113 70506149898193126235338585)
      ·
        refine ⟨52879612423644844676503939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70506149898193126235338585 52879612423644844676503939)
        ·
          refine ⟨79319418635467267014755909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52879612423644844676503939 79319418635467267014755909)
          ·
            refine ⟨14872390994150112565266733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79319418635467267014755909 14872390994150112565266733)
            ·
              refine ⟨5577146622806292211975025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14872390994150112565266733 5577146622806292211975025)
              ·
                refine ⟨4182859967104719158981269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5577146622806292211975025 4182859967104719158981269)
                ·
                  refine ⟨196071560958033710577247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4182859967104719158981269 196071560958033710577247)
                  ·
                    rfl

theorem cell23_3436632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 6].length) (baseStart_3436632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436632 prefixEnd_3436632 := by exact prefixLift 3436632
  have htrace : WordTrace (prefixWord ++ tailWord_3436632) baseStart_3436632 baseEnd_3436632 := by
    simpa [prefixWord, tailWord_3436632, baseEnd_3436632] using wordTrace_append hprefix tailTrace_3436632
  have hstable : (prefixWord ++ tailWord_3436632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436632).length < 2 ^ (prefixWord ++ tailWord_3436632).sum := by decide
  have hdescent : baseEnd_3436632 < baseStart_3436632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436636 : List Nat := [2, 2, 4, 1, 1, 2, 2, 4, 1, 4]
def baseStart_3436636 : Nat := 118140960795 + 3436636 * 2 ^ 59
def prefixEnd_3436636 : Nat := 4983230072969 + 3 ^ 40 * 3436636 * 2
def baseEnd_3436636 : Nat := 588215367514973793181735

theorem tailTrace_3436636 : CollatzResearch.WordTrace tailWord_3436636 prefixEnd_3436636 588215367514973793181735 := by
  unfold tailWord_3436636
  simp only [CollatzResearch.WordTrace]
  refine ⟨62672206188831088772984881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83562941585108118363979841 62672206188831088772984881)
  ·
    refine ⟨47004154641623316579738661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62672206188831088772984881 47004154641623316579738661)
    ·
      refine ⟨8813278995304371858700999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47004154641623316579738661 8813278995304371858700999)
      ·
        refine ⟨13219918492956557788051499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8813278995304371858700999 13219918492956557788051499)
        ·
          refine ⟨19829877739434836682077249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13219918492956557788051499 19829877739434836682077249)
          ·
            refine ⟨14872408304576127511557937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19829877739434836682077249 14872408304576127511557937)
            ·
              refine ⟨11154306228432095633668453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14872408304576127511557937 11154306228432095633668453)
              ·
                refine ⟨2091432417831017931312835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11154306228432095633668453 2091432417831017931312835)
                ·
                  refine ⟨3137148626746526896969253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2091432417831017931312835 3137148626746526896969253)
                  ·
                    refine ⟨588215367514973793181735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3137148626746526896969253 588215367514973793181735)
                    ·
                      rfl

theorem cell23_3436636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_3436636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436636 prefixEnd_3436636 := by exact prefixLift 3436636
  have htrace : WordTrace (prefixWord ++ tailWord_3436636) baseStart_3436636 baseEnd_3436636 := by
    simpa [prefixWord, tailWord_3436636, baseEnd_3436636] using wordTrace_append hprefix tailTrace_3436636
  have hstable : (prefixWord ++ tailWord_3436636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436636).length < 2 ^ (prefixWord ++ tailWord_3436636).sum := by decide
  have hdescent : baseEnd_3436636 < baseStart_3436636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436669 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 1, 5, 2]
def baseStart_3436669 : Nat := 118140960795 + 3436669 * 2 ^ 59
def prefixEnd_3436669 : Nat := 4983230072969 + 3 ^ 40 * 3436669 * 2
def baseEnd_3436669 : Nat := 1764663047406519750432553

theorem tailTrace_3436669 : CollatzResearch.WordTrace tailWord_3436669 prefixEnd_3436669 1764663047406519750432553 := by
  unfold tailWord_3436669
  simp only [CollatzResearch.WordTrace]
  refine ⟨125345615986542624181921061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83563743991028416121280707 125345615986542624181921061)
  ·
    refine ⟨23502302997476742034110199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125345615986542624181921061 23502302997476742034110199)
    ·
      refine ⟨35253454496215113051165299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23502302997476742034110199 35253454496215113051165299)
      ·
        refine ⟨52880181744322669576747949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35253454496215113051165299 52880181744322669576747949)
        ·
          refine ⟨19830068154121001091280481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52880181744322669576747949 19830068154121001091280481)
          ·
            refine ⟨14872551115590750818460361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19830068154121001091280481 14872551115590750818460361)
            ·
              refine ⟨11154413336693063113845271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14872551115590750818460361 11154413336693063113845271)
              ·
                refine ⟨16731620005039594670767907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11154413336693063113845271 16731620005039594670767907)
                ·
                  refine ⟨25097430007559392006151861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16731620005039594670767907 25097430007559392006151861)
                  ·
                    refine ⟨2352884063208693000576737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25097430007559392006151861 2352884063208693000576737)
                    ·
                      refine ⟨1764663047406519750432553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2352884063208693000576737 1764663047406519750432553)
                      ·
                        rfl

theorem cell23_3436669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_3436669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436669 prefixEnd_3436669 := by exact prefixLift 3436669
  have htrace : WordTrace (prefixWord ++ tailWord_3436669) baseStart_3436669 baseEnd_3436669 := by
    simpa [prefixWord, tailWord_3436669, baseEnd_3436669] using wordTrace_append hprefix tailTrace_3436669
  have hstable : (prefixWord ++ tailWord_3436669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436669).length < 2 ^ (prefixWord ++ tailWord_3436669).sum := by decide
  have hdescent : baseEnd_3436669 < baseStart_3436669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436693 : List Nat := [1, 3, 2, 1, 1, 1, 7, 2, 1, 1, 3]
def baseStart_3436693 : Nat := 118140960795 + 3436693 * 2 ^ 59
def prefixEnd_3436693 : Nat := 4983230072969 + 3 ^ 40 * 3436693 * 2
def baseEnd_3436693 : Nat := 1764675370942227656532443

theorem tailTrace_3436693 : CollatzResearch.WordTrace tailWord_3436693 prefixEnd_3436693 1764675370942227656532443 := by
  unfold tailWord_3436693
  simp only [CollatzResearch.WordTrace]
  refine ⟨125346491338455676280794733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83564327558970450853863155 125346491338455676280794733)
  ·
    refine ⟨47004934251920878605298025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125346491338455676280794733 47004934251920878605298025)
    ·
      refine ⟨35253700688940658953973519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47004934251920878605298025 35253700688940658953973519)
      ·
        refine ⟨52880551033410988430960279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35253700688940658953973519 52880551033410988430960279)
        ·
          refine ⟨79320826550116482646440419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52880551033410988430960279 79320826550116482646440419)
          ·
            refine ⟨118981239825174723969660629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79320826550116482646440419 118981239825174723969660629)
            ·
              refine ⟨2788622808402532593038921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 118981239825174723969660629 2788622808402532593038921)
              ·
                refine ⟨2091467106301899444779191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2788622808402532593038921 2091467106301899444779191)
                ·
                  refine ⟨3137200659452849167168787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2091467106301899444779191 3137200659452849167168787)
                  ·
                    refine ⟨4705800989179273750753181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3137200659452849167168787 4705800989179273750753181)
                    ·
                      refine ⟨1764675370942227656532443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4705800989179273750753181 1764675370942227656532443)
                      ·
                        rfl

theorem cell23_3436693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 1, 1, 3].length) (baseStart_3436693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436693 prefixEnd_3436693 := by exact prefixLift 3436693
  have htrace : WordTrace (prefixWord ++ tailWord_3436693) baseStart_3436693 baseEnd_3436693 := by
    simpa [prefixWord, tailWord_3436693, baseEnd_3436693] using wordTrace_append hprefix tailTrace_3436693
  have hstable : (prefixWord ++ tailWord_3436693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436693).length < 2 ^ (prefixWord ++ tailWord_3436693).sum := by decide
  have hdescent : baseEnd_3436693 < baseStart_3436693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436699 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 7, 2, 2]
def baseStart_3436699 : Nat := 118140960795 + 3436699 * 2 ^ 59
def prefixEnd_3436699 : Nat := 4983230072969 + 3 ^ 40 * 3436699 * 2
def baseEnd_3436699 : Nat := 1764678451826154633057415

theorem tailTrace_3436699 : CollatzResearch.WordTrace tailWord_3436699 prefixEnd_3436699 1764678451826154633057415 := by
  unfold tailWord_3436699
  simp only [CollatzResearch.WordTrace]
  refine ⟨125346710176433939305513151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83564473450955959537008767 125346710176433939305513151)
  ·
    refine ⟨188020065264650908958269727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125346710176433939305513151 188020065264650908958269727)
    ·
      refine ⟨282030097896976363437404591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188020065264650908958269727 282030097896976363437404591)
      ·
        refine ⟨423045146845464545156106887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282030097896976363437404591 423045146845464545156106887)
        ·
          refine ⟨634567720268196817734160331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423045146845464545156106887 634567720268196817734160331)
          ·
            refine ⟨951851580402295226601240497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634567720268196817734160331 951851580402295226601240497)
            ·
              refine ⟨713888685301721419950930373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951851580402295226601240497 713888685301721419950930373)
              ·
                refine ⟨133854128494072766240799445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 713888685301721419950930373 133854128494072766240799445)
                ·
                  refine ⟨3137206136579830458768737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 133854128494072766240799445 3137206136579830458768737)
                  ·
                    refine ⟨2352904602434872844076553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3137206136579830458768737 2352904602434872844076553)
                    ·
                      refine ⟨1764678451826154633057415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2352904602434872844076553 1764678451826154633057415)
                      ·
                        rfl

theorem cell23_3436699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 2, 2].length) (baseStart_3436699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436699 prefixEnd_3436699 := by exact prefixLift 3436699
  have htrace : WordTrace (prefixWord ++ tailWord_3436699) baseStart_3436699 baseEnd_3436699 := by
    simpa [prefixWord, tailWord_3436699, baseEnd_3436699] using wordTrace_append hprefix tailTrace_3436699
  have hstable : (prefixWord ++ tailWord_3436699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436699).length < 2 ^ (prefixWord ++ tailWord_3436699).sum := by decide
  have hdescent : baseEnd_3436699 < baseStart_3436699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436709 : List Nat := [1, 3, 1, 2, 1, 3, 3, 3, 2, 4]
def baseStart_3436709 : Nat := 118140960795 + 3436709 * 2 ^ 59
def prefixEnd_3436709 : Nat := 4983230072969 + 3 ^ 40 * 3436709 * 2
def baseEnd_3436709 : Nat := 588227862210899864644123

theorem tailTrace_3436709 : CollatzResearch.WordTrace tailWord_3436709 prefixEnd_3436709 588227862210899864644123 := by
  unfold tailWord_3436709
  simp only [CollatzResearch.WordTrace]
  refine ⟨125347074906397711013377181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83564716604265140675584787 125347074906397711013377181)
  ·
    refine ⟨47005153089899141630016443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125347074906397711013377181 47005153089899141630016443)
    ·
      refine ⟨70507729634848712445024665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47005153089899141630016443 70507729634848712445024665)
      ·
        refine ⟨52880797226136534333768499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70507729634848712445024665 52880797226136534333768499)
        ·
          refine ⟨79321195839204801500652749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52880797226136534333768499 79321195839204801500652749)
          ·
            refine ⟨29745448439701800562744781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79321195839204801500652749 29745448439701800562744781)
            ·
              refine ⟨11154543164888175211029293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29745448439701800562744781 11154543164888175211029293)
              ·
                refine ⟨4182953686833065704135985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11154543164888175211029293 4182953686833065704135985)
                ·
                  refine ⟨3137215265124799278101989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4182953686833065704135985 3137215265124799278101989)
                  ·
                    refine ⟨588227862210899864644123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3137215265124799278101989 588227862210899864644123)
                    ·
                      rfl

theorem cell23_3436709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_3436709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436709 prefixEnd_3436709 := by exact prefixLift 3436709
  have htrace : WordTrace (prefixWord ++ tailWord_3436709) baseStart_3436709 baseEnd_3436709 := by
    simpa [prefixWord, tailWord_3436709, baseEnd_3436709] using wordTrace_append hprefix tailTrace_3436709
  have hstable : (prefixWord ++ tailWord_3436709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436709).length < 2 ^ (prefixWord ++ tailWord_3436709).sum := by decide
  have hdescent : baseEnd_3436709 < baseStart_3436709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436733 : List Nat := [1, 4, 1, 2, 1, 1, 1, 7, 1, 2, 2]
def baseStart_3436733 : Nat := 118140960795 + 3436733 * 2 ^ 59
def prefixEnd_3436733 : Nat := 4983230072969 + 3 ^ 40 * 3436733 * 2
def baseEnd_3436733 : Nat := 1764695910168407500032259

theorem tailTrace_3436733 : CollatzResearch.WordTrace tailWord_3436733 prefixEnd_3436733 1764695910168407500032259 := by
  unfold tailWord_3436733
  simp only [CollatzResearch.WordTrace]
  refine ⟨125347950258310763112250853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83565300172207175408167235 125347950258310763112250853)
  ·
    refine ⟨23502740673433268083547035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125347950258310763112250853 23502740673433268083547035)
    ·
      refine ⟨35254111010149902125320553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23502740673433268083547035 35254111010149902125320553)
      ·
        refine ⟨26440583257612426593990415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35254111010149902125320553 26440583257612426593990415)
        ·
          refine ⟨39660874886418639890985623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26440583257612426593990415 39660874886418639890985623)
          ·
            refine ⟨59491312329627959836478435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39660874886418639890985623 59491312329627959836478435)
            ·
              refine ⟨89236968494441939754717653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59491312329627959836478435 89236968494441939754717653)
              ·
                refine ⟨2091491449088482963001195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 89236968494441939754717653 2091491449088482963001195)
                ·
                  refine ⟨3137237173632724444501793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2091491449088482963001195 3137237173632724444501793)
                  ·
                    refine ⟨2352927880224543333376345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3137237173632724444501793 2352927880224543333376345)
                    ·
                      refine ⟨1764695910168407500032259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2352927880224543333376345 1764695910168407500032259)
                      ·
                        rfl

theorem cell23_3436733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_3436733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436733 prefixEnd_3436733 := by exact prefixLift 3436733
  have htrace : WordTrace (prefixWord ++ tailWord_3436733) baseStart_3436733 baseEnd_3436733 := by
    simpa [prefixWord, tailWord_3436733, baseEnd_3436733] using wordTrace_append hprefix tailTrace_3436733
  have hstable : (prefixWord ++ tailWord_3436733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436733).length < 2 ^ (prefixWord ++ tailWord_3436733).sum := by decide
  have hdescent : baseEnd_3436733 < baseStart_3436733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436750 : List Nat := [4, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2]
def baseStart_3436750 : Nat := 118140960795 + 3436750 * 2 ^ 59
def prefixEnd_3436750 : Nat := 4983230072969 + 3 ^ 40 * 3436750 * 2
def baseEnd_3436750 : Nat := 1764704639339533933519681

theorem tailTrace_3436750 : CollatzResearch.WordTrace tailWord_3436750 prefixEnd_3436750 1764704639339533933519681 := by
  unfold tailWord_3436750
  simp only [CollatzResearch.WordTrace]
  refine ⟨15668571287406146876952463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83565713532832783343746469 15668571287406146876952463)
  ·
    refine ⟨23502856931109220315428695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15668571287406146876952463 23502856931109220315428695)
    ·
      refine ⟨35254285396663830473143043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23502856931109220315428695 35254285396663830473143043)
      ·
        refine ⟨52881428094995745709714565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35254285396663830473143043 52881428094995745709714565)
        ·
          refine ⟨9915267767811702320571481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52881428094995745709714565 9915267767811702320571481)
          ·
            refine ⟨7436450825858776740428611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9915267767811702320571481 7436450825858776740428611)
            ·
              refine ⟨11154676238788165110642917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7436450825858776740428611 11154676238788165110642917)
              ·
                refine ⟨2091501794772780958245547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11154676238788165110642917 2091501794772780958245547)
                ·
                  refine ⟨3137252692159171437368321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2091501794772780958245547 3137252692159171437368321)
                  ·
                    refine ⟨2352939519119378578026241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3137252692159171437368321 2352939519119378578026241)
                    ·
                      refine ⟨1764704639339533933519681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2352939519119378578026241 1764704639339533933519681)
                      ·
                        rfl

theorem cell23_3436750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2].length) (baseStart_3436750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436750 prefixEnd_3436750 := by exact prefixLift 3436750
  have htrace : WordTrace (prefixWord ++ tailWord_3436750) baseStart_3436750 baseEnd_3436750 := by
    simpa [prefixWord, tailWord_3436750, baseEnd_3436750] using wordTrace_append hprefix tailTrace_3436750
  have hstable : (prefixWord ++ tailWord_3436750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436750).length < 2 ^ (prefixWord ++ tailWord_3436750).sum := by decide
  have hdescent : baseEnd_3436750 < baseStart_3436750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436772 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_3436772 : Nat := 118140960795 + 3436772 * 2 ^ 59
def prefixEnd_3436772 : Nat := 4983230072969 + 3 ^ 40 * 3436772 * 2
def baseEnd_3436772 : Nat := 1764715935913932847444579

theorem tailTrace_3436772 : CollatzResearch.WordTrace tailWord_3436772 prefixEnd_3436772 1764715935913932847444579 := by
  unfold tailWord_3436772
  simp only [CollatzResearch.WordTrace]
  refine ⟨62674686352584736386460285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83566248470112981848613713 62674686352584736386460285)
  ·
    refine ⟨23503007382219276144922607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62674686352584736386460285 23503007382219276144922607)
    ·
      refine ⟨35254511073328914217383911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23503007382219276144922607 35254511073328914217383911)
      ·
        refine ⟨52881766609993371326075867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35254511073328914217383911 52881766609993371326075867)
        ·
          refine ⟨79322649914990056989113801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52881766609993371326075867 79322649914990056989113801)
          ·
            refine ⟨59491987436242542741835351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79322649914990056989113801 59491987436242542741835351)
            ·
              refine ⟨89237981154363814112753027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59491987436242542741835351 89237981154363814112753027)
              ·
                refine ⟨133856971731545721169129541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89237981154363814112753027 133856971731545721169129541)
                ·
                  refine ⟨25098182199664822719211789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133856971731545721169129541 25098182199664822719211789)
                  ·
                    refine ⟨9411818324874308519704421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25098182199664822719211789 9411818324874308519704421)
                    ·
                      refine ⟨1764715935913932847444579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9411818324874308519704421 1764715935913932847444579)
                      ·
                        rfl

theorem cell23_3436772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_3436772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436772 prefixEnd_3436772 := by exact prefixLift 3436772
  have htrace : WordTrace (prefixWord ++ tailWord_3436772) baseStart_3436772 baseEnd_3436772 := by
    simpa [prefixWord, tailWord_3436772, baseEnd_3436772] using wordTrace_append hprefix tailTrace_3436772
  have hstable : (prefixWord ++ tailWord_3436772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436772).length < 2 ^ (prefixWord ++ tailWord_3436772).sum := by decide
  have hdescent : baseEnd_3436772 < baseStart_3436772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436776 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 3, 3, 2]
def baseStart_3436776 : Nat := 118140960795 + 3436776 * 2 ^ 59
def prefixEnd_3436776 : Nat := 4983230072969 + 3 ^ 40 * 3436776 * 2
def baseEnd_3436776 : Nat := 1764717989836550831794561

theorem tailTrace_3436776 : CollatzResearch.WordTrace tailWord_3436776 prefixEnd_3436776 1764717989836550831794561 := by
  unfold tailWord_3436776
  simp only [CollatzResearch.WordTrace]
  refine ⟨62674759298577490728033091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83566345731436654304044121 62674759298577490728033091)
  ·
    refine ⟨94012138947866236092049637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62674759298577490728033091 94012138947866236092049637)
    ·
      refine ⟨17627276052724919267259307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94012138947866236092049637 17627276052724919267259307)
      ·
        refine ⟨26440914079087378900888961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17627276052724919267259307 26440914079087378900888961)
        ·
          refine ⟨19830685559315534175666721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26440914079087378900888961 19830685559315534175666721)
          ·
            refine ⟨14873014169486650631750041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19830685559315534175666721 14873014169486650631750041)
            ·
              refine ⟨11154760627114987973812531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14873014169486650631750041 11154760627114987973812531)
              ·
                refine ⟨16732140940672481960718797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11154760627114987973812531 16732140940672481960718797)
                ·
                  refine ⟨6274552852752180735269549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16732140940672481960718797 6274552852752180735269549)
                  ·
                    refine ⟨2352957319782067775726081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6274552852752180735269549 2352957319782067775726081)
                    ·
                      refine ⟨1764717989836550831794561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2352957319782067775726081 1764717989836550831794561)
                      ·
                        rfl

theorem cell23_3436776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_3436776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436776 prefixEnd_3436776 := by exact prefixLift 3436776
  have htrace : WordTrace (prefixWord ++ tailWord_3436776) baseStart_3436776 baseEnd_3436776 := by
    simpa [prefixWord, tailWord_3436776, baseEnd_3436776] using wordTrace_append hprefix tailTrace_3436776
  have hstable : (prefixWord ++ tailWord_3436776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436776).length < 2 ^ (prefixWord ++ tailWord_3436776).sum := by decide
  have hdescent : baseEnd_3436776 < baseStart_3436776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436782 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 3, 8]
def baseStart_3436782 : Nat := 118140960795 + 3436782 * 2 ^ 59
def prefixEnd_3436782 : Nat := 4983230072969 + 3 ^ 40 * 3436782 * 2
def baseEnd_3436782 : Nat := 588240356906825936106511

theorem tailTrace_3436782 : CollatzResearch.WordTrace tailWord_3436782 prefixEnd_3436782 588240356906825936106511 := by
  unfold tailWord_3436782
  simp only [CollatzResearch.WordTrace]
  refine ⟨15668717179391655560098075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83566491623422162987189733 15668717179391655560098075)
  ·
    refine ⟨23503075769087483340147113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15668717179391655560098075 23503075769087483340147113)
    ·
      refine ⟨17627306826815612505110335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23503075769087483340147113 17627306826815612505110335)
      ·
        refine ⟨26440960240223418757665503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17627306826815612505110335 26440960240223418757665503)
        ·
          refine ⟨39661440360335128136498255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26440960240223418757665503 39661440360335128136498255)
          ·
            refine ⟨59492160540502692204747383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39661440360335128136498255 59492160540502692204747383)
            ·
              refine ⟨89238240810754038307121075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59492160540502692204747383 89238240810754038307121075)
              ·
                refine ⟨133857361216131057460681613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89238240810754038307121075 133857361216131057460681613)
                ·
                  refine ⟨50196510456049146547755605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133857361216131057460681613 50196510456049146547755605)
                  ·
                    refine ⟨588240356906825936106511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50196510456049146547755605 588240356906825936106511)
                    ·
                      rfl

theorem cell23_3436782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_3436782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436782 prefixEnd_3436782 := by exact prefixLift 3436782
  have htrace : WordTrace (prefixWord ++ tailWord_3436782) baseStart_3436782 baseEnd_3436782 := by
    simpa [prefixWord, tailWord_3436782, baseEnd_3436782] using wordTrace_append hprefix tailTrace_3436782
  have hstable : (prefixWord ++ tailWord_3436782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436782).length < 2 ^ (prefixWord ++ tailWord_3436782).sum := by decide
  have hdescent : baseEnd_3436782 < baseStart_3436782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436792 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 2, 1, 5]
def baseStart_3436792 : Nat := 118140960795 + 3436792 * 2 ^ 59
def prefixEnd_3436792 : Nat := 4983230072969 + 3 ^ 40 * 3436792 * 2
def baseEnd_3436792 : Nat := 1764726205527022769194487

theorem tailTrace_3436792 : CollatzResearch.WordTrace tailWord_3436792 prefixEnd_3436792 1764726205527022769194487 := by
  unfold tailWord_3436792
  simp only [CollatzResearch.WordTrace]
  refine ⟨62675051082548508094324315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83566734776731344125765753 62675051082548508094324315)
  ·
    refine ⟨94012576623822762141486473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62675051082548508094324315 94012576623822762141486473)
    ·
      refine ⟨70509432467867071606114855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94012576623822762141486473 70509432467867071606114855)
      ·
        refine ⟨105764148701800607409172283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70509432467867071606114855 105764148701800607409172283)
        ·
          refine ⟨158646223052700911113758425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105764148701800607409172283 158646223052700911113758425)
          ·
            refine ⟨118984667289525683335318819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158646223052700911113758425 118984667289525683335318819)
            ·
              refine ⟨178477000934288525002978229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118984667289525683335318819 178477000934288525002978229)
              ·
                refine ⟨16732218837589549219029209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178477000934288525002978229 16732218837589549219029209)
                ·
                  refine ⟨12549164128192161914271907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16732218837589549219029209 12549164128192161914271907)
                  ·
                    refine ⟨18823746192288242871407861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12549164128192161914271907 18823746192288242871407861)
                    ·
                      refine ⟨1764726205527022769194487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18823746192288242871407861 1764726205527022769194487)
                      ·
                        rfl

theorem cell23_3436792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_3436792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436792 prefixEnd_3436792 := by exact prefixLift 3436792
  have htrace : WordTrace (prefixWord ++ tailWord_3436792) baseStart_3436792 baseEnd_3436792 := by
    simpa [prefixWord, tailWord_3436792, baseEnd_3436792] using wordTrace_append hprefix tailTrace_3436792
  have hstable : (prefixWord ++ tailWord_3436792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436792).length < 2 ^ (prefixWord ++ tailWord_3436792).sum := by decide
  have hdescent : baseEnd_3436792 < baseStart_3436792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436823 : List Nat := [1, 1, 3, 4, 1, 4, 1, 1, 1, 4, 2]
def baseStart_3436823 : Nat := 118140960795 + 3436823 * 2 ^ 59
def prefixEnd_3436823 : Nat := 4983230072969 + 3 ^ 40 * 3436823 * 2
def baseEnd_3436823 : Nat := 1764742123427312147906845

theorem tailTrace_3436823 : CollatzResearch.WordTrace tailWord_3436823 prefixEnd_3436823 1764742123427312147906845 := by
  unfold tailWord_3436823
  simp only [CollatzResearch.WordTrace]
  refine ⟨125351232827984708483027123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83567488551989805655351415 125351232827984708483027123)
  ·
    refine ⟨188026849241977062724540685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125351232827984708483027123 188026849241977062724540685)
    ·
      refine ⟨70510068465741398521702757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188026849241977062724540685 70510068465741398521702757)
      ·
        refine ⟨13220637837326512222819267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70510068465741398521702757 13220637837326512222819267)
        ·
          refine ⟨19830956755989768334228901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13220637837326512222819267 19830956755989768334228901)
          ·
            refine ⟨3718304391748081562667919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19830956755989768334228901 3718304391748081562667919)
            ·
              refine ⟨5577456587622122344001879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3718304391748081562667919 5577456587622122344001879)
              ·
                refine ⟨8366184881433183516002819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5577456587622122344001879 8366184881433183516002819)
                ·
                  refine ⟨12549277322149775274004229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8366184881433183516002819 12549277322149775274004229)
                  ·
                    refine ⟨2352989497903082863875793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12549277322149775274004229 2352989497903082863875793)
                    ·
                      refine ⟨1764742123427312147906845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2352989497903082863875793 1764742123427312147906845)
                      ·
                        rfl

theorem cell23_3436823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_3436823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436823 prefixEnd_3436823 := by exact prefixLift 3436823
  have htrace : WordTrace (prefixWord ++ tailWord_3436823) baseStart_3436823 baseEnd_3436823 := by
    simpa [prefixWord, tailWord_3436823, baseEnd_3436823] using wordTrace_append hprefix tailTrace_3436823
  have hstable : (prefixWord ++ tailWord_3436823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436823).length < 2 ^ (prefixWord ++ tailWord_3436823).sum := by decide
  have hdescent : baseEnd_3436823 < baseStart_3436823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436889 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 5, 4]
def baseStart_3436889 : Nat := 118140960795 + 3436889 * 2 ^ 59
def prefixEnd_3436889 : Nat := 4983230072969 + 3 ^ 40 * 3436889 * 2
def baseEnd_3436889 : Nat := 588258671050169629893847

theorem tailTrace_3436889 : CollatzResearch.WordTrace tailWord_3436889 prefixEnd_3436889 588258671050169629893847 := by
  unfold tailWord_3436889
  simp only [CollatzResearch.WordTrace]
  refine ⟨125353640045745601754929721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83569093363830401169953147 125353640045745601754929721)
  ·
    refine ⟨94015230034309201316197291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125353640045745601754929721 94015230034309201316197291)
    ·
      refine ⟨141022845051463801974295937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94015230034309201316197291 141022845051463801974295937)
      ·
        refine ⟨105767133788597851480721953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141022845051463801974295937 105767133788597851480721953)
        ·
          refine ⟨79325350341448388610541465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105767133788597851480721953 79325350341448388610541465)
          ·
            refine ⟨59494012756086291457906099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79325350341448388610541465 59494012756086291457906099)
            ·
              refine ⟨89241019134129437186859149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59494012756086291457906099 89241019134129437186859149)
              ·
                refine ⟨33465382175298538945072181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89241019134129437186859149 33465382175298538945072181)
                ·
                  refine ⟨3137379578934238026100517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33465382175298538945072181 3137379578934238026100517)
                  ·
                    refine ⟨588258671050169629893847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3137379578934238026100517 588258671050169629893847)
                    ·
                      rfl

theorem cell23_3436889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 4].length) (baseStart_3436889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436889 prefixEnd_3436889 := by exact prefixLift 3436889
  have htrace : WordTrace (prefixWord ++ tailWord_3436889) baseStart_3436889 baseEnd_3436889 := by
    simpa [prefixWord, tailWord_3436889, baseEnd_3436889] using wordTrace_append hprefix tailTrace_3436889
  have hstable : (prefixWord ++ tailWord_3436889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436889).length < 2 ^ (prefixWord ++ tailWord_3436889).sum := by decide
  have hdescent : baseEnd_3436889 < baseStart_3436889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436909 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_3436909 : Nat := 118140960795 + 3436909 * 2 ^ 59
def prefixEnd_3436909 : Nat := 4983230072969 + 3 ^ 40 * 3436909 * 2
def baseEnd_3436909 : Nat := 1764786282763598811431449

theorem tailTrace_3436909 : CollatzResearch.WordTrace tailWord_3436909 prefixEnd_3436909 1764786282763598811431449 := by
  unfold tailWord_3436909
  simp only [CollatzResearch.WordTrace]
  refine ⟨125354369505673145170657781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83569579670448763447105187 125354369505673145170657781)
  ·
    refine ⟨11751972141156857359749167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125354369505673145170657781 11751972141156857359749167)
    ·
      refine ⟨17627958211735286039623751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11751972141156857359749167 17627958211735286039623751)
      ·
        refine ⟨26441937317602929059435627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17627958211735286039623751 26441937317602929059435627)
        ·
          refine ⟨39662905976404393589153441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26441937317602929059435627 39662905976404393589153441)
          ·
            refine ⟨29747179482303295191865081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39662905976404393589153441 29747179482303295191865081)
            ·
              refine ⟨22310384611727471393898811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29747179482303295191865081 22310384611727471393898811)
              ·
                refine ⟨33465576917591207090848217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22310384611727471393898811 33465576917591207090848217)
                ·
                  refine ⟨25099182688193405318136163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33465576917591207090848217 25099182688193405318136163)
                  ·
                    refine ⟨37648774032290107977204245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25099182688193405318136163 37648774032290107977204245)
                    ·
                      refine ⟨1764786282763598811431449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37648774032290107977204245 1764786282763598811431449)
                      ·
                        rfl

theorem cell23_3436909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_3436909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436909 prefixEnd_3436909 := by exact prefixLift 3436909
  have htrace : WordTrace (prefixWord ++ tailWord_3436909) baseStart_3436909 baseEnd_3436909 := by
    simpa [prefixWord, tailWord_3436909, baseEnd_3436909] using wordTrace_append hprefix tailTrace_3436909
  have hstable : (prefixWord ++ tailWord_3436909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436909).length < 2 ^ (prefixWord ++ tailWord_3436909).sum := by decide
  have hdescent : baseEnd_3436909 < baseStart_3436909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436923 : List Nat := [1, 1, 1, 1, 1, 8, 1, 4, 1, 4]
def baseStart_3436923 : Nat := 118140960795 + 3436923 * 2 ^ 59
def prefixEnd_3436923 : Nat := 4983230072969 + 3 ^ 40 * 3436923 * 2
def baseEnd_3436923 : Nat := 588264490497587252218795

theorem tailTrace_3436923 : CollatzResearch.WordTrace tailWord_3436923 prefixEnd_3436923 588264490497587252218795 := by
  unfold tailWord_3436923
  simp only [CollatzResearch.WordTrace]
  refine ⟨125354880127622425561667423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83569920085081617041111615 125354880127622425561667423)
  ·
    refine ⟨188032320191433638342501135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125354880127622425561667423 188032320191433638342501135)
    ·
      refine ⟨282048480287150457513751703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188032320191433638342501135 282048480287150457513751703)
      ·
        refine ⟨423072720430725686270627555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282048480287150457513751703 423072720430725686270627555)
        ·
          refine ⟨634609080646088529405941333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423072720430725686270627555 634609080646088529405941333)
          ·
            refine ⟨7436825163821349953975875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 634609080646088529405941333 7436825163821349953975875)
            ·
              refine ⟨11155237745732024930963813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7436825163821349953975875 11155237745732024930963813)
              ·
                refine ⟨2091607077324754674555715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11155237745732024930963813 2091607077324754674555715)
                ·
                  refine ⟨3137410615987132011833573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2091607077324754674555715 3137410615987132011833573)
                  ·
                    refine ⟨588264490497587252218795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3137410615987132011833573 588264490497587252218795)
                    ·
                      rfl

theorem cell23_3436923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 1, 4].length) (baseStart_3436923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436923 prefixEnd_3436923 := by exact prefixLift 3436923
  have htrace : WordTrace (prefixWord ++ tailWord_3436923) baseStart_3436923 baseEnd_3436923 := by
    simpa [prefixWord, tailWord_3436923, baseEnd_3436923] using wordTrace_append hprefix tailTrace_3436923
  have hstable : (prefixWord ++ tailWord_3436923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436923).length < 2 ^ (prefixWord ++ tailWord_3436923).sum := by decide
  have hdescent : baseEnd_3436923 < baseStart_3436923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436970 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 8]
def baseStart_3436970 : Nat := 118140960795 + 3436970 * 2 ^ 59
def prefixEnd_3436970 : Nat := 4983230072969 + 3 ^ 40 * 3436970 * 2
def baseEnd_3436970 : Nat := 196090845009280341418741

theorem tailTrace_3436970 : CollatzResearch.WordTrace tailWord_3436970 prefixEnd_3436970 196090845009280341418741 := by
  unfold tailWord_3436970
  simp only [CollatzResearch.WordTrace]
  refine ⟨31339148589613038147157091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83571062905634768392418909 31339148589613038147157091)
  ·
    refine ⟨47008722884419557220735637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31339148589613038147157091 47008722884419557220735637)
    ·
      refine ⟨2203533885207166744721983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47008722884419557220735637 2203533885207166744721983)
      ·
        refine ⟨3305300827810750117082975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2203533885207166744721983 3305300827810750117082975)
        ·
          refine ⟨4957951241716125175624463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3305300827810750117082975 4957951241716125175624463)
          ·
            refine ⟨7436926862574187763436695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4957951241716125175624463 7436926862574187763436695)
            ·
              refine ⟨11155390293861281645155043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7436926862574187763436695 11155390293861281645155043)
              ·
                refine ⟨16733085440791922467732565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11155390293861281645155043 16733085440791922467732565)
                ·
                  refine ⟨196090845009280341418741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16733085440791922467732565 196090845009280341418741)
                  ·
                    rfl

theorem cell23_3436970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 8].length) (baseStart_3436970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436970 prefixEnd_3436970 := by exact prefixLift 3436970
  have htrace : WordTrace (prefixWord ++ tailWord_3436970) baseStart_3436970 baseEnd_3436970 := by
    simpa [prefixWord, tailWord_3436970, baseEnd_3436970] using wordTrace_append hprefix tailTrace_3436970
  have hstable : (prefixWord ++ tailWord_3436970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436970).length < 2 ^ (prefixWord ++ tailWord_3436970).sum := by decide
  have hdescent : baseEnd_3436970 < baseStart_3436970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437023 : List Nat := [1, 1, 2, 3, 3, 2, 2, 3, 1, 2, 3]
def baseStart_3437023 : Nat := 118140960795 + 3437023 * 2 ^ 59
def prefixEnd_3437023 : Nat := 4983230072969 + 3 ^ 40 * 3437023 * 2
def baseEnd_3437023 : Nat := 1764844819558211365405925

theorem tailTrace_3437023 : CollatzResearch.WordTrace tailWord_3437023 prefixEnd_3437023 1764844819558211365405925 := by
  unfold tailWord_3437023
  simp only [CollatzResearch.WordTrace]
  refine ⟨125358527427260142640307723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83572351618173428426871815 125358527427260142640307723)
  ·
    refine ⟨188037791140890213960461585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125358527427260142640307723 188037791140890213960461585)
    ·
      refine ⟨141028343355667660470346189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188037791140890213960461585 141028343355667660470346189)
      ·
        refine ⟨52885628758375372676379821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141028343355667660470346189 52885628758375372676379821)
        ·
          refine ⟨19832110784390764753642433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52885628758375372676379821 19832110784390764753642433)
          ·
            refine ⟨14874083088293073565231825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19832110784390764753642433 14874083088293073565231825)
            ·
              refine ⟨11155562316219805173923869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14874083088293073565231825 11155562316219805173923869)
              ·
                refine ⟨4183335868582426940221451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11155562316219805173923869 4183335868582426940221451)
                ·
                  refine ⟨6275003802873640410332177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4183335868582426940221451 6275003802873640410332177)
                  ·
                    refine ⟨4706252852155230307749133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6275003802873640410332177 4706252852155230307749133)
                    ·
                      refine ⟨1764844819558211365405925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4706252852155230307749133 1764844819558211365405925)
                      ·
                        rfl

theorem cell23_3437023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_3437023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437023 prefixEnd_3437023 := by exact prefixLift 3437023
  have htrace : WordTrace (prefixWord ++ tailWord_3437023) baseStart_3437023 baseEnd_3437023 := by
    simpa [prefixWord, tailWord_3437023, baseEnd_3437023] using wordTrace_append hprefix tailTrace_3437023
  have hstable : (prefixWord ++ tailWord_3437023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437023).length < 2 ^ (prefixWord ++ tailWord_3437023).sum := by decide
  have hdescent : baseEnd_3437023 < baseStart_3437023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437037 : List Nat := [1, 5, 1, 3, 1, 1, 3, 1, 3, 2, 2]
def baseStart_3437037 : Nat := 118140960795 + 3437037 * 2 ^ 59
def prefixEnd_3437037 : Nat := 4983230072969 + 3 ^ 40 * 3437037 * 2
def baseEnd_3437037 : Nat := 1764852008287374310630861

theorem tailTrace_3437037 : CollatzResearch.WordTrace tailWord_3437037 prefixEnd_3437037 1764852008287374310630861 := by
  unfold tailWord_3437037
  simp only [CollatzResearch.WordTrace]
  refine ⟨125359038049209423031317365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83572692032806282020878243 125359038049209423031317365)
  ·
    refine ⟨11752409817113383409186003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125359038049209423031317365 11752409817113383409186003)
    ·
      refine ⟨17628614725670075113779005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11752409817113383409186003 17628614725670075113779005)
      ·
        refine ⟨6610730522126278167667127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17628614725670075113779005 6610730522126278167667127)
        ·
          refine ⟨9916095783189417251500691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6610730522126278167667127 9916095783189417251500691)
          ·
            refine ⟨14874143674784125877251037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9916095783189417251500691 14874143674784125877251037)
            ·
              refine ⟨5577803878044047203969139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14874143674784125877251037 5577803878044047203969139)
              ·
                refine ⟨8366705817066070805953709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5577803878044047203969139 8366705817066070805953709)
                ·
                  refine ⟨3137514681399776552232641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8366705817066070805953709 3137514681399776552232641)
                  ·
                    refine ⟨2353136011049832414174481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3137514681399776552232641 2353136011049832414174481)
                    ·
                      refine ⟨1764852008287374310630861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2353136011049832414174481 1764852008287374310630861)
                      ·
                        rfl

theorem cell23_3437037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_3437037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437037 prefixEnd_3437037 := by exact prefixLift 3437037
  have htrace : WordTrace (prefixWord ++ tailWord_3437037) baseStart_3437037 baseEnd_3437037 := by
    simpa [prefixWord, tailWord_3437037, baseEnd_3437037] using wordTrace_append hprefix tailTrace_3437037
  have hstable : (prefixWord ++ tailWord_3437037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437037).length < 2 ^ (prefixWord ++ tailWord_3437037).sum := by decide
  have hdescent : baseEnd_3437037 < baseStart_3437037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437039 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 2, 7]
def baseStart_3437039 : Nat := 118140960795 + 3437039 * 2 ^ 59
def prefixEnd_3437039 : Nat := 4983230072969 + 3 ^ 40 * 3437039 * 2
def baseEnd_3437039 : Nat := 588284345082894434268617

theorem tailTrace_3437039 : CollatzResearch.WordTrace tailWord_3437039 prefixEnd_3437039 588284345082894434268617 := by
  unfold tailWord_3437039
  simp only [CollatzResearch.WordTrace]
  refine ⟨125359110995202177372890171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83572740663468118248593447 125359110995202177372890171)
  ·
    refine ⟨188038666492803266059335257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125359110995202177372890171 188038666492803266059335257)
    ·
      refine ⟨141028999869602449544501443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188038666492803266059335257 141028999869602449544501443)
      ·
        refine ⟨211543499804403674316752165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141028999869602449544501443 211543499804403674316752165)
        ·
          refine ⟨39664406213325688934391031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211543499804403674316752165 39664406213325688934391031)
          ·
            refine ⟨59496609319988533401586547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39664406213325688934391031 59496609319988533401586547)
            ·
              refine ⟨89244913979982800102379821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59496609319988533401586547 89244913979982800102379821)
              ·
                refine ⟨33466842742493550038392433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89244913979982800102379821 33466842742493550038392433)
                ·
                  refine ⟨25100132056870162528794325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33466842742493550038392433 25100132056870162528794325)
                  ·
                    refine ⟨588284345082894434268617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25100132056870162528794325 588284345082894434268617)
                    ·
                      rfl

theorem cell23_3437039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 7].length) (baseStart_3437039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437039 prefixEnd_3437039 := by exact prefixLift 3437039
  have htrace : WordTrace (prefixWord ++ tailWord_3437039) baseStart_3437039 baseEnd_3437039 := by
    simpa [prefixWord, tailWord_3437039, baseEnd_3437039] using wordTrace_append hprefix tailTrace_3437039
  have hstable : (prefixWord ++ tailWord_3437039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437039).length < 2 ^ (prefixWord ++ tailWord_3437039).sum := by decide
  have hdescent : baseEnd_3437039 < baseStart_3437039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437046 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_3437046 : Nat := 118140960795 + 3437046 * 2 ^ 59
def prefixEnd_3437046 : Nat := 4983230072969 + 3 ^ 40 * 3437046 * 2
def baseEnd_3437046 : Nat := 1764856629613264775418319

theorem tailTrace_3437046 : CollatzResearch.WordTrace tailWord_3437046 prefixEnd_3437046 1764856629613264775418319 := by
  unfold tailWord_3437046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7834960394136051098024687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83572910870784545045596661 7834960394136051098024687)
  ·
    refine ⟨11752440591204076647037031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7834960394136051098024687 11752440591204076647037031)
    ·
      refine ⟨17628660886806114970555547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11752440591204076647037031 17628660886806114970555547)
      ·
        refine ⟨26442991330209172455833321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17628660886806114970555547 26442991330209172455833321)
        ·
          refine ⟨19832243497656879341874991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26442991330209172455833321 19832243497656879341874991)
          ·
            refine ⟨29748365246485319012812487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19832243497656879341874991 29748365246485319012812487)
            ·
              refine ⟨44622547869727978519218731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29748365246485319012812487 44622547869727978519218731)
              ·
                refine ⟨66933821804591967778828097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44622547869727978519218731 66933821804591967778828097)
                ·
                  refine ⟨50200366353443975834121073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66933821804591967778828097 50200366353443975834121073)
                  ·
                    refine ⟨37650274765082981875590805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50200366353443975834121073 37650274765082981875590805)
                    ·
                      refine ⟨1764856629613264775418319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37650274765082981875590805 1764856629613264775418319)
                      ·
                        rfl

theorem cell23_3437046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_3437046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437046 prefixEnd_3437046 := by exact prefixLift 3437046
  have htrace : WordTrace (prefixWord ++ tailWord_3437046) baseStart_3437046 baseEnd_3437046 := by
    simpa [prefixWord, tailWord_3437046, baseEnd_3437046] using wordTrace_append hprefix tailTrace_3437046
  have hstable : (prefixWord ++ tailWord_3437046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437046).length < 2 ^ (prefixWord ++ tailWord_3437046).sum := by decide
  have hdescent : baseEnd_3437046 < baseStart_3437046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437088 : List Nat := [2, 1, 1, 6, 3, 1, 2, 2, 1, 2, 2]
def baseStart_3437088 : Nat := 118140960795 + 3437088 * 2 ^ 59
def prefixEnd_3437088 : Nat := 4983230072969 + 3 ^ 40 * 3437088 * 2
def baseEnd_3437088 : Nat := 1764878195800753611093127

theorem tailTrace_3437088 : CollatzResearch.WordTrace tailWord_3437088 prefixEnd_3437088 1764878195800753611093127 := by
  unfold tailWord_3437088
  simp only [CollatzResearch.WordTrace]
  refine ⟨62680449086012329370711959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83573932114683105827615945 62680449086012329370711959)
  ·
    refine ⟨94020673629018494056067939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62680449086012329370711959 94020673629018494056067939)
    ·
      refine ⟨141031010443527741084101909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94020673629018494056067939 141031010443527741084101909)
      ·
        refine ⟨6610828614540362863317277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 141031010443527741084101909 6610828614540362863317277)
        ·
          refine ⟨2479060730452636073743979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6610828614540362863317277 2479060730452636073743979)
          ·
            refine ⟨3718591095678954110615969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2479060730452636073743979 3718591095678954110615969)
            ·
              refine ⟨2788943321759215582961977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3718591095678954110615969 2788943321759215582961977)
              ·
                refine ⟨2091707491319411687221483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2788943321759215582961977 2091707491319411687221483)
                ·
                  refine ⟨3137561236979117530832225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2091707491319411687221483 3137561236979117530832225)
                  ·
                    refine ⟨2353170927734338148124169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3137561236979117530832225 2353170927734338148124169)
                    ·
                      refine ⟨1764878195800753611093127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2353170927734338148124169 1764878195800753611093127)
                      ·
                        rfl

theorem cell23_3437088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_3437088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437088 prefixEnd_3437088 := by exact prefixLift 3437088
  have htrace : WordTrace (prefixWord ++ tailWord_3437088) baseStart_3437088 baseEnd_3437088 := by
    simpa [prefixWord, tailWord_3437088, baseEnd_3437088] using wordTrace_append hprefix tailTrace_3437088
  have hstable : (prefixWord ++ tailWord_3437088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437088).length < 2 ^ (prefixWord ++ tailWord_3437088).sum := by decide
  have hdescent : baseEnd_3437088 < baseStart_3437088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437099 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 11]
def baseStart_3437099 : Nat := 118140960795 + 3437099 * 2 ^ 59
def prefixEnd_3437099 : Nat := 4983230072969 + 3 ^ 40 * 3437099 * 2
def baseEnd_3437099 : Nat := 196098204898661452006175

theorem tailTrace_3437099 : CollatzResearch.WordTrace tailWord_3437099 prefixEnd_3437099 196098204898661452006175 := by
  unfold tailWord_3437099
  simp only [CollatzResearch.WordTrace]
  refine ⟨125361299374984807620074351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83574199583323205080049567 125361299374984807620074351)
  ·
    refine ⟨188041949062477211430111527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125361299374984807620074351 188041949062477211430111527)
    ·
      refine ⟨282062923593715817145167291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188041949062477211430111527 282062923593715817145167291)
      ·
        refine ⟨423094385390573725717750937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282062923593715817145167291 423094385390573725717750937)
        ·
          refine ⟨317320789042930294288313203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423094385390573725717750937 317320789042930294288313203)
          ·
            refine ⟨475981183564395441432469805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317320789042930294288313203 475981183564395441432469805)
            ·
              refine ⟨178492943836648290537176177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 475981183564395441432469805 178492943836648290537176177)
              ·
                refine ⟨133869707877486217902882133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178492943836648290537176177 133869707877486217902882133)
                ·
                  refine ⟨196098204898661452006175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 133869707877486217902882133 196098204898661452006175)
                  ·
                    rfl

theorem cell23_3437099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 11].length) (baseStart_3437099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437099 prefixEnd_3437099 := by exact prefixLift 3437099
  have htrace : WordTrace (prefixWord ++ tailWord_3437099) baseStart_3437099 baseEnd_3437099 := by
    simpa [prefixWord, tailWord_3437099, baseEnd_3437099] using wordTrace_append hprefix tailTrace_3437099
  have hstable : (prefixWord ++ tailWord_3437099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437099).length < 2 ^ (prefixWord ++ tailWord_3437099).sum := by decide
  have hdescent : baseEnd_3437099 < baseStart_3437099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437106 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_3437106 : Nat := 118140960795 + 3437106 * 2 ^ 59
def prefixEnd_3437106 : Nat := 4983230072969 + 3 ^ 40 * 3437106 * 2
def baseEnd_3437106 : Nat := 1764887438452534540668043

theorem tailTrace_3437106 : CollatzResearch.WordTrace tailWord_3437106 prefixEnd_3437106 1764887438452534540668043 := by
  unfold tailWord_3437106
  simp only [CollatzResearch.WordTrace]
  refine ⟨31340388671489861953894793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83574369790639631877052781 31340388671489861953894793)
  ·
    refine ⟨23505291503617396465421095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31340388671489861953894793 23505291503617396465421095)
    ·
      refine ⟨35257937255426094698131643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23505291503617396465421095 35257937255426094698131643)
      ·
        refine ⟨52886905883139142047197465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35257937255426094698131643 52886905883139142047197465)
        ·
          refine ⟨39665179412354356535398099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52886905883139142047197465 39665179412354356535398099)
          ·
            refine ⟨59497769118531534803097149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39665179412354356535398099 59497769118531534803097149)
            ·
              refine ⟨22311663419449325551161431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59497769118531534803097149 22311663419449325551161431)
              ·
                refine ⟨33467495129173988326742147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22311663419449325551161431 33467495129173988326742147)
                ·
                  refine ⟨50201242693760982490113221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33467495129173988326742147 50201242693760982490113221)
                  ·
                    refine ⟨9412733005080184216896229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50201242693760982490113221 9412733005080184216896229)
                    ·
                      refine ⟨1764887438452534540668043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9412733005080184216896229 1764887438452534540668043)
                      ·
                        rfl

theorem cell23_3437106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_3437106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437106 prefixEnd_3437106 := by exact prefixLift 3437106
  have htrace : WordTrace (prefixWord ++ tailWord_3437106) baseStart_3437106 baseEnd_3437106 := by
    simpa [prefixWord, tailWord_3437106, baseEnd_3437106] using wordTrace_append hprefix tailTrace_3437106
  have hstable : (prefixWord ++ tailWord_3437106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437106).length < 2 ^ (prefixWord ++ tailWord_3437106).sum := by decide
  have hdescent : baseEnd_3437106 < baseStart_3437106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437116 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 9]
def baseStart_3437116 : Nat := 118140960795 + 3437116 * 2 ^ 59
def prefixEnd_3437116 : Nat := 4983230072969 + 3 ^ 40 * 3437116 * 2
def baseEnd_3437116 : Nat := 196099174806564389060333

theorem tailTrace_3437116 : CollatzResearch.WordTrace tailWord_3437116 prefixEnd_3437116 196099174806564389060333 := by
  unfold tailWord_3437116
  simp only [CollatzResearch.WordTrace]
  refine ⟨62680959707961609761721601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83574612943948813015628801 62680959707961609761721601)
  ·
    refine ⟨47010719780971207321291201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62680959707961609761721601 47010719780971207321291201)
    ·
      refine ⟨35258039835728405490968401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47010719780971207321291201 35258039835728405490968401)
      ·
        refine ⟨26443529876796304118226301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35258039835728405490968401 26443529876796304118226301)
        ·
          refine ⟨9916323703798614044334863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26443529876796304118226301 9916323703798614044334863)
          ·
            refine ⟨14874485555697921066502295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9916323703798614044334863 14874485555697921066502295)
            ·
              refine ⟨22311728333546881599753443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14874485555697921066502295 22311728333546881599753443)
              ·
                refine ⟨33467592500320322399630165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22311728333546881599753443 33467592500320322399630165)
                ·
                  refine ⟨196099174806564389060333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33467592500320322399630165 196099174806564389060333)
                  ·
                    rfl

theorem cell23_3437116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 9].length) (baseStart_3437116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437116 prefixEnd_3437116 := by exact prefixLift 3437116
  have htrace : WordTrace (prefixWord ++ tailWord_3437116) baseStart_3437116 baseEnd_3437116 := by
    simpa [prefixWord, tailWord_3437116, baseEnd_3437116] using wordTrace_append hprefix tailTrace_3437116
  have hstable : (prefixWord ++ tailWord_3437116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437116).length < 2 ^ (prefixWord ++ tailWord_3437116).sum := by decide
  have hdescent : baseEnd_3437116 < baseStart_3437116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437156 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_3437156 : Nat := 118140960795 + 3437156 * 2 ^ 59
def prefixEnd_3437156 : Nat := 4983230072969 + 3 ^ 40 * 3437156 * 2
def baseEnd_3437156 : Nat := 1764913112485259345042813

theorem tailTrace_3437156 : CollatzResearch.WordTrace tailWord_3437156 prefixEnd_3437156 1764913112485259345042813 := by
  unfold tailWord_3437156
  simp only [CollatzResearch.WordTrace]
  refine ⟨62681689167889153177449661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83575585557185537569932881 62681689167889153177449661)
  ·
    refine ⟨23505633437958432441543623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62681689167889153177449661 23505633437958432441543623)
    ·
      refine ⟨35258450156937648662315435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23505633437958432441543623 35258450156937648662315435)
      ·
        refine ⟨52887675235406472993473153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35258450156937648662315435 52887675235406472993473153)
        ·
          refine ⟨39665756426554854745104865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52887675235406472993473153 39665756426554854745104865)
          ·
            refine ⟨29749317319916141058828649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39665756426554854745104865 29749317319916141058828649)
            ·
              refine ⟨22311987989937105794121487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29749317319916141058828649 22311987989937105794121487)
              ·
                refine ⟨33467981984905658691182231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22311987989937105794121487 33467981984905658691182231)
                ·
                  refine ⟨50201972977358488036773347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33467981984905658691182231 50201972977358488036773347)
                  ·
                    refine ⟨75302959466037732055160021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50201972977358488036773347 75302959466037732055160021)
                    ·
                      refine ⟨1764913112485259345042813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 75302959466037732055160021 1764913112485259345042813)
                      ·
                        rfl

theorem cell23_3437156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_3437156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437156 prefixEnd_3437156 := by exact prefixLift 3437156
  have htrace : WordTrace (prefixWord ++ tailWord_3437156) baseStart_3437156 baseEnd_3437156 := by
    simpa [prefixWord, tailWord_3437156, baseEnd_3437156] using wordTrace_append hprefix tailTrace_3437156
  have hstable : (prefixWord ++ tailWord_3437156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437156).length < 2 ^ (prefixWord ++ tailWord_3437156).sum := by decide
  have hdescent : baseEnd_3437156 < baseStart_3437156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437183 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 4, 4, 2]
def baseStart_3437183 : Nat := 118140960795 + 3437183 * 2 ^ 59
def prefixEnd_3437183 : Nat := 4983230072969 + 3 ^ 40 * 3437183 * 2
def baseEnd_3437183 : Nat := 1764926976462930739405189

theorem tailTrace_3437183 : CollatzResearch.WordTrace tailWord_3437183 prefixEnd_3437183 1764926976462930739405189 := by
  unfold tailWord_3437183
  simp only [CollatzResearch.WordTrace]
  refine ⟨125364363106680489966132203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83576242071120326644088135 125364363106680489966132203)
  ·
    refine ⟨188046544660020734949198305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125364363106680489966132203 188046544660020734949198305)
    ·
      refine ⟨141034908495015551211898729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188046544660020734949198305 141034908495015551211898729)
      ·
        refine ⟨105776181371261663408924047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141034908495015551211898729 105776181371261663408924047)
        ·
          refine ⟨158664272056892495113386071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105776181371261663408924047 158664272056892495113386071)
          ·
            refine ⟨237996408085338742670079107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158664272056892495113386071 237996408085338742670079107)
            ·
              refine ⟨356994612128008114005118661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237996408085338742670079107 356994612128008114005118661)
              ·
                refine ⟨66936489774001521375959749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 356994612128008114005118661 66936489774001521375959749)
                ·
                  refine ⟨12550591832625285257992453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66936489774001521375959749 12550591832625285257992453)
                  ·
                    refine ⟨2353235968617240985873585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12550591832625285257992453 2353235968617240985873585)
                    ·
                      refine ⟨1764926976462930739405189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2353235968617240985873585 1764926976462930739405189)
                      ·
                        rfl

theorem cell23_3437183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 4, 2].length) (baseStart_3437183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437183 prefixEnd_3437183 := by exact prefixLift 3437183
  have htrace : WordTrace (prefixWord ++ tailWord_3437183) baseStart_3437183 baseEnd_3437183 := by
    simpa [prefixWord, tailWord_3437183, baseEnd_3437183] using wordTrace_append hprefix tailTrace_3437183
  have hstable : (prefixWord ++ tailWord_3437183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437183).length < 2 ^ (prefixWord ++ tailWord_3437183).sum := by decide
  have hdescent : baseEnd_3437183 < baseStart_3437183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437196 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 6]
def baseStart_3437196 : Nat := 118140960795 + 3437196 * 2 ^ 59
def prefixEnd_3437196 : Nat := 4983230072969 + 3 ^ 40 * 3437196 * 2
def baseEnd_3437196 : Nat := 1764933651711439188542629

theorem tailTrace_3437196 : CollatzResearch.WordTrace tailWord_3437196 prefixEnd_3437196 1764933651711439188542629 := by
  unfold tailWord_3437196
  simp only [CollatzResearch.WordTrace]
  refine ⟨62682418627816696593177721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83576558170422262124236961 62682418627816696593177721)
  ·
    refine ⟨47011813970862522444883291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62682418627816696593177721 47011813970862522444883291)
    ·
      refine ⟨70517720956293783667324937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47011813970862522444883291 70517720956293783667324937)
      ·
        refine ⟨52888290717220337750493703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70517720956293783667324937 52888290717220337750493703)
        ·
          refine ⟨79332436075830506625740555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52888290717220337750493703 79332436075830506625740555)
          ·
            refine ⟨118998654113745759938610833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79332436075830506625740555 118998654113745759938610833)
            ·
              refine ⟨89248990585309319953958125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118998654113745759938610833 89248990585309319953958125)
              ·
                refine ⟨33468371469490994982734297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89248990585309319953958125 33468371469490994982734297)
                ·
                  refine ⟨25101278602118246237050723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33468371469490994982734297 25101278602118246237050723)
                  ·
                    refine ⟨37651917903177369355576085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25101278602118246237050723 37651917903177369355576085)
                    ·
                      refine ⟨1764933651711439188542629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37651917903177369355576085 1764933651711439188542629)
                      ·
                        rfl

theorem cell23_3437196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_3437196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437196 prefixEnd_3437196 := by exact prefixLift 3437196
  have htrace : WordTrace (prefixWord ++ tailWord_3437196) baseStart_3437196 baseEnd_3437196 := by
    simpa [prefixWord, tailWord_3437196, baseEnd_3437196] using wordTrace_append hprefix tailTrace_3437196
  have hstable : (prefixWord ++ tailWord_3437196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437196).length < 2 ^ (prefixWord ++ tailWord_3437196).sum := by decide
  have hdescent : baseEnd_3437196 < baseStart_3437196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437203 : List Nat := [1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 3]
def baseStart_3437203 : Nat := 118140960795 + 3437203 * 2 ^ 59
def prefixEnd_3437203 : Nat := 4983230072969 + 3 ^ 40 * 3437203 * 2
def baseEnd_3437203 : Nat := 1764937246076020661155097

theorem tailTrace_3437203 : CollatzResearch.WordTrace tailWord_3437203 prefixEnd_3437203 1764937246076020661155097 := by
  unfold tailWord_3437203
  simp only [CollatzResearch.WordTrace]
  refine ⟨125365092566608033381860263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83576728377738688921240175 125365092566608033381860263)
  ·
    refine ⟨188047638849912050072790395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125365092566608033381860263 188047638849912050072790395)
    ·
      refine ⟨282071458274868075109185593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188047638849912050072790395 282071458274868075109185593)
      ·
        refine ⟨211553593706151056331889195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282071458274868075109185593 211553593706151056331889195)
        ·
          refine ⟨317330390559226584497833793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211553593706151056331889195 317330390559226584497833793)
          ·
            refine ⟨237997792919419938373375345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317330390559226584497833793 237997792919419938373375345)
            ·
              refine ⟨178498344689564953780031509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237997792919419938373375345 178498344689564953780031509)
              ·
                refine ⟨8367109907323357208438977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 178498344689564953780031509 8367109907323357208438977)
                ·
                  refine ⟨6275332430492517906329233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8367109907323357208438977 6275332430492517906329233)
                  ·
                    refine ⟨4706499322869388429746925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6275332430492517906329233 4706499322869388429746925)
                    ·
                      refine ⟨1764937246076020661155097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4706499322869388429746925 1764937246076020661155097)
                      ·
                        rfl

theorem cell23_3437203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 3].length) (baseStart_3437203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437203 prefixEnd_3437203 := by exact prefixLift 3437203
  have htrace : WordTrace (prefixWord ++ tailWord_3437203) baseStart_3437203 baseEnd_3437203 := by
    simpa [prefixWord, tailWord_3437203, baseEnd_3437203] using wordTrace_append hprefix tailTrace_3437203
  have hstable : (prefixWord ++ tailWord_3437203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437203).length < 2 ^ (prefixWord ++ tailWord_3437203).sum := by decide
  have hdescent : baseEnd_3437203 < baseStart_3437203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437237 : List Nat := [1, 3, 3, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_3437237 : Nat := 118140960795 + 3437237 * 2 ^ 59
def prefixEnd_3437237 : Nat := 4983230072969 + 3 ^ 40 * 3437237 * 2
def baseEnd_3437237 : Nat := 1764954704418273528129941

theorem tailTrace_3437237 : CollatzResearch.WordTrace tailWord_3437237 prefixEnd_3437237 1764954704418273528129941 := by
  unfold tailWord_3437237
  simp only [CollatzResearch.WordTrace]
  refine ⟨125366332648484857188597965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83577555098989904792398643 125366332648484857188597965)
  ·
    refine ⟨47012374743181821445724237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125366332648484857188597965 47012374743181821445724237)
    ·
      refine ⟨17629640528693183042146589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47012374743181821445724237 17629640528693183042146589)
      ·
        refine ⟨6611115198259943640804971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17629640528693183042146589 6611115198259943640804971)
        ·
          refine ⟨9916672797389915461207457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6611115198259943640804971 9916672797389915461207457)
          ·
            refine ⟨7437504598042436595905593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9916672797389915461207457 7437504598042436595905593)
            ·
              refine ⟨5578128448531827446929195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7437504598042436595905593 5578128448531827446929195)
              ·
                refine ⟨8367192672797741170393793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5578128448531827446929195 8367192672797741170393793)
                ·
                  refine ⟨6275394504598305877795345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8367192672797741170393793 6275394504598305877795345)
                  ·
                    refine ⟨4706545878448729408346509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6275394504598305877795345 4706545878448729408346509)
                    ·
                      refine ⟨1764954704418273528129941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4706545878448729408346509 1764954704418273528129941)
                      ·
                        rfl

theorem cell23_3437237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_3437237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437237 prefixEnd_3437237 := by exact prefixLift 3437237
  have htrace : WordTrace (prefixWord ++ tailWord_3437237) baseStart_3437237 baseEnd_3437237 := by
    simpa [prefixWord, tailWord_3437237, baseEnd_3437237] using wordTrace_append hprefix tailTrace_3437237
  have hstable : (prefixWord ++ tailWord_3437237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437237).length < 2 ^ (prefixWord ++ tailWord_3437237).sum := by decide
  have hdescent : baseEnd_3437237 < baseStart_3437237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437261 : List Nat := [1, 6, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_3437261 : Nat := 118140960795 + 3437261 * 2 ^ 59
def prefixEnd_3437261 : Nat := 4983230072969 + 3 ^ 40 * 3437261 * 2
def baseEnd_3437261 : Nat := 588322342651327144743277

theorem tailTrace_3437261 : CollatzResearch.WordTrace tailWord_3437261 prefixEnd_3437261 588322342651327144743277 := by
  unfold tailWord_3437261
  simp only [CollatzResearch.WordTrace]
  refine ⟨125367208000397909287471637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83578138666931939524981091 125367208000397909287471637)
  ·
    refine ⟨5876587875018651997850233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 125367208000397909287471637 5876587875018651997850233)
    ·
      refine ⟨4407440906263988998387675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5876587875018651997850233 4407440906263988998387675)
      ·
        refine ⟨6611161359395983497581513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4407440906263988998387675 6611161359395983497581513)
        ·
          refine ⟨4958371019546987623186135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6611161359395983497581513 4958371019546987623186135)
          ·
            refine ⟨7437556529320481434779203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4958371019546987623186135 7437556529320481434779203)
            ·
              refine ⟨11156334793980722152168805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7437556529320481434779203 11156334793980722152168805)
              ·
                refine ⟨2091812773871385403531651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11156334793980722152168805 2091812773871385403531651)
                ·
                  refine ⟨3137719160807078105297477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2091812773871385403531651 3137719160807078105297477)
                  ·
                    refine ⟨588322342651327144743277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3137719160807078105297477 588322342651327144743277)
                    ·
                      rfl

theorem cell23_3437261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_3437261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437261 prefixEnd_3437261 := by exact prefixLift 3437261
  have htrace : WordTrace (prefixWord ++ tailWord_3437261) baseStart_3437261 baseEnd_3437261 := by
    simpa [prefixWord, tailWord_3437261, baseEnd_3437261] using wordTrace_append hprefix tailTrace_3437261
  have hstable : (prefixWord ++ tailWord_3437261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437261).length < 2 ^ (prefixWord ++ tailWord_3437261).sum := by decide
  have hdescent : baseEnd_3437261 < baseStart_3437261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437273 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 5, 1, 4]
def baseStart_3437273 : Nat := 118140960795 + 3437273 * 2 ^ 59
def prefixEnd_3437273 : Nat := 4983230072969 + 3 ^ 40 * 3437273 * 2
def baseEnd_3437273 : Nat := 1764973189721835387279775

theorem tailTrace_3437273 : CollatzResearch.WordTrace tailWord_3437273 prefixEnd_3437273 1764973189721835387279775 := by
  unfold tailWord_3437273
  simp only [CollatzResearch.WordTrace]
  refine ⟨125367645676354435336908473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83578430450902956891272315 125367645676354435336908473)
  ·
    refine ⟨94025734257265826502681355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125367645676354435336908473 94025734257265826502681355)
    ·
      refine ⟨141038601385898739754022033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94025734257265826502681355 141038601385898739754022033)
      ·
        refine ⟨105778951039424054815516525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141038601385898739754022033 105778951039424054815516525)
        ·
          refine ⟨39667106639784020555818697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105778951039424054815516525 39667106639784020555818697)
          ·
            refine ⟨29750329979838015416864023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39667106639784020555818697 29750329979838015416864023)
            ·
              refine ⟨44625494969757023125296035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29750329979838015416864023 44625494969757023125296035)
              ·
                refine ⟨66938242454635534687944053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44625494969757023125296035 66938242454635534687944053)
                ·
                  refine ⟨6275460230122081376994755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66938242454635534687944053 6275460230122081376994755)
                  ·
                    refine ⟨9413190345183122065492133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6275460230122081376994755 9413190345183122065492133)
                    ·
                      refine ⟨1764973189721835387279775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9413190345183122065492133 1764973189721835387279775)
                      ·
                        rfl

theorem cell23_3437273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_3437273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437273 prefixEnd_3437273 := by exact prefixLift 3437273
  have htrace : WordTrace (prefixWord ++ tailWord_3437273) baseStart_3437273 baseEnd_3437273 := by
    simpa [prefixWord, tailWord_3437273, baseEnd_3437273] using wordTrace_append hprefix tailTrace_3437273
  have hstable : (prefixWord ++ tailWord_3437273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437273).length < 2 ^ (prefixWord ++ tailWord_3437273).sum := by decide
  have hdescent : baseEnd_3437273 < baseStart_3437273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437290 : List Nat := [3, 1, 3, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_3437290 : Nat := 118140960795 + 3437290 * 2 ^ 59
def prefixEnd_3437290 : Nat := 4983230072969 + 3 ^ 40 * 3437290 * 2
def baseEnd_3437290 : Nat := 1764981918892961820767197

theorem tailTrace_3437290 : CollatzResearch.WordTrace tailWord_3437290 prefixEnd_3437290 1764981918892961820767197 := by
  unfold tailWord_3437290
  simp only [CollatzResearch.WordTrace]
  refine ⟨31342066429323211810069331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83578843811528564826851549 31342066429323211810069331)
  ·
    refine ⟨47013099643984817715103997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31342066429323211810069331 47013099643984817715103997)
    ·
      refine ⟨17629912366494306643163999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47013099643984817715103997 17629912366494306643163999)
      ·
        refine ⟨26444868549741459964745999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17629912366494306643163999 26444868549741459964745999)
        ·
          refine ⟨39667302824612189947118999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26444868549741459964745999 39667302824612189947118999)
          ·
            refine ⟨59500954236918284920678499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39667302824612189947118999 59500954236918284920678499)
            ·
              refine ⟨89251431355377427381017749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59500954236918284920678499 89251431355377427381017749)
              ·
                refine ⟨4183660844783316908485207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89251431355377427381017749 4183660844783316908485207)
                ·
                  refine ⟨6275491267174975362727811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4183660844783316908485207 6275491267174975362727811)
                  ·
                    refine ⟨9413236900762463044091717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6275491267174975362727811 9413236900762463044091717)
                    ·
                      refine ⟨1764981918892961820767197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9413236900762463044091717 1764981918892961820767197)
                      ·
                        rfl

theorem cell23_3437290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_3437290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437290 prefixEnd_3437290 := by exact prefixLift 3437290
  have htrace : WordTrace (prefixWord ++ tailWord_3437290) baseStart_3437290 baseEnd_3437290 := by
    simpa [prefixWord, tailWord_3437290, baseEnd_3437290] using wordTrace_append hprefix tailTrace_3437290
  have hstable : (prefixWord ++ tailWord_3437290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437290).length < 2 ^ (prefixWord ++ tailWord_3437290).sum := by decide
  have hdescent : baseEnd_3437290 < baseStart_3437290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437294 : List Nat := [4, 1, 2, 1, 1, 5, 1, 1, 2, 3, 2]
def baseStart_3437294 : Nat := 118140960795 + 3437294 * 2 ^ 59
def prefixEnd_3437294 : Nat := 4983230072969 + 3 ^ 40 * 3437294 * 2
def baseEnd_3437294 : Nat := 1764983972815579805117179

theorem tailTrace_3437294 : CollatzResearch.WordTrace tailWord_3437294 prefixEnd_3437294 1764983972815579805117179 := by
  unfold tailWord_3437294
  simp only [CollatzResearch.WordTrace]
  refine ⟨15671051451159794490427867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83578941072852237282281957 15671051451159794490427867)
  ·
    refine ⟨23506577176739691735641801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15671051451159794490427867 23506577176739691735641801)
    ·
      refine ⟨17629932882554768801731351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23506577176739691735641801 17629932882554768801731351)
      ·
        refine ⟨26444899323832153202597027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17629932882554768801731351 26444899323832153202597027)
        ·
          refine ⟨39667348985748229803895541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26444899323832153202597027 39667348985748229803895541)
          ·
            refine ⟨3718813967413896544115207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39667348985748229803895541 3718813967413896544115207)
            ·
              refine ⟨5578220951120844816172811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3718813967413896544115207 5578220951120844816172811)
              ·
                refine ⟨8367331426681267224259217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5578220951120844816172811 8367331426681267224259217)
                ·
                  refine ⟨6275498570010950418194413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8367331426681267224259217 6275498570010950418194413)
                  ·
                    refine ⟨2353311963754106406822905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6275498570010950418194413 2353311963754106406822905)
                    ·
                      refine ⟨1764983972815579805117179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2353311963754106406822905 1764983972815579805117179)
                      ·
                        rfl

theorem cell23_3437294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_3437294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437294 prefixEnd_3437294 := by exact prefixLift 3437294
  have htrace : WordTrace (prefixWord ++ tailWord_3437294) baseStart_3437294 baseEnd_3437294 := by
    simpa [prefixWord, tailWord_3437294, baseEnd_3437294] using wordTrace_append hprefix tailTrace_3437294
  have hstable : (prefixWord ++ tailWord_3437294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437294).length < 2 ^ (prefixWord ++ tailWord_3437294).sum := by decide
  have hdescent : baseEnd_3437294 < baseStart_3437294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437358 : List Nat := [4, 1, 3, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_3437358 : Nat := 118140960795 + 3437358 * 2 ^ 59
def prefixEnd_3437358 : Nat := 4983230072969 + 3 ^ 40 * 3437358 * 2
def baseEnd_3437358 : Nat := 1765016835577467554716885

theorem tailTrace_3437358 : CollatzResearch.WordTrace tailWord_3437358 prefixEnd_3437358 1765016835577467554716885 := by
  unfold tailWord_3437358
  simp only [CollatzResearch.WordTrace]
  refine ⟨15671343235130811856719091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83580497254030996569168485 15671343235130811856719091)
  ·
    refine ⟨23507014852696217785078637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15671343235130811856719091 23507014852696217785078637)
    ·
      refine ⟨8815130569761081669404489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23507014852696217785078637 8815130569761081669404489)
      ·
        refine ⟨6611347927320811252053367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8815130569761081669404489 6611347927320811252053367)
        ·
          refine ⟨9917021890981216878080051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6611347927320811252053367 9917021890981216878080051)
          ·
            refine ⟨14875532836471825317120077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9917021890981216878080051 14875532836471825317120077)
            ·
              refine ⟨5578324813676934493920029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14875532836471825317120077 5578324813676934493920029)
              ·
                refine ⟨2091871805128850435220011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5578324813676934493920029 2091871805128850435220011)
                ·
                  refine ⟨3137807707693275652830017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2091871805128850435220011 3137807707693275652830017)
                  ·
                    refine ⟨2353355780769956739622513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3137807707693275652830017 2353355780769956739622513)
                    ·
                      refine ⟨1765016835577467554716885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2353355780769956739622513 1765016835577467554716885)
                      ·
                        rfl

theorem cell23_3437358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_3437358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437358 prefixEnd_3437358 := by exact prefixLift 3437358
  have htrace : WordTrace (prefixWord ++ tailWord_3437358) baseStart_3437358 baseEnd_3437358 := by
    simpa [prefixWord, tailWord_3437358, baseEnd_3437358] using wordTrace_append hprefix tailTrace_3437358
  have hstable : (prefixWord ++ tailWord_3437358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437358).length < 2 ^ (prefixWord ++ tailWord_3437358).sum := by decide
  have hdescent : baseEnd_3437358 < baseStart_3437358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437367 : List Nat := [1, 1, 3, 1, 2, 1, 3, 5, 1, 3, 2]
def baseStart_3437367 : Nat := 118140960795 + 3437367 * 2 ^ 59
def prefixEnd_3437367 : Nat := 4983230072969 + 3 ^ 40 * 3437367 * 2
def baseEnd_3437367 : Nat := 1765021456903358019504343

theorem tailTrace_3437367 : CollatzResearch.WordTrace tailWord_3437367 prefixEnd_3437367 1765021456903358019504343 := by
  unfold tailWord_3437367
  simp only [CollatzResearch.WordTrace]
  refine ⟨125371074138013889390830355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83580716092009259593886903 125371074138013889390830355)
  ·
    refine ⟨188056611207020834086245533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125371074138013889390830355 188056611207020834086245533)
    ·
      refine ⟨70521229202632812782342075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188056611207020834086245533 70521229202632812782342075)
      ·
        refine ⟨105781843803949219173513113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70521229202632812782342075 105781843803949219173513113)
        ·
          refine ⟨79336382852961914380134835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105781843803949219173513113 79336382852961914380134835)
          ·
            refine ⟨119004574279442871570202253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79336382852961914380134835 119004574279442871570202253)
            ·
              refine ⟨44626715354791076838825845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119004574279442871570202253 44626715354791076838825845)
              ·
                refine ⟨4183754564511663453639923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44626715354791076838825845 4183754564511663453639923)
                ·
                  refine ⟨6275631846767495180459885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4183754564511663453639923 6275631846767495180459885)
                  ·
                    refine ⟨2353361942537810692672457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6275631846767495180459885 2353361942537810692672457)
                    ·
                      refine ⟨1765021456903358019504343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2353361942537810692672457 1765021456903358019504343)
                      ·
                        rfl

theorem cell23_3437367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 3, 2].length) (baseStart_3437367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437367 prefixEnd_3437367 := by exact prefixLift 3437367
  have htrace : WordTrace (prefixWord ++ tailWord_3437367) baseStart_3437367 baseEnd_3437367 := by
    simpa [prefixWord, tailWord_3437367, baseEnd_3437367] using wordTrace_append hprefix tailTrace_3437367
  have hstable : (prefixWord ++ tailWord_3437367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437367).length < 2 ^ (prefixWord ++ tailWord_3437367).sum := by decide
  have hdescent : baseEnd_3437367 < baseStart_3437367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437383 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_3437383 : Nat := 118140960795 + 3437383 * 2 ^ 59
def prefixEnd_3437383 : Nat := 4983230072969 + 3 ^ 40 * 3437383 * 2
def baseEnd_3437383 : Nat := 1765029672593829956904269

theorem tailTrace_3437383 : CollatzResearch.WordTrace tailWord_3437383 prefixEnd_3437383 1765029672593829956904269 := by
  unfold tailWord_3437383
  simp only [CollatzResearch.WordTrace]
  refine ⟨125371657705955924123412803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83581105137303949415608535 125371657705955924123412803)
  ·
    refine ⟨188057486558933886185119205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125371657705955924123412803 188057486558933886185119205)
    ·
      refine ⟨35260778729800103659709851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188057486558933886185119205 35260778729800103659709851)
      ·
        refine ⟨52891168094700155489564777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35260778729800103659709851 52891168094700155489564777)
        ·
          refine ⟨39668376071025116617173583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52891168094700155489564777 39668376071025116617173583)
          ·
            refine ⟨59502564106537674925760375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39668376071025116617173583 59502564106537674925760375)
            ·
              refine ⟨89253846159806512388640563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59502564106537674925760375 89253846159806512388640563)
              ·
                refine ⟨133880769239709768582960845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89253846159806512388640563 133880769239709768582960845)
                ·
                  refine ⟨50205288464891163218610317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133880769239709768582960845 50205288464891163218610317)
                  ·
                    refine ⟨18826983174334186206978869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50205288464891163218610317 18826983174334186206978869)
                    ·
                      refine ⟨1765029672593829956904269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18826983174334186206978869 1765029672593829956904269)
                      ·
                        rfl

theorem cell23_3437383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_3437383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437383 prefixEnd_3437383 := by exact prefixLift 3437383
  have htrace : WordTrace (prefixWord ++ tailWord_3437383) baseStart_3437383 baseEnd_3437383 := by
    simpa [prefixWord, tailWord_3437383, baseEnd_3437383] using wordTrace_append hprefix tailTrace_3437383
  have hstable : (prefixWord ++ tailWord_3437383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437383).length < 2 ^ (prefixWord ++ tailWord_3437383).sum := by decide
  have hdescent : baseEnd_3437383 < baseStart_3437383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437397 : List Nat := [1, 3, 2, 2, 2, 1, 2, 3, 1, 4, 2]
def baseStart_3437397 : Nat := 118140960795 + 3437397 * 2 ^ 59
def prefixEnd_3437397 : Nat := 4983230072969 + 3 ^ 40 * 3437397 * 2
def baseEnd_3437397 : Nat := 1765036861322992902129205

theorem tailTrace_3437397 : CollatzResearch.WordTrace tailWord_3437397 prefixEnd_3437397 1765036861322992902129205 := by
  unfold tailWord_3437397
  simp only [CollatzResearch.WordTrace]
  refine ⟨125372168327905204514422445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83581445551936803009614963 125372168327905204514422445)
  ·
    refine ⟨47014563122964451692908417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125372168327905204514422445 47014563122964451692908417)
    ·
      refine ⟨35260922342223338769681313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47014563122964451692908417 35260922342223338769681313)
      ·
        refine ⟨26445691756667504077260985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35260922342223338769681313 26445691756667504077260985)
        ·
          refine ⟨19834268817500628057945739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26445691756667504077260985 19834268817500628057945739)
          ·
            refine ⟨29751403226250942086918609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19834268817500628057945739 29751403226250942086918609)
            ·
              refine ⟨22313552419688206565188957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29751403226250942086918609 22313552419688206565188957)
              ·
                refine ⟨8367582157383077461945859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22313552419688206565188957 8367582157383077461945859)
                ·
                  refine ⟨12551373236074616192918789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8367582157383077461945859 12551373236074616192918789)
                  ·
                    refine ⟨2353382481763990536172273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12551373236074616192918789 2353382481763990536172273)
                    ·
                      refine ⟨1765036861322992902129205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2353382481763990536172273 1765036861322992902129205)
                      ·
                        rfl

theorem cell23_3437397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_3437397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437397 prefixEnd_3437397 := by exact prefixLift 3437397
  have htrace : WordTrace (prefixWord ++ tailWord_3437397) baseStart_3437397 baseEnd_3437397 := by
    simpa [prefixWord, tailWord_3437397, baseEnd_3437397] using wordTrace_append hprefix tailTrace_3437397
  have hstable : (prefixWord ++ tailWord_3437397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437397).length < 2 ^ (prefixWord ++ tailWord_3437397).sum := by decide
  have hdescent : baseEnd_3437397 < baseStart_3437397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437447 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 3]
def baseStart_3437447 : Nat := 118140960795 + 3437447 * 2 ^ 59
def prefixEnd_3437447 : Nat := 4983230072969 + 3 ^ 40 * 3437447 * 2
def baseEnd_3437447 : Nat := 1765062535355717706503975

theorem tailTrace_3437447 : CollatzResearch.WordTrace tailWord_3437447 prefixEnd_3437447 1765062535355717706503975 := by
  unfold tailWord_3437447
  simp only [CollatzResearch.WordTrace]
  refine ⟨125373991977724063053742595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83582661318482708702495063 125373991977724063053742595)
  ·
    refine ⟨188060987966586094580613893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125373991977724063053742595 188060987966586094580613893)
    ·
      refine ⟨35261435243734892733865105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188060987966586094580613893 35261435243734892733865105)
      ·
        refine ⟨26446076432801169550398829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35261435243734892733865105 26446076432801169550398829)
        ·
          refine ⟨9917278662300438581399561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26446076432801169550398829 9917278662300438581399561)
          ·
            refine ⟨7437958996725328936049671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9917278662300438581399561 7437958996725328936049671)
            ·
              refine ⟨11156938495087993404074507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7437958996725328936049671 11156938495087993404074507)
              ·
                refine ⟨16735407742631990106111761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11156938495087993404074507 16735407742631990106111761)
                ·
                  refine ⟨12551555806973992579583821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16735407742631990106111761 12551555806973992579583821)
                  ·
                    refine ⟨4706833427615247217343933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12551555806973992579583821 4706833427615247217343933)
                    ·
                      refine ⟨1765062535355717706503975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4706833427615247217343933 1765062535355717706503975)
                      ·
                        rfl

theorem cell23_3437447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_3437447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437447 prefixEnd_3437447 := by exact prefixLift 3437447
  have htrace : WordTrace (prefixWord ++ tailWord_3437447) baseStart_3437447 baseEnd_3437447 := by
    simpa [prefixWord, tailWord_3437447, baseEnd_3437447] using wordTrace_append hprefix tailTrace_3437447
  have hstable : (prefixWord ++ tailWord_3437447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437447).length < 2 ^ (prefixWord ++ tailWord_3437447).sum := by decide
  have hdescent : baseEnd_3437447 < baseStart_3437447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437497 : List Nat := [1, 2, 1, 4, 2, 2, 1, 3, 3, 4]
def baseStart_3437497 : Nat := 118140960795 + 3437497 * 2 ^ 59
def prefixEnd_3437497 : Nat := 4983230072969 + 3 ^ 40 * 3437497 * 2
def baseEnd_3437497 : Nat := 588362736462814170292915

theorem tailTrace_3437497 : CollatzResearch.WordTrace tailWord_3437497 prefixEnd_3437497 588362736462814170292915 := by
  unfold tailWord_3437497
  simp only [CollatzResearch.WordTrace]
  refine ⟨125375815627542921593062745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83583877085028614395375163 125375815627542921593062745)
  ·
    refine ⟨94031861720657191194797059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125375815627542921593062745 94031861720657191194797059)
    ·
      refine ⟨141047792580985786792195589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94031861720657191194797059 141047792580985786792195589)
      ·
        refine ⟨26446461108934835023536673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141047792580985786792195589 26446461108934835023536673)
        ·
          refine ⟨19834845831701126267652505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26446461108934835023536673 19834845831701126267652505)
          ·
            refine ⟨14876134373775844700739379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19834845831701126267652505 14876134373775844700739379)
            ·
              refine ⟨22314201560663767051109069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14876134373775844700739379 22314201560663767051109069)
              ·
                refine ⟨8367825585248912644165901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22314201560663767051109069 8367825585248912644165901)
                ·
                  refine ⟨3137934594468342241562213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8367825585248912644165901 3137934594468342241562213)
                  ·
                    refine ⟨588362736462814170292915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3137934594468342241562213 588362736462814170292915)
                    ·
                      rfl

theorem cell23_3437497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 4].length) (baseStart_3437497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437497 prefixEnd_3437497 := by exact prefixLift 3437497
  have htrace : WordTrace (prefixWord ++ tailWord_3437497) baseStart_3437497 baseEnd_3437497 := by
    simpa [prefixWord, tailWord_3437497, baseEnd_3437497] using wordTrace_append hprefix tailTrace_3437497
  have hstable : (prefixWord ++ tailWord_3437497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437497).length < 2 ^ (prefixWord ++ tailWord_3437497).sum := by decide
  have hdescent : baseEnd_3437497 < baseStart_3437497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437520 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 3]
def baseStart_3437520 : Nat := 118140960795 + 3437520 * 2 ^ 59
def prefixEnd_3437520 : Nat := 4983230072969 + 3 ^ 40 * 3437520 * 2
def baseEnd_3437520 : Nat := 1765100019443495920891139

theorem tailTrace_3437520 : CollatzResearch.WordTrace tailWord_3437520 prefixEnd_3437520 1765100019443495920891139 := by
  unfold tailWord_3437520
  simp only [CollatzResearch.WordTrace]
  refine ⟨62688327253229798260575007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83584436337639731014100009 62688327253229798260575007)
  ·
    refine ⟨94032490879844697390862511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62688327253229798260575007 94032490879844697390862511)
    ·
      refine ⟨141048736319767046086293767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94032490879844697390862511 141048736319767046086293767)
      ·
        refine ⟨211573104479650569129440651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141048736319767046086293767 211573104479650569129440651)
        ·
          refine ⟨317359656719475853694160977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211573104479650569129440651 317359656719475853694160977)
          ·
            refine ⟨238019742539606890270620733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317359656719475853694160977 238019742539606890270620733)
            ·
              refine ⟨89257403452352583851482775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238019742539606890270620733 89257403452352583851482775)
              ·
                refine ⟨133886105178528875777224163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89257403452352583851482775 133886105178528875777224163)
                ·
                  refine ⟨200829157767793313665836245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133886105178528875777224163 200829157767793313665836245)
                  ·
                    refine ⟨4706933385182655789043037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 200829157767793313665836245 4706933385182655789043037)
                    ·
                      refine ⟨1765100019443495920891139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4706933385182655789043037 1765100019443495920891139)
                      ·
                        rfl

theorem cell23_3437520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 3].length) (baseStart_3437520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437520 prefixEnd_3437520 := by exact prefixLift 3437520
  have htrace : WordTrace (prefixWord ++ tailWord_3437520) baseStart_3437520 baseEnd_3437520 := by
    simpa [prefixWord, tailWord_3437520, baseEnd_3437520] using wordTrace_append hprefix tailTrace_3437520
  have hstable : (prefixWord ++ tailWord_3437520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437520).length < 2 ^ (prefixWord ++ tailWord_3437520).sum := by decide
  have hdescent : baseEnd_3437520 < baseStart_3437520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437541 : List Nat := [1, 3, 1, 6, 1, 1, 1, 2, 2, 2, 3]
def baseStart_3437541 : Nat := 118140960795 + 3437541 * 2 ^ 59
def prefixEnd_3437541 : Nat := 4983230072969 + 3 ^ 40 * 3437541 * 2
def baseEnd_3437541 : Nat := 1765110802537240338728543

theorem tailTrace_3437541 : CollatzResearch.WordTrace tailWord_3437541 prefixEnd_3437541 1765110802537240338728543 := by
  unfold tailWord_3437541
  simp only [CollatzResearch.WordTrace]
  refine ⟨125377420439383517107664477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83584946959589011405109651 125377420439383517107664477)
  ·
    refine ⟨47016532664768818915374179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125377420439383517107664477 47016532664768818915374179)
    ·
      refine ⟨70524798997153228373061269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47016532664768818915374179 70524798997153228373061269)
      ·
        refine ⟨3305849952991557579987247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70524798997153228373061269 3305849952991557579987247)
        ·
          refine ⟨4958774929487336369980871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3305849952991557579987247 4958774929487336369980871)
          ·
            refine ⟨7438162394231004554971307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4958774929487336369980871 7438162394231004554971307)
            ·
              refine ⟨11157243591346506832456961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7438162394231004554971307 11157243591346506832456961)
              ·
                refine ⟨8367932693509880124342721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11157243591346506832456961 8367932693509880124342721)
                ·
                  refine ⟨6275949520132410093257041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8367932693509880124342721 6275949520132410093257041)
                  ·
                    refine ⟨4706962140099307569942781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6275949520132410093257041 4706962140099307569942781)
                    ·
                      refine ⟨1765110802537240338728543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4706962140099307569942781 1765110802537240338728543)
                      ·
                        rfl

theorem cell23_3437541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_3437541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437541 prefixEnd_3437541 := by exact prefixLift 3437541
  have htrace : WordTrace (prefixWord ++ tailWord_3437541) baseStart_3437541 baseEnd_3437541 := by
    simpa [prefixWord, tailWord_3437541, baseEnd_3437541] using wordTrace_append hprefix tailTrace_3437541
  have hstable : (prefixWord ++ tailWord_3437541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437541).length < 2 ^ (prefixWord ++ tailWord_3437541).sum := by decide
  have hdescent : baseEnd_3437541 < baseStart_3437541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437560 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 2, 5, 4]
def baseStart_3437560 : Nat := 118140960795 + 3437560 * 2 ^ 59
def prefixEnd_3437560 : Nat := 4983230072969 + 3 ^ 40 * 3437560 * 2
def baseEnd_3437560 : Nat := 1765120558669675764390955

theorem tailTrace_3437560 : CollatzResearch.WordTrace tailWord_3437560 prefixEnd_3437560 1765120558669675764390955 := by
  unfold tailWord_3437560
  simp only [CollatzResearch.WordTrace]
  refine ⟨62689056713157341676303067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83585408950876455568404089 62689056713157341676303067)
  ·
    refine ⟨94033585069736012514454601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62689056713157341676303067 94033585069736012514454601)
    ·
      refine ⟨70525188802302009385840951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94033585069736012514454601 70525188802302009385840951)
      ·
        refine ⟨105787783203453014078761427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70525188802302009385840951 105787783203453014078761427)
        ·
          refine ⟨158681674805179521118142141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105787783203453014078761427 158681674805179521118142141)
          ·
            refine ⟨59505628051942320419303303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158681674805179521118142141 59505628051942320419303303)
            ·
              refine ⟨89258442077913480628954955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59505628051942320419303303 89258442077913480628954955)
              ·
                refine ⟨133887663116870220943432433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89258442077913480628954955 133887663116870220943432433)
                ·
                  refine ⟨100415747337652665707574325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133887663116870220943432433 100415747337652665707574325)
                  ·
                    refine ⟨9413976312904937410085093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100415747337652665707574325 9413976312904937410085093)
                    ·
                      refine ⟨1765120558669675764390955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9413976312904937410085093 1765120558669675764390955)
                      ·
                        rfl

theorem cell23_3437560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_3437560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437560 prefixEnd_3437560 := by exact prefixLift 3437560
  have htrace : WordTrace (prefixWord ++ tailWord_3437560) baseStart_3437560 baseEnd_3437560 := by
    simpa [prefixWord, tailWord_3437560, baseEnd_3437560] using wordTrace_append hprefix tailTrace_3437560
  have hstable : (prefixWord ++ tailWord_3437560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437560).length < 2 ^ (prefixWord ++ tailWord_3437560).sum := by decide
  have hdescent : baseEnd_3437560 < baseStart_3437560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437577 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 2, 6, 2]
def baseStart_3437577 : Nat := 118140960795 + 3437577 * 2 ^ 59
def prefixEnd_3437577 : Nat := 4983230072969 + 3 ^ 40 * 3437577 * 2
def baseEnd_3437577 : Nat := 1765129287840802197878377

theorem tailTrace_3437577 : CollatzResearch.WordTrace tailWord_3437577 prefixEnd_3437577 1765129287840802197878377 := by
  unfold tailWord_3437577
  simp only [CollatzResearch.WordTrace]
  refine ⟨125378733467253095255974985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83585822311502063503983323 125378733467253095255974985)
  ·
    refine ⟨94034050100439821441981239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125378733467253095255974985 94034050100439821441981239)
    ·
      refine ⟨141051075150659732162971859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94034050100439821441981239 141051075150659732162971859)
      ·
        refine ⟨211576612725989598244457789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141051075150659732162971859 211576612725989598244457789)
        ·
          refine ⟨79341229772246099341671671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211576612725989598244457789 79341229772246099341671671)
          ·
            refine ⟨119011844658369149012507507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79341229772246099341671671 119011844658369149012507507)
            ·
              refine ⟨178517766987553723518761261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119011844658369149012507507 178517766987553723518761261)
              ·
                refine ⟨66944162620332646319535473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178517766987553723518761261 66944162620332646319535473)
                ·
                  refine ⟨50208121965249484739651605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66944162620332646319535473 50208121965249484739651605)
                  ·
                    refine ⟨2353505717121069597171169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50208121965249484739651605 2353505717121069597171169)
                    ·
                      refine ⟨1765129287840802197878377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2353505717121069597171169 1765129287840802197878377)
                      ·
                        rfl

theorem cell23_3437577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 6, 2].length) (baseStart_3437577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437577 prefixEnd_3437577 := by exact prefixLift 3437577
  have htrace : WordTrace (prefixWord ++ tailWord_3437577) baseStart_3437577 baseEnd_3437577 := by
    simpa [prefixWord, tailWord_3437577, baseEnd_3437577] using wordTrace_append hprefix tailTrace_3437577
  have hstable : (prefixWord ++ tailWord_3437577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437577).length < 2 ^ (prefixWord ++ tailWord_3437577).sum := by decide
  have hdescent : baseEnd_3437577 < baseStart_3437577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437591 : List Nat := [1, 1, 3, 5, 1, 2, 3, 1, 1, 5]
def baseStart_3437591 : Nat := 118140960795 + 3437591 * 2 ^ 59
def prefixEnd_3437591 : Nat := 4983230072969 + 3 ^ 40 * 3437591 * 2
def baseEnd_3437591 : Nat := 588378825523321714367771

theorem tailTrace_3437591 : CollatzResearch.WordTrace tailWord_3437591 prefixEnd_3437591 588378825523321714367771 := by
  unfold tailWord_3437591
  simp only [CollatzResearch.WordTrace]
  refine ⟨125379244089202375646984627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83586162726134917097989751 125379244089202375646984627)
  ·
    refine ⟨188068866133803563470476941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125379244089202375646984627 188068866133803563470476941)
    ·
      refine ⟨70525824800176336301428853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188068866133803563470476941 70525824800176336301428853)
      ·
        refine ⟨6611796075016531528258955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70525824800176336301428853 6611796075016531528258955)
        ·
          refine ⟨9917694112524797292388433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6611796075016531528258955 9917694112524797292388433)
          ·
            refine ⟨7438270584393597969291325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9917694112524797292388433 7438270584393597969291325)
            ·
              refine ⟨2789351469147599238484247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7438270584393597969291325 2789351469147599238484247)
              ·
                refine ⟨4184027203721398857726371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2789351469147599238484247 4184027203721398857726371)
                ·
                  refine ⟨6276040805582098286589557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4184027203721398857726371 6276040805582098286589557)
                  ·
                    refine ⟨588378825523321714367771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6276040805582098286589557 588378825523321714367771)
                    ·
                      rfl

theorem cell23_3437591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 1, 5].length) (baseStart_3437591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437591 prefixEnd_3437591 := by exact prefixLift 3437591
  have htrace : WordTrace (prefixWord ++ tailWord_3437591) baseStart_3437591 baseEnd_3437591 := by
    simpa [prefixWord, tailWord_3437591, baseEnd_3437591] using wordTrace_append hprefix tailTrace_3437591
  have hstable : (prefixWord ++ tailWord_3437591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437591).length < 2 ^ (prefixWord ++ tailWord_3437591).sum := by decide
  have hdescent : baseEnd_3437591 < baseStart_3437591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437614 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_3437614 : Nat := 118140960795 + 3437614 * 2 ^ 59
def prefixEnd_3437614 : Nat := 4983230072969 + 3 ^ 40 * 3437614 * 2
def baseEnd_3437614 : Nat := 1765148286625018553115707

theorem tailTrace_3437614 : CollatzResearch.WordTrace tailWord_3437614 prefixEnd_3437614 1765148286625018553115707 := by
  unfold tailWord_3437614
  simp only [CollatzResearch.WordTrace]
  refine ⟨15672510371014881321883987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83586721978746033716714597 15672510371014881321883987)
  ·
    refine ⟨23508765556522321982825981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15672510371014881321883987 23508765556522321982825981)
    ·
      refine ⟨8815787083695870743559743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23508765556522321982825981 8815787083695870743559743)
      ·
        refine ⟨13223680625543806115339615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8815787083695870743559743 13223680625543806115339615)
        ·
          refine ⟨19835520938315709173009423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13223680625543806115339615 19835520938315709173009423)
          ·
            refine ⟨29753281407473563759514135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19835520938315709173009423 29753281407473563759514135)
            ·
              refine ⟨44629922111210345639271203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29753281407473563759514135 44629922111210345639271203)
              ·
                refine ⟨66944883166815518458906805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44629922111210345639271203 66944883166815518458906805)
                ·
                  refine ⟨6276082796888954855522513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66944883166815518458906805 6276082796888954855522513)
                  ·
                    refine ⟨4707062097666716141641885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6276082796888954855522513 4707062097666716141641885)
                    ·
                      refine ⟨1765148286625018553115707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4707062097666716141641885 1765148286625018553115707)
                      ·
                        rfl

theorem cell23_3437614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_3437614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437614 prefixEnd_3437614 := by exact prefixLift 3437614
  have htrace : WordTrace (prefixWord ++ tailWord_3437614) baseStart_3437614 baseEnd_3437614 := by
    simpa [prefixWord, tailWord_3437614, baseEnd_3437614] using wordTrace_append hprefix tailTrace_3437614
  have hstable : (prefixWord ++ tailWord_3437614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437614).length < 2 ^ (prefixWord ++ tailWord_3437614).sum := by decide
  have hdescent : baseEnd_3437614 < baseStart_3437614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437624 : List Nat := [2, 1, 2, 1, 5, 2, 2, 1, 1, 2, 4]
def baseStart_3437624 : Nat := 118140960795 + 3437624 * 2 ^ 59
def prefixEnd_3437624 : Nat := 4983230072969 + 3 ^ 40 * 3437624 * 2
def baseEnd_3437624 : Nat := 1765153421431563513990661

theorem tailTrace_3437624 : CollatzResearch.WordTrace tailWord_3437624 prefixEnd_3437624 1765153421431563513990661 := by
  unfold tailWord_3437624
  simp only [CollatzResearch.WordTrace]
  refine ⟨62690223849041411141467963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83586965132055214855290617 62690223849041411141467963)
  ·
    refine ⟨94035335773562116712201945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62690223849041411141467963 94035335773562116712201945)
    ·
      refine ⟨70526501830171587534151459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94035335773562116712201945 70526501830171587534151459)
      ·
        refine ⟨105789752745257381301227189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70526501830171587534151459 105789752745257381301227189)
        ·
          refine ⟨9917789319867879496990049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105789752745257381301227189 9917789319867879496990049)
          ·
            refine ⟨7438341989900909622742537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9917789319867879496990049 7438341989900909622742537)
            ·
              refine ⟨5578756492425682217056903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7438341989900909622742537 5578756492425682217056903)
              ·
                refine ⟨8368134738638523325585355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5578756492425682217056903 8368134738638523325585355)
                ·
                  refine ⟨12552202107957784988378033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8368134738638523325585355 12552202107957784988378033)
                  ·
                    refine ⟨9414151580968338741283525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12552202107957784988378033 9414151580968338741283525)
                    ·
                      refine ⟨1765153421431563513990661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9414151580968338741283525 1765153421431563513990661)
                      ·
                        rfl

theorem cell23_3437624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_3437624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437624 prefixEnd_3437624 := by exact prefixLift 3437624
  have htrace : WordTrace (prefixWord ++ tailWord_3437624) baseStart_3437624 baseEnd_3437624 := by
    simpa [prefixWord, tailWord_3437624, baseEnd_3437624] using wordTrace_append hprefix tailTrace_3437624
  have hstable : (prefixWord ++ tailWord_3437624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437624).length < 2 ^ (prefixWord ++ tailWord_3437624).sum := by decide
  have hdescent : baseEnd_3437624 < baseStart_3437624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437644 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 4, 1, 3]
def baseStart_3437644 : Nat := 118140960795 + 3437644 * 2 ^ 59
def prefixEnd_3437644 : Nat := 4983230072969 + 3 ^ 40 * 3437644 * 2
def baseEnd_3437644 : Nat := 1765163691044653435740569

theorem tailTrace_3437644 : CollatzResearch.WordTrace tailWord_3437644 prefixEnd_3437644 1765163691044653435740569 := by
  unfold tailWord_3437644
  simp only [CollatzResearch.WordTrace]
  refine ⟨62690588579005182849331993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83587451438673577132442657 62690588579005182849331993)
  ·
    refine ⟨47017941434253887136998995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62690588579005182849331993 47017941434253887136998995)
    ·
      refine ⟨70526912151380830705498493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47017941434253887136998995 70526912151380830705498493)
      ·
        refine ⟨26447592056767811514561935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70526912151380830705498493 26447592056767811514561935)
        ·
          refine ⟨39671388085151717271842903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26447592056767811514561935 39671388085151717271842903)
          ·
            refine ⟨59507082127727575907764355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39671388085151717271842903 59507082127727575907764355)
            ·
              refine ⟨89260623191591363861646533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59507082127727575907764355 89260623191591363861646533)
              ·
                refine ⟨16736366848423380724058725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89260623191591363861646533 16736366848423380724058725)
                ·
                  refine ⟨3138068784079383885761011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16736366848423380724058725 3138068784079383885761011)
                  ·
                    refine ⟨4707103176119075828641517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3138068784079383885761011 4707103176119075828641517)
                    ·
                      refine ⟨1765163691044653435740569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4707103176119075828641517 1765163691044653435740569)
                      ·
                        rfl

theorem cell23_3437644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_3437644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437644 prefixEnd_3437644 := by exact prefixLift 3437644
  have htrace : WordTrace (prefixWord ++ tailWord_3437644) baseStart_3437644 baseEnd_3437644 := by
    simpa [prefixWord, tailWord_3437644, baseEnd_3437644] using wordTrace_append hprefix tailTrace_3437644
  have hstable : (prefixWord ++ tailWord_3437644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437644).length < 2 ^ (prefixWord ++ tailWord_3437644).sum := by decide
  have hdescent : baseEnd_3437644 < baseStart_3437644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437645 : List Nat := [1, 6, 1, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_3437645 : Nat := 118140960795 + 3437645 * 2 ^ 59
def prefixEnd_3437645 : Nat := 4983230072969 + 3 ^ 40 * 3437645 * 2
def baseEnd_3437645 : Nat := 1765164204525307931828065

theorem tailTrace_3437645 : CollatzResearch.WordTrace tailWord_3437645 prefixEnd_3437645 1765164204525307931828065 := by
  unfold tailWord_3437645
  simp only [CollatzResearch.WordTrace]
  refine ⟨125381213631006742869450389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83587475754004495246300259 125381213631006742869450389)
  ·
    refine ⟨5877244388953441072005487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 125381213631006742869450389 5877244388953441072005487)
    ·
      refine ⟨8815866583430161608008231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5877244388953441072005487 8815866583430161608008231)
      ·
        refine ⟨13223799875145242412012347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8815866583430161608008231 13223799875145242412012347)
        ·
          refine ⟨19835699812717863618018521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13223799875145242412012347 19835699812717863618018521)
          ·
            refine ⟨14876774859538397713513891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19835699812717863618018521 14876774859538397713513891)
            ·
              refine ⟨22315162289307596570270837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14876774859538397713513891 22315162289307596570270837)
              ·
                refine ⟨2092046464622587178462891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22315162289307596570270837 2092046464622587178462891)
                ·
                  refine ⟨3138069696933880767694337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2092046464622587178462891 3138069696933880767694337)
                  ·
                    refine ⟨2353552272700410575770753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3138069696933880767694337 2353552272700410575770753)
                    ·
                      refine ⟨1765164204525307931828065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2353552272700410575770753 1765164204525307931828065)
                      ·
                        rfl

theorem cell23_3437645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_3437645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437645 prefixEnd_3437645 := by exact prefixLift 3437645
  have htrace : WordTrace (prefixWord ++ tailWord_3437645) baseStart_3437645 baseEnd_3437645 := by
    simpa [prefixWord, tailWord_3437645, baseEnd_3437645] using wordTrace_append hprefix tailTrace_3437645
  have hstable : (prefixWord ++ tailWord_3437645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437645).length < 2 ^ (prefixWord ++ tailWord_3437645).sum := by decide
  have hdescent : baseEnd_3437645 < baseStart_3437645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437662 : List Nat := [4, 4, 1, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_3437662 : Nat := 118140960795 + 3437662 * 2 ^ 59
def prefixEnd_3437662 : Nat := 4983230072969 + 3 ^ 40 * 3437662 * 2
def baseEnd_3437662 : Nat := 1765172933696434365315487

theorem tailTrace_3437662 : CollatzResearch.WordTrace tailWord_3437662 prefixEnd_3437662 1765172933696434365315487 := by
  unfold tailWord_3437662
  simp only [CollatzResearch.WordTrace]
  refine ⟨15672729208993144346602405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83587889114630103181879493 15672729208993144346602405)
  ·
    refine ⟨2938636726686214564987951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15672729208993144346602405 2938636726686214564987951)
    ·
      refine ⟨4407955090029321847481927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2938636726686214564987951 4407955090029321847481927)
      ·
        refine ⟨6611932635043982771222891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4407955090029321847481927 6611932635043982771222891)
        ·
          refine ⟨9917898952565974156834337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6611932635043982771222891 9917898952565974156834337)
          ·
            refine ⟨7438424214424480617625753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9917898952565974156834337 7438424214424480617625753)
            ·
              refine ⟨5578818160818360463219315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7438424214424480617625753 5578818160818360463219315)
              ·
                refine ⟨8368227241227540694828973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5578818160818360463219315 8368227241227540694828973)
                ·
                  refine ⟨3138085215460327760560865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8368227241227540694828973 3138085215460327760560865)
                  ·
                    refine ⟨2353563911595245820420649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3138085215460327760560865 2353563911595245820420649)
                    ·
                      refine ⟨1765172933696434365315487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2353563911595245820420649 1765172933696434365315487)
                      ·
                        rfl

theorem cell23_3437662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_3437662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437662 prefixEnd_3437662 := by exact prefixLift 3437662
  have htrace : WordTrace (prefixWord ++ tailWord_3437662) baseStart_3437662 baseEnd_3437662 := by
    simpa [prefixWord, tailWord_3437662, baseEnd_3437662] using wordTrace_append hprefix tailTrace_3437662
  have hstable : (prefixWord ++ tailWord_3437662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437662).length < 2 ^ (prefixWord ++ tailWord_3437662).sum := by decide
  have hdescent : baseEnd_3437662 < baseStart_3437662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437687 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 5]
def baseStart_3437687 : Nat := 118140960795 + 3437687 * 2 ^ 59
def prefixEnd_3437687 : Nat := 4983230072969 + 3 ^ 40 * 3437687 * 2
def baseEnd_3437687 : Nat := 1765185770712796767502871

theorem tailTrace_3437687 : CollatzResearch.WordTrace tailWord_3437687 prefixEnd_3437687 1765185770712796767502871 := by
  unfold tailWord_3437687
  simp only [CollatzResearch.WordTrace]
  refine ⟨125382745496854584042479315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83588496997903056028319543 125382745496854584042479315)
  ·
    refine ⟨188074118245281876063718973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125382745496854584042479315 188074118245281876063718973)
    ·
      refine ⟨70527794341980703523894615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188074118245281876063718973 70527794341980703523894615)
      ·
        refine ⟨105791691512971055285841923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70527794341980703523894615 105791691512971055285841923)
        ·
          refine ⟨158687537269456582928762885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105791691512971055285841923 158687537269456582928762885)
          ·
            refine ⟨29753913238023109299143041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158687537269456582928762885 29753913238023109299143041)
            ·
              refine ⟨22315434928517331974357281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29753913238023109299143041 22315434928517331974357281)
              ·
                refine ⟨16736576196387998980767961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22315434928517331974357281 16736576196387998980767961)
                ·
                  refine ⟨12552432147290999235575971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16736576196387998980767961 12552432147290999235575971)
                  ·
                    refine ⟨18828648220936498853363957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12552432147290999235575971 18828648220936498853363957)
                    ·
                      refine ⟨1765185770712796767502871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18828648220936498853363957 1765185770712796767502871)
                      ·
                        rfl

theorem cell23_3437687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_3437687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437687 prefixEnd_3437687 := by exact prefixLift 3437687
  have htrace : WordTrace (prefixWord ++ tailWord_3437687) baseStart_3437687 baseEnd_3437687 := by
    simpa [prefixWord, tailWord_3437687, baseEnd_3437687] using wordTrace_append hprefix tailTrace_3437687
  have hstable : (prefixWord ++ tailWord_3437687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437687).length < 2 ^ (prefixWord ++ tailWord_3437687).sum := by decide
  have hdescent : baseEnd_3437687 < baseStart_3437687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437724 : List Nat := [2, 2, 3, 2, 1, 2, 3, 1, 7]
def baseStart_3437724 : Nat := 118140960795 + 3437724 * 2 ^ 59
def prefixEnd_3437724 : Nat := 4983230072969 + 3 ^ 40 * 3437724 * 2
def baseEnd_3437724 : Nat := 196133863277445902526689

theorem tailTrace_3437724 : CollatzResearch.WordTrace tailWord_3437724 prefixEnd_3437724 196133863277445902526689 := by
  unfold tailWord_3437724
  simp only [CollatzResearch.WordTrace]
  refine ⟨62692047498860269680788113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83589396665147026241050817 62692047498860269680788113)
  ·
    refine ⟨47019035624145202260591085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62692047498860269680788113 47019035624145202260591085)
    ·
      refine ⟨17632138359054450847721657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47019035624145202260591085 17632138359054450847721657)
      ·
        refine ⟨13224103769290838135791243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17632138359054450847721657 13224103769290838135791243)
        ·
          refine ⟨19836155653936257203686865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13224103769290838135791243 19836155653936257203686865)
          ·
            refine ⟨14877116740452192902765149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19836155653936257203686865 14877116740452192902765149)
            ·
              refine ⟨5578918777669572338536931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14877116740452192902765149 5578918777669572338536931)
              ·
                refine ⟨8368378166504358507805397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5578918777669572338536931 8368378166504358507805397)
                ·
                  refine ⟨196133863277445902526689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8368378166504358507805397 196133863277445902526689)
                  ·
                    rfl

theorem cell23_3437724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 7].length) (baseStart_3437724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437724 prefixEnd_3437724 := by exact prefixLift 3437724
  have htrace : WordTrace (prefixWord ++ tailWord_3437724) baseStart_3437724 baseEnd_3437724 := by
    simpa [prefixWord, tailWord_3437724, baseEnd_3437724] using wordTrace_append hprefix tailTrace_3437724
  have hstable : (prefixWord ++ tailWord_3437724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437724).length < 2 ^ (prefixWord ++ tailWord_3437724).sum := by decide
  have hdescent : baseEnd_3437724 < baseStart_3437724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437735 : List Nat := [1, 1, 6, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_3437735 : Nat := 118140960795 + 3437735 * 2 ^ 59
def prefixEnd_3437735 : Nat := 4983230072969 + 3 ^ 40 * 3437735 * 2
def baseEnd_3437735 : Nat := 1765210417784212579702651

theorem tailTrace_3437735 : CollatzResearch.WordTrace tailWord_3437735 prefixEnd_3437735 1765210417784212579702651 := by
  unfold tailWord_3437735
  simp only [CollatzResearch.WordTrace]
  refine ⟨125384496200680688240226659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83589664133787125493484439 125384496200680688240226659)
  ·
    refine ⟨188076744301021032360339989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125384496200680688240226659 188076744301021032360339989)
    ·
      refine ⟨8816097389110360891890937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 188076744301021032360339989 8816097389110360891890937)
      ·
        refine ⟨6612073041832770668918203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8816097389110360891890937 6612073041832770668918203)
        ·
          refine ⟨9918109562749156003377305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6612073041832770668918203 9918109562749156003377305)
          ·
            refine ⟨7438582172061867002532979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9918109562749156003377305 7438582172061867002532979)
            ·
              refine ⟨11157873258092800503799469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7438582172061867002532979 11157873258092800503799469)
              ·
                refine ⟨4184202471784800188924801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11157873258092800503799469 4184202471784800188924801)
                ·
                  refine ⟨3138151853838600141693601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4184202471784800188924801 3138151853838600141693601)
                  ·
                    refine ⟨2353613890378950106270201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3138151853838600141693601 2353613890378950106270201)
                    ·
                      refine ⟨1765210417784212579702651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2353613890378950106270201 1765210417784212579702651)
                      ·
                        rfl

theorem cell23_3437735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_3437735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437735 prefixEnd_3437735 := by exact prefixLift 3437735
  have htrace : WordTrace (prefixWord ++ tailWord_3437735) baseStart_3437735 baseEnd_3437735 := by
    simpa [prefixWord, tailWord_3437735, baseEnd_3437735] using wordTrace_append hprefix tailTrace_3437735
  have hstable : (prefixWord ++ tailWord_3437735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437735).length < 2 ^ (prefixWord ++ tailWord_3437735).sum := by decide
  have hdescent : baseEnd_3437735 < baseStart_3437735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437744 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 2, 5, 2]
def baseStart_3437744 : Nat := 118140960795 + 3437744 * 2 ^ 59
def prefixEnd_3437744 : Nat := 4983230072969 + 3 ^ 40 * 3437744 * 2
def baseEnd_3437744 : Nat := 1765215039110103044490109

theorem tailTrace_3437744 : CollatzResearch.WordTrace tailWord_3437744 prefixEnd_3437744 1765215039110103044490109 := by
  unfold tailWord_3437744
  simp only [CollatzResearch.WordTrace]
  refine ⟨62692412228824041388652143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83589882971765388518202857 62692412228824041388652143)
  ·
    refine ⟨94038618343236062082978215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62692412228824041388652143 94038618343236062082978215)
    ·
      refine ⟨141057927514854093124467323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94038618343236062082978215 141057927514854093124467323)
      ·
        refine ⟨211586891272281139686700985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141057927514854093124467323 211586891272281139686700985)
        ·
          refine ⟨158690168454210854765025739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211586891272281139686700985 158690168454210854765025739)
          ·
            refine ⟨238035252681316282147538609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158690168454210854765025739 238035252681316282147538609)
            ·
              refine ⟨178526439510987211610653957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238035252681316282147538609 178526439510987211610653957)
              ·
                refine ⟨33473707408310102176997617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178526439510987211610653957 33473707408310102176997617)
                ·
                  refine ⟨25105280556232576632748213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33473707408310102176997617 25105280556232576632748213)
                  ·
                    refine ⟨2353620052146804059320145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25105280556232576632748213 2353620052146804059320145)
                    ·
                      refine ⟨1765215039110103044490109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2353620052146804059320145 1765215039110103044490109)
                      ·
                        rfl

theorem cell23_3437744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 2, 5, 2].length) (baseStart_3437744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437744 prefixEnd_3437744 := by exact prefixLift 3437744
  have htrace : WordTrace (prefixWord ++ tailWord_3437744) baseStart_3437744 baseEnd_3437744 := by
    simpa [prefixWord, tailWord_3437744, baseEnd_3437744] using wordTrace_append hprefix tailTrace_3437744
  have hstable : (prefixWord ++ tailWord_3437744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437744).length < 2 ^ (prefixWord ++ tailWord_3437744).sum := by decide
  have hdescent : baseEnd_3437744 < baseStart_3437744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437777 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 1, 5, 5]
def baseStart_3437777 : Nat := 118140960795 + 3437777 * 2 ^ 59
def prefixEnd_3437777 : Nat := 4983230072969 + 3 ^ 40 * 3437777 * 2
def baseEnd_3437777 : Nat := 1765231983971701415377457

theorem tailTrace_3437777 : CollatzResearch.WordTrace tailWord_3437777 prefixEnd_3437777 1765231983971701415377457 := by
  unfold tailWord_3437777
  simp only [CollatzResearch.WordTrace]
  refine ⟨125386028066528529413255585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83590685377685686275503723 125386028066528529413255585)
  ·
    refine ⟨94039521049896397059941689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125386028066528529413255585 94039521049896397059941689)
    ·
      refine ⟨70529640787422297794956267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94039521049896397059941689 70529640787422297794956267)
      ·
        refine ⟨105794461181133446692434401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70529640787422297794956267 105794461181133446692434401)
        ·
          refine ⟨79345845885850085019325801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105794461181133446692434401 79345845885850085019325801)
          ·
            refine ⟨59509384414387563764494351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79345845885850085019325801 59509384414387563764494351)
            ·
              refine ⟨89264076621581345646741527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59509384414387563764494351 89264076621581345646741527)
              ·
                refine ⟨133896114932372018470112291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89264076621581345646741527 133896114932372018470112291)
                ·
                  refine ⟨200844172398558027705168437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133896114932372018470112291 200844172398558027705168437)
                  ·
                    refine ⟨18829141162364815097359541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 200844172398558027705168437 18829141162364815097359541)
                    ·
                      refine ⟨1765231983971701415377457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18829141162364815097359541 1765231983971701415377457)
                      ·
                        rfl

theorem cell23_3437777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_3437777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437777 prefixEnd_3437777 := by exact prefixLift 3437777
  have htrace : WordTrace (prefixWord ++ tailWord_3437777) baseStart_3437777 baseEnd_3437777 := by
    simpa [prefixWord, tailWord_3437777, baseEnd_3437777] using wordTrace_append hprefix tailTrace_3437777
  have hstable : (prefixWord ++ tailWord_3437777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437777).length < 2 ^ (prefixWord ++ tailWord_3437777).sum := by decide
  have hdescent : baseEnd_3437777 < baseStart_3437777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437811 : List Nat := [1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 3]
def baseStart_3437811 : Nat := 118140960795 + 3437811 * 2 ^ 59
def prefixEnd_3437811 : Nat := 4983230072969 + 3 ^ 40 * 3437811 * 2
def baseEnd_3437811 : Nat := 1765249442313954282352301

theorem tailTrace_3437811 : CollatzResearch.WordTrace tailWord_3437811 prefixEnd_3437811 1765249442313954282352301 := by
  unfold tailWord_3437811
  simp only [CollatzResearch.WordTrace]
  refine ⟨125387268148405353219993287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83591512098936902146662191 125387268148405353219993287)
  ·
    refine ⟨188080902222608029829989931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125387268148405353219993287 188080902222608029829989931)
    ·
      refine ⟨282121353333912044744984897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188080902222608029829989931 282121353333912044744984897)
      ·
        refine ⟨211591015000434033558738673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282121353333912044744984897 211591015000434033558738673)
        ·
          refine ⟨158693261250325525169054005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211591015000434033558738673 158693261250325525169054005)
          ·
            refine ⟨14877493242218017984598813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158693261250325525169054005 14877493242218017984598813)
            ·
              refine ⟨5579059965831756744224555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14877493242218017984598813 5579059965831756744224555)
              ·
                refine ⟨8368589948747635116336833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5579059965831756744224555 8368589948747635116336833)
                ·
                  refine ⟨6276442461560726337252625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8368589948747635116336833 6276442461560726337252625)
                  ·
                    refine ⟨4707331846170544752939469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6276442461560726337252625 4707331846170544752939469)
                    ·
                      refine ⟨1765249442313954282352301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4707331846170544752939469 1765249442313954282352301)
                      ·
                        rfl

theorem cell23_3437811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 3].length) (baseStart_3437811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437811 prefixEnd_3437811 := by exact prefixLift 3437811
  have htrace : WordTrace (prefixWord ++ tailWord_3437811) baseStart_3437811 baseEnd_3437811 := by
    simpa [prefixWord, tailWord_3437811, baseEnd_3437811] using wordTrace_append hprefix tailTrace_3437811
  have hstable : (prefixWord ++ tailWord_3437811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437811).length < 2 ^ (prefixWord ++ tailWord_3437811).sum := by decide
  have hdescent : baseEnd_3437811 < baseStart_3437811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437814 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 8]
def baseStart_3437814 : Nat := 118140960795 + 3437814 * 2 ^ 59
def prefixEnd_3437814 : Nat := 4983230072969 + 3 ^ 40 * 3437814 * 2
def baseEnd_3437814 : Nat := 196138998083990863401643

theorem tailTrace_3437814 : CollatzResearch.WordTrace tailWord_3437814 prefixEnd_3437814 196138998083990863401643 := by
  unfold tailWord_3437814
  simp only [CollatzResearch.WordTrace]
  refine ⟨7836711097962155295772031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83591585044929656488234997 7836711097962155295772031)
  ·
    refine ⟨11755066646943232943658047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7836711097962155295772031 11755066646943232943658047)
    ·
      refine ⟨17632599970414849415487071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11755066646943232943658047 17632599970414849415487071)
      ·
        refine ⟨26448899955622274123230607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17632599970414849415487071 26448899955622274123230607)
        ·
          refine ⟨39673349933433411184845911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26448899955622274123230607 39673349933433411184845911)
          ·
            refine ⟨59510024900150116777268867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39673349933433411184845911 59510024900150116777268867)
            ·
              refine ⟨89265037350225175165903301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59510024900150116777268867 89265037350225175165903301)
              ·
                refine ⟨16737194503167220343606869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89265037350225175165903301 16737194503167220343606869)
                ·
                  refine ⟨196138998083990863401643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16737194503167220343606869 196138998083990863401643)
                  ·
                    rfl

theorem cell23_3437814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_3437814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437814 prefixEnd_3437814 := by exact prefixLift 3437814
  have htrace : WordTrace (prefixWord ++ tailWord_3437814) baseStart_3437814 baseEnd_3437814 := by
    simpa [prefixWord, tailWord_3437814, baseEnd_3437814] using wordTrace_append hprefix tailTrace_3437814
  have hstable : (prefixWord ++ tailWord_3437814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437814).length < 2 ^ (prefixWord ++ tailWord_3437814).sum := by decide
  have hdescent : baseEnd_3437814 < baseStart_3437814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437818 : List Nat := [3, 1, 1, 1, 1, 4, 4, 3, 1, 4]
def baseStart_3437818 : Nat := 118140960795 + 3437818 * 2 ^ 59
def prefixEnd_3437818 : Nat := 4983230072969 + 3 ^ 40 * 3437818 * 2
def baseEnd_3437818 : Nat := 588417678892845251654923

theorem tailTrace_3437818 : CollatzResearch.WordTrace tailWord_3437818 prefixEnd_3437818 588417678892845251654923 := by
  unfold tailWord_3437818
  simp only [CollatzResearch.WordTrace]
  refine ⟨31346880864844998353874527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83591682306253328943665405 31346880864844998353874527)
  ·
    refine ⟨47020321297267497530811791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31346880864844998353874527 47020321297267497530811791)
    ·
      refine ⟨70530481945901246296217687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47020321297267497530811791 70530481945901246296217687)
      ·
        refine ⟨105795722918851869444326531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70530481945901246296217687 105795722918851869444326531)
        ·
          refine ⟨158693584378277804166489797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105795722918851869444326531 158693584378277804166489797)
          ·
            refine ⟨29755047070927088281216837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158693584378277804166489797 29755047070927088281216837)
            ·
              refine ⟨5579071325798829052728157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29755047070927088281216837 5579071325798829052728157)
              ·
                refine ⟨2092151747174560894773059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5579071325798829052728157 2092151747174560894773059)
                ·
                  refine ⟨3138227620761841342159589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2092151747174560894773059 3138227620761841342159589)
                  ·
                    refine ⟨588417678892845251654923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3138227620761841342159589 588417678892845251654923)
                    ·
                      rfl

theorem cell23_3437818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 1, 4].length) (baseStart_3437818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437818 prefixEnd_3437818 := by exact prefixLift 3437818
  have htrace : WordTrace (prefixWord ++ tailWord_3437818) baseStart_3437818 baseEnd_3437818 := by
    simpa [prefixWord, tailWord_3437818, baseEnd_3437818] using wordTrace_append hprefix tailTrace_3437818
  have hstable : (prefixWord ++ tailWord_3437818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437818).length < 2 ^ (prefixWord ++ tailWord_3437818).sum := by decide
  have hdescent : baseEnd_3437818 < baseStart_3437818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437861 : List Nat := [1, 3, 1, 2, 4, 1, 1, 4, 1, 5]
def baseStart_3437861 : Nat := 118140960795 + 3437861 * 2 ^ 59
def prefixEnd_3437861 : Nat := 4983230072969 + 3 ^ 40 * 3437861 * 2
def baseEnd_3437861 : Nat := 588425038782226362242357

theorem tailTrace_3437861 : CollatzResearch.WordTrace tailWord_3437861 prefixEnd_3437861 588425038782226362242357 := by
  unfold tailWord_3437861
  simp only [CollatzResearch.WordTrace]
  refine ⟨125389091798224211759313437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83592727865482807839542291 125389091798224211759313437)
  ·
    refine ⟨47020909424334079409742539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125389091798224211759313437 47020909424334079409742539)
    ·
      refine ⟨70531364136501119114613809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47020909424334079409742539 70531364136501119114613809)
      ·
        refine ⟨52898523102375839335960357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70531364136501119114613809 52898523102375839335960357)
        ·
          refine ⟨9918473081695469875492567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52898523102375839335960357 9918473081695469875492567)
          ·
            refine ⟨14877709622543204813238851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9918473081695469875492567 14877709622543204813238851)
            ·
              refine ⟨22316564433814807219858277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14877709622543204813238851 22316564433814807219858277)
              ·
                refine ⟨4184355831340276353723427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22316564433814807219858277 4184355831340276353723427)
                ·
                  refine ⟨6276533747010414530585141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4184355831340276353723427 6276533747010414530585141)
                  ·
                    refine ⟨588425038782226362242357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6276533747010414530585141 588425038782226362242357)
                    ·
                      rfl

theorem cell23_3437861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_3437861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437861 prefixEnd_3437861 := by exact prefixLift 3437861
  have htrace : WordTrace (prefixWord ++ tailWord_3437861) baseStart_3437861 baseEnd_3437861 := by
    simpa [prefixWord, tailWord_3437861, baseEnd_3437861] using wordTrace_append hprefix tailTrace_3437861
  have hstable : (prefixWord ++ tailWord_3437861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437861).length < 2 ^ (prefixWord ++ tailWord_3437861).sum := by decide
  have hdescent : baseEnd_3437861 < baseStart_3437861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437875 : List Nat := [1, 1, 1, 2, 5, 2, 3, 3, 1, 1, 3]
def baseStart_3437875 : Nat := 118140960795 + 3437875 * 2 ^ 59
def prefixEnd_3437875 : Nat := 4983230072969 + 3 ^ 40 * 3437875 * 2
def baseEnd_3437875 : Nat := 1765282305075842031952007

theorem tailTrace_3437875 : CollatzResearch.WordTrace tailWord_3437875 prefixEnd_3437875 1765282305075842031952007 := by
  unfold tailWord_3437875
  simp only [CollatzResearch.WordTrace]
  refine ⟨125389602420173492150323079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83593068280115661433548719 125389602420173492150323079)
  ·
    refine ⟨188084403630260238225484619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125389602420173492150323079 188084403630260238225484619)
    ·
      refine ⟨282126605445390357338226929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188084403630260238225484619 282126605445390357338226929)
      ·
        refine ⟨211594954084042768003670197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282126605445390357338226929 211594954084042768003670197)
        ·
          refine ⟨19837026945379009500344081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 211594954084042768003670197 19837026945379009500344081)
          ·
            refine ⟨14877770209034257125258061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19837026945379009500344081 14877770209034257125258061)
            ·
              refine ⟨5579163828387846421971773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14877770209034257125258061 5579163828387846421971773)
              ·
                refine ⟨2092186435645442408239415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5579163828387846421971773 2092186435645442408239415)
                ·
                  refine ⟨3138279653468163612359123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2092186435645442408239415 3138279653468163612359123)
                  ·
                    refine ⟨4707419480202245418538685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3138279653468163612359123 4707419480202245418538685)
                    ·
                      refine ⟨1765282305075842031952007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4707419480202245418538685 1765282305075842031952007)
                      ·
                        rfl

theorem cell23_3437875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 1, 1, 3].length) (baseStart_3437875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437875 prefixEnd_3437875 := by exact prefixLift 3437875
  have htrace : WordTrace (prefixWord ++ tailWord_3437875) baseStart_3437875 baseEnd_3437875 := by
    simpa [prefixWord, tailWord_3437875, baseEnd_3437875] using wordTrace_append hprefix tailTrace_3437875
  have hstable : (prefixWord ++ tailWord_3437875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437875).length < 2 ^ (prefixWord ++ tailWord_3437875).sum := by decide
  have hdescent : baseEnd_3437875 < baseStart_3437875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437891 : List Nat := [1, 1, 1, 3, 1, 3, 1, 6, 2, 4]
def baseStart_3437891 : Nat := 118140960795 + 3437891 * 2 ^ 59
def prefixEnd_3437891 : Nat := 4983230072969 + 3 ^ 40 * 3437891 * 2
def baseEnd_3437891 : Nat := 588430173588771323117311

theorem tailTrace_3437891 : CollatzResearch.WordTrace tailWord_3437891 prefixEnd_3437891 588430173588771323117311 := by
  unfold tailWord_3437891
  simp only [CollatzResearch.WordTrace]
  refine ⟨125390185988115526882905527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83593457325410351255270351 125390185988115526882905527)
  ·
    refine ⟨188085278982173290324358291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125390185988115526882905527 188085278982173290324358291)
    ·
      refine ⟨282127918473259935486537437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188085278982173290324358291 282127918473259935486537437)
      ·
        refine ⟨105797969427472475807451539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282127918473259935486537437 105797969427472475807451539)
        ·
          refine ⟨158696954141208713711177309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105797969427472475807451539 158696954141208713711177309)
          ·
            refine ⟨59511357802953267641691491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158696954141208713711177309 59511357802953267641691491)
            ·
              refine ⟨89267036704429901462537237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59511357802953267641691491 89267036704429901462537237)
              ·
                refine ⟨4184392345520151631056433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89267036704429901462537237 4184392345520151631056433)
                ·
                  refine ⟨3138294259140113723292325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4184392345520151631056433 3138294259140113723292325)
                  ·
                    refine ⟨588430173588771323117311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3138294259140113723292325 588430173588771323117311)
                    ·
                      rfl

theorem cell23_3437891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 4].length) (baseStart_3437891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437891 prefixEnd_3437891 := by exact prefixLift 3437891
  have htrace : WordTrace (prefixWord ++ tailWord_3437891) baseStart_3437891 baseEnd_3437891 := by
    simpa [prefixWord, tailWord_3437891, baseEnd_3437891] using wordTrace_append hprefix tailTrace_3437891
  have hstable : (prefixWord ++ tailWord_3437891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437891).length < 2 ^ (prefixWord ++ tailWord_3437891).sum := by decide
  have hdescent : baseEnd_3437891 < baseStart_3437891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437892 : List Nat := [2, 3, 4, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_3437892 : Nat := 118140960795 + 3437892 * 2 ^ 59
def prefixEnd_3437892 : Nat := 4983230072969 + 3 ^ 40 * 3437892 * 2
def baseEnd_3437892 : Nat := 1765291034246968465439429

theorem tailTrace_3437892 : CollatzResearch.WordTrace tailWord_3437892 prefixEnd_3437892 1765291034246968465439429 := by
  unfold tailWord_3437892
  simp only [CollatzResearch.WordTrace]
  refine ⟨62695111230555952026845965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83593481640741269369127953 62695111230555952026845965)
  ·
    refine ⟨23510666711458482010067237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62695111230555952026845965 23510666711458482010067237)
    ·
      refine ⟨4408250008398465376887607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23510666711458482010067237 4408250008398465376887607)
      ·
        refine ⟨6612375012597698065331411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4408250008398465376887607 6612375012597698065331411)
        ·
          refine ⟨9918562518896547097997117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6612375012597698065331411 9918562518896547097997117)
          ·
            refine ⟨3719460944586205161748919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9918562518896547097997117 3719460944586205161748919)
            ·
              refine ⟨5579191416879307742623379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3719460944586205161748919 5579191416879307742623379)
              ·
                refine ⟨8368787125318961613935069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5579191416879307742623379 8368787125318961613935069)
                ·
                  refine ⟨3138295171994610605225651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8368787125318961613935069 3138295171994610605225651)
                  ·
                    refine ⟨4707442757991915907838477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3138295171994610605225651 4707442757991915907838477)
                    ·
                      refine ⟨1765291034246968465439429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4707442757991915907838477 1765291034246968465439429)
                      ·
                        rfl

theorem cell23_3437892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_3437892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437892 prefixEnd_3437892 := by exact prefixLift 3437892
  have htrace : WordTrace (prefixWord ++ tailWord_3437892) baseStart_3437892 baseEnd_3437892 := by
    simpa [prefixWord, tailWord_3437892, baseEnd_3437892] using wordTrace_append hprefix tailTrace_3437892
  have hstable : (prefixWord ++ tailWord_3437892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437892).length < 2 ^ (prefixWord ++ tailWord_3437892).sum := by decide
  have hdescent : baseEnd_3437892 < baseStart_3437892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437904 : List Nat := [2, 1, 1, 1, 1, 5, 4, 8]
def baseStart_3437904 : Nat := 118140960795 + 3437904 * 2 ^ 59
def prefixEnd_3437904 : Nat := 4983230072969 + 3 ^ 40 * 3437904 * 2
def baseEnd_3437904 : Nat := 65381377630178608092199

theorem tailTrace_3437904 : CollatzResearch.WordTrace tailWord_3437904 prefixEnd_3437904 65381377630178608092199 := by
  unfold tailWord_3437904
  simp only [CollatzResearch.WordTrace]
  refine ⟨62695330068534215051564383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83593773424712286735419177 62695330068534215051564383)
  ·
    refine ⟨94042995102801322577346575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62695330068534215051564383 94042995102801322577346575)
    ·
      refine ⟨141064492654201983866019863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94042995102801322577346575 141064492654201983866019863)
      ·
        refine ⟨211596738981302975799029795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141064492654201983866019863 211596738981302975799029795)
        ·
          refine ⟨317395108471954463698544693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211596738981302975799029795 317395108471954463698544693)
          ·
            refine ⟨29755791419245730971738565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 317395108471954463698544693 29755791419245730971738565)
            ·
              refine ⟨5579210891108574557200981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29755791419245730971738565 5579210891108574557200981)
              ·
                refine ⟨65381377630178608092199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5579210891108574557200981 65381377630178608092199)
                ·
                  rfl

theorem cell23_3437904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 8].length) (baseStart_3437904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437904 prefixEnd_3437904 := by exact prefixLift 3437904
  have htrace : WordTrace (prefixWord ++ tailWord_3437904) baseStart_3437904 baseEnd_3437904 := by
    simpa [prefixWord, tailWord_3437904, baseEnd_3437904] using wordTrace_append hprefix tailTrace_3437904
  have hstable : (prefixWord ++ tailWord_3437904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437904).length < 2 ^ (prefixWord ++ tailWord_3437904).sum := by decide
  have hdescent : baseEnd_3437904 < baseStart_3437904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437908 : List Nat := [2, 4, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_3437908 : Nat := 118140960795 + 3437908 * 2 ^ 59
def prefixEnd_3437908 : Nat := 4983230072969 + 3 ^ 40 * 3437908 * 2
def baseEnd_3437908 : Nat := 588433083312480134279785

theorem tailTrace_3437908 : CollatzResearch.WordTrace tailWord_3437908 prefixEnd_3437908 588433083312480134279785 := by
  unfold tailWord_3437908
  simp only [CollatzResearch.WordTrace]
  refine ⟨62695403014526969393137189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83593870686035959190849585 62695403014526969393137189)
  ·
    refine ⟨11755388065223806761213223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62695403014526969393137189 11755388065223806761213223)
    ·
      refine ⟨17633082097835710141819835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11755388065223806761213223 17633082097835710141819835)
      ·
        refine ⟨26449623146753565212729753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17633082097835710141819835 26449623146753565212729753)
        ·
          refine ⟨19837217360065173909547315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26449623146753565212729753 19837217360065173909547315)
          ·
            refine ⟨29755826040097760864320973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19837217360065173909547315 29755826040097760864320973)
            ·
              refine ⟨11158434765036660324120365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29755826040097760864320973 11158434765036660324120365)
              ·
                refine ⟨4184413036888747621545137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11158434765036660324120365 4184413036888747621545137)
                ·
                  refine ⟨3138309777666560716158853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4184413036888747621545137 3138309777666560716158853)
                  ·
                    refine ⟨588433083312480134279785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3138309777666560716158853 588433083312480134279785)
                    ·
                      rfl

theorem cell23_3437908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_3437908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437908 prefixEnd_3437908 := by exact prefixLift 3437908
  have htrace : WordTrace (prefixWord ++ tailWord_3437908) baseStart_3437908 baseEnd_3437908 := by
    simpa [prefixWord, tailWord_3437908, baseEnd_3437908] using wordTrace_append hprefix tailTrace_3437908
  have hstable : (prefixWord ++ tailWord_3437908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437908).length < 2 ^ (prefixWord ++ tailWord_3437908).sum := by decide
  have hdescent : baseEnd_3437908 < baseStart_3437908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437928 : List Nat := [2, 1, 4, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_3437928 : Nat := 118140960795 + 3437928 * 2 ^ 59
def prefixEnd_3437928 : Nat := 4983230072969 + 3 ^ 40 * 3437928 * 2
def baseEnd_3437928 : Nat := 1765309519550530324589263

theorem tailTrace_3437928 : CollatzResearch.WordTrace tailWord_3437928 prefixEnd_3437928 1765309519550530324589263 := by
  unfold tailWord_3437928
  simp only [CollatzResearch.WordTrace]
  refine ⟨62695767744490741101001219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83594356992654321468001625 62695767744490741101001219)
  ·
    refine ⟨94043651616736111651501829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62695767744490741101001219 94043651616736111651501829)
    ·
      refine ⟨17633184678138020934656593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94043651616736111651501829 17633184678138020934656593)
      ·
        refine ⟨13224888508603515700992445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17633184678138020934656593 13224888508603515700992445)
        ·
          refine ⟨4959333190726318387872167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13224888508603515700992445 4959333190726318387872167)
          ·
            refine ⟨7438999786089477581808251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4959333190726318387872167 7438999786089477581808251)
            ·
              refine ⟨11158499679134216372712377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7438999786089477581808251 11158499679134216372712377)
              ·
                refine ⟨8368874759350662279534283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11158499679134216372712377 8368874759350662279534283)
                ·
                  refine ⟨12553312139025993419301425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8368874759350662279534283 12553312139025993419301425)
                  ·
                    refine ⟨9414984104269495064476069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12553312139025993419301425 9414984104269495064476069)
                    ·
                      refine ⟨1765309519550530324589263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9414984104269495064476069 1765309519550530324589263)
                      ·
                        rfl

theorem cell23_3437928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_3437928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437928 prefixEnd_3437928 := by exact prefixLift 3437928
  have htrace : WordTrace (prefixWord ++ tailWord_3437928) baseStart_3437928 baseEnd_3437928 := by
    simpa [prefixWord, tailWord_3437928, baseEnd_3437928] using wordTrace_append hprefix tailTrace_3437928
  have hstable : (prefixWord ++ tailWord_3437928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437928).length < 2 ^ (prefixWord ++ tailWord_3437928).sum := by decide
  have hdescent : baseEnd_3437928 < baseStart_3437928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437991 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_3437991 : Nat := 118140960795 + 3437991 * 2 ^ 59
def prefixEnd_3437991 : Nat := 4983230072969 + 3 ^ 40 * 3437991 * 2
def baseEnd_3437991 : Nat := 1765341868831763578101473

theorem tailTrace_3437991 : CollatzResearch.WordTrace tailWord_3437991 prefixEnd_3437991 1765341868831763578101473 := by
  unfold tailWord_3437991
  simp only [CollatzResearch.WordTrace]
  refine ⟨125393833287753243961545827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83595888858502162641030551 125393833287753243961545827)
  ·
    refine ⟨188090749931629865942318741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125393833287753243961545827 188090749931629865942318741)
    ·
      refine ⟨8816753903045149966046191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 188090749931629865942318741 8816753903045149966046191)
      ·
        refine ⟨13225130854567724949069287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8816753903045149966046191 13225130854567724949069287)
        ·
          refine ⟨19837696281851587423603931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13225130854567724949069287 19837696281851587423603931)
          ·
            refine ⟨29756544422777381135405897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19837696281851587423603931 29756544422777381135405897)
            ·
              refine ⟨22317408317083035851554423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29756544422777381135405897 22317408317083035851554423)
              ·
                refine ⟨33476112475624553777331635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22317408317083035851554423 33476112475624553777331635)
                ·
                  refine ⟨50214168713436830665997453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33476112475624553777331635 50214168713436830665997453)
                  ·
                    refine ⟨18830313267538811499749045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50214168713436830665997453 18830313267538811499749045)
                    ·
                      refine ⟨1765341868831763578101473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18830313267538811499749045 1765341868831763578101473)
                      ·
                        rfl

theorem cell23_3437991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_3437991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3437991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3437991 prefixEnd_3437991 := by exact prefixLift 3437991
  have htrace : WordTrace (prefixWord ++ tailWord_3437991) baseStart_3437991 baseEnd_3437991 := by
    simpa [prefixWord, tailWord_3437991, baseEnd_3437991] using wordTrace_append hprefix tailTrace_3437991
  have hstable : (prefixWord ++ tailWord_3437991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437991).length < 2 ^ (prefixWord ++ tailWord_3437991).sum := by decide
  have hdescent : baseEnd_3437991 < baseStart_3437991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438001 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 4, 2, 4]
def baseStart_3438001 : Nat := 118140960795 + 3438001 * 2 ^ 59
def prefixEnd_3438001 : Nat := 4983230072969 + 3 ^ 40 * 3438001 * 2
def baseEnd_3438001 : Nat := 1765347003638308538976427

theorem tailTrace_3438001 : CollatzResearch.WordTrace tailWord_3438001 prefixEnd_3438001 1765347003638308538976427 := by
  unfold tailWord_3438001
  simp only [CollatzResearch.WordTrace]
  refine ⟨125394198017717015669409857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83596132011811343779606571 125394198017717015669409857)
  ·
    refine ⟨94045648513287761752057393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125394198017717015669409857 94045648513287761752057393)
    ·
      refine ⟨70534236384965821314043045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94045648513287761752057393 70534236384965821314043045)
      ·
        refine ⟨13225169322181091496383071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70534236384965821314043045 13225169322181091496383071)
        ·
          refine ⟨19837753983271637244574607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13225169322181091496383071 19837753983271637244574607)
          ·
            refine ⟨29756630974907455866861911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19837753983271637244574607 29756630974907455866861911)
            ·
              refine ⟨44634946462361183800292867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29756630974907455866861911 44634946462361183800292867)
              ·
                refine ⟨66952419693541775700439301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44634946462361183800292867 66952419693541775700439301)
                ·
                  refine ⟨12553578692539082943832369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66952419693541775700439301 12553578692539082943832369)
                  ·
                    refine ⟨9415184019404312207874277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12553578692539082943832369 9415184019404312207874277)
                    ·
                      refine ⟨1765347003638308538976427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9415184019404312207874277 1765347003638308538976427)
                      ·
                        rfl

theorem cell23_3438001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_3438001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438001 prefixEnd_3438001 := by exact prefixLift 3438001
  have htrace : WordTrace (prefixWord ++ tailWord_3438001) baseStart_3438001 baseEnd_3438001 := by
    simpa [prefixWord, tailWord_3438001, baseEnd_3438001] using wordTrace_append hprefix tailTrace_3438001
  have hstable : (prefixWord ++ tailWord_3438001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438001).length < 2 ^ (prefixWord ++ tailWord_3438001).sum := by decide
  have hdescent : baseEnd_3438001 < baseStart_3438001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438041 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 1, 7]
def baseStart_3438041 : Nat := 118140960795 + 3438041 * 2 ^ 59
def prefixEnd_3438041 : Nat := 4983230072969 + 3 ^ 40 * 3438041 * 2
def baseEnd_3438041 : Nat := 588455847621496127492081

theorem tailTrace_3438041 : CollatzResearch.WordTrace tailWord_3438041 prefixEnd_3438041 588455847621496127492081 := by
  unfold tailWord_3438041
  simp only [CollatzResearch.WordTrace]
  refine ⟨125395656937572102500865977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83597104625048068333910651 125395656937572102500865977)
  ·
    refine ⟨94046742703179076875649483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125395656937572102500865977 94046742703179076875649483)
    ·
      refine ⟨141070114054768615313474225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94046742703179076875649483 141070114054768615313474225)
      ·
        refine ⟨105802585541076461485105669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141070114054768615313474225 105802585541076461485105669)
        ·
          refine ⟨19837984788951836528457313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105802585541076461485105669 19837984788951836528457313)
          ·
            refine ⟨14878488591713877396342985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19837984788951836528457313 14878488591713877396342985)
            ·
              refine ⟨11158866443785408047257239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14878488591713877396342985 11158866443785408047257239)
              ·
                refine ⟨16738299665678112070885859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11158866443785408047257239 16738299665678112070885859)
                ·
                  refine ⟨25107449498517168106328789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16738299665678112070885859 25107449498517168106328789)
                  ·
                    refine ⟨588455847621496127492081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25107449498517168106328789 588455847621496127492081)
                    ·
                      rfl

theorem cell23_3438041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 7].length) (baseStart_3438041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438041 prefixEnd_3438041 := by exact prefixLift 3438041
  have htrace : WordTrace (prefixWord ++ tailWord_3438041) baseStart_3438041 baseEnd_3438041 := by
    simpa [prefixWord, tailWord_3438041, baseEnd_3438041] using wordTrace_append hprefix tailTrace_3438041
  have hstable : (prefixWord ++ tailWord_3438041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438041).length < 2 ^ (prefixWord ++ tailWord_3438041).sum := by decide
  have hdescent : baseEnd_3438041 < baseStart_3438041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438045 : List Nat := [1, 4, 3, 1, 1, 2, 3, 3, 5]
def baseStart_3438045 : Nat := 118140960795 + 3438045 * 2 ^ 59
def prefixEnd_3438045 : Nat := 4983230072969 + 3 ^ 40 * 3438045 * 2
def baseEnd_3438045 : Nat := 196152177420789596314025

theorem tailTrace_3438045 : CollatzResearch.WordTrace tailWord_3438045 prefixEnd_3438045 196152177420789596314025 := by
  unfold tailWord_3438045
  simp only [CollatzResearch.WordTrace]
  refine ⟨125395802829557611184011589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83597201886371740789341059 125395802829557611184011589)
  ·
    refine ⟨23511713030542052097002173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125395802829557611184011589 23511713030542052097002173)
    ·
      refine ⟨8816892386453269536375815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23511713030542052097002173 8816892386453269536375815)
      ·
        refine ⟨13225338579679904304563723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8816892386453269536375815 13225338579679904304563723)
        ·
          refine ⟨19838007869519856456845585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13225338579679904304563723 19838007869519856456845585)
          ·
            refine ⟨14878505902139892342634189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19838007869519856456845585 14878505902139892342634189)
            ·
              refine ⟨5579439713302459628487821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14878505902139892342634189 5579439713302459628487821)
              ·
                refine ⟨2092289892488422360682933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5579439713302459628487821 2092289892488422360682933)
                ·
                  refine ⟨196152177420789596314025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2092289892488422360682933 196152177420789596314025)
                  ·
                    rfl

theorem cell23_3438045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_3438045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438045 prefixEnd_3438045 := by exact prefixLift 3438045
  have htrace : WordTrace (prefixWord ++ tailWord_3438045) baseStart_3438045 baseEnd_3438045 := by
    simpa [prefixWord, tailWord_3438045, baseEnd_3438045] using wordTrace_append hprefix tailTrace_3438045
  have hstable : (prefixWord ++ tailWord_3438045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438045).length < 2 ^ (prefixWord ++ tailWord_3438045).sum := by decide
  have hdescent : baseEnd_3438045 < baseStart_3438045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438088 : List Nat := [2, 1, 3, 2, 1, 1, 2, 4, 3, 4]
def baseStart_3438088 : Nat := 118140960795 + 3438088 * 2 ^ 59
def prefixEnd_3438088 : Nat := 4983230072969 + 3 ^ 40 * 3438088 * 2
def baseEnd_3438088 : Nat := 588463892151749899529509

theorem tailTrace_3438088 : CollatzResearch.WordTrace tailWord_3438088 prefixEnd_3438088 588463892151749899529509 := by
  unfold tailWord_3438088
  simp only [CollatzResearch.WordTrace]
  refine ⟨62698685584200914763913459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83598247445601219685217945 62698685584200914763913459)
  ·
    refine ⟨94048028376301372145870189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62698685584200914763913459 94048028376301372145870189)
    ·
      refine ⟨35268010641113014554701321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94048028376301372145870189 35268010641113014554701321)
      ·
        refine ⟨26451007980834760916025991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35268010641113014554701321 26451007980834760916025991)
        ·
          refine ⟨39676511971252141374038987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26451007980834760916025991 39676511971252141374038987)
          ·
            refine ⟨59514767956878212061058481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39676511971252141374038987 59514767956878212061058481)
            ·
              refine ⟨44636075967658659045793861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59514767956878212061058481 44636075967658659045793861)
              ·
                refine ⟨8369264243935998571086349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44636075967658659045793861 8369264243935998571086349)
                ·
                  refine ⟨3138474091475999464157381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8369264243935998571086349 3138474091475999464157381)
                  ·
                    refine ⟨588463892151749899529509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3138474091475999464157381 588463892151749899529509)
                    ·
                      rfl

theorem cell23_3438088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_3438088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438088 prefixEnd_3438088 := by exact prefixLift 3438088
  have htrace : WordTrace (prefixWord ++ tailWord_3438088) baseStart_3438088 baseEnd_3438088 := by
    simpa [prefixWord, tailWord_3438088, baseEnd_3438088] using wordTrace_append hprefix tailTrace_3438088
  have hstable : (prefixWord ++ tailWord_3438088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438088).length < 2 ^ (prefixWord ++ tailWord_3438088).sum := by decide
  have hdescent : baseEnd_3438088 < baseStart_3438088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438122 : List Nat := [3, 1, 4, 1, 1, 1, 3, 4, 1, 4]
def baseStart_3438122 : Nat := 118140960795 + 3438122 * 2 ^ 59
def prefixEnd_3438122 : Nat := 4983230072969 + 3 ^ 40 * 3438122 * 2
def baseEnd_3438122 : Nat := 588469711599167521854457

theorem tailTrace_3438122 : CollatzResearch.WordTrace tailWord_3438122 prefixEnd_3438122 588469711599167521854457 := by
  unfold tailWord_3438122
  simp only [CollatzResearch.WordTrace]
  refine ⟨31349652812569663333641155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83599074166852435556376413 31349652812569663333641155)
  ·
    refine ⟨47024479218854495000461733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31349652812569663333641155 47024479218854495000461733)
    ·
      refine ⟨8817089853535217812586575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47024479218854495000461733 8817089853535217812586575)
      ·
        refine ⟨13225634780302826718879863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8817089853535217812586575 13225634780302826718879863)
        ·
          refine ⟨19838452170454240078319795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13225634780302826718879863 19838452170454240078319795)
          ·
            refine ⟨29757678255681360117479693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19838452170454240078319795 29757678255681360117479693)
            ·
              refine ⟨11159129345880510044054885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29757678255681360117479693 11159129345880510044054885)
              ·
                refine ⟨2092336752352595633260291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11159129345880510044054885 2092336752352595633260291)
                ·
                  refine ⟨3138505128528893449890437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2092336752352595633260291 3138505128528893449890437)
                  ·
                    refine ⟨588469711599167521854457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3138505128528893449890437 588469711599167521854457)
                    ·
                      rfl

theorem cell23_3438122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_3438122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438122 prefixEnd_3438122 := by exact prefixLift 3438122
  have htrace : WordTrace (prefixWord ++ tailWord_3438122) baseStart_3438122 baseEnd_3438122 := by
    simpa [prefixWord, tailWord_3438122, baseEnd_3438122] using wordTrace_append hprefix tailTrace_3438122
  have hstable : (prefixWord ++ tailWord_3438122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438122).length < 2 ^ (prefixWord ++ tailWord_3438122).sum := by decide
  have hdescent : baseEnd_3438122 < baseStart_3438122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438191 : List Nat := [1, 1, 2, 1, 3, 2, 1, 12]
def baseStart_3438191 : Nat := 118140960795 + 3438191 * 2 ^ 59
def prefixEnd_3438191 : Nat := 4983230072969 + 3 ^ 40 * 3438191 * 2
def baseEnd_3438191 : Nat := 65386835739357881318539

theorem tailTrace_3438191 : CollatzResearch.WordTrace tailWord_3438191 prefixEnd_3438191 65386835739357881318539 := by
  unfold tailWord_3438191
  simp only [CollatzResearch.WordTrace]
  refine ⟨125401127887028678118826427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83600751924685785412550951 125401127887028678118826427)
  ·
    refine ⟨188101691830543017178239641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125401127887028678118826427 188101691830543017178239641)
    ·
      refine ⟨141076268872907262883679731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188101691830543017178239641 141076268872907262883679731)
      ·
        refine ⟨211614403309360894325519597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141076268872907262883679731 211614403309360894325519597)
        ·
          refine ⟨79355401241010335372069849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211614403309360894325519597 79355401241010335372069849)
          ·
            refine ⟨59516550930757751529052387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79355401241010335372069849 59516550930757751529052387)
            ·
              refine ⟨89274826396136627293578581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59516550930757751529052387 89274826396136627293578581)
              ·
                refine ⟨65386835739357881318539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 89274826396136627293578581 65386835739357881318539)
                ·
                  rfl

theorem cell23_3438191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 12].length) (baseStart_3438191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438191 prefixEnd_3438191 := by exact prefixLift 3438191
  have htrace : WordTrace (prefixWord ++ tailWord_3438191) baseStart_3438191 baseEnd_3438191 := by
    simpa [prefixWord, tailWord_3438191, baseEnd_3438191] using wordTrace_append hprefix tailTrace_3438191
  have hstable : (prefixWord ++ tailWord_3438191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438191).length < 2 ^ (prefixWord ++ tailWord_3438191).sum := by decide
  have hdescent : baseEnd_3438191 < baseStart_3438191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438222 : List Nat := [4, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3]
def baseStart_3438222 : Nat := 118140960795 + 3438222 * 2 ^ 59
def prefixEnd_3438222 : Nat := 4983230072969 + 3 ^ 40 * 3438222 * 2
def baseEnd_3438222 : Nat := 1765460482862952174312911

theorem tailTrace_3438222 : CollatzResearch.WordTrace tailWord_3438222 prefixEnd_3438222 1765460482862952174312911 := by
  unfold tailWord_3438222
  simp only [CollatzResearch.WordTrace]
  refine ⟨15675282318739546301650615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83601505699944246942136613 15675282318739546301650615)
  ·
    refine ⟨23512923478109319452475923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15675282318739546301650615 23512923478109319452475923)
    ·
      refine ⟨35269385217163979178713885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23512923478109319452475923 35269385217163979178713885)
      ·
        refine ⟨13226019456436492192017707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35269385217163979178713885 13226019456436492192017707)
        ·
          refine ⟨19839029184654738288026561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13226019456436492192017707 19839029184654738288026561)
          ·
            refine ⟨14879271888491053716019921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19839029184654738288026561 14879271888491053716019921)
            ·
              refine ⟨11159453916368290287014941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14879271888491053716019921 11159453916368290287014941)
              ·
                refine ⟨4184795218638108857630603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11159453916368290287014941 4184795218638108857630603)
                ·
                  refine ⟨6277192827957163286445905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4184795218638108857630603 6277192827957163286445905)
                  ·
                    refine ⟨4707894620967872464834429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6277192827957163286445905 4707894620967872464834429)
                    ·
                      refine ⟨1765460482862952174312911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4707894620967872464834429 1765460482862952174312911)
                      ·
                        rfl

theorem cell23_3438222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_3438222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438222 prefixEnd_3438222 := by exact prefixLift 3438222
  have htrace : WordTrace (prefixWord ++ tailWord_3438222) baseStart_3438222 baseEnd_3438222 := by
    simpa [prefixWord, tailWord_3438222, baseEnd_3438222] using wordTrace_append hprefix tailTrace_3438222
  have hstable : (prefixWord ++ tailWord_3438222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438222).length < 2 ^ (prefixWord ++ tailWord_3438222).sum := by decide
  have hdescent : baseEnd_3438222 < baseStart_3438222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438236 : List Nat := [2, 2, 3, 2, 3, 2, 1, 1, 3, 2, 2]
def baseStart_3438236 : Nat := 118140960795 + 3438236 * 2 ^ 59
def prefixEnd_3438236 : Nat := 4983230072969 + 3 ^ 40 * 3438236 * 2
def baseEnd_3438236 : Nat := 1765467671592115119537847

theorem tailTrace_3438236 : CollatzResearch.WordTrace tailWord_3438236 prefixEnd_3438236 1765467671592115119537847 := by
  unfold tailWord_3438236
  simp only [CollatzResearch.WordTrace]
  refine ⟨62701384585932825402107281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83601846114577100536143041 62701384585932825402107281)
  ·
    refine ⟨47026038439449619051580461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62701384585932825402107281 47026038439449619051580461)
    ·
      refine ⟨17634764414793607144342673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47026038439449619051580461 17634764414793607144342673)
      ·
        refine ⟨13226073311095205358257005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17634764414793607144342673 13226073311095205358257005)
        ·
          refine ⟨4959777491660702009346377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13226073311095205358257005 4959777491660702009346377)
          ·
            refine ⟨3719833118745526507009783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4959777491660702009346377 3719833118745526507009783)
            ·
              refine ⟨5579749678118289760514675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3719833118745526507009783 5579749678118289760514675)
              ·
                refine ⟨8369624517177434640772013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5579749678118289760514675 8369624517177434640772013)
                ·
                  refine ⟨3138609193941537990289505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8369624517177434640772013 3138609193941537990289505)
                  ·
                    refine ⟨2353956895456153492717129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3138609193941537990289505 2353956895456153492717129)
                    ·
                      refine ⟨1765467671592115119537847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2353956895456153492717129 1765467671592115119537847)
                      ·
                        rfl

theorem cell23_3438236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_3438236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438236 prefixEnd_3438236 := by exact prefixLift 3438236
  have htrace : WordTrace (prefixWord ++ tailWord_3438236) baseStart_3438236 baseEnd_3438236 := by
    simpa [prefixWord, tailWord_3438236, baseEnd_3438236] using wordTrace_append hprefix tailTrace_3438236
  have hstable : (prefixWord ++ tailWord_3438236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438236).length < 2 ^ (prefixWord ++ tailWord_3438236).sum := by decide
  have hdescent : baseEnd_3438236 < baseStart_3438236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438242 : List Nat := [3, 3, 1, 4, 1, 1, 2, 8]
def baseStart_3438242 : Nat := 118140960795 + 3438242 * 2 ^ 59
def prefixEnd_3438242 : Nat := 4983230072969 + 3 ^ 40 * 3438242 * 2
def baseEnd_3438242 : Nat := 65387805647260818372697

theorem tailTrace_3438242 : CollatzResearch.WordTrace tailWord_3438242 prefixEnd_3438242 65387805647260818372697 := by
  unfold tailWord_3438242
  simp only [CollatzResearch.WordTrace]
  refine ⟨31350747002460978457233245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83601992006562609219288653 31350747002460978457233245)
  ·
    refine ⟨11756530125922866921462467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31350747002460978457233245 11756530125922866921462467)
    ·
      refine ⟨17634795188884300382193701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11756530125922866921462467 17634795188884300382193701)
      ·
        refine ⟨3306524097915806321661319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17634795188884300382193701 3306524097915806321661319)
        ·
          refine ⟨4959786146873709482491979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3306524097915806321661319 4959786146873709482491979)
          ·
            refine ⟨7439679220310564223737969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4959786146873709482491979 7439679220310564223737969)
            ·
              refine ⟨5579759415232923167803477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7439679220310564223737969 5579759415232923167803477)
              ·
                refine ⟨65387805647260818372697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5579759415232923167803477 65387805647260818372697)
                ·
                  rfl

theorem cell23_3438242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 8].length) (baseStart_3438242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438242 prefixEnd_3438242 := by exact prefixLift 3438242
  have htrace : WordTrace (prefixWord ++ tailWord_3438242) baseStart_3438242 baseEnd_3438242 := by
    simpa [prefixWord, tailWord_3438242, baseEnd_3438242] using wordTrace_append hprefix tailTrace_3438242
  have hstable : (prefixWord ++ tailWord_3438242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438242).length < 2 ^ (prefixWord ++ tailWord_3438242).sum := by decide
  have hdescent : baseEnd_3438242 < baseStart_3438242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438279 : List Nat := [1, 1, 4, 1, 1, 1, 7, 1, 1, 3, 2]
def baseStart_3438279 : Nat := 118140960795 + 3438279 * 2 ^ 59
def prefixEnd_3438279 : Nat := 4983230072969 + 3 ^ 40 * 3438279 * 2
def baseEnd_3438279 : Nat := 1765489751260258451300149

theorem tailTrace_3438279 : CollatzResearch.WordTrace tailWord_3438279 prefixEnd_3438279 1765489751260258451300149 := by
  unfold tailWord_3438279
  simp only [CollatzResearch.WordTrace]
  refine ⟨125404337510709869148029891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83602891673806579432019927 125404337510709869148029891)
  ·
    refine ⟨188106506266064803722044837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125404337510709869148029891 188106506266064803722044837)
    ·
      refine ⟨35269969924887150697883407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188106506266064803722044837 35269969924887150697883407)
      ·
        refine ⟨52904954887330726046825111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35269969924887150697883407 52904954887330726046825111)
        ·
          refine ⟨79357432330996089070237667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52904954887330726046825111 79357432330996089070237667)
          ·
            refine ⟨119036148496494133605356501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79357432330996089070237667 119036148496494133605356501)
            ·
              refine ⟨2789909730386581256375543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 119036148496494133605356501 2789909730386581256375543)
              ·
                refine ⟨4184864595579871884563315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2789909730386581256375543 4184864595579871884563315)
                ·
                  refine ⟨6277296893369807826844973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4184864595579871884563315 6277296893369807826844973)
                  ·
                    refine ⟨2353986335013677935066865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6277296893369807826844973 2353986335013677935066865)
                    ·
                      refine ⟨1765489751260258451300149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2353986335013677935066865 1765489751260258451300149)
                      ·
                        rfl

theorem cell23_3438279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_3438279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438279 prefixEnd_3438279 := by exact prefixLift 3438279
  have htrace : WordTrace (prefixWord ++ tailWord_3438279) baseStart_3438279 baseEnd_3438279 := by
    simpa [prefixWord, tailWord_3438279, baseEnd_3438279] using wordTrace_append hprefix tailTrace_3438279
  have hstable : (prefixWord ++ tailWord_3438279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438279).length < 2 ^ (prefixWord ++ tailWord_3438279).sum := by decide
  have hdescent : baseEnd_3438279 < baseStart_3438279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438309 : List Nat := [1, 3, 1, 4, 1, 1, 1, 5, 2, 2, 2]
def baseStart_3438309 : Nat := 118140960795 + 3438309 * 2 ^ 59
def prefixEnd_3438309 : Nat := 4983230072969 + 3 ^ 40 * 3438309 * 2
def baseEnd_3438309 : Nat := 1765505155679893333925011

theorem tailTrace_3438309 : CollatzResearch.WordTrace tailWord_3438309 prefixEnd_3438309 1765505155679893333925011 := by
  unfold tailWord_3438309
  simp only [CollatzResearch.WordTrace]
  refine ⟨125405431700601184271621981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83603621133734122847747987 125405431700601184271621981)
  ·
    refine ⟨47027036887725444101858243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125405431700601184271621981 47027036887725444101858243)
    ·
      refine ⟨70540555331588166152787365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47027036887725444101858243 70540555331588166152787365)
      ·
        refine ⟨13226354124672781153647631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70540555331588166152787365 13226354124672781153647631)
        ·
          refine ⟨19839531187009171730471447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13226354124672781153647631 19839531187009171730471447)
          ·
            refine ⟨29759296780513757595707171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19839531187009171730471447 29759296780513757595707171)
            ·
              refine ⟨44638945170770636393560757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29759296780513757595707171 44638945170770636393560757)
              ·
                refine ⟨4184901109759747161896321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44638945170770636393560757 4184901109759747161896321)
                ·
                  refine ⟨3138675832319810371422241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4184901109759747161896321 3138675832319810371422241)
                  ·
                    refine ⟨2354006874239857778566681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3138675832319810371422241 2354006874239857778566681)
                    ·
                      refine ⟨1765505155679893333925011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2354006874239857778566681 1765505155679893333925011)
                      ·
                        rfl

theorem cell23_3438309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_3438309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438309 prefixEnd_3438309 := by exact prefixLift 3438309
  have htrace : WordTrace (prefixWord ++ tailWord_3438309) baseStart_3438309 baseEnd_3438309 := by
    simpa [prefixWord, tailWord_3438309, baseEnd_3438309] using wordTrace_append hprefix tailTrace_3438309
  have hstable : (prefixWord ++ tailWord_3438309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438309).length < 2 ^ (prefixWord ++ tailWord_3438309).sum := by decide
  have hdescent : baseEnd_3438309 < baseStart_3438309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438332 : List Nat := [2, 2, 2, 1, 3, 1, 4, 3, 5]
def baseStart_3438332 : Nat := 118140960795 + 3438332 * 2 ^ 59
def prefixEnd_3438332 : Nat := 4983230072969 + 3 ^ 40 * 3438332 * 2
def baseEnd_3438332 : Nat := 196168551748327415993045

theorem tailTrace_3438332 : CollatzResearch.WordTrace tailWord_3438332 prefixEnd_3438332 196168551748327415993045 := by
  unfold tailWord_3438332
  simp only [CollatzResearch.WordTrace]
  refine ⟨62703135289758929599854625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83604180386345239466472833 62703135289758929599854625)
  ·
    refine ⟨47027351467319197199890969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62703135289758929599854625 47027351467319197199890969)
    ·
      refine ⟨35270513600489397899918227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47027351467319197199890969 35270513600489397899918227)
      ·
        refine ⟨52905770400734096849877341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35270513600489397899918227 52905770400734096849877341)
        ·
          refine ⟨19839663900275286318704003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52905770400734096849877341 19839663900275286318704003)
          ·
            refine ⟨29759495850412929478056005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19839663900275286318704003 29759495850412929478056005)
            ·
              refine ⟨5579905471952424277135501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29759495850412929478056005 5579905471952424277135501)
              ·
                refine ⟨2092464551982159103925813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5579905471952424277135501 2092464551982159103925813)
                ·
                  refine ⟨196168551748327415993045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2092464551982159103925813 196168551748327415993045)
                  ·
                    rfl

theorem cell23_3438332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 5].length) (baseStart_3438332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438332 prefixEnd_3438332 := by exact prefixLift 3438332
  have htrace : WordTrace (prefixWord ++ tailWord_3438332) baseStart_3438332 baseEnd_3438332 := by
    simpa [prefixWord, tailWord_3438332, baseEnd_3438332] using wordTrace_append hprefix tailTrace_3438332
  have hstable : (prefixWord ++ tailWord_3438332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438332).length < 2 ^ (prefixWord ++ tailWord_3438332).sum := by decide
  have hdescent : baseEnd_3438332 < baseStart_3438332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438343 : List Nat := [1, 1, 4, 4, 2, 2, 1, 2, 2, 2, 2]
def baseStart_3438343 : Nat := 118140960795 + 3438343 * 2 ^ 59
def prefixEnd_3438343 : Nat := 4983230072969 + 3 ^ 40 * 3438343 * 2
def baseEnd_3438343 : Nat := 1765522614022146200899855

theorem tailTrace_3438343 : CollatzResearch.WordTrace tailWord_3438343 prefixEnd_3438343 1765522614022146200899855 := by
  unfold tailWord_3438343
  simp only [CollatzResearch.WordTrace]
  refine ⟨125406671782478008078359683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83604447854985338718906455 125406671782478008078359683)
  ·
    refine ⟨188110007673717012117539525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125406671782478008078359683 188110007673717012117539525)
    ·
      refine ⟨35270626438821939772038661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188110007673717012117539525 35270626438821939772038661)
      ·
        refine ⟨6613242457279113707257249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35270626438821939772038661 6613242457279113707257249)
        ·
          refine ⟨4959931842959335280442937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6613242457279113707257249 4959931842959335280442937)
          ·
            refine ⟨3719948882219501460332203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4959931842959335280442937 3719948882219501460332203)
            ·
              refine ⟨5579923323329252190498305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3719948882219501460332203 5579923323329252190498305)
              ·
                refine ⟨4184942492496939142873729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5579923323329252190498305 4184942492496939142873729)
                ·
                  refine ⟨3138706869372704357155297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4184942492496939142873729 3138706869372704357155297)
                  ·
                    refine ⟨2354030152029528267866473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3138706869372704357155297 2354030152029528267866473)
                    ·
                      refine ⟨1765522614022146200899855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2354030152029528267866473 1765522614022146200899855)
                      ·
                        rfl

theorem cell23_3438343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_3438343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438343 prefixEnd_3438343 := by exact prefixLift 3438343
  have htrace : WordTrace (prefixWord ++ tailWord_3438343) baseStart_3438343 baseEnd_3438343 := by
    simpa [prefixWord, tailWord_3438343, baseEnd_3438343] using wordTrace_append hprefix tailTrace_3438343
  have hstable : (prefixWord ++ tailWord_3438343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438343).length < 2 ^ (prefixWord ++ tailWord_3438343).sum := by decide
  have hdescent : baseEnd_3438343 < baseStart_3438343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438405 : List Nat := [1, 3, 1, 1, 1, 2, 4, 4, 6]
def baseStart_3438405 : Nat := 118140960795 + 3438405 * 2 ^ 59
def prefixEnd_3438405 : Nat := 4983230072969 + 3 ^ 40 * 3438405 * 2
def baseEnd_3438405 : Nat := 196172716646969439813841

theorem tailTrace_3438405 : CollatzResearch.WordTrace tailWord_3438405 prefixEnd_3438405 196172716646969439813841 := by
  unfold tailWord_3438405
  simp only [CollatzResearch.WordTrace]
  refine ⟨125408933108253392667116669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83605955405502261778077779 125408933108253392667116669)
  ·
    refine ⟨47028349915595022250168751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125408933108253392667116669 47028349915595022250168751)
    ·
      refine ⟨70542524873392533375253127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47028349915595022250168751 70542524873392533375253127)
      ·
        refine ⟨105813787310088800062879691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70542524873392533375253127 105813787310088800062879691)
        ·
          refine ⟨158720680965133200094319537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105813787310088800062879691 158720680965133200094319537)
          ·
            refine ⟨119040510723849900070739653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158720680965133200094319537 119040510723849900070739653)
            ·
              refine ⟨22320095760721856263263685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119040510723849900070739653 22320095760721856263263685)
              ·
                refine ⟨4185017955135348049361941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22320095760721856263263685 4185017955135348049361941)
                ·
                  refine ⟨196172716646969439813841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4185017955135348049361941 196172716646969439813841)
                  ·
                    rfl

theorem cell23_3438405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 6].length) (baseStart_3438405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438405 prefixEnd_3438405 := by exact prefixLift 3438405
  have htrace : WordTrace (prefixWord ++ tailWord_3438405) baseStart_3438405 baseEnd_3438405 := by
    simpa [prefixWord, tailWord_3438405, baseEnd_3438405] using wordTrace_append hprefix tailTrace_3438405
  have hstable : (prefixWord ++ tailWord_3438405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438405).length < 2 ^ (prefixWord ++ tailWord_3438405).sum := by decide
  have hdescent : baseEnd_3438405 < baseStart_3438405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438475 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 5]
def baseStart_3438475 : Nat := 118140960795 + 3438475 * 2 ^ 59
def prefixEnd_3438475 : Nat := 4983230072969 + 3 ^ 40 * 3438475 * 2
def baseEnd_3438475 : Nat := 1765590393468539684449247

theorem tailTrace_3438475 : CollatzResearch.WordTrace tailWord_3438475 prefixEnd_3438475 1765590393468539684449247 := by
  unfold tailWord_3438475
  simp only [CollatzResearch.WordTrace]
  refine ⟨125411486217999794622164879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83607657478666529748109919 125411486217999794622164879)
  ·
    refine ⟨188117229326999691933247319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125411486217999794622164879 188117229326999691933247319)
    ·
      refine ⟨282175843990499537899870979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188117229326999691933247319 282175843990499537899870979)
      ·
        refine ⟨423263765985749306849806469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282175843990499537899870979 423263765985749306849806469)
        ·
          refine ⟨79361956122327995034338713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 423263765985749306849806469 79361956122327995034338713)
          ·
            refine ⟨59521467091745996275754035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79361956122327995034338713 59521467091745996275754035)
            ·
              refine ⟨89282200637618994413631053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59521467091745996275754035 89282200637618994413631053)
              ·
                refine ⟨33480825239107122905111645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89282200637618994413631053 33480825239107122905111645)
                ·
                  refine ⟨12555309464665171089416867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33480825239107122905111645 12555309464665171089416867)
                  ·
                    refine ⟨18832964196997756634125301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12555309464665171089416867 18832964196997756634125301)
                    ·
                      refine ⟨1765590393468539684449247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18832964196997756634125301 1765590393468539684449247)
                      ·
                        rfl

theorem cell23_3438475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 5].length) (baseStart_3438475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438475 prefixEnd_3438475 := by exact prefixLift 3438475
  have htrace : WordTrace (prefixWord ++ tailWord_3438475) baseStart_3438475 baseEnd_3438475 := by
    simpa [prefixWord, tailWord_3438475, baseEnd_3438475] using wordTrace_append hprefix tailTrace_3438475
  have hstable : (prefixWord ++ tailWord_3438475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438475).length < 2 ^ (prefixWord ++ tailWord_3438475).sum := by decide
  have hdescent : baseEnd_3438475 < baseStart_3438475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438489 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 5, 2, 2]
def baseStart_3438489 : Nat := 118140960795 + 3438489 * 2 ^ 59
def prefixEnd_3438489 : Nat := 4983230072969 + 3 ^ 40 * 3438489 * 2
def baseEnd_3438489 : Nat := 1765597582197702629674183

theorem tailTrace_3438489 : CollatzResearch.WordTrace tailWord_3438489 prefixEnd_3438489 1765597582197702629674183 := by
  unfold tailWord_3438489
  simp only [CollatzResearch.WordTrace]
  refine ⟨125411996839949075013174521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83607997893299383342116347 125411996839949075013174521)
  ·
    refine ⟨94058997629961806259880891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125411996839949075013174521 94058997629961806259880891)
    ·
      refine ⟨141088496444942709389821337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94058997629961806259880891 141088496444942709389821337)
      ·
        refine ⟨105816372333707032042366003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141088496444942709389821337 105816372333707032042366003)
        ·
          refine ⟨158724558500560548063549005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105816372333707032042366003 158724558500560548063549005)
          ·
            refine ⟨59521709437710205523830877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158724558500560548063549005 59521709437710205523830877)
            ·
              refine ⟨22320641039141327071436579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59521709437710205523830877 22320641039141327071436579)
              ·
                refine ⟨33480961558711990607154869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22320641039141327071436579 33480961558711990607154869)
                ·
                  refine ⟨3138840146129249119420769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33480961558711990607154869 3138840146129249119420769)
                  ·
                    refine ⟨2354130109596936839565577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3138840146129249119420769 2354130109596936839565577)
                    ·
                      refine ⟨1765597582197702629674183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2354130109596936839565577 1765597582197702629674183)
                      ·
                        rfl

theorem cell23_3438489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 2, 2].length) (baseStart_3438489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438489 prefixEnd_3438489 := by exact prefixLift 3438489
  have htrace : WordTrace (prefixWord ++ tailWord_3438489) baseStart_3438489 baseEnd_3438489 := by
    simpa [prefixWord, tailWord_3438489, baseEnd_3438489] using wordTrace_append hprefix tailTrace_3438489
  have hstable : (prefixWord ++ tailWord_3438489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438489).length < 2 ^ (prefixWord ++ tailWord_3438489).sum := by decide
  have hdescent : baseEnd_3438489 < baseStart_3438489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438545 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 8]
def baseStart_3438545 : Nat := 118140960795 + 3438545 * 2 ^ 59
def prefixEnd_3438545 : Nat := 4983230072969 + 3 ^ 40 * 3438545 * 2
def baseEnd_3438545 : Nat := 1765626337114354410573925

theorem tailTrace_3438545 : CollatzResearch.WordTrace tailWord_3438545 prefixEnd_3438545 1765626337114354410573925 := by
  unfold tailWord_3438545
  simp only [CollatzResearch.WordTrace]
  refine ⟨125414039327746196577213089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83609359551830797718142059 125414039327746196577213089)
  ·
    refine ⟨94060529495809647432909817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125414039327746196577213089 94060529495809647432909817)
    ·
      refine ⟨70545397121857235574682363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94060529495809647432909817 70545397121857235574682363)
      ·
        refine ⟨105818095682785853362023545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70545397121857235574682363 105818095682785853362023545)
        ·
          refine ⟨79363571762089390021517659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105818095682785853362023545 79363571762089390021517659)
          ·
            refine ⟨119045357643134085032276489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79363571762089390021517659 119045357643134085032276489)
            ·
              refine ⟨89284018232350563774207367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119045357643134085032276489 89284018232350563774207367)
              ·
                refine ⟨133926027348525845661311051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89284018232350563774207367 133926027348525845661311051)
                ·
                  refine ⟨200889041022788768491966577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133926027348525845661311051 200889041022788768491966577)
                  ·
                    refine ⟨150666780767091576368974933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 200889041022788768491966577 150666780767091576368974933)
                    ·
                      refine ⟨1765626337114354410573925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 150666780767091576368974933 1765626337114354410573925)
                      ·
                        rfl

theorem cell23_3438545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_3438545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438545 prefixEnd_3438545 := by exact prefixLift 3438545
  have htrace : WordTrace (prefixWord ++ tailWord_3438545) baseStart_3438545 baseEnd_3438545 := by
    simpa [prefixWord, tailWord_3438545, baseEnd_3438545] using wordTrace_append hprefix tailTrace_3438545
  have hstable : (prefixWord ++ tailWord_3438545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438545).length < 2 ^ (prefixWord ++ tailWord_3438545).sum := by decide
  have hdescent : baseEnd_3438545 < baseStart_3438545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438546 : List Nat := [3, 2, 2, 3, 2, 2, 2, 7]
def baseStart_3438546 : Nat := 118140960795 + 3438546 * 2 ^ 59
def prefixEnd_3438546 : Nat := 4983230072969 + 3 ^ 40 * 3438546 * 2
def baseEnd_3438546 : Nat := 65393587059074403950423

theorem tailTrace_3438546 : CollatzResearch.WordTrace tailWord_3438546 prefixEnd_3438546 65393587059074403950423 := by
  unfold tailWord_3438546
  simp only [CollatzResearch.WordTrace]
  refine ⟨31353518950185643436999873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83609383867161715831999661 31353518950185643436999873)
  ·
    refine ⟨23515139212639232577749905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31353518950185643436999873 23515139212639232577749905)
    ·
      refine ⟨17636354409479424433312429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23515139212639232577749905 17636354409479424433312429)
      ·
        refine ⟨6613632903554784162492161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17636354409479424433312429 6613632903554784162492161)
        ·
          refine ⟨4960224677666088121869121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6613632903554784162492161 4960224677666088121869121)
          ·
            refine ⟨3720168508249566091401841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4960224677666088121869121 3720168508249566091401841)
            ·
              refine ⟨2790126381187174568551381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3720168508249566091401841 2790126381187174568551381)
              ·
                refine ⟨65393587059074403950423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2790126381187174568551381 65393587059074403950423)
                ·
                  rfl

theorem cell23_3438546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 7].length) (baseStart_3438546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438546 prefixEnd_3438546 := by exact prefixLift 3438546
  have htrace : WordTrace (prefixWord ++ tailWord_3438546) baseStart_3438546 baseEnd_3438546 := by
    simpa [prefixWord, tailWord_3438546, baseEnd_3438546] using wordTrace_append hprefix tailTrace_3438546
  have hstable : (prefixWord ++ tailWord_3438546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438546).length < 2 ^ (prefixWord ++ tailWord_3438546).sum := by decide
  have hdescent : baseEnd_3438546 < baseStart_3438546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438557 : List Nat := [1, 4, 3, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_3438557 : Nat := 118140960795 + 3438557 * 2 ^ 59
def prefixEnd_3438557 : Nat := 4983230072969 + 3 ^ 40 * 3438557 * 2
def baseEnd_3438557 : Nat := 1765632498882208363623871

theorem tailTrace_3438557 : CollatzResearch.WordTrace tailWord_3438557 prefixEnd_3438557 1765632498882208363623871 := by
  unfold tailWord_3438557
  simp only [CollatzResearch.WordTrace]
  refine ⟨125414477003702722626649925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83609651335801815084433283 125414477003702722626649925)
  ·
    refine ⟨23515214438194260492496861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125414477003702722626649925 23515214438194260492496861)
    ·
      refine ⟨8818205414322847684686323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23515214438194260492496861 8818205414322847684686323)
      ·
        refine ⟨13227308121484271527029485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8818205414322847684686323 13227308121484271527029485)
        ·
          refine ⟨4960240545556601822636057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13227308121484271527029485 4960240545556601822636057)
          ·
            refine ⟨3720180409167451366977043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4960240545556601822636057 3720180409167451366977043)
            ·
              refine ⟨5580270613751177050465565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3720180409167451366977043 5580270613751177050465565)
              ·
                refine ⟨2092601480156691393924587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5580270613751177050465565 2092601480156691393924587)
                ·
                  refine ⟨3138902220235037090886881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2092601480156691393924587 3138902220235037090886881)
                  ·
                    refine ⟨2354176665176277818165161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3138902220235037090886881 2354176665176277818165161)
                    ·
                      refine ⟨1765632498882208363623871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2354176665176277818165161 1765632498882208363623871)
                      ·
                        rfl

theorem cell23_3438557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_3438557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438557 prefixEnd_3438557 := by exact prefixLift 3438557
  have htrace : WordTrace (prefixWord ++ tailWord_3438557) baseStart_3438557 baseEnd_3438557 := by
    simpa [prefixWord, tailWord_3438557, baseEnd_3438557] using wordTrace_append hprefix tailTrace_3438557
  have hstable : (prefixWord ++ tailWord_3438557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438557).length < 2 ^ (prefixWord ++ tailWord_3438557).sum := by decide
  have hdescent : baseEnd_3438557 < baseStart_3438557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438590 : List Nat := [4, 2, 2, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_3438590 : Nat := 118140960795 + 3438590 * 2 ^ 59
def prefixEnd_3438590 : Nat := 4983230072969 + 3 ^ 40 * 3438590 * 2
def baseEnd_3438590 : Nat := 1765649443743806734511219

theorem tailTrace_3438590 : CollatzResearch.WordTrace tailWord_3438590 prefixEnd_3438590 1765649443743806734511219 := by
  unfold tailWord_3438590
  simp only [CollatzResearch.WordTrace]
  refine ⟨15676960076572896157825153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83610453741722112841734149 15676960076572896157825153)
  ·
    refine ⟨11757720057429672118368865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15676960076572896157825153 11757720057429672118368865)
    ·
      refine ⟨8818290043072254088776649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11757720057429672118368865 8818290043072254088776649)
      ·
        refine ⟨6613717532304190566582487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8818290043072254088776649 6613717532304190566582487)
        ·
          refine ⟨9920576298456285849873731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6613717532304190566582487 9920576298456285849873731)
          ·
            refine ⟨14880864447684428774810597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9920576298456285849873731 14880864447684428774810597)
            ·
              refine ⟨2790162083940830395276987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14880864447684428774810597 2790162083940830395276987)
              ·
                refine ⟨4185243125911245592915481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2790162083940830395276987 4185243125911245592915481)
                ·
                  refine ⟨3138932344433434194686611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4185243125911245592915481 3138932344433434194686611)
                  ·
                    refine ⟨4708398516650151292029917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3138932344433434194686611 4708398516650151292029917)
                    ·
                      refine ⟨1765649443743806734511219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4708398516650151292029917 1765649443743806734511219)
                      ·
                        rfl

theorem cell23_3438590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_3438590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438590 prefixEnd_3438590 := by exact prefixLift 3438590
  have htrace : WordTrace (prefixWord ++ tailWord_3438590) baseStart_3438590 baseEnd_3438590 := by
    simpa [prefixWord, tailWord_3438590, baseEnd_3438590] using wordTrace_append hprefix tailTrace_3438590
  have hstable : (prefixWord ++ tailWord_3438590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438590).length < 2 ^ (prefixWord ++ tailWord_3438590).sum := by decide
  have hdescent : baseEnd_3438590 < baseStart_3438590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438646 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_3438646 : Nat := 118140960795 + 3438646 * 2 ^ 59
def prefixEnd_3438646 : Nat := 4983230072969 + 3 ^ 40 * 3438646 * 2
def baseEnd_3438646 : Nat := 1765678198660458515410961

theorem tailTrace_3438646 : CollatzResearch.WordTrace tailWord_3438646 prefixEnd_3438646 1765678198660458515410961 := by
  unfold tailWord_3438646
  simp only [CollatzResearch.WordTrace]
  refine ⟨7838607693773768176664987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83611815400253527217759861 7838607693773768176664987)
  ·
    refine ⟨11757911540660652264997481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7838607693773768176664987 11757911540660652264997481)
    ·
      refine ⟨8818433655495489198748111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11757911540660652264997481 8818433655495489198748111)
      ·
        refine ⟨13227650483243233798122167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8818433655495489198748111 13227650483243233798122167)
        ·
          refine ⟨19841475724864850697183251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13227650483243233798122167 19841475724864850697183251)
          ·
            refine ⟨29762213587297276045774877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19841475724864850697183251 29762213587297276045774877)
            ·
              refine ⟨11160830095236478517165579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29762213587297276045774877 11160830095236478517165579)
              ·
                refine ⟨16741245142854717775748369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11160830095236478517165579 16741245142854717775748369)
                ·
                  refine ⟨12555933857141038331811277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16741245142854717775748369 12555933857141038331811277)
                  ·
                    refine ⟨4708475196427889374429229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12555933857141038331811277 4708475196427889374429229)
                    ·
                      refine ⟨1765678198660458515410961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4708475196427889374429229 1765678198660458515410961)
                      ·
                        rfl

theorem cell23_3438646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_3438646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438646 prefixEnd_3438646 := by exact prefixLift 3438646
  have htrace : WordTrace (prefixWord ++ tailWord_3438646) baseStart_3438646 baseEnd_3438646 := by
    simpa [prefixWord, tailWord_3438646, baseEnd_3438646] using wordTrace_append hprefix tailTrace_3438646
  have hstable : (prefixWord ++ tailWord_3438646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438646).length < 2 ^ (prefixWord ++ tailWord_3438646).sum := by decide
  have hdescent : baseEnd_3438646 < baseStart_3438646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438682 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6]
def baseStart_3438682 : Nat := 118140960795 + 3438682 * 2 ^ 59
def prefixEnd_3438682 : Nat := 4983230072969 + 3 ^ 40 * 3438682 * 2
def baseEnd_3438682 : Nat := 1765696683964020374560795

theorem tailTrace_3438682 : CollatzResearch.WordTrace tailWord_3438682 prefixEnd_3438682 1765696683964020374560795 := by
  unfold tailWord_3438682
  simp only [CollatzResearch.WordTrace]
  refine ⟨31354759032062467243737575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83612690752166579316633533 31354759032062467243737575)
  ·
    refine ⟨47032138548093700865606363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31354759032062467243737575 47032138548093700865606363)
    ·
      refine ⟨70548207822140551298409545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47032138548093700865606363 70548207822140551298409545)
      ·
        refine ⟨52911155866605413473807159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70548207822140551298409545 52911155866605413473807159)
        ·
          refine ⟨79366733799908120210710739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52911155866605413473807159 79366733799908120210710739)
          ·
            refine ⟨119050100699862180316066109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79366733799908120210710739 119050100699862180316066109)
            ·
              refine ⟨44643787762448317618524791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119050100699862180316066109 44643787762448317618524791)
              ·
                refine ⟨66965681643672476427787187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44643787762448317618524791 66965681643672476427787187)
                ·
                  refine ⟨100448522465508714641680781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66965681643672476427787187 100448522465508714641680781)
                  ·
                    refine ⟨37668195924565767990630293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100448522465508714641680781 37668195924565767990630293)
                    ·
                      refine ⟨1765696683964020374560795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37668195924565767990630293 1765696683964020374560795)
                      ·
                        rfl

theorem cell23_3438682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_3438682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438682 prefixEnd_3438682 := by exact prefixLift 3438682
  have htrace : WordTrace (prefixWord ++ tailWord_3438682) baseStart_3438682 baseEnd_3438682 := by
    simpa [prefixWord, tailWord_3438682, baseEnd_3438682] using wordTrace_append hprefix tailTrace_3438682
  have hstable : (prefixWord ++ tailWord_3438682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438682).length < 2 ^ (prefixWord ++ tailWord_3438682).sum := by decide
  have hdescent : baseEnd_3438682 < baseStart_3438682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438689 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 4, 2, 3]
def baseStart_3438689 : Nat := 118140960795 + 3438689 * 2 ^ 59
def prefixEnd_3438689 : Nat := 4983230072969 + 3 ^ 40 * 3438689 * 2
def baseEnd_3438689 : Nat := 1765700278328601847173263

theorem tailTrace_3438689 : CollatzResearch.WordTrace tailWord_3438689 prefixEnd_3438689 1765700278328601847173263 := by
  unfold tailWord_3438689
  simp only [CollatzResearch.WordTrace]
  refine ⟨125419291439224509170455121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83612860959483006113636747 125419291439224509170455121)
  ·
    refine ⟨94064468579418381877841341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125419291439224509170455121 94064468579418381877841341)
    ·
      refine ⟨35274175717281893204190503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94064468579418381877841341 35274175717281893204190503)
      ·
        refine ⟨52911263575922839806285755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35274175717281893204190503 52911263575922839806285755)
        ·
          refine ⟨79366895363884259709428633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52911263575922839806285755 79366895363884259709428633)
          ·
            refine ⟨59525171522913194782071475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79366895363884259709428633 59525171522913194782071475)
            ·
              refine ⟨89287757284369792173107213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59525171522913194782071475 89287757284369792173107213)
              ·
                refine ⟨33482908981638672064915205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89287757284369792173107213 33482908981638672064915205)
                ·
                  refine ⟨6278045434057251012171601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33482908981638672064915205 6278045434057251012171601)
                  ·
                    refine ⟨4708534075542938259128701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6278045434057251012171601 4708534075542938259128701)
                    ·
                      refine ⟨1765700278328601847173263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4708534075542938259128701 1765700278328601847173263)
                      ·
                        rfl

theorem cell23_3438689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_3438689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438689 prefixEnd_3438689 := by exact prefixLift 3438689
  have htrace : WordTrace (prefixWord ++ tailWord_3438689) baseStart_3438689 baseEnd_3438689 := by
    simpa [prefixWord, tailWord_3438689, baseEnd_3438689] using wordTrace_append hprefix tailTrace_3438689
  have hstable : (prefixWord ++ tailWord_3438689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438689).length < 2 ^ (prefixWord ++ tailWord_3438689).sum := by decide
  have hdescent : baseEnd_3438689 < baseStart_3438689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438712 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 3, 2, 6]
def baseStart_3438712 : Nat := 118140960795 + 3438712 * 2 ^ 59
def prefixEnd_3438712 : Nat := 4983230072969 + 3 ^ 40 * 3438712 * 2
def baseEnd_3438712 : Nat := 1765712088383655257185657

theorem tailTrace_3438712 : CollatzResearch.WordTrace tailWord_3438712 prefixEnd_3438712 1765712088383655257185657 := by
  unfold tailWord_3438712
  simp only [CollatzResearch.WordTrace]
  refine ⟨62710065159070592049271195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83613420212094122732361593 62710065159070592049271195)
  ·
    refine ⟨94065097738605888073906793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62710065159070592049271195 94065097738605888073906793)
    ·
      refine ⟨70548823303954416055430095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94065097738605888073906793 70548823303954416055430095)
      ·
        refine ⟨105823234955931624083145143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70548823303954416055430095 105823234955931624083145143)
        ·
          refine ⟨158734852433897436124717715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105823234955931624083145143 158734852433897436124717715)
          ·
            refine ⟨238102278650846154187076573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158734852433897436124717715 238102278650846154187076573)
            ·
              refine ⟨89288354494067307820153715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238102278650846154187076573 89288354494067307820153715)
              ·
                refine ⟨133932531741100961730230573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89288354494067307820153715 133932531741100961730230573)
                ·
                  refine ⟨50224699402912860648836465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133932531741100961730230573 50224699402912860648836465)
                  ·
                    refine ⟨37668524552184645486627349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50224699402912860648836465 37668524552184645486627349)
                    ·
                      refine ⟨1765712088383655257185657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37668524552184645486627349 1765712088383655257185657)
                      ·
                        rfl

theorem cell23_3438712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_3438712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438712 prefixEnd_3438712 := by exact prefixLift 3438712
  have htrace : WordTrace (prefixWord ++ tailWord_3438712) baseStart_3438712 baseEnd_3438712 := by
    simpa [prefixWord, tailWord_3438712, baseEnd_3438712] using wordTrace_append hprefix tailTrace_3438712
  have hstable : (prefixWord ++ tailWord_3438712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438712).length < 2 ^ (prefixWord ++ tailWord_3438712).sum := by decide
  have hdescent : baseEnd_3438712 < baseStart_3438712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438730 : List Nat := [3, 1, 2, 3, 1, 4, 1, 3, 1, 4]
def baseStart_3438730 : Nat := 118140960795 + 3438730 * 2 ^ 59
def prefixEnd_3438730 : Nat := 4983230072969 + 3 ^ 40 * 3438730 * 2
def baseEnd_3438730 : Nat := 588573777011812062253525

theorem tailTrace_3438730 : CollatzResearch.WordTrace tailWord_3438730 prefixEnd_3438730 588573777011812062253525 := by
  unfold tailWord_3438730
  simp only [CollatzResearch.WordTrace]
  refine ⟨31355196708018993293174411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83613857888050648781798429 31355196708018993293174411)
  ·
    refine ⟨47032795062028489939761617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31355196708018993293174411 47032795062028489939761617)
    ·
      refine ⟨35274596296521367454821213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47032795062028489939761617 35274596296521367454821213)
      ·
        refine ⟨13227973611195512795557955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35274596296521367454821213 13227973611195512795557955)
        ·
          refine ⟨19841960416793269193336933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13227973611195512795557955 19841960416793269193336933)
          ·
            refine ⟨3720367578148737973750675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19841960416793269193336933 3720367578148737973750675)
            ·
              refine ⟨5580551367223106960626013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3720367578148737973750675 5580551367223106960626013)
              ·
                refine ⟨2092706762708665110234755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5580551367223106960626013 2092706762708665110234755)
                ·
                  refine ⟨3139060144062997665352133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2092706762708665110234755 3139060144062997665352133)
                  ·
                    refine ⟨588573777011812062253525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3139060144062997665352133 588573777011812062253525)
                    ·
                      rfl

theorem cell23_3438730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_3438730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438730 prefixEnd_3438730 := by exact prefixLift 3438730
  have htrace : WordTrace (prefixWord ++ tailWord_3438730) baseStart_3438730 baseEnd_3438730 := by
    simpa [prefixWord, tailWord_3438730, baseEnd_3438730] using wordTrace_append hprefix tailTrace_3438730
  have hstable : (prefixWord ++ tailWord_3438730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438730).length < 2 ^ (prefixWord ++ tailWord_3438730).sum := by decide
  have hdescent : baseEnd_3438730 < baseStart_3438730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438740 : List Nat := [2, 4, 2, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_3438740 : Nat := 118140960795 + 3438740 * 2 ^ 59
def prefixEnd_3438740 : Nat := 4983230072969 + 3 ^ 40 * 3438740 * 2
def baseEnd_3438740 : Nat := 1765726465841981147635529

theorem tailTrace_3438740 : CollatzResearch.WordTrace tailWord_3438740 prefixEnd_3438740 1765726465841981147635529 := by
  unfold tailWord_3438740
  simp only [CollatzResearch.WordTrace]
  refine ⟨62710575781019872440280837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83614101041359829920374449 62710575781019872440280837)
  ·
    refine ⟨11758232958941226082552657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62710575781019872440280837 11758232958941226082552657)
    ·
      refine ⟨8818674719205919561914493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11758232958941226082552657 8818674719205919561914493)
      ·
        refine ⟨3307003019702219835717935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8818674719205919561914493 3307003019702219835717935)
        ·
          refine ⟨4960504529553329753576903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3307003019702219835717935 4960504529553329753576903)
          ·
            refine ⟨7440756794329994630365355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4960504529553329753576903 7440756794329994630365355)
            ·
              refine ⟨11161135191494991945548033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7440756794329994630365355 11161135191494991945548033)
              ·
                refine ⟨8370851393621243959161025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11161135191494991945548033 8370851393621243959161025)
                ·
                  refine ⟨6278138545215932969370769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8370851393621243959161025 6278138545215932969370769)
                  ·
                    refine ⟨4708603908911949727028077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6278138545215932969370769 4708603908911949727028077)
                    ·
                      refine ⟨1765726465841981147635529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4708603908911949727028077 1765726465841981147635529)
                      ·
                        rfl

theorem cell23_3438740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_3438740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438740 prefixEnd_3438740 := by exact prefixLift 3438740
  have htrace : WordTrace (prefixWord ++ tailWord_3438740) baseStart_3438740 baseEnd_3438740 := by
    simpa [prefixWord, tailWord_3438740, baseEnd_3438740] using wordTrace_append hprefix tailTrace_3438740
  have hstable : (prefixWord ++ tailWord_3438740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438740).length < 2 ^ (prefixWord ++ tailWord_3438740).sum := by decide
  have hdescent : baseEnd_3438740 < baseStart_3438740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438753 : List Nat := [1, 2, 3, 3, 1, 2, 3, 1, 3, 1, 3]
def baseStart_3438753 : Nat := 118140960795 + 3438753 * 2 ^ 59
def prefixEnd_3438753 : Nat := 4983230072969 + 3 ^ 40 * 3438753 * 2
def baseEnd_3438753 : Nat := 1765733141090489596772969

theorem tailTrace_3438753 : CollatzResearch.WordTrace tailWord_3438753 prefixEnd_3438753 1765733141090489596772969 := by
  unfold tailWord_3438753
  simp only [CollatzResearch.WordTrace]
  refine ⟨125421625710992648100784913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83614417140661765400523275 125421625710992648100784913)
  ·
    refine ⟨94066219283244486075588685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125421625710992648100784913 94066219283244486075588685)
    ·
      refine ⟨35274832231216682278345757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94066219283244486075588685 35274832231216682278345757)
      ·
        refine ⟨13228062086706255854379659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35274832231216682278345757 13228062086706255854379659)
        ·
          refine ⟨19842093130059383781569489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13228062086706255854379659 19842093130059383781569489)
          ·
            refine ⟨14881569847544537836177117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19842093130059383781569489 14881569847544537836177117)
            ·
              refine ⟨5580588692829201688566419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14881569847544537836177117 5580588692829201688566419)
              ·
                refine ⟨8370883039243802532849629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5580588692829201688566419 8370883039243802532849629)
                ·
                  refine ⟨3139081139716425949818611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8370883039243802532849629 3139081139716425949818611)
                  ·
                    refine ⟨4708621709574638924727917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3139081139716425949818611 4708621709574638924727917)
                    ·
                      refine ⟨1765733141090489596772969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4708621709574638924727917 1765733141090489596772969)
                      ·
                        rfl

theorem cell23_3438753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_3438753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438753 prefixEnd_3438753 := by exact prefixLift 3438753
  have htrace : WordTrace (prefixWord ++ tailWord_3438753) baseStart_3438753 baseEnd_3438753 := by
    simpa [prefixWord, tailWord_3438753, baseEnd_3438753] using wordTrace_append hprefix tailTrace_3438753
  have hstable : (prefixWord ++ tailWord_3438753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438753).length < 2 ^ (prefixWord ++ tailWord_3438753).sum := by decide
  have hdescent : baseEnd_3438753 < baseStart_3438753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438773 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 3, 5]
def baseStart_3438773 : Nat := 118140960795 + 3438773 * 2 ^ 59
def prefixEnd_3438773 : Nat := 4983230072969 + 3 ^ 40 * 3438773 * 2
def baseEnd_3438773 : Nat := 588581136901193172840959

theorem tailTrace_3438773 : CollatzResearch.WordTrace tailWord_3438773 prefixEnd_3438773 588581136901193172840959 := by
  unfold tailWord_3438773
  simp only [CollatzResearch.WordTrace]
  refine ⟨125422355170920191516512973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83614903447280127677675315 125422355170920191516512973)
  ·
    refine ⟨47033383189095071818692365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125422355170920191516512973 47033383189095071818692365)
    ·
      refine ⟨17637518695910651932009637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47033383189095071818692365 17637518695910651932009637)
      ·
        refine ⟨3307034755483247237251807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17637518695910651932009637 3307034755483247237251807)
        ·
          refine ⟨4960552133224870855877711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3307034755483247237251807 4960552133224870855877711)
          ·
            refine ⟨7440828199837306283816567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4960552133224870855877711 7440828199837306283816567)
            ·
              refine ⟨11161242299755959425724851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7440828199837306283816567 11161242299755959425724851)
              ·
                refine ⟨16741863449633939138587277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11161242299755959425724851 16741863449633939138587277)
                ·
                  refine ⟨6278198793612727176970229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16741863449633939138587277 6278198793612727176970229)
                  ·
                    refine ⟨588581136901193172840959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6278198793612727176970229 588581136901193172840959)
                    ·
                      rfl

theorem cell23_3438773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_3438773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438773 prefixEnd_3438773 := by exact prefixLift 3438773
  have htrace : WordTrace (prefixWord ++ tailWord_3438773) baseStart_3438773 baseEnd_3438773 := by
    simpa [prefixWord, tailWord_3438773, baseEnd_3438773] using wordTrace_append hprefix tailTrace_3438773
  have hstable : (prefixWord ++ tailWord_3438773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438773).length < 2 ^ (prefixWord ++ tailWord_3438773).sum := by decide
  have hdescent : baseEnd_3438773 < baseStart_3438773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438780 : List Nat := [2, 2, 2, 3, 3, 1, 2, 1, 2, 3, 2]
def baseStart_3438780 : Nat := 118140960795 + 3438780 * 2 ^ 59
def prefixEnd_3438780 : Nat := 4983230072969 + 3 ^ 40 * 3438780 * 2
def baseEnd_3438780 : Nat := 1765747005068160991135345

theorem tailTrace_3438780 : CollatzResearch.WordTrace tailWord_3438780 prefixEnd_3438780 1765747005068160991135345 := by
  unfold tailWord_3438780
  simp only [CollatzResearch.WordTrace]
  refine ⟨62711305240947415856008897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83615073654596554474678529 62711305240947415856008897)
  ·
    refine ⟨47033478930710561892006673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62711305240947415856008897 47033478930710561892006673)
    ·
      refine ⟨35275109198032921419005005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47033478930710561892006673 35275109198032921419005005)
      ·
        refine ⟨13228165949262345532126877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35275109198032921419005005 13228165949262345532126877)
        ·
          refine ⟨4960562230973379574547579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13228165949262345532126877 4960562230973379574547579)
          ·
            refine ⟨7440843346460069361821369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4960562230973379574547579 7440843346460069361821369)
            ·
              refine ⟨5580632509845052021366027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7440843346460069361821369 5580632509845052021366027)
              ·
                refine ⟨8370948764767578032049041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5580632509845052021366027 8370948764767578032049041)
                ·
                  refine ⟨6278211573575683524036781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8370948764767578032049041 6278211573575683524036781)
                  ·
                    refine ⟨2354329340090881321513793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6278211573575683524036781 2354329340090881321513793)
                    ·
                      refine ⟨1765747005068160991135345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2354329340090881321513793 1765747005068160991135345)
                      ·
                        rfl

theorem cell23_3438780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_3438780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438780 prefixEnd_3438780 := by exact prefixLift 3438780
  have htrace : WordTrace (prefixWord ++ tailWord_3438780) baseStart_3438780 baseEnd_3438780 := by
    simpa [prefixWord, tailWord_3438780, baseEnd_3438780] using wordTrace_append hprefix tailTrace_3438780
  have hstable : (prefixWord ++ tailWord_3438780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438780).length < 2 ^ (prefixWord ++ tailWord_3438780).sum := by decide
  have hdescent : baseEnd_3438780 < baseStart_3438780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438789 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 3, 2, 4]
def baseStart_3438789 : Nat := 118140960795 + 3438789 * 2 ^ 59
def prefixEnd_3438789 : Nat := 4983230072969 + 3 ^ 40 * 3438789 * 2
def baseEnd_3438789 : Nat := 1765751626394051455922803

theorem tailTrace_3438789 : CollatzResearch.WordTrace tailWord_3438789 prefixEnd_3438789 1765751626394051455922803 := by
  unfold tailWord_3438789
  simp only [CollatzResearch.WordTrace]
  refine ⟨125422938738862226249095421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83615292492574817499396947 125422938738862226249095421)
  ·
    refine ⟨47033602027073334843410783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125422938738862226249095421 47033602027073334843410783)
    ·
      refine ⟨70550403040610002265116175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47033602027073334843410783 70550403040610002265116175)
      ·
        refine ⟨105825604560915003397674263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70550403040610002265116175 105825604560915003397674263)
        ·
          refine ⟨158738406841372505096511395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105825604560915003397674263 158738406841372505096511395)
          ·
            refine ⟨238107610262058757644767093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158738406841372505096511395 238107610262058757644767093)
            ·
              refine ⟨22322588462068008529196915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 238107610262058757644767093 22322588462068008529196915)
              ·
                refine ⟨33483882693102012793795373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22322588462068008529196915 33483882693102012793795373)
                ·
                  refine ⟨12556456009913254797673265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33483882693102012793795373 12556456009913254797673265)
                  ·
                    refine ⟨9417342007434941098254949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12556456009913254797673265 9417342007434941098254949)
                    ·
                      refine ⟨1765751626394051455922803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9417342007434941098254949 1765751626394051455922803)
                      ·
                        rfl

theorem cell23_3438789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_3438789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438789 prefixEnd_3438789 := by exact prefixLift 3438789
  have htrace : WordTrace (prefixWord ++ tailWord_3438789) baseStart_3438789 baseEnd_3438789 := by
    simpa [prefixWord, tailWord_3438789, baseEnd_3438789] using wordTrace_append hprefix tailTrace_3438789
  have hstable : (prefixWord ++ tailWord_3438789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438789).length < 2 ^ (prefixWord ++ tailWord_3438789).sum := by decide
  have hdescent : baseEnd_3438789 < baseStart_3438789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438813 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_3438813 : Nat := 118140960795 + 3438813 * 2 ^ 59
def prefixEnd_3438813 : Nat := 4983230072969 + 3 ^ 40 * 3438813 * 2
def baseEnd_3438813 : Nat := 1765763949929759362022693

theorem tailTrace_3438813 : CollatzResearch.WordTrace tailWord_3438813 prefixEnd_3438813 1765763949929759362022693 := by
  unfold tailWord_3438813
  simp only [CollatzResearch.WordTrace]
  refine ⟨125423814090775278347969093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83615876060516852231979395 125423814090775278347969093)
  ·
    refine ⟨23516965142020364690244205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125423814090775278347969093 23516965142020364690244205)
    ·
      refine ⟨8818861928257636758841577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23516965142020364690244205 8818861928257636758841577)
      ·
        refine ⟨6614146446193227569131183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8818861928257636758841577 6614146446193227569131183)
        ·
          refine ⟨9921219669289841353696775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6614146446193227569131183 9921219669289841353696775)
          ·
            refine ⟨14881829503934762030545163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9921219669289841353696775 14881829503934762030545163)
            ·
              refine ⟨22322744255902143045817745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14881829503934762030545163 22322744255902143045817745)
              ·
                refine ⟨16742058191926607284363309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22322744255902143045817745 16742058191926607284363309)
                ·
                  refine ⟨6278271821972477731636241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16742058191926607284363309 6278271821972477731636241)
                  ·
                    refine ⟨4708703866479358298727181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6278271821972477731636241 4708703866479358298727181)
                    ·
                      refine ⟨1765763949929759362022693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4708703866479358298727181 1765763949929759362022693)
                      ·
                        rfl

theorem cell23_3438813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_3438813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438813 prefixEnd_3438813 := by exact prefixLift 3438813
  have htrace : WordTrace (prefixWord ++ tailWord_3438813) baseStart_3438813 baseEnd_3438813 := by
    simpa [prefixWord, tailWord_3438813, baseEnd_3438813] using wordTrace_append hprefix tailTrace_3438813
  have hstable : (prefixWord ++ tailWord_3438813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438813).length < 2 ^ (prefixWord ++ tailWord_3438813).sum := by decide
  have hdescent : baseEnd_3438813 < baseStart_3438813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438823 : List Nat := [1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_3438823 : Nat := 118140960795 + 3438823 * 2 ^ 59
def prefixEnd_3438823 : Nat := 4983230072969 + 3 ^ 40 * 3438823 * 2
def baseEnd_3438823 : Nat := 1765769084736304322897647

theorem tailTrace_3438823 : CollatzResearch.WordTrace tailWord_3438823 prefixEnd_3438823 1765769084736304322897647 := by
  unfold tailWord_3438823
  simp only [CollatzResearch.WordTrace]
  refine ⟨125424178820739050055833123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83616119213826033370555415 125424178820739050055833123)
  ·
    refine ⟨188136268231108575083749685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125424178820739050055833123 188136268231108575083749685)
    ·
      refine ⟨17637775146666428914101533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188136268231108575083749685 17637775146666428914101533)
      ·
        refine ⟨6614165679999910842788075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17637775146666428914101533 6614165679999910842788075)
        ·
          refine ⟨9921248519999866264182113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6614165679999910842788075 9921248519999866264182113)
          ·
            refine ⟨7440936389999899698136585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9921248519999866264182113 7440936389999899698136585)
            ·
              refine ⟨5580702292499924773602439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7440936389999899698136585 5580702292499924773602439)
              ·
                refine ⟨8371053438749887160403659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5580702292499924773602439 8371053438749887160403659)
                ·
                  refine ⟨12556580158124830740605489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8371053438749887160403659 12556580158124830740605489)
                  ·
                    refine ⟨9417435118593623055454117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12556580158124830740605489 9417435118593623055454117)
                    ·
                      refine ⟨1765769084736304322897647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9417435118593623055454117 1765769084736304322897647)
                      ·
                        rfl

theorem cell23_3438823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_3438823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438823 prefixEnd_3438823 := by exact prefixLift 3438823
  have htrace : WordTrace (prefixWord ++ tailWord_3438823) baseStart_3438823 baseEnd_3438823 := by
    simpa [prefixWord, tailWord_3438823, baseEnd_3438823] using wordTrace_append hprefix tailTrace_3438823
  have hstable : (prefixWord ++ tailWord_3438823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438823).length < 2 ^ (prefixWord ++ tailWord_3438823).sum := by decide
  have hdescent : baseEnd_3438823 < baseStart_3438823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438859 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 4, 6]
def baseStart_3438859 : Nat := 118140960795 + 3438859 * 2 ^ 59
def prefixEnd_3438859 : Nat := 4983230072969 + 3 ^ 40 * 3438859 * 2
def baseEnd_3438859 : Nat := 588595856679955394015827

theorem tailTrace_3438859 : CollatzResearch.WordTrace tailWord_3438859 prefixEnd_3438859 588595856679955394015827 := by
  unfold tailWord_3438859
  simp only [CollatzResearch.WordTrace]
  refine ⟨125425491848608628204143631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83616994565739085469429087 125425491848608628204143631)
  ·
    refine ⟨188138237772912942306215447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125425491848608628204143631 188138237772912942306215447)
    ·
      refine ⟨282207356659369413459323171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188138237772912942306215447 282207356659369413459323171)
      ·
        refine ⟨423311034989054120188984757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282207356659369413459323171 423311034989054120188984757)
        ·
          refine ⟨39685409530223823767717321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 423311034989054120188984757 39685409530223823767717321)
          ·
            refine ⟨29764057147667867825787991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39685409530223823767717321 29764057147667867825787991)
            ·
              refine ⟨44646085721501801738681987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29764057147667867825787991 44646085721501801738681987)
              ·
                refine ⟨66969128582252702608022981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44646085721501801738681987 66969128582252702608022981)
                ·
                  refine ⟨12556711609172381739004309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66969128582252702608022981 12556711609172381739004309)
                  ·
                    refine ⟨588595856679955394015827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12556711609172381739004309 588595856679955394015827)
                    ·
                      rfl

theorem cell23_3438859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 6].length) (baseStart_3438859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438859 prefixEnd_3438859 := by exact prefixLift 3438859
  have htrace : WordTrace (prefixWord ++ tailWord_3438859) baseStart_3438859 baseEnd_3438859 := by
    simpa [prefixWord, tailWord_3438859, baseEnd_3438859] using wordTrace_append hprefix tailTrace_3438859
  have hstable : (prefixWord ++ tailWord_3438859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438859).length < 2 ^ (prefixWord ++ tailWord_3438859).sum := by decide
  have hdescent : baseEnd_3438859 < baseStart_3438859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438877 : List Nat := [1, 4, 2, 3, 3, 1, 1, 1, 1, 3, 3]
def baseStart_3438877 : Nat := 118140960795 + 3438877 * 2 ^ 59
def prefixEnd_3438877 : Nat := 4983230072969 + 3 ^ 40 * 3438877 * 2
def baseEnd_3438877 : Nat := 1765796812691647111622399

theorem tailTrace_3438877 : CollatzResearch.WordTrace tailWord_3438877 prefixEnd_3438877 1765796812691647111622399 := by
  unfold tailWord_3438877
  simp only [CollatzResearch.WordTrace]
  refine ⟨125426148362543417278298885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83617432241695611518865923 125426148362543417278298885)
  ·
    refine ⟨23517402817976890739681041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125426148362543417278298885 23517402817976890739681041)
    ·
      refine ⟨17638052113482668054760781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23517402817976890739681041 17638052113482668054760781)
      ·
        refine ⟨6614269542556000520535293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17638052113482668054760781 6614269542556000520535293)
        ·
          refine ⟨2480351078458500195200735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6614269542556000520535293 2480351078458500195200735)
          ·
            refine ⟨3720526617687750292801103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2480351078458500195200735 3720526617687750292801103)
            ·
              refine ⟨5580789926531625439201655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3720526617687750292801103 5580789926531625439201655)
              ·
                refine ⟨8371184889797438158802483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5580789926531625439201655 8371184889797438158802483)
                ·
                  refine ⟨12556777334696157238203725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8371184889797438158802483 12556777334696157238203725)
                  ·
                    refine ⟨4708791500511058964326397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12556777334696157238203725 4708791500511058964326397)
                    ·
                      refine ⟨1765796812691647111622399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4708791500511058964326397 1765796812691647111622399)
                      ·
                        rfl

theorem cell23_3438877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_3438877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438877 prefixEnd_3438877 := by exact prefixLift 3438877
  have htrace : WordTrace (prefixWord ++ tailWord_3438877) baseStart_3438877 baseEnd_3438877 := by
    simpa [prefixWord, tailWord_3438877, baseEnd_3438877] using wordTrace_append hprefix tailTrace_3438877
  have hstable : (prefixWord ++ tailWord_3438877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438877).length < 2 ^ (prefixWord ++ tailWord_3438877).sum := by decide
  have hdescent : baseEnd_3438877 < baseStart_3438877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438973 : List Nat := [1, 4, 1, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_3438973 : Nat := 118140960795 + 3438973 * 2 ^ 59
def prefixEnd_3438973 : Nat := 4983230072969 + 3 ^ 40 * 3438973 * 2
def baseEnd_3438973 : Nat := 1765846106834478736021957

theorem tailTrace_3438973 : CollatzResearch.WordTrace tailWord_3438973 prefixEnd_3438973 1765846106834478736021957 := by
  unfold tailWord_3438973
  simp only [CollatzResearch.WordTrace]
  refine ⟨125429649770195625673793573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83619766513463750449195715 125429649770195625673793573)
  ·
    refine ⟨23518059331911679813836295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125429649770195625673793573 23518059331911679813836295)
    ·
      refine ⟨35277088997867519720754443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23518059331911679813836295 35277088997867519720754443)
      ·
        refine ⟨52915633496801279581131665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35277088997867519720754443 52915633496801279581131665)
        ·
          refine ⟨39686725122600959685848749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52915633496801279581131665 39686725122600959685848749)
          ·
            refine ⟨14882521920975359882193281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39686725122600959685848749 14882521920975359882193281)
            ·
              refine ⟨11161891440731519911644961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14882521920975359882193281 11161891440731519911644961)
              ·
                refine ⟨8371418580548639933733721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11161891440731519911644961 8371418580548639933733721)
                ·
                  refine ⟨6278563935411479950300291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8371418580548639933733721 6278563935411479950300291)
                  ·
                    refine ⟨9417845903117219925450437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6278563935411479950300291 9417845903117219925450437)
                    ·
                      refine ⟨1765846106834478736021957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9417845903117219925450437 1765846106834478736021957)
                      ·
                        rfl

theorem cell23_3438973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_3438973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438973 prefixEnd_3438973 := by exact prefixLift 3438973
  have htrace : WordTrace (prefixWord ++ tailWord_3438973) baseStart_3438973 baseEnd_3438973 := by
    simpa [prefixWord, tailWord_3438973, baseEnd_3438973] using wordTrace_append hprefix tailTrace_3438973
  have hstable : (prefixWord ++ tailWord_3438973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438973).length < 2 ^ (prefixWord ++ tailWord_3438973).sum := by decide
  have hdescent : baseEnd_3438973 < baseStart_3438973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438976 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 3]
def baseStart_3438976 : Nat := 118140960795 + 3438976 * 2 ^ 59
def prefixEnd_3438976 : Nat := 4983230072969 + 3 ^ 40 * 3438976 * 2
def baseEnd_3438976 : Nat := 1765847647276442224284443

theorem tailTrace_3438976 : CollatzResearch.WordTrace tailWord_3438976 prefixEnd_3438976 1765847647276442224284443 := by
  unfold tailWord_3438976
  simp only [CollatzResearch.WordTrace]
  refine ⟨62714879594592378593076391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83619839459456504790768521 62714879594592378593076391)
  ·
    refine ⟨94072319391888567889614587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62714879594592378593076391 94072319391888567889614587)
    ·
      refine ⟨141108479087832851834421881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94072319391888567889614587 141108479087832851834421881)
      ·
        refine ⟨105831359315874638875816411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141108479087832851834421881 105831359315874638875816411)
        ·
          refine ⟨158747038973811958313724617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105831359315874638875816411 158747038973811958313724617)
          ·
            refine ⟨119060279230358968735293463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158747038973811958313724617 119060279230358968735293463)
            ·
              refine ⟨178590418845538453102940195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119060279230358968735293463 178590418845538453102940195)
              ·
                refine ⟨267885628268307679654410293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178590418845538453102940195 267885628268307679654410293)
                ·
                  refine ⟨25114277650153844967600965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 267885628268307679654410293 25114277650153844967600965)
                  ·
                    refine ⟨4708927059403845931425181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25114277650153844967600965 4708927059403845931425181)
                    ·
                      refine ⟨1765847647276442224284443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4708927059403845931425181 1765847647276442224284443)
                      ·
                        rfl

theorem cell23_3438976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_3438976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438976 prefixEnd_3438976 := by exact prefixLift 3438976
  have htrace : WordTrace (prefixWord ++ tailWord_3438976) baseStart_3438976 baseEnd_3438976 := by
    simpa [prefixWord, tailWord_3438976, baseEnd_3438976] using wordTrace_append hprefix tailTrace_3438976
  have hstable : (prefixWord ++ tailWord_3438976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438976).length < 2 ^ (prefixWord ++ tailWord_3438976).sum := by decide
  have hdescent : baseEnd_3438976 < baseStart_3438976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438983 : List Nat := [1, 1, 4, 2, 2, 1, 2, 3, 3, 4]
def baseStart_3438983 : Nat := 118140960795 + 3438983 * 2 ^ 59
def prefixEnd_3438983 : Nat := 4983230072969 + 3 ^ 40 * 3438983 * 2
def baseEnd_3438983 : Nat := 588617080547007898965637

theorem tailTrace_3438983 : CollatzResearch.WordTrace tailWord_3438983 prefixEnd_3438983 588617080547007898965637 := by
  unfold tailWord_3438983
  simp only [CollatzResearch.WordTrace]
  refine ⟨125430014500159397381657603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83620009666772931587771735 125430014500159397381657603)
  ·
    refine ⟨188145021750239096072486405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125430014500159397381657603 188145021750239096072486405)
    ·
      refine ⟨35277191578169830513591201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188145021750239096072486405 35277191578169830513591201)
      ·
        refine ⟨26457893683627372885193401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35277191578169830513591201 26457893683627372885193401)
        ·
          refine ⟨19843420262720529663895051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26457893683627372885193401 19843420262720529663895051)
          ·
            refine ⟨29765130394080794495842577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19843420262720529663895051 29765130394080794495842577)
            ·
              refine ⟨22323847795560595871881933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29765130394080794495842577 22323847795560595871881933)
              ·
                refine ⟨8371442923335223451955725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22323847795560595871881933 8371442923335223451955725)
                ·
                  refine ⟨3139291096250708794483397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8371442923335223451955725 3139291096250708794483397)
                  ·
                    refine ⟨588617080547007898965637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3139291096250708794483397 588617080547007898965637)
                    ·
                      rfl

theorem cell23_3438983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_3438983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438983 prefixEnd_3438983 := by exact prefixLift 3438983
  have htrace : WordTrace (prefixWord ++ tailWord_3438983) baseStart_3438983 baseEnd_3438983 := by
    simpa [prefixWord, tailWord_3438983, baseEnd_3438983] using wordTrace_append hprefix tailTrace_3438983
  have hstable : (prefixWord ++ tailWord_3438983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438983).length < 2 ^ (prefixWord ++ tailWord_3438983).sum := by decide
  have hdescent : baseEnd_3438983 < baseStart_3438983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438990 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2]
def baseStart_3438990 : Nat := 118140960795 + 3438990 * 2 ^ 59
def prefixEnd_3438990 : Nat := 4983230072969 + 3 ^ 40 * 3438990 * 2
def baseEnd_3438990 : Nat := 1765854836005605169509379

theorem tailTrace_3438990 : CollatzResearch.WordTrace tailWord_3438990 prefixEnd_3438990 1765854836005605169509379 := by
  unfold tailWord_3438990
  simp only [CollatzResearch.WordTrace]
  refine ⟨15678783726391754697145303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83620179874089358384774949 15678783726391754697145303)
  ·
    refine ⟨23518175589587632045717955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15678783726391754697145303 23518175589587632045717955)
    ·
      refine ⟨35277263384381448068576933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23518175589587632045717955 35277263384381448068576933)
      ·
        refine ⟨6614486884571521512858175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35277263384381448068576933 6614486884571521512858175)
        ·
          refine ⟨9921730326857282269287263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6614486884571521512858175 9921730326857282269287263)
          ·
            refine ⟨14882595490285923403930895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9921730326857282269287263 14882595490285923403930895)
            ·
              refine ⟨22323893235428885105896343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14882595490285923403930895 22323893235428885105896343)
              ·
                refine ⟨33485839853143327658844515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22323893235428885105896343 33485839853143327658844515)
                ·
                  refine ⟨50228759779714991488266773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33485839853143327658844515 50228759779714991488266773)
                  ·
                    refine ⟨2354473114674140226012505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50228759779714991488266773 2354473114674140226012505)
                    ·
                      refine ⟨1765854836005605169509379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2354473114674140226012505 1765854836005605169509379)
                      ·
                        rfl

theorem cell23_3438990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_3438990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3438990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3438990 prefixEnd_3438990 := by exact prefixLift 3438990
  have htrace : WordTrace (prefixWord ++ tailWord_3438990) baseStart_3438990 baseEnd_3438990 := by
    simpa [prefixWord, tailWord_3438990, baseEnd_3438990] using wordTrace_append hprefix tailTrace_3438990
  have hstable : (prefixWord ++ tailWord_3438990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438990).length < 2 ^ (prefixWord ++ tailWord_3438990).sum := by decide
  have hdescent : baseEnd_3438990 < baseStart_3438990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439000 : List Nat := [2, 1, 2, 5, 1, 2, 1, 2, 3, 4]
def baseStart_3439000 : Nat := 118140960795 + 3439000 * 2 ^ 59
def prefixEnd_3439000 : Nat := 4983230072969 + 3 ^ 40 * 3439000 * 2
def baseEnd_3439000 : Nat := 588619990270716710128111

theorem tailTrace_3439000 : CollatzResearch.WordTrace tailWord_3439000 prefixEnd_3439000 588619990270716710128111 := by
  unfold tailWord_3439000
  simp only [CollatzResearch.WordTrace]
  refine ⟨62715317270548904642513227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83620423027398539523350969 62715317270548904642513227)
  ·
    refine ⟨94072975905823356963769841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62715317270548904642513227 94072975905823356963769841)
    ·
      refine ⟨70554731929367517722827381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94072975905823356963769841 70554731929367517722827381)
      ·
        refine ⟨6614506118378204786515067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70554731929367517722827381 6614506118378204786515067)
        ·
          refine ⟨9921759177567307179772601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6614506118378204786515067 9921759177567307179772601)
          ·
            refine ⟨7441319383175480384829451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9921759177567307179772601 7441319383175480384829451)
            ·
              refine ⟨11161979074763220577244177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7441319383175480384829451 11161979074763220577244177)
              ·
                refine ⟨8371484306072415432933133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11161979074763220577244177 8371484306072415432933133)
                ·
                  refine ⟨3139306614777155787349925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8371484306072415432933133 3139306614777155787349925)
                  ·
                    refine ⟨588619990270716710128111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3139306614777155787349925 588619990270716710128111)
                    ·
                      rfl

theorem cell23_3439000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_3439000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439000 prefixEnd_3439000 := by exact prefixLift 3439000
  have htrace : WordTrace (prefixWord ++ tailWord_3439000) baseStart_3439000 baseEnd_3439000 := by
    simpa [prefixWord, tailWord_3439000, baseEnd_3439000] using wordTrace_append hprefix tailTrace_3439000
  have hstable : (prefixWord ++ tailWord_3439000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439000).length < 2 ^ (prefixWord ++ tailWord_3439000).sum := by decide
  have hdescent : baseEnd_3439000 < baseStart_3439000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439060 : List Nat := [2, 4, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_3439060 : Nat := 118140960795 + 3439060 * 2 ^ 59
def prefixEnd_3439060 : Nat := 4983230072969 + 3 ^ 40 * 3439060 * 2
def baseEnd_3439060 : Nat := 588630259883806631878019

theorem tailTrace_3439060 : CollatzResearch.WordTrace tailWord_3439060 prefixEnd_3439060 588630259883806631878019 := by
  unfold tailWord_3439060
  simp only [CollatzResearch.WordTrace]
  refine ⟨62716411460440219766105317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83621881947253626354807089 62716411460440219766105317)
  ·
    refine ⟨11759327148832541206144747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62716411460440219766105317 11759327148832541206144747)
    ·
      refine ⟨17638990723248811809217121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11759327148832541206144747 17638990723248811809217121)
      ·
        refine ⟨13229243042436608856912841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17638990723248811809217121 13229243042436608856912841)
        ·
          refine ⟨9921932281827456642684631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13229243042436608856912841 9921932281827456642684631)
          ·
            refine ⟨14882898422741184964026947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9921932281827456642684631 14882898422741184964026947)
            ·
              refine ⟨22324347634111777446040421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14882898422741184964026947 22324347634111777446040421)
              ·
                refine ⟨4185815181395958271132579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22324347634111777446040421 4185815181395958271132579)
                ·
                  refine ⟨6278722772093937406698869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4185815181395958271132579 6278722772093937406698869)
                  ·
                    refine ⟨588630259883806631878019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6278722772093937406698869 588630259883806631878019)
                    ·
                      rfl

theorem cell23_3439060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_3439060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439060 prefixEnd_3439060 := by exact prefixLift 3439060
  have htrace : WordTrace (prefixWord ++ tailWord_3439060) baseStart_3439060 baseEnd_3439060 := by
    simpa [prefixWord, tailWord_3439060, baseEnd_3439060] using wordTrace_append hprefix tailTrace_3439060
  have hstable : (prefixWord ++ tailWord_3439060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439060).length < 2 ^ (prefixWord ++ tailWord_3439060).sum := by decide
  have hdescent : baseEnd_3439060 < baseStart_3439060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439073 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 6, 4]
def baseStart_3439073 : Nat := 118140960795 + 3439073 * 2 ^ 59
def prefixEnd_3439073 : Nat := 4983230072969 + 3 ^ 40 * 3439073 * 2
def baseEnd_3439073 : Nat := 588632484966642781590499

theorem tailTrace_3439073 : CollatzResearch.WordTrace tailWord_3439073 prefixEnd_3439073 588632484966642781590499 := by
  unfold tailWord_3439073
  simp only [CollatzResearch.WordTrace]
  refine ⟨125433297069833342752433873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83622198046555561834955915 125433297069833342752433873)
  ·
    refine ⟨94074972802375007064325405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125433297069833342752433873 94074972802375007064325405)
    ·
      refine ⟨35278114800890627649122027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94074972802375007064325405 35278114800890627649122027)
      ·
        refine ⟨52917172201335941473683041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35278114800890627649122027 52917172201335941473683041)
        ·
          refine ⟨39687879151001956105262281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52917172201335941473683041 39687879151001956105262281)
          ·
            refine ⟨29765909363251467078946711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39687879151001956105262281 29765909363251467078946711)
            ·
              refine ⟨44648864044877200618420067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29765909363251467078946711 44648864044877200618420067)
              ·
                refine ⟨66973296067315800927630101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44648864044877200618420067 66973296067315800927630101)
                ·
                  refine ⟨3139373253155428168482661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66973296067315800927630101 3139373253155428168482661)
                  ·
                    refine ⟨588632484966642781590499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3139373253155428168482661 588632484966642781590499)
                    ·
                      rfl

theorem cell23_3439073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_3439073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439073 prefixEnd_3439073 := by exact prefixLift 3439073
  have htrace : WordTrace (prefixWord ++ tailWord_3439073) baseStart_3439073 baseEnd_3439073 := by
    simpa [prefixWord, tailWord_3439073, baseEnd_3439073] using wordTrace_append hprefix tailTrace_3439073
  have hstable : (prefixWord ++ tailWord_3439073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439073).length < 2 ^ (prefixWord ++ tailWord_3439073).sum := by decide
  have hdescent : baseEnd_3439073 < baseStart_3439073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439080 : List Nat := [2, 1, 4, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_3439080 : Nat := 118140960795 + 3439080 * 2 ^ 59
def prefixEnd_3439080 : Nat := 4983230072969 + 3 ^ 40 * 3439080 * 2
def baseEnd_3439080 : Nat := 1765901049264509817383965

theorem tailTrace_3439080 : CollatzResearch.WordTrace tailWord_3439080 prefixEnd_3439080 1765901049264509817383965 := by
  unfold tailWord_3439080
  simp only [CollatzResearch.WordTrace]
  refine ⟨62716776190403991473969347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83622368253871988631959129 62716776190403991473969347)
  ·
    refine ⟨94075164285605987210954021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62716776190403991473969347 94075164285605987210954021)
    ·
      refine ⟨17639093303551122602053879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94075164285605987210954021 17639093303551122602053879)
      ·
        refine ⟨26458639955326683903080819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17639093303551122602053879 26458639955326683903080819)
        ·
          refine ⟨39687959932990025854621229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26458639955326683903080819 39687959932990025854621229)
          ·
            refine ⟨14882984974871259695482961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39687959932990025854621229 14882984974871259695482961)
            ·
              refine ⟨11162238731153444771612221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14882984974871259695482961 11162238731153444771612221)
              ·
                refine ⟨4185839524182541789354583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11162238731153444771612221 4185839524182541789354583)
                ·
                  refine ⟨6278759286273812684031875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4185839524182541789354583 6278759286273812684031875)
                  ·
                    refine ⟨9418138929410719026047813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6278759286273812684031875 9418138929410719026047813)
                    ·
                      refine ⟨1765901049264509817383965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9418138929410719026047813 1765901049264509817383965)
                      ·
                        rfl

theorem cell23_3439080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_3439080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439080 prefixEnd_3439080 := by exact prefixLift 3439080
  have htrace : WordTrace (prefixWord ++ tailWord_3439080) baseStart_3439080 baseEnd_3439080 := by
    simpa [prefixWord, tailWord_3439080, baseEnd_3439080] using wordTrace_append hprefix tailTrace_3439080
  have hstable : (prefixWord ++ tailWord_3439080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439080).length < 2 ^ (prefixWord ++ tailWord_3439080).sum := by decide
  have hdescent : baseEnd_3439080 < baseStart_3439080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439083 : List Nat := [1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 5]
def baseStart_3439083 : Nat := 118140960795 + 3439083 * 2 ^ 59
def prefixEnd_3439083 : Nat := 4983230072969 + 3 ^ 40 * 3439083 * 2
def baseEnd_3439083 : Nat := 1765902589706473305646451

theorem tailTrace_3439083 : CollatzResearch.WordTrace tailWord_3439083 prefixEnd_3439083 1765902589706473305646451 := by
  unfold tailWord_3439083
  simp only [CollatzResearch.WordTrace]
  refine ⟨125433661799797114460297903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83622441199864742973531935 125433661799797114460297903)
  ·
    refine ⟨188150492699695671690446855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125433661799797114460297903 188150492699695671690446855)
    ·
      refine ⟨282225739049543507535670283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188150492699695671690446855 282225739049543507535670283)
      ·
        refine ⟨423338608574315261303505425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282225739049543507535670283 423338608574315261303505425)
        ·
          refine ⟨317503956430736445977629069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423338608574315261303505425 317503956430736445977629069)
          ·
            refine ⟨119063983661526167241610901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317503956430736445977629069 119063983661526167241610901)
            ·
              refine ⟨5581124234134039089450511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119063983661526167241610901 5581124234134039089450511)
              ·
                refine ⟨8371686351201058634175767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5581124234134039089450511 8371686351201058634175767)
                ·
                  refine ⟨12557529526801587951263651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8371686351201058634175767 12557529526801587951263651)
                  ·
                    refine ⟨18836294290202381926895477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12557529526801587951263651 18836294290202381926895477)
                    ·
                      refine ⟨1765902589706473305646451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18836294290202381926895477 1765902589706473305646451)
                      ·
                        rfl

theorem cell23_3439083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 5].length) (baseStart_3439083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439083 prefixEnd_3439083 := by exact prefixLift 3439083
  have htrace : WordTrace (prefixWord ++ tailWord_3439083) baseStart_3439083 baseEnd_3439083 := by
    simpa [prefixWord, tailWord_3439083, baseEnd_3439083] using wordTrace_append hprefix tailTrace_3439083
  have hstable : (prefixWord ++ tailWord_3439083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439083).length < 2 ^ (prefixWord ++ tailWord_3439083).sum := by decide
  have hdescent : baseEnd_3439083 < baseStart_3439083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439097 : List Nat := [1, 2, 1, 3, 1, 2, 5, 1, 3, 2, 2]
def baseStart_3439097 : Nat := 118140960795 + 3439097 * 2 ^ 59
def prefixEnd_3439097 : Nat := 4983230072969 + 3 ^ 40 * 3439097 * 2
def baseEnd_3439097 : Nat := 1765909778435636250871387

theorem tailTrace_3439097 : CollatzResearch.WordTrace tailWord_3439097 prefixEnd_3439097 1765909778435636250871387 := by
  unfold tailWord_3439097
  simp only [CollatzResearch.WordTrace]
  refine ⟨125434172421746394851307545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83622781614497596567538363 125434172421746394851307545)
  ·
    refine ⟨94075629316309796138480659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125434172421746394851307545 94075629316309796138480659)
    ·
      refine ⟨141113443974464694207720989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94075629316309796138480659 141113443974464694207720989)
      ·
        refine ⟨52917541490424260327895371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141113443974464694207720989 52917541490424260327895371)
        ·
          refine ⟨79376312235636390491843057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52917541490424260327895371 79376312235636390491843057)
          ·
            refine ⟨59532234176727292868882293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79376312235636390491843057 59532234176727292868882293)
            ·
              refine ⟨5581146954068183706457715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59532234176727292868882293 5581146954068183706457715)
              ·
                refine ⟨8371720431102275559686573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5581146954068183706457715 8371720431102275559686573)
                ·
                  refine ⟨3139395161663353334882465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8371720431102275559686573 3139395161663353334882465)
                  ·
                    refine ⟨2354546371247515001161849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3139395161663353334882465 2354546371247515001161849)
                    ·
                      refine ⟨1765909778435636250871387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2354546371247515001161849 1765909778435636250871387)
                      ·
                        rfl

theorem cell23_3439097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_3439097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439097 prefixEnd_3439097 := by exact prefixLift 3439097
  have htrace : WordTrace (prefixWord ++ tailWord_3439097) baseStart_3439097 baseEnd_3439097 := by
    simpa [prefixWord, tailWord_3439097, baseEnd_3439097] using wordTrace_append hprefix tailTrace_3439097
  have hstable : (prefixWord ++ tailWord_3439097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439097).length < 2 ^ (prefixWord ++ tailWord_3439097).sum := by decide
  have hdescent : baseEnd_3439097 < baseStart_3439097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439127 : List Nat := [1, 1, 3, 6, 1, 1, 1, 2, 1, 2, 4]
def baseStart_3439127 : Nat := 118140960795 + 3439127 * 2 ^ 59
def prefixEnd_3439127 : Nat := 4983230072969 + 3 ^ 40 * 3439127 * 2
def baseEnd_3439127 : Nat := 1765925182855271133496249

theorem tailTrace_3439127 : CollatzResearch.WordTrace tailWord_3439127 prefixEnd_3439127 1765925182855271133496249 := by
  unfold tailWord_3439127
  simp only [CollatzResearch.WordTrace]
  refine ⟨125435266611637709974899635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83623511074425139983266423 125435266611637709974899635)
  ·
    refine ⟨188152899917456564962349453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125435266611637709974899635 188152899917456564962349453)
    ·
      refine ⟨70557337469046211860881045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188152899917456564962349453 70557337469046211860881045)
      ·
        refine ⟨3307375193861541180978799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70557337469046211860881045 3307375193861541180978799)
        ·
          refine ⟨4961062790792311771468199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3307375193861541180978799 4961062790792311771468199)
          ·
            refine ⟨7441594186188467657202299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4961062790792311771468199 7441594186188467657202299)
            ·
              refine ⟨11162391279282701485803449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7441594186188467657202299 11162391279282701485803449)
              ·
                refine ⟨8371793459462026114352587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11162391279282701485803449 8371793459462026114352587)
                ·
                  refine ⟨12557690189193039171528881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8371793459462026114352587 12557690189193039171528881)
                  ·
                    refine ⟨9418267641894779378646661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12557690189193039171528881 9418267641894779378646661)
                    ·
                      refine ⟨1765925182855271133496249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9418267641894779378646661 1765925182855271133496249)
                      ·
                        rfl

theorem cell23_3439127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_3439127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439127 prefixEnd_3439127 := by exact prefixLift 3439127
  have htrace : WordTrace (prefixWord ++ tailWord_3439127) baseStart_3439127 baseEnd_3439127 := by
    simpa [prefixWord, tailWord_3439127, baseEnd_3439127] using wordTrace_append hprefix tailTrace_3439127
  have hstable : (prefixWord ++ tailWord_3439127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439127).length < 2 ^ (prefixWord ++ tailWord_3439127).sum := by decide
  have hdescent : baseEnd_3439127 < baseStart_3439127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439130 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3]
def baseStart_3439130 : Nat := 118140960795 + 3439130 * 2 ^ 59
def prefixEnd_3439130 : Nat := 4983230072969 + 3 ^ 40 * 3439130 * 2
def baseEnd_3439130 : Nat := 1765926723297234621758735

theorem tailTrace_3439130 : CollatzResearch.WordTrace tailWord_3439130 prefixEnd_3439130 1765926723297234621758735 := by
  unfold tailWord_3439130
  simp only [CollatzResearch.WordTrace]
  refine ⟨31358844007656710371814711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83623584020417894324839229 31358844007656710371814711)
  ·
    refine ⟨47038266011485065557722067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31358844007656710371814711 47038266011485065557722067)
    ·
      refine ⟨70557399017227598336583101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47038266011485065557722067 70557399017227598336583101)
      ·
        refine ⟨26459024631460349376218663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70557399017227598336583101 26459024631460349376218663)
        ·
          refine ⟨39688536947190524064327995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26459024631460349376218663 39688536947190524064327995)
          ·
            refine ⟨59532805420785786096491993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39688536947190524064327995 59532805420785786096491993)
            ·
              refine ⟨44649604065589339572368995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59532805420785786096491993 44649604065589339572368995)
              ·
                refine ⟨66974406098384009358553493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44649604065589339572368995 66974406098384009358553493)
                ·
                  refine ⟨3139425285861750438682195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66974406098384009358553493 3139425285861750438682195)
                  ·
                    refine ⟨4709137928792625658023293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3139425285861750438682195 4709137928792625658023293)
                    ·
                      refine ⟨1765926723297234621758735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4709137928792625658023293 1765926723297234621758735)
                      ·
                        rfl

theorem cell23_3439130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_3439130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439130 prefixEnd_3439130 := by exact prefixLift 3439130
  have htrace : WordTrace (prefixWord ++ tailWord_3439130) baseStart_3439130 baseEnd_3439130 := by
    simpa [prefixWord, tailWord_3439130, baseEnd_3439130] using wordTrace_append hprefix tailTrace_3439130
  have hstable : (prefixWord ++ tailWord_3439130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439130).length < 2 ^ (prefixWord ++ tailWord_3439130).sum := by decide
  have hdescent : baseEnd_3439130 < baseStart_3439130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439153 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 2, 3, 4]
def baseStart_3439153 : Nat := 118140960795 + 3439153 * 2 ^ 59
def prefixEnd_3439153 : Nat := 4983230072969 + 3 ^ 40 * 3439153 * 2
def baseEnd_3439153 : Nat := 1765938533352288031771129

theorem tailTrace_3439153 : CollatzResearch.WordTrace tailWord_3439153 prefixEnd_3439153 1765938533352288031771129 := by
  unfold tailWord_3439153
  simp only [CollatzResearch.WordTrace]
  refine ⟨125436214909543516415346113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83624143273029010943564075 125436214909543516415346113)
  ·
    refine ⟨94077161182157637311509585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125436214909543516415346113 94077161182157637311509585)
    ·
      refine ⟨70557870886618227983632189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94077161182157637311509585 70557870886618227983632189)
      ·
        refine ⟨26459201582481835493862071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70557870886618227983632189 26459201582481835493862071)
        ·
          refine ⟨39688802373722753240793107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26459201582481835493862071 39688802373722753240793107)
          ·
            refine ⟨59533203560584129861189661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39688802373722753240793107 59533203560584129861189661)
            ·
              refine ⟨22324951335219048697946123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59533203560584129861189661 22324951335219048697946123)
              ·
                refine ⟨33487427002828573046919185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22324951335219048697946123 33487427002828573046919185)
                ·
                  refine ⟨25115570252121429785189389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33487427002828573046919185 25115570252121429785189389)
                  ·
                    refine ⟨9418338844545536169446021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25115570252121429785189389 9418338844545536169446021)
                    ·
                      refine ⟨1765938533352288031771129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9418338844545536169446021 1765938533352288031771129)
                      ·
                        rfl

theorem cell23_3439153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_3439153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439153 prefixEnd_3439153 := by exact prefixLift 3439153
  have htrace : WordTrace (prefixWord ++ tailWord_3439153) baseStart_3439153 baseEnd_3439153 := by
    simpa [prefixWord, tailWord_3439153, baseEnd_3439153] using wordTrace_append hprefix tailTrace_3439153
  have hstable : (prefixWord ++ tailWord_3439153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439153).length < 2 ^ (prefixWord ++ tailWord_3439153).sum := by decide
  have hdescent : baseEnd_3439153 < baseStart_3439153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439198 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_3439198 : Nat := 118140960795 + 3439198 * 2 ^ 59
def prefixEnd_3439198 : Nat := 4983230072969 + 3 ^ 40 * 3439198 * 2
def baseEnd_3439198 : Nat := 1765961639981740355708423

theorem tailTrace_3439198 : CollatzResearch.WordTrace tailWord_3439198 prefixEnd_3439198 1765961639981740355708423 := by
  unfold tailWord_3439198
  simp only [CollatzResearch.WordTrace]
  refine ⟨15679732024297561137591781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83625237462920326067156165 15679732024297561137591781)
  ·
    refine ⟨2939949754555792713298459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15679732024297561137591781 2939949754555792713298459)
    ·
      refine ⟨4409924631833689069947689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2939949754555792713298459 4409924631833689069947689)
      ·
        refine ⟨3307443473875266802460767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4409924631833689069947689 3307443473875266802460767)
        ·
          refine ⟨4961165210812900203691151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3307443473875266802460767 4961165210812900203691151)
          ·
            refine ⟨7441747816219350305536727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4961165210812900203691151 7441747816219350305536727)
            ·
              refine ⟨11162621724329025458305091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7441747816219350305536727 11162621724329025458305091)
              ·
                refine ⟨16743932586493538187457637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11162621724329025458305091 16743932586493538187457637)
                ·
                  refine ⟨3139487359967538410148307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16743932586493538187457637 3139487359967538410148307)
                  ·
                    refine ⟨4709231039951307615222461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3139487359967538410148307 4709231039951307615222461)
                    ·
                      refine ⟨1765961639981740355708423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4709231039951307615222461 1765961639981740355708423)
                      ·
                        rfl

theorem cell23_3439198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_3439198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439198 prefixEnd_3439198 := by exact prefixLift 3439198
  have htrace : WordTrace (prefixWord ++ tailWord_3439198) baseStart_3439198 baseEnd_3439198 := by
    simpa [prefixWord, tailWord_3439198, baseEnd_3439198] using wordTrace_append hprefix tailTrace_3439198
  have hstable : (prefixWord ++ tailWord_3439198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439198).length < 2 ^ (prefixWord ++ tailWord_3439198).sum := by decide
  have hdescent : baseEnd_3439198 < baseStart_3439198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439210 : List Nat := [3, 1, 3, 2, 1, 1, 4, 1, 7]
def baseStart_3439210 : Nat := 118140960795 + 3439210 * 2 ^ 59
def prefixEnd_3439210 : Nat := 4983230072969 + 3 ^ 40 * 3439210 * 2
def baseEnd_3439210 : Nat := 196218644638843812084263

theorem tailTrace_3439210 : CollatzResearch.WordTrace tailWord_3439210 prefixEnd_3439210 196218644638843812084263 := by
  unfold tailWord_3439210
  simp only [CollatzResearch.WordTrace]
  refine ⟨31359573467584253787542771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83625529246891343433447389 31359573467584253787542771)
  ·
    refine ⟨47039360201376380681314157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31359573467584253787542771 47039360201376380681314157)
    ·
      refine ⟨17639760075516142755492809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47039360201376380681314157 17639760075516142755492809)
      ·
        refine ⟨13229820056637107066619607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17639760075516142755492809 13229820056637107066619607)
        ·
          refine ⟨19844730084955660599929411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13229820056637107066619607 19844730084955660599929411)
          ·
            refine ⟨29767095127433490899894117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19844730084955660599929411 29767095127433490899894117)
            ·
              refine ⟨5581330336393779543730147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29767095127433490899894117 5581330336393779543730147)
              ·
                refine ⟨8371995504590669315595221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5581330336393779543730147 8371995504590669315595221)
                ·
                  refine ⟨196218644638843812084263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8371995504590669315595221 196218644638843812084263)
                  ·
                    rfl

theorem cell23_3439210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 7].length) (baseStart_3439210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439210 prefixEnd_3439210 := by exact prefixLift 3439210
  have htrace : WordTrace (prefixWord ++ tailWord_3439210) baseStart_3439210 baseEnd_3439210 := by
    simpa [prefixWord, tailWord_3439210, baseEnd_3439210] using wordTrace_append hprefix tailTrace_3439210
  have hstable : (prefixWord ++ tailWord_3439210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439210).length < 2 ^ (prefixWord ++ tailWord_3439210).sum := by decide
  have hdescent : baseEnd_3439210 < baseStart_3439210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439221 : List Nat := [1, 3, 4, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_3439221 : Nat := 118140960795 + 3439221 * 2 ^ 59
def prefixEnd_3439221 : Nat := 4983230072969 + 3 ^ 40 * 3439221 * 2
def baseEnd_3439221 : Nat := 1765973450036793765720817

theorem tailTrace_3439221 : CollatzResearch.WordTrace tailWord_3439221 prefixEnd_3439221 1765973450036793765720817 := by
  unfold tailWord_3439221
  simp only [CollatzResearch.WordTrace]
  refine ⟨125438695073297164028821517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83625796715531442685881011 125438695073297164028821517)
  ·
    refine ⟨47039510652486436510808069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125438695073297164028821517 47039510652486436510808069)
    ·
      refine ⟨8819908247341206845776513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47039510652486436510808069 8819908247341206845776513)
      ·
        refine ⟨6614931185505905134332385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8819908247341206845776513 6614931185505905134332385)
        ·
          refine ⟨4961198389129428850749289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6614931185505905134332385 4961198389129428850749289)
          ·
            refine ⟨3720898791847071638061967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4961198389129428850749289 3720898791847071638061967)
            ·
              refine ⟨5581348187770607457092951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3720898791847071638061967 5581348187770607457092951)
              ·
                refine ⟨8372022281655911185639427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5581348187770607457092951 8372022281655911185639427)
                ·
                  refine ⟨12558033422483866778459141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8372022281655911185639427 12558033422483866778459141)
                  ·
                    refine ⟨2354631266715725020961089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12558033422483866778459141 2354631266715725020961089)
                    ·
                      refine ⟨1765973450036793765720817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2354631266715725020961089 1765973450036793765720817)
                      ·
                        rfl

theorem cell23_3439221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_3439221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439221 prefixEnd_3439221 := by exact prefixLift 3439221
  have htrace : WordTrace (prefixWord ++ tailWord_3439221) baseStart_3439221 baseEnd_3439221 := by
    simpa [prefixWord, tailWord_3439221, baseEnd_3439221] using wordTrace_append hprefix tailTrace_3439221
  have hstable : (prefixWord ++ tailWord_3439221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439221).length < 2 ^ (prefixWord ++ tailWord_3439221).sum := by decide
  have hdescent : baseEnd_3439221 < baseStart_3439221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439223 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 1, 7]
def baseStart_3439223 : Nat := 118140960795 + 3439223 * 2 ^ 59
def prefixEnd_3439223 : Nat := 4983230072969 + 3 ^ 40 * 3439223 * 2
def baseEnd_3439223 : Nat := 588658158999367585965269

theorem tailTrace_3439223 : CollatzResearch.WordTrace tailWord_3439223 prefixEnd_3439223 588658158999367585965269 := by
  unfold tailWord_3439223
  simp only [CollatzResearch.WordTrace]
  refine ⟨125438768019289918370394323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83625845346193278913596215 125438768019289918370394323)
  ·
    refine ⟨188158152028934877555591485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125438768019289918370394323 188158152028934877555591485)
    ·
      refine ⟨70559307010850579083346807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188158152028934877555591485 70559307010850579083346807)
      ·
        refine ⟨105838960516275868625020211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70559307010850579083346807 105838960516275868625020211)
        ·
          refine ⟨158758440774413802937530317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105838960516275868625020211 158758440774413802937530317)
          ·
            refine ⟨59534415290405176101573869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158758440774413802937530317 59534415290405176101573869)
            ·
              refine ⟨22325405733901941038090201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59534415290405176101573869 22325405733901941038090201)
              ·
                refine ⟨16744054300426455778567651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22325405733901941038090201 16744054300426455778567651)
                ·
                  refine ⟨25116081450639683667851477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16744054300426455778567651 25116081450639683667851477)
                  ·
                    refine ⟨588658158999367585965269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25116081450639683667851477 588658158999367585965269)
                    ·
                      rfl

theorem cell23_3439223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_3439223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439223 prefixEnd_3439223 := by exact prefixLift 3439223
  have htrace : WordTrace (prefixWord ++ tailWord_3439223) baseStart_3439223 baseEnd_3439223 := by
    simpa [prefixWord, tailWord_3439223, baseEnd_3439223] using wordTrace_append hprefix tailTrace_3439223
  have hstable : (prefixWord ++ tailWord_3439223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439223).length < 2 ^ (prefixWord ++ tailWord_3439223).sum := by decide
  have hdescent : baseEnd_3439223 < baseStart_3439223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439273 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 4, 1, 6]
def baseStart_3439273 : Nat := 118140960795 + 3439273 * 2 ^ 59
def prefixEnd_3439273 : Nat := 4983230072969 + 3 ^ 40 * 3439273 * 2
def baseEnd_3439273 : Nat := 1766000151030827562270577

theorem tailTrace_3439273 : CollatzResearch.WordTrace tailWord_3439273 prefixEnd_3439273 1766000151030827562270577 := by
  unfold tailWord_3439273
  simp only [CollatzResearch.WordTrace]
  refine ⟨125440591669108776909714473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83627061112739184606476315 125440591669108776909714473)
  ·
    refine ⟨94080443751831582682285855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125440591669108776909714473 94080443751831582682285855)
    ·
      refine ⟨141120665627747374023428783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94080443751831582682285855 141120665627747374023428783)
      ·
        refine ⟨211680998441621061035143175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141120665627747374023428783 211680998441621061035143175)
        ·
          refine ⟨317521497662431591552714763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211680998441621061035143175 317521497662431591552714763)
          ·
            refine ⟨476282246493647387329072145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317521497662431591552714763 476282246493647387329072145)
            ·
              refine ⟨357211684870235540496804109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476282246493647387329072145 357211684870235540496804109)
              ·
                refine ⟨133954381826338327686301541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357211684870235540496804109 133954381826338327686301541)
                ·
                  refine ⟨25116446592438436441181539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133954381826338327686301541 25116446592438436441181539)
                  ·
                    refine ⟨37674669888657654661772309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25116446592438436441181539 37674669888657654661772309)
                    ·
                      refine ⟨1766000151030827562270577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37674669888657654661772309 1766000151030827562270577)
                      ·
                        rfl

theorem cell23_3439273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_3439273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439273 prefixEnd_3439273 := by exact prefixLift 3439273
  have htrace : WordTrace (prefixWord ++ tailWord_3439273) baseStart_3439273 baseEnd_3439273 := by
    simpa [prefixWord, tailWord_3439273, baseEnd_3439273] using wordTrace_append hprefix tailTrace_3439273
  have hstable : (prefixWord ++ tailWord_3439273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439273).length < 2 ^ (prefixWord ++ tailWord_3439273).sum := by decide
  have hdescent : baseEnd_3439273 < baseStart_3439273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439280 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 3]
def baseStart_3439280 : Nat := 118140960795 + 3439280 * 2 ^ 59
def prefixEnd_3439280 : Nat := 4983230072969 + 3 ^ 40 * 3439280 * 2
def baseEnd_3439280 : Nat := 1766003745395409034883045

theorem tailTrace_3439280 : CollatzResearch.WordTrace tailWord_3439280 prefixEnd_3439280 1766003745395409034883045 := by
  unfold tailWord_3439280
  simp only [CollatzResearch.WordTrace]
  refine ⟨62720423490041708552609647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83627231320055611403479529 62720423490041708552609647)
  ·
    refine ⟨94080635235062562828914471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62720423490041708552609647 94080635235062562828914471)
    ·
      refine ⟨141120952852593844243371707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94080635235062562828914471 141120952852593844243371707)
      ·
        refine ⟨211681429278890766365057561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141120952852593844243371707 211681429278890766365057561)
        ·
          refine ⟨158761071959168074773793171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211681429278890766365057561 158761071959168074773793171)
          ·
            refine ⟨238141607938752112160689757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158761071959168074773793171 238141607938752112160689757)
            ·
              refine ⟨89303102977032042060258659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238141607938752112160689757 89303102977032042060258659)
              ·
                refine ⟨133954654465548063090387989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89303102977032042060258659 133954654465548063090387989)
                ·
                  refine ⟨6279124428072565457361937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 133954654465548063090387989 6279124428072565457361937)
                  ·
                    refine ⟨4709343321054424093021453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6279124428072565457361937 4709343321054424093021453)
                    ·
                      refine ⟨1766003745395409034883045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4709343321054424093021453 1766003745395409034883045)
                      ·
                        rfl

theorem cell23_3439280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 3].length) (baseStart_3439280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439280 prefixEnd_3439280 := by exact prefixLift 3439280
  have htrace : WordTrace (prefixWord ++ tailWord_3439280) baseStart_3439280 baseEnd_3439280 := by
    simpa [prefixWord, tailWord_3439280, baseEnd_3439280] using wordTrace_append hprefix tailTrace_3439280
  have hstable : (prefixWord ++ tailWord_3439280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439280).length < 2 ^ (prefixWord ++ tailWord_3439280).sum := by decide
  have hdescent : baseEnd_3439280 < baseStart_3439280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439337 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 4, 3, 2]
def baseStart_3439337 : Nat := 118140960795 + 3439337 * 2 ^ 59
def prefixEnd_3439337 : Nat := 4983230072969 + 3 ^ 40 * 3439337 * 2
def baseEnd_3439337 : Nat := 1766033013792715311870283

theorem tailTrace_3439337 : CollatzResearch.WordTrace tailWord_3439337 prefixEnd_3439337 1766033013792715311870283 := by
  unfold tailWord_3439337
  simp only [CollatzResearch.WordTrace]
  refine ⟨125442925940876915840044265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83628617293917943893362843 125442925940876915840044265)
  ·
    refine ⟨94082194455657686880033199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125442925940876915840044265 94082194455657686880033199)
    ·
      refine ⟨141123291683486530320049799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94082194455657686880033199 141123291683486530320049799)
      ·
        refine ⟨211684937525229795480074699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141123291683486530320049799 211684937525229795480074699)
        ·
          refine ⟨317527406287844693220112049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211684937525229795480074699 317527406287844693220112049)
          ·
            refine ⟨238145554715883519915084037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317527406287844693220112049 238145554715883519915084037)
            ·
              refine ⟨44652291509228159984078257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 238145554715883519915084037 44652291509228159984078257)
              ·
                refine ⟨33489218631921119988058693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44652291509228159984078257 33489218631921119988058693)
                ·
                  refine ⟨6279228493485209997761005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33489218631921119988058693 6279228493485209997761005)
                  ·
                    refine ⟨2354710685056953749160377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6279228493485209997761005 2354710685056953749160377)
                    ·
                      refine ⟨1766033013792715311870283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2354710685056953749160377 1766033013792715311870283)
                      ·
                        rfl

theorem cell23_3439337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 3, 2].length) (baseStart_3439337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439337 prefixEnd_3439337 := by exact prefixLift 3439337
  have htrace : WordTrace (prefixWord ++ tailWord_3439337) baseStart_3439337 baseEnd_3439337 := by
    simpa [prefixWord, tailWord_3439337, baseEnd_3439337] using wordTrace_append hprefix tailTrace_3439337
  have hstable : (prefixWord ++ tailWord_3439337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439337).length < 2 ^ (prefixWord ++ tailWord_3439337).sum := by decide
  have hdescent : baseEnd_3439337 < baseStart_3439337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439354 : List Nat := [3, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2]
def baseStart_3439354 : Nat := 118140960795 + 3439354 * 2 ^ 59
def prefixEnd_3439354 : Nat := 4983230072969 + 3 ^ 40 * 3439354 * 2
def baseEnd_3439354 : Nat := 1766041742963841745357705

theorem tailTrace_3439354 : CollatzResearch.WordTrace tailWord_3439354 prefixEnd_3439354 1766041742963841745357705 := by
  unfold tailWord_3439354
  simp only [CollatzResearch.WordTrace]
  refine ⟨31360886495453831935853279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83629030654543551828942077 31360886495453831935853279)
  ·
    refine ⟨47041329743180747903779919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31360886495453831935853279 47041329743180747903779919)
    ·
      refine ⟨70561994614771121855669879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47041329743180747903779919 70561994614771121855669879)
      ·
        refine ⟨105842991922156682783504819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70561994614771121855669879 105842991922156682783504819)
        ·
          refine ⟨158764487883235024175257229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105842991922156682783504819 158764487883235024175257229)
          ·
            refine ⟨59536682956213134065721461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158764487883235024175257229 59536682956213134065721461)
            ·
              refine ⟨5581564027144981318661387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59536682956213134065721461 5581564027144981318661387)
              ·
                refine ⟨8372346040717471977992081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5581564027144981318661387 8372346040717471977992081)
                ·
                  refine ⟨6279259530538103983494061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8372346040717471977992081 6279259530538103983494061)
                  ·
                    refine ⟨2354722323951788993810273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6279259530538103983494061 2354722323951788993810273)
                    ·
                      refine ⟨1766041742963841745357705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2354722323951788993810273 1766041742963841745357705)
                      ·
                        rfl

theorem cell23_3439354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2].length) (baseStart_3439354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439354 prefixEnd_3439354 := by exact prefixLift 3439354
  have htrace : WordTrace (prefixWord ++ tailWord_3439354) baseStart_3439354 baseEnd_3439354 := by
    simpa [prefixWord, tailWord_3439354, baseEnd_3439354] using wordTrace_append hprefix tailTrace_3439354
  have hstable : (prefixWord ++ tailWord_3439354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439354).length < 2 ^ (prefixWord ++ tailWord_3439354).sum := by decide
  have hdescent : baseEnd_3439354 < baseStart_3439354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439378 : List Nat := [3, 2, 4, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_3439378 : Nat := 118140960795 + 3439378 * 2 ^ 59
def prefixEnd_3439378 : Nat := 4983230072969 + 3 ^ 40 * 3439378 * 2
def baseEnd_3439378 : Nat := 1766054066499549651457595

theorem tailTrace_3439378 : CollatzResearch.WordTrace tailWord_3439378 prefixEnd_3439378 1766054066499549651457595 := by
  unfold tailWord_3439378
  simp only [CollatzResearch.WordTrace]
  refine ⟨31361105333432094960571697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83629614222485586561524525 31361105333432094960571697)
  ·
    refine ⟨23520829000074071220428773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31361105333432094960571697 23520829000074071220428773)
    ·
      refine ⟨4410155437513888353830395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23520829000074071220428773 4410155437513888353830395)
      ·
        refine ⟨6615233156270832530745593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4410155437513888353830395 6615233156270832530745593)
        ·
          refine ⟨4961424867203124398059195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6615233156270832530745593 4961424867203124398059195)
          ·
            refine ⟨7442137300804686597088793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4961424867203124398059195 7442137300804686597088793)
            ·
              refine ⟨5581602975603514947816595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7442137300804686597088793 5581602975603514947816595)
              ·
                refine ⟨8372404463405272421724893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5581602975603514947816595 8372404463405272421724893)
                ·
                  refine ⟨3139651673776977158146835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8372404463405272421724893 3139651673776977158146835)
                  ·
                    refine ⟨4709477510665465737220253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3139651673776977158146835 4709477510665465737220253)
                    ·
                      refine ⟨1766054066499549651457595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4709477510665465737220253 1766054066499549651457595)
                      ·
                        rfl

theorem cell23_3439378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_3439378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439378 prefixEnd_3439378 := by exact prefixLift 3439378
  have htrace : WordTrace (prefixWord ++ tailWord_3439378) baseStart_3439378 baseEnd_3439378 := by
    simpa [prefixWord, tailWord_3439378, baseEnd_3439378] using wordTrace_append hprefix tailTrace_3439378
  have hstable : (prefixWord ++ tailWord_3439378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439378).length < 2 ^ (prefixWord ++ tailWord_3439378).sum := by decide
  have hdescent : baseEnd_3439378 < baseStart_3439378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439394 : List Nat := [3, 3, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_3439394 : Nat := 118140960795 + 3439394 * 2 ^ 59
def prefixEnd_3439394 : Nat := 4983230072969 + 3 ^ 40 * 3439394 * 2
def baseEnd_3439394 : Nat := 588687427396673862952507

theorem tailTrace_3439394 : CollatzResearch.WordTrace tailWord_3439394 prefixEnd_3439394 588687427396673862952507 := by
  unfold tailWord_3439394
  simp only [CollatzResearch.WordTrace]
  refine ⟨31361251225417603643717309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83630003267780276383246157 31361251225417603643717309)
  ·
    refine ⟨11760469209531601366393991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31361251225417603643717309 11760469209531601366393991)
    ·
      refine ⟨17640703814297402049590987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11760469209531601366393991 17640703814297402049590987)
      ·
        refine ⟨26461055721446103074386481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17640703814297402049590987 26461055721446103074386481)
        ·
          refine ⟨19845791791084577305789861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26461055721446103074386481 19845791791084577305789861)
          ·
            refine ⟨3721085960828358244835599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19845791791084577305789861 3721085960828358244835599)
            ·
              refine ⟨5581628941242537367253399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3721085960828358244835599 5581628941242537367253399)
              ·
                refine ⟨8372443411863806050880099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5581628941242537367253399 8372443411863806050880099)
                ·
                  refine ⟨12558665117795709076320149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8372443411863806050880099 12558665117795709076320149)
                  ·
                    refine ⟨588687427396673862952507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12558665117795709076320149 588687427396673862952507)
                    ·
                      rfl

theorem cell23_3439394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_3439394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439394 prefixEnd_3439394 := by exact prefixLift 3439394
  have htrace : WordTrace (prefixWord ++ tailWord_3439394) baseStart_3439394 baseEnd_3439394 := by
    simpa [prefixWord, tailWord_3439394, baseEnd_3439394] using wordTrace_append hprefix tailTrace_3439394
  have hstable : (prefixWord ++ tailWord_3439394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439394).length < 2 ^ (prefixWord ++ tailWord_3439394).sum := by decide
  have hdescent : baseEnd_3439394 < baseStart_3439394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439404 : List Nat := [2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 3]
def baseStart_3439404 : Nat := 118140960795 + 3439404 * 2 ^ 59
def prefixEnd_3439404 : Nat := 4983230072969 + 3 ^ 40 * 3439404 * 2
def baseEnd_3439404 : Nat := 1766067416996566549732475

theorem tailTrace_3439404 : CollatzResearch.WordTrace tailWord_3439404 prefixEnd_3439404 1766067416996566549732475 := by
  unfold tailWord_3439404
  simp only [CollatzResearch.WordTrace]
  refine ⟨62722684815817093141366633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83630246421089457521822177 62722684815817093141366633)
  ·
    refine ⟨47042013611862819856024975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62722684815817093141366633 47042013611862819856024975)
    ·
      refine ⟨70563020417794229784037463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47042013611862819856024975 70563020417794229784037463)
      ·
        refine ⟨105844530626691344676056195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70563020417794229784037463 105844530626691344676056195)
        ·
          refine ⟨158766795940037017014084293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105844530626691344676056195 158766795940037017014084293)
          ·
            refine ⟨29768774238756940690140805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158766795940037017014084293 29768774238756940690140805)
            ·
              refine ⟨5581645169766926379401401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29768774238756940690140805 5581645169766926379401401)
              ·
                refine ⟨4186233877325194784551051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5581645169766926379401401 4186233877325194784551051)
                ·
                  refine ⟨6279350815987792176826577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4186233877325194784551051 6279350815987792176826577)
                  ·
                    refine ⟨4709513111990844132619933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6279350815987792176826577 4709513111990844132619933)
                    ·
                      refine ⟨1766067416996566549732475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4709513111990844132619933 1766067416996566549732475)
                      ·
                        rfl

theorem cell23_3439404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 3].length) (baseStart_3439404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439404 prefixEnd_3439404 := by exact prefixLift 3439404
  have htrace : WordTrace (prefixWord ++ tailWord_3439404) baseStart_3439404 baseEnd_3439404 := by
    simpa [prefixWord, tailWord_3439404, baseEnd_3439404] using wordTrace_append hprefix tailTrace_3439404
  have hstable : (prefixWord ++ tailWord_3439404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439404).length < 2 ^ (prefixWord ++ tailWord_3439404).sum := by decide
  have hdescent : baseEnd_3439404 < baseStart_3439404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439412 : List Nat := [2, 5, 1, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_3439412 : Nat := 118140960795 + 3439412 * 2 ^ 59
def prefixEnd_3439412 : Nat := 4983230072969 + 3 ^ 40 * 3439412 * 2
def baseEnd_3439412 : Nat := 1766071524841802518432439

theorem tailTrace_3439412 : CollatzResearch.WordTrace tailWord_3439412 prefixEnd_3439412 1766071524841802518432439 := by
  unfold tailWord_3439412
  simp only [CollatzResearch.WordTrace]
  refine ⟨62722830707802601824512245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83630440943736802432682993 62722830707802601824512245)
  ·
    refine ⟨5880265378856493921048023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62722830707802601824512245 5880265378856493921048023)
    ·
      refine ⟨8820398068284740881572035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5880265378856493921048023 8820398068284740881572035)
      ·
        refine ⟨13230597102427111322358053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8820398068284740881572035 13230597102427111322358053)
        ·
          refine ⟨2480736956705083372942135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13230597102427111322358053 2480736956705083372942135)
          ·
            refine ⟨3721105435057625059413203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2480736956705083372942135 3721105435057625059413203)
            ·
              refine ⟨5581658152586437589119805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3721105435057625059413203 5581658152586437589119805)
              ·
                refine ⟨2093121807219914095919927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5581658152586437589119805 2093121807219914095919927)
                ·
                  refine ⟨3139682710829871143879891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2093121807219914095919927 3139682710829871143879891)
                  ·
                    refine ⟨4709524066244806715819837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3139682710829871143879891 4709524066244806715819837)
                    ·
                      refine ⟨1766071524841802518432439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4709524066244806715819837 1766071524841802518432439)
                      ·
                        rfl

theorem cell23_3439412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_3439412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439412 prefixEnd_3439412 := by exact prefixLift 3439412
  have htrace : WordTrace (prefixWord ++ tailWord_3439412) baseStart_3439412 baseEnd_3439412 := by
    simpa [prefixWord, tailWord_3439412, baseEnd_3439412] using wordTrace_append hprefix tailTrace_3439412
  have hstable : (prefixWord ++ tailWord_3439412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439412).length < 2 ^ (prefixWord ++ tailWord_3439412).sum := by decide
  have hdescent : baseEnd_3439412 < baseStart_3439412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439420 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 1, 9]
def baseStart_3439420 : Nat := 118140960795 + 3439420 * 2 ^ 59
def prefixEnd_3439420 : Nat := 4983230072969 + 3 ^ 40 * 3439420 * 2
def baseEnd_3439420 : Nat := 588691877562346162377467

theorem tailTrace_3439420 : CollatzResearch.WordTrace tailWord_3439420 prefixEnd_3439420 588691877562346162377467 := by
  unfold tailWord_3439420
  simp only [CollatzResearch.WordTrace]
  refine ⟨62722976599788110507657857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83630635466384147343543809 62722976599788110507657857)
  ·
    refine ⟨47042232449841082880743393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62722976599788110507657857 47042232449841082880743393)
    ·
      refine ⟨35281674337380812160557545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47042232449841082880743393 35281674337380812160557545)
      ·
        refine ⟨26461255753035609120418159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35281674337380812160557545 26461255753035609120418159)
        ·
          refine ⟨39691883629553413680627239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26461255753035609120418159 39691883629553413680627239)
          ·
            refine ⟨59537825444330120520940859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39691883629553413680627239 59537825444330120520940859)
            ·
              refine ⟨89306738166495180781411289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59537825444330120520940859 89306738166495180781411289)
              ·
                refine ⟨66980053624871385586058467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89306738166495180781411289 66980053624871385586058467)
                ·
                  refine ⟨100470080437307078379087701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66980053624871385586058467 100470080437307078379087701)
                  ·
                    refine ⟨588691877562346162377467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 100470080437307078379087701 588691877562346162377467)
                    ·
                      rfl

theorem cell23_3439420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_3439420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439420 prefixEnd_3439420 := by exact prefixLift 3439420
  have htrace : WordTrace (prefixWord ++ tailWord_3439420) baseStart_3439420 baseEnd_3439420 := by
    simpa [prefixWord, tailWord_3439420, baseEnd_3439420] using wordTrace_append hprefix tailTrace_3439420
  have hstable : (prefixWord ++ tailWord_3439420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439420).length < 2 ^ (prefixWord ++ tailWord_3439420).sum := by decide
  have hdescent : baseEnd_3439420 < baseStart_3439420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439461 : List Nat := [1, 3, 1, 3, 1, 1, 5, 2, 1, 3, 2]
def baseStart_3439461 : Nat := 118140960795 + 3439461 * 2 ^ 59
def prefixEnd_3439461 : Nat := 4983230072969 + 3 ^ 40 * 3439461 * 2
def baseEnd_3439461 : Nat := 1766096685393872826719713

theorem tailTrace_3439461 : CollatzResearch.WordTrace tailWord_3439461 prefixEnd_3439461 1766096685393872826719713 := by
  unfold tailWord_3439461
  simp only [CollatzResearch.WordTrace]
  refine ⟨125447448592427685017558237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83631632394951790011705491 125447448592427685017558237)
  ·
    refine ⟨47042793222160381881584339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125447448592427685017558237 47042793222160381881584339)
    ·
      refine ⟨70564189833240572822376509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47042793222160381881584339 70564189833240572822376509)
      ·
        refine ⟨26461571187465214808391191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70564189833240572822376509 26461571187465214808391191)
        ·
          refine ⟨39692356781197822212586787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26461571187465214808391191 39692356781197822212586787)
          ·
            refine ⟨59538535171796733318880181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39692356781197822212586787 59538535171796733318880181)
            ·
              refine ⟨5581737672355943748645017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59538535171796733318880181 5581737672355943748645017)
              ·
                refine ⟨4186303254266957811483763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5581737672355943748645017 4186303254266957811483763)
                ·
                  refine ⟨6279454881400436717225645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4186303254266957811483763 6279454881400436717225645)
                  ·
                    refine ⟨2354795580525163768959617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6279454881400436717225645 2354795580525163768959617)
                    ·
                      refine ⟨1766096685393872826719713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2354795580525163768959617 1766096685393872826719713)
                      ·
                        rfl

theorem cell23_3439461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_3439461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439461 prefixEnd_3439461 := by exact prefixLift 3439461
  have htrace : WordTrace (prefixWord ++ tailWord_3439461) baseStart_3439461 baseEnd_3439461 := by
    simpa [prefixWord, tailWord_3439461, baseEnd_3439461] using wordTrace_append hprefix tailTrace_3439461
  have hstable : (prefixWord ++ tailWord_3439461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439461).length < 2 ^ (prefixWord ++ tailWord_3439461).sum := by decide
  have hdescent : baseEnd_3439461 < baseStart_3439461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439474 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 3, 4, 2]
def baseStart_3439474 : Nat := 118140960795 + 3439474 * 2 ^ 59
def prefixEnd_3439474 : Nat := 4983230072969 + 3 ^ 40 * 3439474 * 2
def baseEnd_3439474 : Nat := 1766103360642381275857153

theorem tailTrace_3439474 : CollatzResearch.WordTrace tailWord_3439474 prefixEnd_3439474 1766103360642381275857153 := by
  unfold tailWord_3439474
  simp only [CollatzResearch.WordTrace]
  refine ⟨31361980685345147059445369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83631948494253725491854317 31361980685345147059445369)
  ·
    refine ⟨23521485514008860294584027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31361980685345147059445369 23521485514008860294584027)
    ·
      refine ⟨35282228271013290441876041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23521485514008860294584027 35282228271013290441876041)
      ·
        refine ⟨26461671203259967831407031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35282228271013290441876041 26461671203259967831407031)
        ·
          refine ⟨39692506804889951747110547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26461671203259967831407031 39692506804889951747110547)
          ·
            refine ⟨59538760207334927620665821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39692506804889951747110547 59538760207334927620665821)
            ·
              refine ⟨22327035077750597857749683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59538760207334927620665821 22327035077750597857749683)
              ·
                refine ⟨33490552616625896786624525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22327035077750597857749683 33490552616625896786624525)
                ·
                  refine ⟨12558957231234711294984197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33490552616625896786624525 12558957231234711294984197)
                  ·
                    refine ⟨2354804480856508367809537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12558957231234711294984197 2354804480856508367809537)
                    ·
                      refine ⟨1766103360642381275857153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2354804480856508367809537 1766103360642381275857153)
                      ·
                        rfl

theorem cell23_3439474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_3439474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439474 prefixEnd_3439474 := by exact prefixLift 3439474
  have htrace : WordTrace (prefixWord ++ tailWord_3439474) baseStart_3439474 baseEnd_3439474 := by
    simpa [prefixWord, tailWord_3439474, baseEnd_3439474] using wordTrace_append hprefix tailTrace_3439474
  have hstable : (prefixWord ++ tailWord_3439474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439474).length < 2 ^ (prefixWord ++ tailWord_3439474).sum := by decide
  have hdescent : baseEnd_3439474 < baseStart_3439474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439480 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 11]
def baseStart_3439480 : Nat := 118140960795 + 3439480 * 2 ^ 59
def prefixEnd_3439480 : Nat := 4983230072969 + 3 ^ 40 * 3439480 * 2
def baseEnd_3439480 : Nat := 196234049058478694709125

theorem tailTrace_3439480 : CollatzResearch.WordTrace tailWord_3439480 prefixEnd_3439480 196234049058478694709125 := by
  unfold tailWord_3439480
  simp only [CollatzResearch.WordTrace]
  refine ⟨62724070789679425631249947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83632094386239234174999929 62724070789679425631249947)
  ·
    refine ⟨94086106184519138446874921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62724070789679425631249947 94086106184519138446874921)
    ·
      refine ⟨70564579638389353835156191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94086106184519138446874921 70564579638389353835156191)
      ·
        refine ⟨105846869457584030752734287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70564579638389353835156191 105846869457584030752734287)
        ·
          refine ⟨158770304186376046129101431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105846869457584030752734287 158770304186376046129101431)
          ·
            refine ⟨238155456279564069193652147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158770304186376046129101431 238155456279564069193652147)
            ·
              refine ⟨357233184419346103790478221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238155456279564069193652147 357233184419346103790478221)
              ·
                refine ⟨133962444157254788921429333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357233184419346103790478221 133962444157254788921429333)
                ·
                  refine ⟨196234049058478694709125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 133962444157254788921429333 196234049058478694709125)
                  ·
                    rfl

theorem cell23_3439480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 11].length) (baseStart_3439480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439480 prefixEnd_3439480 := by exact prefixLift 3439480
  have htrace : WordTrace (prefixWord ++ tailWord_3439480) baseStart_3439480 baseEnd_3439480 := by
    simpa [prefixWord, tailWord_3439480, baseEnd_3439480] using wordTrace_append hprefix tailTrace_3439480
  have hstable : (prefixWord ++ tailWord_3439480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439480).length < 2 ^ (prefixWord ++ tailWord_3439480).sum := by decide
  have hdescent : baseEnd_3439480 < baseStart_3439480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439486 : List Nat := [4, 2, 3, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_3439486 : Nat := 118140960795 + 3439486 * 2 ^ 59
def prefixEnd_3439486 : Nat := 4983230072969 + 3 ^ 40 * 3439486 * 2
def baseEnd_3439486 : Nat := 1766109522410235228907099

theorem tailTrace_3439486 : CollatzResearch.WordTrace tailWord_3439486 prefixEnd_3439486 1766109522410235228907099 := by
  unfold tailWord_3439486
  simp only [CollatzResearch.WordTrace]
  refine ⟨15681045052167139285902289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83632240278224742858145541 15681045052167139285902289)
  ·
    refine ⟨11760783789125354464426717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15681045052167139285902289 11760783789125354464426717)
    ·
      refine ⟨4410293920922007924160019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11760783789125354464426717 4410293920922007924160019)
      ·
        refine ⟨6615440881383011886240029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4410293920922007924160019 6615440881383011886240029)
        ·
          refine ⟨2480790330518629457340011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6615440881383011886240029 2480790330518629457340011)
          ·
            refine ⟨3721185495777944186010017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2480790330518629457340011 3721185495777944186010017)
            ·
              refine ⟨2790889121833458139507513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3721185495777944186010017 2790889121833458139507513)
              ·
                refine ⟨2093166841375093604630635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2790889121833458139507513 2093166841375093604630635)
                ·
                  refine ⟨3139750262062640406945953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2093166841375093604630635 3139750262062640406945953)
                  ·
                    refine ⟨2354812696546980305209465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3139750262062640406945953 2354812696546980305209465)
                    ·
                      refine ⟨1766109522410235228907099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2354812696546980305209465 1766109522410235228907099)
                      ·
                        rfl

theorem cell23_3439486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_3439486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439486 prefixEnd_3439486 := by exact prefixLift 3439486
  have htrace : WordTrace (prefixWord ++ tailWord_3439486) baseStart_3439486 baseEnd_3439486 := by
    simpa [prefixWord, tailWord_3439486, baseEnd_3439486] using wordTrace_append hprefix tailTrace_3439486
  have hstable : (prefixWord ++ tailWord_3439486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439486).length < 2 ^ (prefixWord ++ tailWord_3439486).sum := by decide
  have hdescent : baseEnd_3439486 < baseStart_3439486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439508 : List Nat := [2, 4, 2, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_3439508 : Nat := 118140960795 + 3439508 * 2 ^ 59
def prefixEnd_3439508 : Nat := 4983230072969 + 3 ^ 40 * 3439508 * 2
def baseEnd_3439508 : Nat := 1766120818984634142831997

theorem tailTrace_3439508 : CollatzResearch.WordTrace tailWord_3439508 prefixEnd_3439508 1766120818984634142831997 := by
  unfold tailWord_3439508
  simp only [CollatzResearch.WordTrace]
  refine ⟨62724581411628706022259589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83632775215504941363012785 62724581411628706022259589)
  ·
    refine ⟨11760859014680382379173673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62724581411628706022259589 11760859014680382379173673)
    ·
      refine ⟨8820644261010286784380255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11760859014680382379173673 8820644261010286784380255)
      ·
        refine ⟨13230966391515430176570383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8820644261010286784380255 13230966391515430176570383)
        ·
          refine ⟨19846449587273145264855575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13230966391515430176570383 19846449587273145264855575)
          ·
            refine ⟨29769674380909717897283363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19846449587273145264855575 29769674380909717897283363)
            ·
              refine ⟨44654511571364576845925045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29769674380909717897283363 44654511571364576845925045)
              ·
                refine ⟨4186360459815429079305473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44654511571364576845925045 4186360459815429079305473)
                ·
                  refine ⟨3139770344861571809479105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4186360459815429079305473 3139770344861571809479105)
                  ·
                    refine ⟨2354827758646178857109329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3139770344861571809479105 2354827758646178857109329)
                    ·
                      refine ⟨1766120818984634142831997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2354827758646178857109329 1766120818984634142831997)
                      ·
                        rfl

theorem cell23_3439508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_3439508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439508 prefixEnd_3439508 := by exact prefixLift 3439508
  have htrace : WordTrace (prefixWord ++ tailWord_3439508) baseStart_3439508 baseEnd_3439508 := by
    simpa [prefixWord, tailWord_3439508, baseEnd_3439508] using wordTrace_append hprefix tailTrace_3439508
  have hstable : (prefixWord ++ tailWord_3439508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439508).length < 2 ^ (prefixWord ++ tailWord_3439508).sum := by decide
  have hdescent : baseEnd_3439508 < baseStart_3439508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439514 : List Nat := [3, 1, 1, 4, 3, 1, 1, 2, 7]
def baseStart_3439514 : Nat := 118140960795 + 3439514 * 2 ^ 59
def prefixEnd_3439514 : Nat := 4983230072969 + 3 ^ 40 * 3439514 * 2
def baseEnd_3439514 : Nat := 196235988874284568817441

theorem tailTrace_3439514 : CollatzResearch.WordTrace tailWord_3439514 prefixEnd_3439514 196235988874284568817441 := by
  unfold tailWord_3439514
  simp only [CollatzResearch.WordTrace]
  refine ⟨31362345415308918767309399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83632921107490450046158397 31362345415308918767309399)
  ·
    refine ⟨47043518122963378150964099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31362345415308918767309399 47043518122963378150964099)
    ·
      refine ⟨70565277184445067226446149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47043518122963378150964099 70565277184445067226446149)
      ·
        refine ⟨13230989472083450104958653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70565277184445067226446149 13230989472083450104958653)
        ·
          refine ⟨4961621052031293789359495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13230989472083450104958653 4961621052031293789359495)
          ·
            refine ⟨7442431578046940684039243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4961621052031293789359495 7442431578046940684039243)
            ·
              refine ⟨11163647367070411026058865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7442431578046940684039243 11163647367070411026058865)
              ·
                refine ⟨8372735525302808269544149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11163647367070411026058865 8372735525302808269544149)
                ·
                  refine ⟨196235988874284568817441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8372735525302808269544149 196235988874284568817441)
                  ·
                    rfl

theorem cell23_3439514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 7].length) (baseStart_3439514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439514 prefixEnd_3439514 := by exact prefixLift 3439514
  have htrace : WordTrace (prefixWord ++ tailWord_3439514) baseStart_3439514 baseEnd_3439514 := by
    simpa [prefixWord, tailWord_3439514, baseEnd_3439514] using wordTrace_append hprefix tailTrace_3439514
  have hstable : (prefixWord ++ tailWord_3439514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439514).length < 2 ^ (prefixWord ++ tailWord_3439514).sum := by decide
  have hdescent : baseEnd_3439514 < baseStart_3439514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439587 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 10]
def baseStart_3439587 : Nat := 118140960795 + 3439587 * 2 ^ 59
def prefixEnd_3439587 : Nat := 4983230072969 + 3 ^ 40 * 3439587 * 2
def baseEnd_3439587 : Nat := 196240153772926592638237

theorem tailTrace_3439587 : CollatzResearch.WordTrace tailWord_3439587 prefixEnd_3439587 196240153772926592638237 := by
  unfold tailWord_3439587
  simp only [CollatzResearch.WordTrace]
  refine ⟨125452044189971208536645015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83634696126647472357763343 125452044189971208536645015)
  ·
    refine ⟨188178066284956812804967523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125452044189971208536645015 188178066284956812804967523)
    ·
      refine ⟨282267099427435219207451285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188178066284956812804967523 282267099427435219207451285)
      ·
        refine ⟨13231270285661025900349279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 282267099427435219207451285 13231270285661025900349279)
        ·
          refine ⟨19846905428491538850523919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13231270285661025900349279 19846905428491538850523919)
          ·
            refine ⟨29770358142737308275785879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19846905428491538850523919 29770358142737308275785879)
            ·
              refine ⟨44655537214105962413678819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29770358142737308275785879 44655537214105962413678819)
              ·
                refine ⟨66983305821158943620518229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44655537214105962413678819 66983305821158943620518229)
                ·
                  refine ⟨196240153772926592638237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 66983305821158943620518229 196240153772926592638237)
                  ·
                    rfl

theorem cell23_3439587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 10].length) (baseStart_3439587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439587 prefixEnd_3439587 := by exact prefixLift 3439587
  have htrace : WordTrace (prefixWord ++ tailWord_3439587) baseStart_3439587 baseEnd_3439587 := by
    simpa [prefixWord, tailWord_3439587, baseEnd_3439587] using wordTrace_append hprefix tailTrace_3439587
  have hstable : (prefixWord ++ tailWord_3439587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439587).length < 2 ^ (prefixWord ++ tailWord_3439587).sum := by decide
  have hdescent : baseEnd_3439587 < baseStart_3439587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439601 : List Nat := [1, 2, 2, 2, 4, 2, 1, 2, 2, 2, 3]
def baseStart_3439601 : Nat := 118140960795 + 3439601 * 2 ^ 59
def prefixEnd_3439601 : Nat := 4983230072969 + 3 ^ 40 * 3439601 * 2
def baseEnd_3439601 : Nat := 1766168572685502278969069

theorem tailTrace_3439601 : CollatzResearch.WordTrace tailWord_3439601 prefixEnd_3439601 1766168572685502278969069 := by
  unfold tailWord_3439601
  simp only [CollatzResearch.WordTrace]
  refine ⟨125452554811920488927654657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83635036541280325951769771 125452554811920488927654657)
  ·
    refine ⟨94089416108940366695740993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125452554811920488927654657 94089416108940366695740993)
    ·
      refine ⟨70567062081705275021805745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94089416108940366695740993 70567062081705275021805745)
      ·
        refine ⟨52925296561278956266354309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70567062081705275021805745 52925296561278956266354309)
        ·
          refine ⟨9923493105239804299941433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52925296561278956266354309 9923493105239804299941433)
          ·
            refine ⟨7442619828929853224956075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9923493105239804299941433 7442619828929853224956075)
            ·
              refine ⟨11163929743394779837434113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7442619828929853224956075 11163929743394779837434113)
              ·
                refine ⟨8372947307546084878075585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11163929743394779837434113 8372947307546084878075585)
                ·
                  refine ⟨6279710480659563658556689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8372947307546084878075585 6279710480659563658556689)
                  ·
                    refine ⟨4709782860494672743917517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6279710480659563658556689 4709782860494672743917517)
                    ·
                      refine ⟨1766168572685502278969069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4709782860494672743917517 1766168572685502278969069)
                      ·
                        rfl

theorem cell23_3439601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_3439601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439601 prefixEnd_3439601 := by exact prefixLift 3439601
  have htrace : WordTrace (prefixWord ++ tailWord_3439601) baseStart_3439601 baseEnd_3439601 := by
    simpa [prefixWord, tailWord_3439601, baseEnd_3439601] using wordTrace_append hprefix tailTrace_3439601
  have hstable : (prefixWord ++ tailWord_3439601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439601).length < 2 ^ (prefixWord ++ tailWord_3439601).sum := by decide
  have hdescent : baseEnd_3439601 < baseStart_3439601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439641 : List Nat := [1, 2, 1, 2, 1, 1, 5, 3, 2, 3, 2]
def baseStart_3439641 : Nat := 118140960795 + 3439641 * 2 ^ 59
def prefixEnd_3439641 : Nat := 4983230072969 + 3 ^ 40 * 3439641 * 2
def baseEnd_3439641 : Nat := 1766189111911682122468885

theorem tailTrace_3439641 : CollatzResearch.WordTrace tailWord_3439641 prefixEnd_3439641 1766189111911682122468885 := by
  unfold tailWord_3439641
  simp only [CollatzResearch.WordTrace]
  refine ⟨125454013731775575759110777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83636009154517050506073851 125454013731775575759110777)
  ·
    refine ⟨94090510298831681819333083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125454013731775575759110777 94090510298831681819333083)
    ·
      refine ⟨141135765448247522728999625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94090510298831681819333083 141135765448247522728999625)
      ·
        refine ⟨105851824086185642046749719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141135765448247522728999625 105851824086185642046749719)
        ·
          refine ⟨158777736129278463070124579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105851824086185642046749719 158777736129278463070124579)
          ·
            refine ⟨238166604193917694605186869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158777736129278463070124579 238166604193917694605186869)
            ·
              refine ⟨22328119143179783869236269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 238166604193917694605186869 22328119143179783869236269)
              ·
                refine ⟨8373044678692418950963601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22328119143179783869236269 8373044678692418950963601)
                ·
                  refine ⟨6279783509019314213222701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8373044678692418950963601 6279783509019314213222701)
                  ·
                    refine ⟨2354918815882242829958513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6279783509019314213222701 2354918815882242829958513)
                    ·
                      refine ⟨1766189111911682122468885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2354918815882242829958513 1766189111911682122468885)
                      ·
                        rfl

theorem cell23_3439641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 3, 2].length) (baseStart_3439641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439641 prefixEnd_3439641 := by exact prefixLift 3439641
  have htrace : WordTrace (prefixWord ++ tailWord_3439641) baseStart_3439641 baseEnd_3439641 := by
    simpa [prefixWord, tailWord_3439641, baseEnd_3439641] using wordTrace_append hprefix tailTrace_3439641
  have hstable : (prefixWord ++ tailWord_3439641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439641).length < 2 ^ (prefixWord ++ tailWord_3439641).sum := by decide
  have hdescent : baseEnd_3439641 < baseStart_3439641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439674 : List Nat := [3, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5]
def baseStart_3439674 : Nat := 118140960795 + 3439674 * 2 ^ 59
def prefixEnd_3439674 : Nat := 4983230072969 + 3 ^ 40 * 3439674 * 2
def baseEnd_3439674 : Nat := 1766206056773280493356233

theorem tailTrace_3439674 : CollatzResearch.WordTrace tailWord_3439674 prefixEnd_3439674 1766206056773280493356233 := by
  unfold tailWord_3439674
  simp only [CollatzResearch.WordTrace]
  refine ⟨31363804335164005598765519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83636811560437348263374717 31363804335164005598765519)
  ·
    refine ⟨47045706502746008398148279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31363804335164005598765519 47045706502746008398148279)
    ·
      refine ⟨70568559754119012597222419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47045706502746008398148279 70568559754119012597222419)
      ·
        refine ⟨105852839631178518895833629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70568559754119012597222419 105852839631178518895833629)
        ·
          refine ⟨39694814861691944585937611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105852839631178518895833629 39694814861691944585937611)
          ·
            refine ⟨59542222292537916878906417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39694814861691944585937611 59542222292537916878906417)
            ·
              refine ⟨44656666719403437659179813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59542222292537916878906417 44656666719403437659179813)
              ·
                refine ⟨8373125009888144561096215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44656666719403437659179813 8373125009888144561096215)
                ·
                  refine ⟨12559687514832216841644323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8373125009888144561096215 12559687514832216841644323)
                  ·
                    refine ⟨18839531272248325262466485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12559687514832216841644323 18839531272248325262466485)
                    ·
                      refine ⟨1766206056773280493356233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18839531272248325262466485 1766206056773280493356233)
                      ·
                        rfl

theorem cell23_3439674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_3439674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439674 prefixEnd_3439674 := by exact prefixLift 3439674
  have htrace : WordTrace (prefixWord ++ tailWord_3439674) baseStart_3439674 baseEnd_3439674 := by
    simpa [prefixWord, tailWord_3439674, baseEnd_3439674] using wordTrace_append hprefix tailTrace_3439674
  have hstable : (prefixWord ++ tailWord_3439674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439674).length < 2 ^ (prefixWord ++ tailWord_3439674).sum := by decide
  have hdescent : baseEnd_3439674 < baseStart_3439674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439688 : List Nat := [2, 1, 3, 1, 1, 1, 5, 2, 3, 2, 2]
def baseStart_3439688 : Nat := 118140960795 + 3439688 * 2 ^ 59
def prefixEnd_3439688 : Nat := 4983230072969 + 3 ^ 40 * 3439688 * 2
def baseEnd_3439688 : Nat := 1766213245502443438581169

theorem tailTrace_3439688 : CollatzResearch.WordTrace tailWord_3439688 prefixEnd_3439688 1766213245502443438581169 := by
  unfold tailWord_3439688
  simp only [CollatzResearch.WordTrace]
  refine ⟨62727863981302651393035859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83637151975070201857381145 62727863981302651393035859)
  ·
    refine ⟨94091795971953977089553789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62727863981302651393035859 94091795971953977089553789)
    ·
      refine ⟨35284423489482741408582671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94091795971953977089553789 35284423489482741408582671)
      ·
        refine ⟨52926635234224112112874007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35284423489482741408582671 52926635234224112112874007)
        ·
          refine ⟨79389952851336168169311011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52926635234224112112874007 79389952851336168169311011)
          ·
            refine ⟨119084929277004252253966517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79389952851336168169311011 119084929277004252253966517)
            ·
              refine ⟨11164212119719148648809361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119084929277004252253966517 11164212119719148648809361)
              ·
                refine ⟨8373159089789361486607021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11164212119719148648809361 8373159089789361486607021)
                ·
                  refine ⟨3139934658671010557477633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8373159089789361486607021 3139934658671010557477633)
                  ·
                    refine ⟨2354950994003257918108225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3139934658671010557477633 2354950994003257918108225)
                    ·
                      refine ⟨1766213245502443438581169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2354950994003257918108225 1766213245502443438581169)
                      ·
                        rfl

theorem cell23_3439688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_3439688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439688 prefixEnd_3439688 := by exact prefixLift 3439688
  have htrace : WordTrace (prefixWord ++ tailWord_3439688) baseStart_3439688 baseEnd_3439688 := by
    simpa [prefixWord, tailWord_3439688, baseEnd_3439688] using wordTrace_append hprefix tailTrace_3439688
  have hstable : (prefixWord ++ tailWord_3439688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439688).length < 2 ^ (prefixWord ++ tailWord_3439688).sum := by decide
  have hdescent : baseEnd_3439688 < baseStart_3439688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439708 : List Nat := [2, 2, 4, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_3439708 : Nat := 118140960795 + 3439708 * 2 ^ 59
def prefixEnd_3439708 : Nat := 4983230072969 + 3 ^ 40 * 3439708 * 2
def baseEnd_3439708 : Nat := 1766223515115533360331077

theorem tailTrace_3439708 : CollatzResearch.WordTrace tailWord_3439708 prefixEnd_3439708 1766223515115533360331077 := by
  unfold tailWord_3439708
  simp only [CollatzResearch.WordTrace]
  refine ⟨62728228711266423100899889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83637638281688564134533185 62728228711266423100899889)
  ·
    refine ⟨47046171533449817325674917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62728228711266423100899889 47046171533449817325674917)
    ·
      refine ⟨8821157162521840748564047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47046171533449817325674917 8821157162521840748564047)
      ·
        refine ⟨13231735743782761122846071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8821157162521840748564047 13231735743782761122846071)
        ·
          refine ⟨19847603615674141684269107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13231735743782761122846071 19847603615674141684269107)
          ·
            refine ⟨29771405423511212526403661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19847603615674141684269107 29771405423511212526403661)
            ·
              refine ⟨11164277033816704697401373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29771405423511212526403661 11164277033816704697401373)
              ·
                refine ⟨4186603887681264261525515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11164277033816704697401373 4186603887681264261525515)
                ·
                  refine ⟨6279905831521896392288273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4186603887681264261525515 6279905831521896392288273)
                  ·
                    refine ⟨4709929373641422294216205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6279905831521896392288273 4709929373641422294216205)
                    ·
                      refine ⟨1766223515115533360331077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4709929373641422294216205 1766223515115533360331077)
                      ·
                        rfl

theorem cell23_3439708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_3439708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439708 prefixEnd_3439708 := by exact prefixLift 3439708
  have htrace : WordTrace (prefixWord ++ tailWord_3439708) baseStart_3439708 baseEnd_3439708 := by
    simpa [prefixWord, tailWord_3439708, baseEnd_3439708] using wordTrace_append hprefix tailTrace_3439708
  have hstable : (prefixWord ++ tailWord_3439708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439708).length < 2 ^ (prefixWord ++ tailWord_3439708).sum := by decide
  have hdescent : baseEnd_3439708 < baseStart_3439708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439722 : List Nat := [3, 1, 3, 2, 2, 1, 2, 4, 1, 2, 2]
def baseStart_3439722 : Nat := 118140960795 + 3439722 * 2 ^ 59
def prefixEnd_3439722 : Nat := 4983230072969 + 3 ^ 40 * 3439722 * 2
def baseEnd_3439722 : Nat := 1766230703844696305556013

theorem tailTrace_3439722 : CollatzResearch.WordTrace tailWord_3439722 prefixEnd_3439722 1766230703844696305556013 := by
  unfold tailWord_3439722
  simp only [CollatzResearch.WordTrace]
  refine ⟨31364242011120531648202355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83637978696321417728539613 31364242011120531648202355)
  ·
    refine ⟨47046363016680797472303533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31364242011120531648202355 47046363016680797472303533)
    ·
      refine ⟨17642386131255299052113825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47046363016680797472303533 17642386131255299052113825)
      ·
        refine ⟨13231789598441474289085369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17642386131255299052113825 13231789598441474289085369)
        ·
          refine ⟨9923842198831105716814027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13231789598441474289085369 9923842198831105716814027)
          ·
            refine ⟨14885763298246658575221041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9923842198831105716814027 14885763298246658575221041)
            ·
              refine ⟨11164322473684993931415781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14885763298246658575221041 11164322473684993931415781)
              ·
                refine ⟨2093310463815936362140459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11164322473684993931415781 2093310463815936362140459)
                ·
                  refine ⟨3139965695723904543210689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2093310463815936362140459 3139965695723904543210689)
                  ·
                    refine ⟨2354974271792928407408017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3139965695723904543210689 2354974271792928407408017)
                    ·
                      refine ⟨1766230703844696305556013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2354974271792928407408017 1766230703844696305556013)
                      ·
                        rfl

theorem cell23_3439722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_3439722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439722 prefixEnd_3439722 := by exact prefixLift 3439722
  have htrace : WordTrace (prefixWord ++ tailWord_3439722) baseStart_3439722 baseEnd_3439722 := by
    simpa [prefixWord, tailWord_3439722, baseEnd_3439722] using wordTrace_append hprefix tailTrace_3439722
  have hstable : (prefixWord ++ tailWord_3439722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439722).length < 2 ^ (prefixWord ++ tailWord_3439722).sum := by decide
  have hdescent : baseEnd_3439722 < baseStart_3439722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439744 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 4]
def baseStart_3439744 : Nat := 118140960795 + 3439744 * 2 ^ 59
def prefixEnd_3439744 : Nat := 4983230072969 + 3 ^ 40 * 3439744 * 2
def baseEnd_3439744 : Nat := 1766242000419095219480911

theorem tailTrace_3439744 : CollatzResearch.WordTrace tailWord_3439744 prefixEnd_3439744 1766242000419095219480911 := by
  unfold tailWord_3439744
  simp only [CollatzResearch.WordTrace]
  refine ⟨62728885225201212175055143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83638513633601616233406857 62728885225201212175055143)
  ·
    refine ⟨94093327837801818262582715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62728885225201212175055143 94093327837801818262582715)
    ·
      refine ⟨141139991756702727393874073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94093327837801818262582715 141139991756702727393874073)
      ·
        refine ⟨105854993817527045545405555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141139991756702727393874073 105854993817527045545405555)
        ·
          refine ⟨158782490726290568318108333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105854993817527045545405555 158782490726290568318108333)
          ·
            refine ⟨59543434022358963119290625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158782490726290568318108333 59543434022358963119290625)
            ·
              refine ⟨44657575516769222339467969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59543434022358963119290625 44657575516769222339467969)
              ·
                refine ⟨33493181637576916754600977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44657575516769222339467969 33493181637576916754600977)
                ·
                  refine ⟨25119886228182687565950733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33493181637576916754600977 25119886228182687565950733)
                  ·
                    refine ⟨9419957335568507837231525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25119886228182687565950733 9419957335568507837231525)
                    ·
                      refine ⟨1766242000419095219480911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9419957335568507837231525 1766242000419095219480911)
                      ·
                        rfl

theorem cell23_3439744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_3439744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439744 prefixEnd_3439744 := by exact prefixLift 3439744
  have htrace : WordTrace (prefixWord ++ tailWord_3439744) baseStart_3439744 baseEnd_3439744 := by
    simpa [prefixWord, tailWord_3439744, baseEnd_3439744] using wordTrace_append hprefix tailTrace_3439744
  have hstable : (prefixWord ++ tailWord_3439744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439744).length < 2 ^ (prefixWord ++ tailWord_3439744).sum := by decide
  have hdescent : baseEnd_3439744 < baseStart_3439744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439789 : List Nat := [1, 5, 2, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_3439789 : Nat := 118140960795 + 3439789 * 2 ^ 59
def prefixEnd_3439789 : Nat := 4983230072969 + 3 ^ 40 * 3439789 * 2
def baseEnd_3439789 : Nat := 1766265107048547543418205

theorem tailTrace_3439789 : CollatzResearch.WordTrace tailWord_3439789 prefixEnd_3439789 1766265107048547543418205 := by
  unfold tailWord_3439789
  simp only [CollatzResearch.WordTrace]
  refine ⟨125459411735239397035498421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83639607823492931356998947 125459411735239397035498421)
  ·
    refine ⟨11761819850178693472077977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125459411735239397035498421 11761819850178693472077977)
    ·
      refine ⟨8821364887634020104058483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11761819850178693472077977 8821364887634020104058483)
      ·
        refine ⟨13232047331451030156087725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8821364887634020104058483 13232047331451030156087725)
        ·
          refine ⟨4962017749294136308532897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13232047331451030156087725 4962017749294136308532897)
          ·
            refine ⟨3721513311970602231399673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4962017749294136308532897 3721513311970602231399673)
            ·
              refine ⟨2791134983977951673549755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3721513311970602231399673 2791134983977951673549755)
              ·
                refine ⟨4186702475966927510324633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2791134983977951673549755 4186702475966927510324633)
                ·
                  refine ⟨3140026856975195632743475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4186702475966927510324633 3140026856975195632743475)
                  ·
                    refine ⟨4710040285462793449115213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3140026856975195632743475 4710040285462793449115213)
                    ·
                      refine ⟨1766265107048547543418205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4710040285462793449115213 1766265107048547543418205)
                      ·
                        rfl

theorem cell23_3439789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_3439789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439789 prefixEnd_3439789 := by exact prefixLift 3439789
  have htrace : WordTrace (prefixWord ++ tailWord_3439789) baseStart_3439789 baseEnd_3439789 := by
    simpa [prefixWord, tailWord_3439789, baseEnd_3439789] using wordTrace_append hprefix tailTrace_3439789
  have hstable : (prefixWord ++ tailWord_3439789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439789).length < 2 ^ (prefixWord ++ tailWord_3439789).sum := by decide
  have hdescent : baseEnd_3439789 < baseStart_3439789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439831 : List Nat := [1, 1, 3, 2, 1, 2, 4, 2, 2, 5]
def baseStart_3439831 : Nat := 118140960795 + 3439831 * 2 ^ 59
def prefixEnd_3439831 : Nat := 4983230072969 + 3 ^ 40 * 3439831 * 2
def baseEnd_3439831 : Nat := 588762224412012126364337

theorem tailTrace_3439831 : CollatzResearch.WordTrace tailWord_3439831 prefixEnd_3439831 588762224412012126364337 := by
  unfold tailWord_3439831
  simp only [CollatzResearch.WordTrace]
  refine ⟨125460943601087238208527347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83640629067391492139018231 125460943601087238208527347)
  ·
    refine ⟨188191415401630857312791021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125460943601087238208527347 188191415401630857312791021)
    ·
      refine ⟨70571780775611571492296633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188191415401630857312791021 70571780775611571492296633)
      ·
        refine ⟨52928835581708678619222475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70571780775611571492296633 52928835581708678619222475)
        ·
          refine ⟨79393253372563017928833713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52928835581708678619222475 79393253372563017928833713)
          ·
            refine ⟨59544940029422263446625285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79393253372563017928833713 59544940029422263446625285)
            ·
              refine ⟨11164676255516674396242241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59544940029422263446625285 11164676255516674396242241)
              ·
                refine ⟨8373507191637505797181681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11164676255516674396242241 8373507191637505797181681)
                ·
                  refine ⟨6280130393728129347886261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8373507191637505797181681 6280130393728129347886261)
                  ·
                    refine ⟨588762224412012126364337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6280130393728129347886261 588762224412012126364337)
                    ·
                      rfl

theorem cell23_3439831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_3439831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439831 prefixEnd_3439831 := by exact prefixLift 3439831
  have htrace : WordTrace (prefixWord ++ tailWord_3439831) baseStart_3439831 baseEnd_3439831 := by
    simpa [prefixWord, tailWord_3439831, baseEnd_3439831] using wordTrace_append hprefix tailTrace_3439831
  have hstable : (prefixWord ++ tailWord_3439831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439831).length < 2 ^ (prefixWord ++ tailWord_3439831).sum := by decide
  have hdescent : baseEnd_3439831 < baseStart_3439831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439841 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_3439841 : Nat := 118140960795 + 3439841 * 2 ^ 59
def prefixEnd_3439841 : Nat := 4983230072969 + 3 ^ 40 * 3439841 * 2
def baseEnd_3439841 : Nat := 1766291808042581339967965

theorem tailTrace_3439841 : CollatzResearch.WordTrace tailWord_3439841 prefixEnd_3439841 1766291808042581339967965 := by
  unfold tailWord_3439841
  simp only [CollatzResearch.WordTrace]
  refine ⟨125461308331051009916391377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83640872220700673277594251 125461308331051009916391377)
  ·
    refine ⟨94095981248288257437293533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125461308331051009916391377 94095981248288257437293533)
    ·
      refine ⟨35285992968108096538985075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94095981248288257437293533 35285992968108096538985075)
      ·
        refine ⟨52928989452162144808477613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35285992968108096538985075 52928989452162144808477613)
        ·
          refine ⟨19848371044560804303179105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52928989452162144808477613 19848371044560804303179105)
          ·
            refine ⟨14886278283420603227384329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19848371044560804303179105 14886278283420603227384329)
            ·
              refine ⟨11164708712565452420538247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14886278283420603227384329 11164708712565452420538247)
              ·
                refine ⟨16747063068848178630807371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11164708712565452420538247 16747063068848178630807371)
                ·
                  refine ⟨25120594603272267946211057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16747063068848178630807371 25120594603272267946211057)
                  ·
                    refine ⟨18840445952454200959658293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25120594603272267946211057 18840445952454200959658293)
                    ·
                      refine ⟨1766291808042581339967965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18840445952454200959658293 1766291808042581339967965)
                      ·
                        rfl

theorem cell23_3439841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_3439841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439841 prefixEnd_3439841 := by exact prefixLift 3439841
  have htrace : WordTrace (prefixWord ++ tailWord_3439841) baseStart_3439841 baseEnd_3439841 := by
    simpa [prefixWord, tailWord_3439841, baseEnd_3439841] using wordTrace_append hprefix tailTrace_3439841
  have hstable : (prefixWord ++ tailWord_3439841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439841).length < 2 ^ (prefixWord ++ tailWord_3439841).sum := by decide
  have hdescent : baseEnd_3439841 < baseStart_3439841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439868 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 1, 3, 4]
def baseStart_3439868 : Nat := 118140960795 + 3439868 * 2 ^ 59
def prefixEnd_3439868 : Nat := 4983230072969 + 3 ^ 40 * 3439868 * 2
def baseEnd_3439868 : Nat := 1766305672020252734330341

theorem tailTrace_3439868 : CollatzResearch.WordTrace tailWord_3439868 prefixEnd_3439868 1766305672020252734330341 := by
  unfold tailWord_3439868
  simp only [CollatzResearch.WordTrace]
  refine ⟨62731146550976596763812129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83641528734635462351749505 62731146550976596763812129)
  ·
    refine ⟨47048359913232447572859097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62731146550976596763812129 47048359913232447572859097)
    ·
      refine ⟨35286269934924335679644323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47048359913232447572859097 35286269934924335679644323)
      ·
        refine ⟨52929404902386503519466485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35286269934924335679644323 52929404902386503519466485)
        ·
          refine ⟨4962131709598734704949983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52929404902386503519466485 4962131709598734704949983)
          ·
            refine ⟨7443197564398102057424975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4962131709598734704949983 7443197564398102057424975)
            ·
              refine ⟨11164796346597153086137463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7443197564398102057424975 11164796346597153086137463)
              ·
                refine ⟨16747194519895729629206195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11164796346597153086137463 16747194519895729629206195)
                ·
                  refine ⟨25120791779843594443809293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16747194519895729629206195 25120791779843594443809293)
                  ·
                    refine ⟨9420296917441347916428485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25120791779843594443809293 9420296917441347916428485)
                    ·
                      refine ⟨1766305672020252734330341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9420296917441347916428485 1766305672020252734330341)
                      ·
                        rfl

theorem cell23_3439868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_3439868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439868 prefixEnd_3439868 := by exact prefixLift 3439868
  have htrace : WordTrace (prefixWord ++ tailWord_3439868) baseStart_3439868 baseEnd_3439868 := by
    simpa [prefixWord, tailWord_3439868, baseEnd_3439868] using wordTrace_append hprefix tailTrace_3439868
  have hstable : (prefixWord ++ tailWord_3439868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439868).length < 2 ^ (prefixWord ++ tailWord_3439868).sum := by decide
  have hdescent : baseEnd_3439868 < baseStart_3439868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439895 : List Nat := [1, 1, 3, 4, 1, 1, 1, 6, 1, 4]
def baseStart_3439895 : Nat := 118140960795 + 3439895 * 2 ^ 59
def prefixEnd_3439895 : Nat := 4983230072969 + 3 ^ 40 * 3439895 * 2
def baseEnd_3439895 : Nat := 588773178665974709564239

theorem tailTrace_3439895 : CollatzResearch.WordTrace tailWord_3439895 prefixEnd_3439895 588773178665974709564239 := by
  unfold tailWord_3439895
  simp only [CollatzResearch.WordTrace]
  refine ⟨125463277872855377138857139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83642185248570251425904759 125463277872855377138857139)
  ·
    refine ⟨188194916809283065708285709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125463277872855377138857139 188194916809283065708285709)
    ·
      refine ⟨70573093803481149640607141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188194916809283065708285709 70573093803481149640607141)
      ·
        refine ⟨13232455088152715557613839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70573093803481149640607141 13232455088152715557613839)
        ·
          refine ⟨19848682632229073336420759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13232455088152715557613839 19848682632229073336420759)
          ·
            refine ⟨29773023948343610004631139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19848682632229073336420759 29773023948343610004631139)
            ·
              refine ⟨44659535922515415006946709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29773023948343610004631139 44659535922515415006946709)
              ·
                refine ⟨2093415746367910078450627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44659535922515415006946709 2093415746367910078450627)
                ·
                  refine ⟨3140123619551865117675941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2093415746367910078450627 3140123619551865117675941)
                  ·
                    refine ⟨588773178665974709564239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3140123619551865117675941 588773178665974709564239)
                    ·
                      rfl

theorem cell23_3439895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 1, 4].length) (baseStart_3439895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439895 prefixEnd_3439895 := by exact prefixLift 3439895
  have htrace : WordTrace (prefixWord ++ tailWord_3439895) baseStart_3439895 baseEnd_3439895 := by
    simpa [prefixWord, tailWord_3439895, baseEnd_3439895] using wordTrace_append hprefix tailTrace_3439895
  have hstable : (prefixWord ++ tailWord_3439895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439895).length < 2 ^ (prefixWord ++ tailWord_3439895).sum := by decide
  have hdescent : baseEnd_3439895 < baseStart_3439895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439929 : List Nat := [1, 2, 1, 6, 2, 2, 1, 3, 1, 4]
def baseStart_3439929 : Nat := 118140960795 + 3439929 * 2 ^ 59
def prefixEnd_3439929 : Nat := 4983230072969 + 3 ^ 40 * 3439929 * 2
def baseEnd_3439929 : Nat := 588778998113392331889187

theorem tailTrace_3439929 : CollatzResearch.WordTrace tailWord_3439929 prefixEnd_3439929 588778998113392331889187 := by
  unfold tailWord_3439929
  simp only [CollatzResearch.WordTrace]
  refine ⟨125464517954732200945594841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83643011969821467297063227 125464517954732200945594841)
  ·
    refine ⟨94098388466049150709196131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125464517954732200945594841 94098388466049150709196131)
    ·
      refine ⟨141147582699073726063794197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94098388466049150709196131 141147582699073726063794197)
      ·
        refine ⟨6616292939019080909240353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 141147582699073726063794197 6616292939019080909240353)
        ·
          refine ⟨4962219704264310681930265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6616292939019080909240353 4962219704264310681930265)
          ·
            refine ⟨3721664778198233011447699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4962219704264310681930265 3721664778198233011447699)
            ·
              refine ⟨5582497167297349517171549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3721664778198233011447699 5582497167297349517171549)
              ·
                refine ⟨2093436437736506068939331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5582497167297349517171549 2093436437736506068939331)
                ·
                  refine ⟨3140154656604759103408997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2093436437736506068939331 3140154656604759103408997)
                  ·
                    refine ⟨588778998113392331889187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3140154656604759103408997 588778998113392331889187)
                    ·
                      rfl

theorem cell23_3439929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 1, 4].length) (baseStart_3439929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439929 prefixEnd_3439929 := by exact prefixLift 3439929
  have htrace : WordTrace (prefixWord ++ tailWord_3439929) baseStart_3439929 baseEnd_3439929 := by
    simpa [prefixWord, tailWord_3439929, baseEnd_3439929] using wordTrace_append hprefix tailTrace_3439929
  have hstable : (prefixWord ++ tailWord_3439929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439929).length < 2 ^ (prefixWord ++ tailWord_3439929).sum := by decide
  have hdescent : baseEnd_3439929 < baseStart_3439929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439975 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_3439975 : Nat := 118140960795 + 3439975 * 2 ^ 59
def prefixEnd_3439975 : Nat := 4983230072969 + 3 ^ 40 * 3439975 * 2
def baseEnd_3439975 : Nat := 1766360614450283815692349

theorem tailTrace_3439975 : CollatzResearch.WordTrace tailWord_3439975 prefixEnd_3439975 1766360614450283815692349 := by
  unfold tailWord_3439975
  simp only [CollatzResearch.WordTrace]
  refine ⟨125466195712565550801769379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83644130475043700534512919 125466195712565550801769379)
  ·
    refine ⟨188199293568848326202654069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125466195712565550801769379 188199293568848326202654069)
    ·
      refine ⟨17643683772079530581498819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188199293568848326202654069 17643683772079530581498819)
      ·
        refine ⟨26465525658119295872248229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17643683772079530581498819 26465525658119295872248229)
        ·
          refine ⟨4962286060897367976046543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26465525658119295872248229 4962286060897367976046543)
          ·
            refine ⟨7443429091346051964069815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4962286060897367976046543 7443429091346051964069815)
            ·
              refine ⟨11165143637019077946104723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7443429091346051964069815 11165143637019077946104723)
              ·
                refine ⟨16747715455528616919157085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11165143637019077946104723 16747715455528616919157085)
                ·
                  refine ⟨6280393295823231344683907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16747715455528616919157085 6280393295823231344683907)
                  ·
                    refine ⟨9420589943734847017025861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6280393295823231344683907 9420589943734847017025861)
                    ·
                      refine ⟨1766360614450283815692349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9420589943734847017025861 1766360614450283815692349)
                      ·
                        rfl

theorem cell23_3439975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_3439975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3439975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3439975 prefixEnd_3439975 := by exact prefixLift 3439975
  have htrace : WordTrace (prefixWord ++ tailWord_3439975) baseStart_3439975 baseEnd_3439975 := by
    simpa [prefixWord, tailWord_3439975, baseEnd_3439975] using wordTrace_append hprefix tailTrace_3439975
  have hstable : (prefixWord ++ tailWord_3439975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439975).length < 2 ^ (prefixWord ++ tailWord_3439975).sum := by decide
  have hdescent : baseEnd_3439975 < baseStart_3439975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440011 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 1, 9]
def baseStart_3440011 : Nat := 118140960795 + 3440011 * 2 ^ 59
def prefixEnd_3440011 : Nat := 4983230072969 + 3 ^ 40 * 3440011 * 2
def baseEnd_3440011 : Nat := 588793033251281891614061

theorem tailTrace_3440011 : CollatzResearch.WordTrace tailWord_3440011 prefixEnd_3440011 588793033251281891614061 := by
  unfold tailWord_3440011
  simp only [CollatzResearch.WordTrace]
  refine ⟨125467508740435128950079887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83645005826956752633386591 125467508740435128950079887)
  ·
    refine ⟨188201263110652693425119831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125467508740435128950079887 188201263110652693425119831)
    ·
      refine ⟨282301894665979040137679747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188201263110652693425119831 282301894665979040137679747)
      ·
        refine ⟨423452841998968560206519621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282301894665979040137679747 423452841998968560206519621)
        ·
          refine ⟨79397407874806605038722429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 423452841998968560206519621 79397407874806605038722429)
          ·
            refine ⟨29774027953052476889520911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79397407874806605038722429 29774027953052476889520911)
            ·
              refine ⟨44661041929578715334281367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29774027953052476889520911 44661041929578715334281367)
              ·
                refine ⟨66991562894368073001422051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44661041929578715334281367 66991562894368073001422051)
                ·
                  refine ⟨100487344341552109502133077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66991562894368073001422051 100487344341552109502133077)
                  ·
                    refine ⟨588793033251281891614061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 100487344341552109502133077 588793033251281891614061)
                    ·
                      rfl

theorem cell23_3440011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 9].length) (baseStart_3440011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440011 prefixEnd_3440011 := by exact prefixLift 3440011
  have htrace : WordTrace (prefixWord ++ tailWord_3440011) baseStart_3440011 baseEnd_3440011 := by
    simpa [prefixWord, tailWord_3440011, baseEnd_3440011] using wordTrace_append hprefix tailTrace_3440011
  have hstable : (prefixWord ++ tailWord_3440011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440011).length < 2 ^ (prefixWord ++ tailWord_3440011).sum := by decide
  have hdescent : baseEnd_3440011 < baseStart_3440011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440025 : List Nat := [1, 2, 1, 2, 1, 6, 2, 1, 1, 3, 3]
def baseStart_3440025 : Nat := 118140960795 + 3440025 * 2 ^ 59
def prefixEnd_3440025 : Nat := 4983230072969 + 3 ^ 40 * 3440025 * 2
def baseEnd_3440025 : Nat := 1766386288483008620067119

theorem tailTrace_3440025 : CollatzResearch.WordTrace tailWord_3440025 prefixEnd_3440025 1766386288483008620067119 := by
  unfold tailWord_3440025
  simp only [CollatzResearch.WordTrace]
  refine ⟨125468019362384409341089529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83645346241589606227393019 125468019362384409341089529)
  ·
    refine ⟨94101014521788307005817147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125468019362384409341089529 94101014521788307005817147)
    ·
      refine ⟨141151521782682460508725721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94101014521788307005817147 141151521782682460508725721)
      ·
        refine ⟨105863641337011845381544291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141151521782682460508725721 105863641337011845381544291)
        ·
          refine ⟨158795462005517768072316437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105863641337011845381544291 158795462005517768072316437)
          ·
            refine ⟨7443537281508645378389833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 158795462005517768072316437 7443537281508645378389833)
            ·
              refine ⟨5582652961131484033792375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7443537281508645378389833 5582652961131484033792375)
              ·
                refine ⟨8373979441697226050688563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5582652961131484033792375 8373979441697226050688563)
                ·
                  refine ⟨12560969162545839076032845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8373979441697226050688563 12560969162545839076032845)
                  ·
                    refine ⟨4710363435954689653512317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12560969162545839076032845 4710363435954689653512317)
                    ·
                      refine ⟨1766386288483008620067119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4710363435954689653512317 1766386288483008620067119)
                      ·
                        rfl

theorem cell23_3440025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_3440025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440025 prefixEnd_3440025 := by exact prefixLift 3440025
  have htrace : WordTrace (prefixWord ++ tailWord_3440025) baseStart_3440025 baseEnd_3440025 := by
    simpa [prefixWord, tailWord_3440025, baseEnd_3440025] using wordTrace_append hprefix tailTrace_3440025
  have hstable : (prefixWord ++ tailWord_3440025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440025).length < 2 ^ (prefixWord ++ tailWord_3440025).sum := by decide
  have hdescent : baseEnd_3440025 < baseStart_3440025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440035 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 3, 3, 2]
def baseStart_3440035 : Nat := 118140960795 + 3440035 * 2 ^ 59
def prefixEnd_3440035 : Nat := 4983230072969 + 3 ^ 40 * 3440035 * 2
def baseEnd_3440035 : Nat := 1766391423289553580942073

theorem tailTrace_3440035 : CollatzResearch.WordTrace tailWord_3440035 prefixEnd_3440035 1766391423289553580942073 := by
  unfold tailWord_3440035
  simp only [CollatzResearch.WordTrace]
  refine ⟨125468384092348181048953559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83645589394898787365969039 125468384092348181048953559)
  ·
    refine ⟨188202576138522271573430339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125468384092348181048953559 188202576138522271573430339)
    ·
      refine ⟨282303864207783407360145509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188202576138522271573430339 282303864207783407360145509)
      ·
        refine ⟨52931974538959388880027283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282303864207783407360145509 52931974538959388880027283)
        ·
          refine ⟨79397961808439083320040925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52931974538959388880027283 79397961808439083320040925)
          ·
            refine ⟨29774235678164656245015347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79397961808439083320040925 29774235678164656245015347)
            ·
              refine ⟨44661353517246984367523021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29774235678164656245015347 44661353517246984367523021)
              ·
                refine ⟨16748007568967619137821133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44661353517246984367523021 16748007568967619137821133)
                ·
                  refine ⟨6280502838362857176682925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16748007568967619137821133 6280502838362857176682925)
                  ·
                    refine ⟨2355188564386071441256097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6280502838362857176682925 2355188564386071441256097)
                    ·
                      refine ⟨1766391423289553580942073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2355188564386071441256097 1766391423289553580942073)
                      ·
                        rfl

theorem cell23_3440035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_3440035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440035 prefixEnd_3440035 := by exact prefixLift 3440035
  have htrace : WordTrace (prefixWord ++ tailWord_3440035) baseStart_3440035 baseEnd_3440035 := by
    simpa [prefixWord, tailWord_3440035, baseEnd_3440035] using wordTrace_append hprefix tailTrace_3440035
  have hstable : (prefixWord ++ tailWord_3440035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440035).length < 2 ^ (prefixWord ++ tailWord_3440035).sum := by decide
  have hdescent : baseEnd_3440035 < baseStart_3440035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440086 : List Nat := [5, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_3440086 : Nat := 118140960795 + 3440086 * 2 ^ 59
def prefixEnd_3440086 : Nat := 4983230072969 + 3 ^ 40 * 3440086 * 2
def baseEnd_3440086 : Nat := 1766417610802932881404339

theorem tailTrace_3440086 : CollatzResearch.WordTrace tailWord_3440086 prefixEnd_3440086 1766417610802932881404339 := by
  unfold tailWord_3440086
  simp only [CollatzResearch.WordTrace]
  refine ⟨7841890263447713547441257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83646829476775611172706741 7841890263447713547441257)
  ·
    refine ⟨5881417697585785160580943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7841890263447713547441257 5881417697585785160580943)
    ·
      refine ⟨8822126546378677740871415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5881417697585785160580943 8822126546378677740871415)
      ·
        refine ⟨13233189819568016611307123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8822126546378677740871415 13233189819568016611307123)
        ·
          refine ⟨19849784729352024916960685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13233189819568016611307123 19849784729352024916960685)
          ·
            refine ⟨7443669273507009343860257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19849784729352024916960685 7443669273507009343860257)
            ·
              refine ⟨5582751955130257007895193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7443669273507009343860257 5582751955130257007895193)
              ·
                refine ⟨4187063966347692755921395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5582751955130257007895193 4187063966347692755921395)
                ·
                  refine ⟨6280595949521539133882093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4187063966347692755921395 6280595949521539133882093)
                  ·
                    refine ⟨2355223481070577175205785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6280595949521539133882093 2355223481070577175205785)
                    ·
                      refine ⟨1766417610802932881404339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2355223481070577175205785 1766417610802932881404339)
                      ·
                        rfl

theorem cell23_3440086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_3440086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440086 prefixEnd_3440086 := by exact prefixLift 3440086
  have htrace : WordTrace (prefixWord ++ tailWord_3440086) baseStart_3440086 baseEnd_3440086 := by
    simpa [prefixWord, tailWord_3440086, baseEnd_3440086] using wordTrace_append hprefix tailTrace_3440086
  have hstable : (prefixWord ++ tailWord_3440086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440086).length < 2 ^ (prefixWord ++ tailWord_3440086).sum := by decide
  have hdescent : baseEnd_3440086 < baseStart_3440086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440088 : List Nat := [2, 1, 2, 2, 2, 1, 4, 2, 7]
def baseStart_3440088 : Nat := 118140960795 + 3440088 * 2 ^ 59
def prefixEnd_3440088 : Nat := 4983230072969 + 3 ^ 40 * 3440088 * 2
def baseEnd_3440088 : Nat := 196268737529360208175481

theorem tailTrace_3440088 : CollatzResearch.WordTrace tailWord_3440088 prefixEnd_3440088 196268737529360208175481 := by
  unfold tailWord_3440088
  simp only [CollatzResearch.WordTrace]
  refine ⟨62735158580578085550316459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83646878107437447400421945 62735158580578085550316459)
  ·
    refine ⟨94102737870867128325474689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62735158580578085550316459 94102737870867128325474689)
    ·
      refine ⟨70577053403150346244106017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94102737870867128325474689 70577053403150346244106017)
      ·
        refine ⟨52932790052362759683079513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70577053403150346244106017 52932790052362759683079513)
        ·
          refine ⟨39699592539272069762309635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52932790052362759683079513 39699592539272069762309635)
          ·
            refine ⟨59549388808908104643464453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39699592539272069762309635 59549388808908104643464453)
            ·
              refine ⟨11165510401670269620649585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59549388808908104643464453 11165510401670269620649585)
              ·
                refine ⟨8374132801252702215487189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11165510401670269620649585 8374132801252702215487189)
                ·
                  refine ⟨196268737529360208175481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8374132801252702215487189 196268737529360208175481)
                  ·
                    rfl

theorem cell23_3440088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 7].length) (baseStart_3440088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440088 prefixEnd_3440088 := by exact prefixLift 3440088
  have htrace : WordTrace (prefixWord ++ tailWord_3440088) baseStart_3440088 baseEnd_3440088 := by
    simpa [prefixWord, tailWord_3440088, baseEnd_3440088] using wordTrace_append hprefix tailTrace_3440088
  have hstable : (prefixWord ++ tailWord_3440088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440088).length < 2 ^ (prefixWord ++ tailWord_3440088).sum := by decide
  have hdescent : baseEnd_3440088 < baseStart_3440088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440122 : List Nat := [3, 1, 1, 1, 1, 2, 7, 2, 5]
def baseStart_3440122 : Nat := 118140960795 + 3440122 * 2 ^ 59
def prefixEnd_3440122 : Nat := 4983230072969 + 3 ^ 40 * 3440122 * 2
def baseEnd_3440122 : Nat := 196270677345166082283797

theorem tailTrace_3440122 : CollatzResearch.WordTrace tailWord_3440122 prefixEnd_3440122 196270677345166082283797 := by
  unfold tailWord_3440122
  simp only [CollatzResearch.WordTrace]
  refine ⟨31367889310758248726842655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83647704828688663271580413 31367889310758248726842655)
  ·
    refine ⟨47051833966137373090263983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31367889310758248726842655 47051833966137373090263983)
    ·
      refine ⟨70577750949206059635395975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47051833966137373090263983 70577750949206059635395975)
      ·
        refine ⟨105866626423809089453093963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70577750949206059635395975 105866626423809089453093963)
        ·
          refine ⟨158799939635713634179640945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105866626423809089453093963 158799939635713634179640945)
          ·
            refine ⟨119099954726785225634730709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158799939635713634179640945 119099954726785225634730709)
            ·
              refine ⟨2791405188909028725814001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 119099954726785225634730709 2791405188909028725814001)
              ·
                refine ⟨2093553891681771544360501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2791405188909028725814001 2093553891681771544360501)
                ·
                  refine ⟨196270677345166082283797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2093553891681771544360501 196270677345166082283797)
                  ·
                    rfl

theorem cell23_3440122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 5].length) (baseStart_3440122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440122 prefixEnd_3440122 := by exact prefixLift 3440122
  have htrace : WordTrace (prefixWord ++ tailWord_3440122) baseStart_3440122 baseEnd_3440122 := by
    simpa [prefixWord, tailWord_3440122, baseEnd_3440122] using wordTrace_append hprefix tailTrace_3440122
  have hstable : (prefixWord ++ tailWord_3440122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440122).length < 2 ^ (prefixWord ++ tailWord_3440122).sum := by decide
  have hdescent : baseEnd_3440122 < baseStart_3440122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440152 : List Nat := [2, 1, 2, 3, 4, 1, 2, 1, 2, 5]
def baseStart_3440152 : Nat := 118140960795 + 3440152 * 2 ^ 59
def prefixEnd_3440152 : Nat := 4983230072969 + 3 ^ 40 * 3440152 * 2
def baseEnd_3440152 : Nat := 588817166842043207726345

theorem tailTrace_3440152 : CollatzResearch.WordTrace tailWord_3440152 prefixEnd_3440152 588817166842043207726345 := by
  unfold tailWord_3440152
  simp only [CollatzResearch.WordTrace]
  refine ⟨62736325716462155015481355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83648434288616206687308473 62736325716462155015481355)
  ·
    refine ⟨94104488574693232523222033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62736325716462155015481355 94104488574693232523222033)
    ·
      refine ⟨70578366431019924392416525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94104488574693232523222033 70578366431019924392416525)
      ·
        refine ⟨26466887411632471647156197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70578366431019924392416525 26466887411632471647156197)
        ·
          refine ⟨4962541389681088433841787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26466887411632471647156197 4962541389681088433841787)
          ·
            refine ⟨7443812084521632650762681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4962541389681088433841787 7443812084521632650762681)
            ·
              refine ⟨5582859063391224488072011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7443812084521632650762681 5582859063391224488072011)
              ·
                refine ⟨8374288595086836732108017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5582859063391224488072011 8374288595086836732108017)
                ·
                  refine ⟨6280716446315127549081013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8374288595086836732108017 6280716446315127549081013)
                  ·
                    refine ⟨588817166842043207726345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6280716446315127549081013 588817166842043207726345)
                    ·
                      rfl

theorem cell23_3440152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_3440152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440152 prefixEnd_3440152 := by exact prefixLift 3440152
  have htrace : WordTrace (prefixWord ++ tailWord_3440152) baseStart_3440152 baseEnd_3440152 := by
    simpa [prefixWord, tailWord_3440152, baseEnd_3440152] using wordTrace_append hprefix tailTrace_3440152
  have hstable : (prefixWord ++ tailWord_3440152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440152).length < 2 ^ (prefixWord ++ tailWord_3440152).sum := by decide
  have hdescent : baseEnd_3440152 < baseStart_3440152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440189 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 2, 4, 2]
def baseStart_3440189 : Nat := 118140960795 + 3440189 * 2 ^ 59
def prefixEnd_3440189 : Nat := 4983230072969 + 3 ^ 40 * 3440189 * 2
def baseEnd_3440189 : Nat := 1766470499310345978416365

theorem tailTrace_3440189 : CollatzResearch.WordTrace tailWord_3440189 prefixEnd_3440189 1766470499310345978416365 := by
  unfold tailWord_3440189
  simp only [CollatzResearch.WordTrace]
  refine ⟨125474000933790265350059621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83649333955860176900039747 125474000933790265350059621)
  ·
    refine ⟨23526375175085674753136179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125474000933790265350059621 23526375175085674753136179)
    ·
      refine ⟨35289562762628512129704269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23526375175085674753136179 35289562762628512129704269)
      ·
        refine ⟨13233586035985692048639101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35289562762628512129704269 13233586035985692048639101)
        ·
          refine ⟨4962594763494634518239663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13233586035985692048639101 4962594763494634518239663)
          ·
            refine ⟨7443892145241951777359495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4962594763494634518239663 7443892145241951777359495)
            ·
              refine ⟨11165838217862927666039243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7443892145241951777359495 11165838217862927666039243)
              ·
                refine ⟨16748757326794391499058865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11165838217862927666039243 16748757326794391499058865)
                ·
                  refine ⟨12561567995095793624294149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16748757326794391499058865 12561567995095793624294149)
                  ·
                    refine ⟨2355293999080461304555153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12561567995095793624294149 2355293999080461304555153)
                    ·
                      refine ⟨1766470499310345978416365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2355293999080461304555153 1766470499310345978416365)
                      ·
                        rfl

theorem cell23_3440189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_3440189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440189 prefixEnd_3440189 := by exact prefixLift 3440189
  have htrace : WordTrace (prefixWord ++ tailWord_3440189) baseStart_3440189 baseEnd_3440189 := by
    simpa [prefixWord, tailWord_3440189, baseEnd_3440189] using wordTrace_append hprefix tailTrace_3440189
  have hstable : (prefixWord ++ tailWord_3440189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440189).length < 2 ^ (prefixWord ++ tailWord_3440189).sum := by decide
  have hdescent : baseEnd_3440189 < baseStart_3440189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440290 : List Nat := [3, 3, 1, 4, 2, 1, 1, 1, 3, 1, 3]
def baseStart_3440290 : Nat := 118140960795 + 3440290 * 2 ^ 59
def prefixEnd_3440290 : Nat := 4983230072969 + 3 ^ 40 * 3440290 * 2
def baseEnd_3440290 : Nat := 1766522360856450083253401

theorem tailTrace_3440290 : CollatzResearch.WordTrace tailWord_3440290 prefixEnd_3440290 1766522360856450083253401 := by
  unfold tailWord_3440290
  simp only [CollatzResearch.WordTrace]
  refine ⟨31369421176606089899871581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83651789804282906399657549 31369421176606089899871581)
  ·
    refine ⟨11763532941227283712451843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31369421176606089899871581 11763532941227283712451843)
    ·
      refine ⟨17645299411840925568677765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11763532941227283712451843 17645299411840925568677765)
      ·
        refine ⟨3308493639720173544127081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17645299411840925568677765 3308493639720173544127081)
        ·
          refine ⟨2481370229790130158095311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3308493639720173544127081 2481370229790130158095311)
          ·
            refine ⟨3722055344685195237142967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2481370229790130158095311 3722055344685195237142967)
            ·
              refine ⟨5583083017027792855714451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3722055344685195237142967 5583083017027792855714451)
              ·
                refine ⟨8374624525541689283571677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5583083017027792855714451 8374624525541689283571677)
                ·
                  refine ⟨3140484197078133481339379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8374624525541689283571677 3140484197078133481339379)
                  ·
                    refine ⟨4710726295617200222009069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3140484197078133481339379 4710726295617200222009069)
                    ·
                      refine ⟨1766522360856450083253401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4710726295617200222009069 1766522360856450083253401)
                      ·
                        rfl

theorem cell23_3440290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_3440290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440290 prefixEnd_3440290 := by exact prefixLift 3440290
  have htrace : WordTrace (prefixWord ++ tailWord_3440290) baseStart_3440290 baseEnd_3440290 := by
    simpa [prefixWord, tailWord_3440290, baseEnd_3440290] using wordTrace_append hprefix tailTrace_3440290
  have hstable : (prefixWord ++ tailWord_3440290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440290).length < 2 ^ (prefixWord ++ tailWord_3440290).sum := by decide
  have hdescent : baseEnd_3440290 < baseStart_3440290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440316 : List Nat := [2, 2, 2, 3, 1, 4, 1, 2, 1, 2, 3]
def baseStart_3440316 : Nat := 118140960795 + 3440316 * 2 ^ 59
def prefixEnd_3440316 : Nat := 4983230072969 + 3 ^ 40 * 3440316 * 2
def baseEnd_3440316 : Nat := 1766535711353466981528281

theorem tailTrace_3440316 : CollatzResearch.WordTrace tailWord_3440316 prefixEnd_3440316 1766535711353466981528281 := by
  unfold tailWord_3440316
  simp only [CollatzResearch.WordTrace]
  refine ⟨62739316502165083019966401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83652422002886777359955201 62739316502165083019966401)
  ·
    refine ⟨47054487376623812264974801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62739316502165083019966401 47054487376623812264974801)
    ·
      refine ⟨35290865532467859198731101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47054487376623812264974801 35290865532467859198731101)
      ·
        refine ⟨13234074574675447199524163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35290865532467859198731101 13234074574675447199524163)
        ·
          refine ⟨19851111862013170799286245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13234074574675447199524163 19851111862013170799286245)
          ·
            refine ⟨3722083474127469524866171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19851111862013170799286245 3722083474127469524866171)
            ·
              refine ⟨5583125211191204287299257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3722083474127469524866171 5583125211191204287299257)
              ·
                refine ⟨4187343908393403215474443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5583125211191204287299257 4187343908393403215474443)
                ·
                  refine ⟨6281015862590104823211665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4187343908393403215474443 6281015862590104823211665)
                  ·
                    refine ⟨4710761896942578617408749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6281015862590104823211665 4710761896942578617408749)
                    ·
                      refine ⟨1766535711353466981528281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4710761896942578617408749 1766535711353466981528281)
                      ·
                        rfl

theorem cell23_3440316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_3440316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440316 prefixEnd_3440316 := by exact prefixLift 3440316
  have htrace : WordTrace (prefixWord ++ tailWord_3440316) baseStart_3440316 baseEnd_3440316 := by
    simpa [prefixWord, tailWord_3440316, baseEnd_3440316] using wordTrace_append hprefix tailTrace_3440316
  have hstable : (prefixWord ++ tailWord_3440316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440316).length < 2 ^ (prefixWord ++ tailWord_3440316).sum := by decide
  have hdescent : baseEnd_3440316 < baseStart_3440316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440326 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_3440326 : Nat := 118140960795 + 3440326 * 2 ^ 59
def prefixEnd_3440326 : Nat := 4983230072969 + 3 ^ 40 * 3440326 * 2
def baseEnd_3440326 : Nat := 1766540846160011942403235

theorem tailTrace_3440326 : CollatzResearch.WordTrace tailWord_3440326 prefixEnd_3440326 1766540846160011942403235 := by
  unfold tailWord_3440326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3921218679196685554618651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83652665156195958498531221 3921218679196685554618651)
  ·
    refine ⟨5881828018795028331927977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3921218679196685554618651 5881828018795028331927977)
    ·
      refine ⟨4411371014096271248945983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5881828018795028331927977 4411371014096271248945983)
      ·
        refine ⟨6617056521144406873418975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4411371014096271248945983 6617056521144406873418975)
        ·
          refine ⟨9925584781716610310128463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6617056521144406873418975 9925584781716610310128463)
          ·
            refine ⟨14888377172574915465192695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9925584781716610310128463 14888377172574915465192695)
            ·
              refine ⟨22332565758862373197789043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14888377172574915465192695 22332565758862373197789043)
              ·
                refine ⟨33498848638293559796683565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22332565758862373197789043 33498848638293559796683565)
                ·
                  refine ⟨12562068239360084923756337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33498848638293559796683565 12562068239360084923756337)
                  ·
                    refine ⟨9421551179520063692817253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12562068239360084923756337 9421551179520063692817253)
                    ·
                      refine ⟨1766540846160011942403235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9421551179520063692817253 1766540846160011942403235)
                      ·
                        rfl

theorem cell23_3440326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_3440326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440326 prefixEnd_3440326 := by exact prefixLift 3440326
  have htrace : WordTrace (prefixWord ++ tailWord_3440326) baseStart_3440326 baseEnd_3440326 := by
    simpa [prefixWord, tailWord_3440326, baseEnd_3440326] using wordTrace_append hprefix tailTrace_3440326
  have hstable : (prefixWord ++ tailWord_3440326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440326).length < 2 ^ (prefixWord ++ tailWord_3440326).sum := by decide
  have hdescent : baseEnd_3440326 < baseStart_3440326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440335 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 4]
def baseStart_3440335 : Nat := 118140960795 + 3440335 * 2 ^ 59
def prefixEnd_3440335 : Nat := 4983230072969 + 3 ^ 40 * 3440335 * 2
def baseEnd_3440335 : Nat := 1766545467485902407190693

theorem tailTrace_3440335 : CollatzResearch.WordTrace tailWord_3440335 prefixEnd_3440335 1766545467485902407190693 := by
  unfold tailWord_3440335
  simp only [CollatzResearch.WordTrace]
  refine ⟨125479325991261332284874459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83652883994174221523249639 125479325991261332284874459)
  ·
    refine ⟨188218988986891998427311689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125479325991261332284874459 188218988986891998427311689)
    ·
      refine ⟨141164241740168998820483767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188218988986891998427311689 141164241740168998820483767)
      ·
        refine ⟨211746362610253498230725651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141164241740168998820483767 211746362610253498230725651)
        ·
          refine ⟨317619543915380247346088477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211746362610253498230725651 317619543915380247346088477)
          ·
            refine ⟨119107328968267592754783179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317619543915380247346088477 119107328968267592754783179)
            ·
              refine ⟨178660993452401389132174769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119107328968267592754783179 178660993452401389132174769)
              ·
                refine ⟨133995745089301041849131077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178660993452401389132174769 133995745089301041849131077)
                ·
                  refine ⟨25124202204243945346712077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133995745089301041849131077 25124202204243945346712077)
                  ·
                    refine ⟨9421575826591479505017029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25124202204243945346712077 9421575826591479505017029)
                    ·
                      refine ⟨1766545467485902407190693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9421575826591479505017029 1766545467485902407190693)
                      ·
                        rfl

theorem cell23_3440335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_3440335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440335 prefixEnd_3440335 := by exact prefixLift 3440335
  have htrace : WordTrace (prefixWord ++ tailWord_3440335) baseStart_3440335 baseEnd_3440335 := by
    simpa [prefixWord, tailWord_3440335, baseEnd_3440335] using wordTrace_append hprefix tailTrace_3440335
  have hstable : (prefixWord ++ tailWord_3440335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440335).length < 2 ^ (prefixWord ++ tailWord_3440335).sum := by decide
  have hdescent : baseEnd_3440335 < baseStart_3440335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440346 : List Nat := [3, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3]
def baseStart_3440346 : Nat := 118140960795 + 3440346 * 2 ^ 59
def prefixEnd_3440346 : Nat := 4983230072969 + 3 ^ 40 * 3440346 * 2
def baseEnd_3440346 : Nat := 1766551115773101864153143

theorem tailTrace_3440346 : CollatzResearch.WordTrace tailWord_3440346 prefixEnd_3440346 1766551115773101864153143 := by
  unfold tailWord_3440346
  simp only [CollatzResearch.WordTrace]
  refine ⟨31369931798555370290881223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83653151462814320775683261 31369931798555370290881223)
  ·
    refine ⟨47054897697833055436321835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31369931798555370290881223 47054897697833055436321835)
    ·
      refine ⟨70582346546749583154482753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47054897697833055436321835 70582346546749583154482753)
      ·
        refine ⟨52936759910062187365862065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70582346546749583154482753 52936759910062187365862065)
        ·
          refine ⟨39702569932546640524396549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52936759910062187365862065 39702569932546640524396549)
          ·
            refine ⟨7444231862352495098324353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39702569932546640524396549 7444231862352495098324353)
            ·
              refine ⟨5583173896764371323743265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7444231862352495098324353 5583173896764371323743265)
              ·
                refine ⟨4187380422573278492807449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5583173896764371323743265 4187380422573278492807449)
                ·
                  refine ⟨3140535316929958869605587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4187380422573278492807449 3140535316929958869605587)
                  ·
                    refine ⟨4710802975394938304408381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3140535316929958869605587 4710802975394938304408381)
                    ·
                      refine ⟨1766551115773101864153143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4710802975394938304408381 1766551115773101864153143)
                      ·
                        rfl

theorem cell23_3440346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_3440346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440346 prefixEnd_3440346 := by exact prefixLift 3440346
  have htrace : WordTrace (prefixWord ++ tailWord_3440346) baseStart_3440346 baseEnd_3440346 := by
    simpa [prefixWord, tailWord_3440346, baseEnd_3440346] using wordTrace_append hprefix tailTrace_3440346
  have hstable : (prefixWord ++ tailWord_3440346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440346).length < 2 ^ (prefixWord ++ tailWord_3440346).sum := by decide
  have hdescent : baseEnd_3440346 < baseStart_3440346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440369 : List Nat := [1, 2, 2, 2, 2, 3, 1, 3, 1, 4, 2]
def baseStart_3440369 : Nat := 118140960795 + 3440369 * 2 ^ 59
def prefixEnd_3440369 : Nat := 4983230072969 + 3 ^ 40 * 3440369 * 2
def baseEnd_3440369 : Nat := 1766562925828155274165537

theorem tailTrace_3440369 : CollatzResearch.WordTrace tailWord_3440369 prefixEnd_3440369 1766562925828155274165537 := by
  unfold tailWord_3440369
  simp only [CollatzResearch.WordTrace]
  refine ⟨125480566073138156091612161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83653710715425437394408107 125480566073138156091612161)
  ·
    refine ⟨94110424554853617068709121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125480566073138156091612161 94110424554853617068709121)
    ·
      refine ⟨70582818416140212801531841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94110424554853617068709121 70582818416140212801531841)
      ·
        refine ⟨52937113812105159601148881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70582818416140212801531841 52937113812105159601148881)
        ·
          refine ⟨39702835359078869700861661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52937113812105159601148881 39702835359078869700861661)
          ·
            refine ⟨14888563259654576137823123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39702835359078869700861661 14888563259654576137823123)
            ·
              refine ⟨22332844889481864206734685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14888563259654576137823123 22332844889481864206734685)
              ·
                refine ⟨8374816833555699077525507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22332844889481864206734685 8374816833555699077525507)
                ·
                  refine ⟨12562225250333548616288261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8374816833555699077525507 12562225250333548616288261)
                  ·
                    refine ⟨2355417234437540365554049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12562225250333548616288261 2355417234437540365554049)
                    ·
                      refine ⟨1766562925828155274165537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2355417234437540365554049 1766562925828155274165537)
                      ·
                        rfl

theorem cell23_3440369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_3440369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440369 prefixEnd_3440369 := by exact prefixLift 3440369
  have htrace : WordTrace (prefixWord ++ tailWord_3440369) baseStart_3440369 baseEnd_3440369 := by
    simpa [prefixWord, tailWord_3440369, baseEnd_3440369] using wordTrace_append hprefix tailTrace_3440369
  have hstable : (prefixWord ++ tailWord_3440369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440369).length < 2 ^ (prefixWord ++ tailWord_3440369).sum := by decide
  have hdescent : baseEnd_3440369 < baseStart_3440369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440375 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 9]
def baseStart_3440375 : Nat := 118140960795 + 3440375 * 2 ^ 59
def prefixEnd_3440375 : Nat := 4983230072969 + 3 ^ 40 * 3440375 * 2
def baseEnd_3440375 : Nat := 196285111856898027854501

theorem tailTrace_3440375 : CollatzResearch.WordTrace tailWord_3440375 prefixEnd_3440375 196285111856898027854501 := by
  unfold tailWord_3440375
  simp only [CollatzResearch.WordTrace]
  refine ⟨125480784911116419116330579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83653856607410946077553719 125480784911116419116330579)
  ·
    refine ⟨188221177366674628674495869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125480784911116419116330579 188221177366674628674495869)
    ·
      refine ⟨70582941512502985752935951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188221177366674628674495869 70582941512502985752935951)
      ·
        refine ⟨105874412268754478629403927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70582941512502985752935951 105874412268754478629403927)
        ·
          refine ⟨158811618403131717944105891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105874412268754478629403927 158811618403131717944105891)
          ·
            refine ⟨238217427604697576916158837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158811618403131717944105891 238217427604697576916158837)
            ·
              refine ⟨22332883837940397835889891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 238217427604697576916158837 22332883837940397835889891)
              ·
                refine ⟨33499325756910596753834837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22332883837940397835889891 33499325756910596753834837)
                ·
                  refine ⟨196285111856898027854501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33499325756910596753834837 196285111856898027854501)
                  ·
                    rfl

theorem cell23_3440375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 9].length) (baseStart_3440375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440375 prefixEnd_3440375 := by exact prefixLift 3440375
  have htrace : WordTrace (prefixWord ++ tailWord_3440375) baseStart_3440375 baseEnd_3440375 := by
    simpa [prefixWord, tailWord_3440375, baseEnd_3440375] using wordTrace_append hprefix tailTrace_3440375
  have hstable : (prefixWord ++ tailWord_3440375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440375).length < 2 ^ (prefixWord ++ tailWord_3440375).sum := by decide
  have hdescent : baseEnd_3440375 < baseStart_3440375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440386 : List Nat := [3, 4, 1, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_3440386 : Nat := 118140960795 + 3440386 * 2 ^ 59
def prefixEnd_3440386 : Nat := 4983230072969 + 3 ^ 40 * 3440386 * 2
def baseEnd_3440386 : Nat := 1766571654999281707652959

theorem tailTrace_3440386 : CollatzResearch.WordTrace tailWord_3440386 prefixEnd_3440386 1766571654999281707652959 := by
  unfold tailWord_3440386
  simp only [CollatzResearch.WordTrace]
  refine ⟨31370296528519141998745253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83654124076051045329987341 31370296528519141998745253)
  ·
    refine ⟨5881930599097339124764735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31370296528519141998745253 5881930599097339124764735)
    ·
      refine ⟨8822895898646008687147103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5881930599097339124764735 8822895898646008687147103)
      ·
        refine ⟨13234343847969013030720655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8822895898646008687147103 13234343847969013030720655)
        ·
          refine ⟨19851515771953519546080983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13234343847969013030720655 19851515771953519546080983)
          ·
            refine ⟨29777273657930279319121475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19851515771953519546080983 29777273657930279319121475)
            ·
              refine ⟨44665910486895418978682213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29777273657930279319121475 44665910486895418978682213)
              ·
                refine ⟨8374858216292891058502915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44665910486895418978682213 8374858216292891058502915)
                ·
                  refine ⟨12562287324439336587754373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8374858216292891058502915 12562287324439336587754373)
                  ·
                    refine ⟨2355428873332375610203945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12562287324439336587754373 2355428873332375610203945)
                    ·
                      refine ⟨1766571654999281707652959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2355428873332375610203945 1766571654999281707652959)
                      ·
                        rfl

theorem cell23_3440386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_3440386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440386 prefixEnd_3440386 := by exact prefixLift 3440386
  have htrace : WordTrace (prefixWord ++ tailWord_3440386) baseStart_3440386 baseEnd_3440386 := by
    simpa [prefixWord, tailWord_3440386, baseEnd_3440386] using wordTrace_append hprefix tailTrace_3440386
  have hstable : (prefixWord ++ tailWord_3440386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440386).length < 2 ^ (prefixWord ++ tailWord_3440386).sum := by decide
  have hdescent : baseEnd_3440386 < baseStart_3440386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440397 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_3440397 : Nat := 118140960795 + 3440397 * 2 ^ 59
def prefixEnd_3440397 : Nat := 4983230072969 + 3 ^ 40 * 3440397 * 2
def baseEnd_3440397 : Nat := 1766577303286481164615409

theorem tailTrace_3440397 : CollatzResearch.WordTrace tailWord_3440397 prefixEnd_3440397 1766577303286481164615409 := by
  unfold tailWord_3440397
  simp only [CollatzResearch.WordTrace]
  refine ⟨125481587317036716873631445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83654391544691144582420963 125481587317036716873631445)
  ·
    refine ⟨2940974702743048051725737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 125481587317036716873631445 2940974702743048051725737)
    ·
      refine ⟨2205731027057286038794303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2940974702743048051725737 2205731027057286038794303)
      ·
        refine ⟨3308596540585929058191455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2205731027057286038794303 3308596540585929058191455)
        ·
          refine ⟨4962894810878893587287183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3308596540585929058191455 4962894810878893587287183)
          ·
            refine ⟨7444342216318340380930775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4962894810878893587287183 7444342216318340380930775)
            ·
              refine ⟨11166513324477510571396163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7444342216318340380930775 11166513324477510571396163)
              ·
                refine ⟨16749769986716265857094245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11166513324477510571396163 16749769986716265857094245)
                ·
                  refine ⟨3140581872509299848205171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16749769986716265857094245 3140581872509299848205171)
                  ·
                    refine ⟨4710872808763949772307757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3140581872509299848205171 4710872808763949772307757)
                    ·
                      refine ⟨1766577303286481164615409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4710872808763949772307757 1766577303286481164615409)
                      ·
                        rfl

theorem cell23_3440397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_3440397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440397 prefixEnd_3440397 := by exact prefixLift 3440397
  have htrace : WordTrace (prefixWord ++ tailWord_3440397) baseStart_3440397 baseEnd_3440397 := by
    simpa [prefixWord, tailWord_3440397, baseEnd_3440397] using wordTrace_append hprefix tailTrace_3440397
  have hstable : (prefixWord ++ tailWord_3440397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440397).length < 2 ^ (prefixWord ++ tailWord_3440397).sum := by decide
  have hdescent : baseEnd_3440397 < baseStart_3440397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440420 : List Nat := [2, 3, 1, 3, 2, 2, 3, 1, 2, 2, 2]
def baseStart_3440420 : Nat := 118140960795 + 3440420 * 2 ^ 59
def prefixEnd_3440420 : Nat := 4983230072969 + 3 ^ 40 * 3440420 * 2
def baseEnd_3440420 : Nat := 1766589113341534574627803

theorem tailTrace_3440420 : CollatzResearch.WordTrace tailWord_3440420 prefixEnd_3440420 1766589113341534574627803 := by
  unfold tailWord_3440420
  simp only [CollatzResearch.WordTrace]
  refine ⟨62741213097976695900859357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83654950797302261201145809 62741213097976695900859357)
  ·
    refine ⟨23527954911741260962822259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62741213097976695900859357 23527954911741260962822259)
    ·
      refine ⟨35291932367611891444233389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23527954911741260962822259 35291932367611891444233389)
      ·
        refine ⟨13234474637854459291587521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35291932367611891444233389 13234474637854459291587521)
        ·
          refine ⟨9925855978390844468690641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13234474637854459291587521 9925855978390844468690641)
          ·
            refine ⟨7444391983793133351517981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9925855978390844468690641 7444391983793133351517981)
            ·
              refine ⟨2791646993922425006819243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7444391983793133351517981 2791646993922425006819243)
              ·
                refine ⟨4187470490883637510228865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2791646993922425006819243 4187470490883637510228865)
                ·
                  refine ⟨3140602868162728132671649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4187470490883637510228865 3140602868162728132671649)
                  ·
                    refine ⟨2355452151122046099503737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3140602868162728132671649 2355452151122046099503737)
                    ·
                      refine ⟨1766589113341534574627803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2355452151122046099503737 1766589113341534574627803)
                      ·
                        rfl

theorem cell23_3440420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_3440420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440420 prefixEnd_3440420 := by exact prefixLift 3440420
  have htrace : WordTrace (prefixWord ++ tailWord_3440420) baseStart_3440420 baseEnd_3440420 := by
    simpa [prefixWord, tailWord_3440420, baseEnd_3440420] using wordTrace_append hprefix tailTrace_3440420
  have hstable : (prefixWord ++ tailWord_3440420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440420).length < 2 ^ (prefixWord ++ tailWord_3440420).sum := by decide
  have hdescent : baseEnd_3440420 < baseStart_3440420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440543 : List Nat := [1, 1, 2, 5, 3, 1, 1, 2, 3, 1, 3]
def baseStart_3440543 : Nat := 118140960795 + 3440543 * 2 ^ 59
def prefixEnd_3440543 : Nat := 4983230072969 + 3 ^ 40 * 3440543 * 2
def baseEnd_3440543 : Nat := 1766652271462037593389737

theorem tailTrace_3440543 : CollatzResearch.WordTrace tailWord_3440543 prefixEnd_3440543 1766652271462037593389737 := by
  unfold tailWord_3440543
  simp only [CollatzResearch.WordTrace]
  refine ⟨125486912374507783808446283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83657941583005189205630855 125486912374507783808446283)
  ·
    refine ⟨188230368561761675712669425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125486912374507783808446283 188230368561761675712669425)
    ·
      refine ⟨141172776421321256784502069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188230368561761675712669425 141172776421321256784502069)
      ·
        refine ⟨13234947789498867823547069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141172776421321256784502069 13234947789498867823547069)
        ·
          refine ⟨4963105421062075433830151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13234947789498867823547069 4963105421062075433830151)
          ·
            refine ⟨7444658131593113150745227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4963105421062075433830151 7444658131593113150745227)
            ·
              refine ⟨11166987197389669726117841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7444658131593113150745227 11166987197389669726117841)
              ·
                refine ⟨8375240398042252294588381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11166987197389669726117841 8375240398042252294588381)
                ·
                  refine ⟨3140715149265844610470643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8375240398042252294588381 3140715149265844610470643)
                  ·
                    refine ⟨4711072723898766915705965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3140715149265844610470643 4711072723898766915705965)
                    ·
                      refine ⟨1766652271462037593389737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4711072723898766915705965 1766652271462037593389737)
                      ·
                        rfl

theorem cell23_3440543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_3440543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440543 prefixEnd_3440543 := by exact prefixLift 3440543
  have htrace : WordTrace (prefixWord ++ tailWord_3440543) baseStart_3440543 baseEnd_3440543 := by
    simpa [prefixWord, tailWord_3440543, baseEnd_3440543] using wordTrace_append hprefix tailTrace_3440543
  have hstable : (prefixWord ++ tailWord_3440543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440543).length < 2 ^ (prefixWord ++ tailWord_3440543).sum := by decide
  have hdescent : baseEnd_3440543 < baseStart_3440543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440559 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 4, 4]
def baseStart_3440559 : Nat := 118140960795 + 3440559 * 2 ^ 59
def prefixEnd_3440559 : Nat := 4983230072969 + 3 ^ 40 * 3440559 * 2
def baseEnd_3440559 : Nat := 588886829050836510263221

theorem tailTrace_3440559 : CollatzResearch.WordTrace tailWord_3440559 prefixEnd_3440559 588886829050836510263221 := by
  unfold tailWord_3440559
  simp only [CollatzResearch.WordTrace]
  refine ⟨125487495942449818541028731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83658330628299879027352487 125487495942449818541028731)
  ·
    refine ⟨188231243913674727811543097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125487495942449818541028731 188231243913674727811543097)
    ·
      refine ⟨141173432935256045858657323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188231243913674727811543097 141173432935256045858657323)
      ·
        refine ⟨211760149402884068787985985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141173432935256045858657323 211760149402884068787985985)
        ·
          refine ⟨158820112052163051590989489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211760149402884068787985985 158820112052163051590989489)
          ·
            refine ⟨119115084039122288693242117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158820112052163051590989489 119115084039122288693242117)
            ·
              refine ⟨22334078257335429129982897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119115084039122288693242117 22334078257335429129982897)
              ·
                refine ⟨16750558693001571847487173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22334078257335429129982897 16750558693001571847487173)
                ·
                  refine ⟨3140729754937794721403845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16750558693001571847487173 3140729754937794721403845)
                  ·
                    refine ⟨588886829050836510263221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3140729754937794721403845 588886829050836510263221)
                    ·
                      rfl

theorem cell23_3440559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 4].length) (baseStart_3440559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440559 prefixEnd_3440559 := by exact prefixLift 3440559
  have htrace : WordTrace (prefixWord ++ tailWord_3440559) baseStart_3440559 baseEnd_3440559 := by
    simpa [prefixWord, tailWord_3440559, baseEnd_3440559] using wordTrace_append hprefix tailTrace_3440559
  have hstable : (prefixWord ++ tailWord_3440559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440559).length < 2 ^ (prefixWord ++ tailWord_3440559).sum := by decide
  have hdescent : baseEnd_3440559 < baseStart_3440559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440569 : List Nat := [1, 2, 1, 4, 2, 1, 2, 3, 1, 1, 5]
def baseStart_3440569 : Nat := 118140960795 + 3440569 * 2 ^ 59
def prefixEnd_3440569 : Nat := 4983230072969 + 3 ^ 40 * 3440569 * 2
def baseEnd_3440569 : Nat := 1766665621959054491664617

theorem tailTrace_3440569 : CollatzResearch.WordTrace tailWord_3440569 prefixEnd_3440569 1766665621959054491664617 := by
  unfold tailWord_3440569
  simp only [CollatzResearch.WordTrace]
  refine ⟨125487860672413590248892761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83658573781609060165928507 125487860672413590248892761)
  ·
    refine ⟨94115895504310192686669571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125487860672413590248892761 94115895504310192686669571)
    ·
      refine ⟨141173843256465289030004357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94115895504310192686669571 141173843256465289030004357)
      ·
        refine ⟨26470095610587241693125817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141173843256465289030004357 26470095610587241693125817)
        ·
          refine ⟨19852571707940431269844363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26470095610587241693125817 19852571707940431269844363)
          ·
            refine ⟨29778857561910646904766545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19852571707940431269844363 29778857561910646904766545)
            ·
              refine ⟨22334143171432985178574909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29778857561910646904766545 22334143171432985178574909)
              ·
                refine ⟨8375303689287369441965591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22334143171432985178574909 8375303689287369441965591)
                ·
                  refine ⟨12562955533931054162948387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8375303689287369441965591 12562955533931054162948387)
                  ·
                    refine ⟨18844433300896581244422581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12562955533931054162948387 18844433300896581244422581)
                    ·
                      refine ⟨1766665621959054491664617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18844433300896581244422581 1766665621959054491664617)
                      ·
                        rfl

theorem cell23_3440569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_3440569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440569 prefixEnd_3440569 := by exact prefixLift 3440569
  have htrace : WordTrace (prefixWord ++ tailWord_3440569) baseStart_3440569 baseEnd_3440569 := by
    simpa [prefixWord, tailWord_3440569, baseEnd_3440569] using wordTrace_append hprefix tailTrace_3440569
  have hstable : (prefixWord ++ tailWord_3440569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440569).length < 2 ^ (prefixWord ++ tailWord_3440569).sum := by decide
  have hdescent : baseEnd_3440569 < baseStart_3440569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440644 : List Nat := [2, 3, 2, 4, 2, 1, 2, 1, 2, 4]
def baseStart_3440644 : Nat := 118140960795 + 3440644 * 2 ^ 59
def prefixEnd_3440644 : Nat := 4983230072969 + 3 ^ 40 * 3440644 * 2
def baseEnd_3440644 : Nat := 588901377669380566075591

theorem tailTrace_3440644 : CollatzResearch.WordTrace tailWord_3440644 prefixEnd_3440644 588901377669380566075591 := by
  unfold tailWord_3440644
  simp only [CollatzResearch.WordTrace]
  refine ⟨62745298073570939028936493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83660397431427918705248657 62745298073570939028936493)
  ·
    refine ⟨23529486777589102135851185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62745298073570939028936493 23529486777589102135851185)
    ·
      refine ⟨17647115083191826601888389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23529486777589102135851185 17647115083191826601888389)
      ·
        refine ⟨3308834078098467487854073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17647115083191826601888389 3308834078098467487854073)
        ·
          refine ⟨2481625558573850615890555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3308834078098467487854073 2481625558573850615890555)
          ·
            refine ⟨3722438337860775923835833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2481625558573850615890555 3722438337860775923835833)
            ·
              refine ⟨2791828753395581942876875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3722438337860775923835833 2791828753395581942876875)
              ·
                refine ⟨4187743130093372914315313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2791828753395581942876875 4187743130093372914315313)
                ·
                  refine ⟨3140807347570029685736485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4187743130093372914315313 3140807347570029685736485)
                  ·
                    refine ⟨588901377669380566075591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3140807347570029685736485 588901377669380566075591)
                    ·
                      rfl

theorem cell23_3440644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_3440644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440644 prefixEnd_3440644 := by exact prefixLift 3440644
  have htrace : WordTrace (prefixWord ++ tailWord_3440644) baseStart_3440644 baseEnd_3440644 := by
    simpa [prefixWord, tailWord_3440644, baseEnd_3440644] using wordTrace_append hprefix tailTrace_3440644
  have hstable : (prefixWord ++ tailWord_3440644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440644).length < 2 ^ (prefixWord ++ tailWord_3440644).sum := by decide
  have hdescent : baseEnd_3440644 < baseStart_3440644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440650 : List Nat := [3, 1, 2, 2, 4, 1, 1, 3, 2, 1, 3]
def baseStart_3440650 : Nat := 118140960795 + 3440650 * 2 ^ 59
def prefixEnd_3440650 : Nat := 4983230072969 + 3 ^ 40 * 3440650 * 2
def baseEnd_3440650 : Nat := 1766707213892068674751745

theorem tailTrace_3440650 : CollatzResearch.WordTrace tailWord_3440650 prefixEnd_3440650 1766707213892068674751745 := by
  unfold tailWord_3440650
  simp only [CollatzResearch.WordTrace]
  refine ⟨31372703746280035270647851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83660543323413427388394269 31372703746280035270647851)
  ·
    refine ⟨47059055619420052905971777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31372703746280035270647851 47059055619420052905971777)
    ·
      refine ⟨35294291714565039679478833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47059055619420052905971777 35294291714565039679478833)
      ·
        refine ⟨26470718785923779759609125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35294291714565039679478833 26470718785923779759609125)
        ·
          refine ⟨4963259772360708704926711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26470718785923779759609125 4963259772360708704926711)
          ·
            refine ⟨7444889658541063057390067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4963259772360708704926711 7444889658541063057390067)
            ·
              refine ⟨11167334487811594586085101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7444889658541063057390067 11167334487811594586085101)
              ·
                refine ⟨4187750432929347969781913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11167334487811594586085101 4187750432929347969781913)
                ·
                  refine ⟨3140812824697010977336435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4187750432929347969781913 3140812824697010977336435)
                  ·
                    refine ⟨4711219237045516466004653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3140812824697010977336435 4711219237045516466004653)
                    ·
                      refine ⟨1766707213892068674751745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4711219237045516466004653 1766707213892068674751745)
                      ·
                        rfl

theorem cell23_3440650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_3440650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440650 prefixEnd_3440650 := by exact prefixLift 3440650
  have htrace : WordTrace (prefixWord ++ tailWord_3440650) baseStart_3440650 baseEnd_3440650 := by
    simpa [prefixWord, tailWord_3440650, baseEnd_3440650] using wordTrace_append hprefix tailTrace_3440650
  have hstable : (prefixWord ++ tailWord_3440650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440650).length < 2 ^ (prefixWord ++ tailWord_3440650).sum := by decide
  have hdescent : baseEnd_3440650 < baseStart_3440650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440659 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 5]
def baseStart_3440659 : Nat := 118140960795 + 3440659 * 2 ^ 59
def prefixEnd_3440659 : Nat := 4983230072969 + 3 ^ 40 * 3440659 * 2
def baseEnd_3440659 : Nat := 1766711835217959139539203

theorem tailTrace_3440659 : CollatzResearch.WordTrace tailWord_3440659 prefixEnd_3440659 1766711835217959139539203 := by
  unfold tailWord_3440659
  simp only [CollatzResearch.WordTrace]
  refine ⟨125491143242087535619669031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83660762161391690413112687 125491143242087535619669031)
  ·
    refine ⟨188236714863131303429503547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125491143242087535619669031 188236714863131303429503547)
    ·
      refine ⟨282355072294696955144255321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188236714863131303429503547 282355072294696955144255321)
      ·
        refine ⟨211766304221022716358191491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282355072294696955144255321 211766304221022716358191491)
        ·
          refine ⟨317649456331534074537287237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211766304221022716358191491 317649456331534074537287237)
          ·
            refine ⟨59559273062162638975741357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 317649456331534074537287237 59559273062162638975741357)
            ·
              refine ⟨22334727398310989615903009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59559273062162638975741357 22334727398310989615903009)
              ·
                refine ⟨16751045548733242211927257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22334727398310989615903009 16751045548733242211927257)
                ·
                  refine ⟨12563284161549931658945443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16751045548733242211927257 12563284161549931658945443)
                  ·
                    refine ⟨18844926242324897488418165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12563284161549931658945443 18844926242324897488418165)
                    ·
                      refine ⟨1766711835217959139539203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18844926242324897488418165 1766711835217959139539203)
                      ·
                        rfl

theorem cell23_3440659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_3440659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440659 prefixEnd_3440659 := by exact prefixLift 3440659
  have htrace : WordTrace (prefixWord ++ tailWord_3440659) baseStart_3440659 baseEnd_3440659 := by
    simpa [prefixWord, tailWord_3440659, baseEnd_3440659] using wordTrace_append hprefix tailTrace_3440659
  have hstable : (prefixWord ++ tailWord_3440659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440659).length < 2 ^ (prefixWord ++ tailWord_3440659).sum := by decide
  have hdescent : baseEnd_3440659 < baseStart_3440659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440690 : List Nat := [3, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2]
def baseStart_3440690 : Nat := 118140960795 + 3440690 * 2 ^ 59
def prefixEnd_3440690 : Nat := 4983230072969 + 3 ^ 40 * 3440690 * 2
def baseEnd_3440690 : Nat := 1766727753118248518251561

theorem tailTrace_3440690 : CollatzResearch.WordTrace tailWord_3440690 prefixEnd_3440690 1766727753118248518251561 := by
  unfold tailWord_3440690
  simp only [CollatzResearch.WordTrace]
  refine ⟨31373068476243806978511881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83661515936650151942698349 31373068476243806978511881)
  ·
    refine ⟨23529801357182855233883911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31373068476243806978511881 23529801357182855233883911)
    ·
      refine ⟨35294702035774282850825867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23529801357182855233883911 35294702035774282850825867)
      ·
        refine ⟨52942053053661424276238801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35294702035774282850825867 52942053053661424276238801)
        ·
          refine ⟨39706539790246068207179101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52942053053661424276238801 39706539790246068207179101)
          ·
            refine ⟨14889952421342275577692163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39706539790246068207179101 14889952421342275577692163)
            ·
              refine ⟨22334928632013413366538245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14889952421342275577692163 22334928632013413366538245)
              ·
                refine ⟨4187799118502515006225921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22334928632013413366538245 4187799118502515006225921)
                ·
                  refine ⟨3140849338876886254669441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4187799118502515006225921 3140849338876886254669441)
                  ·
                    refine ⟨2355637004157664691002081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3140849338876886254669441 2355637004157664691002081)
                    ·
                      refine ⟨1766727753118248518251561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2355637004157664691002081 1766727753118248518251561)
                      ·
                        rfl

theorem cell23_3440690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_3440690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440690 prefixEnd_3440690 := by exact prefixLift 3440690
  have htrace : WordTrace (prefixWord ++ tailWord_3440690) baseStart_3440690 baseEnd_3440690 := by
    simpa [prefixWord, tailWord_3440690, baseEnd_3440690] using wordTrace_append hprefix tailTrace_3440690
  have hstable : (prefixWord ++ tailWord_3440690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440690).length < 2 ^ (prefixWord ++ tailWord_3440690).sum := by decide
  have hdescent : baseEnd_3440690 < baseStart_3440690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440709 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 1, 7]
def baseStart_3440709 : Nat := 118140960795 + 3440709 * 2 ^ 59
def prefixEnd_3440709 : Nat := 4983230072969 + 3 ^ 40 * 3440709 * 2
def baseEnd_3440709 : Nat := 588912503083561314637991

theorem tailTrace_3440709 : CollatzResearch.WordTrace tailWord_3440709 prefixEnd_3440709 588912503083561314637991 := by
  unfold tailWord_3440709
  simp only [CollatzResearch.WordTrace]
  refine ⟨125492966891906394158989181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83661977927937596105992787 125492966891906394158989181)
  ·
    refine ⟨47059862584464897809620943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125492966891906394158989181 47059862584464897809620943)
    ·
      refine ⟨70589793876697346714431415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47059862584464897809620943 70589793876697346714431415)
      ·
        refine ⟨105884690815046020071647123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70589793876697346714431415 105884690815046020071647123)
        ·
          refine ⟨158827036222569030107470685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105884690815046020071647123 158827036222569030107470685)
          ·
            refine ⟨59560138583463386290301507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158827036222569030107470685 59560138583463386290301507)
            ·
              refine ⟨89340207875195079435452261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59560138583463386290301507 89340207875195079435452261)
              ·
                refine ⟨16751288976599077394147299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89340207875195079435452261 16751288976599077394147299)
                ·
                  refine ⟨25126933464898616091220949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16751288976599077394147299 25126933464898616091220949)
                  ·
                    refine ⟨588912503083561314637991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25126933464898616091220949 588912503083561314637991)
                    ·
                      rfl

theorem cell23_3440709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_3440709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440709 prefixEnd_3440709 := by exact prefixLift 3440709
  have htrace : WordTrace (prefixWord ++ tailWord_3440709) baseStart_3440709 baseEnd_3440709 := by
    simpa [prefixWord, tailWord_3440709, baseEnd_3440709] using wordTrace_append hprefix tailTrace_3440709
  have hstable : (prefixWord ++ tailWord_3440709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440709).length < 2 ^ (prefixWord ++ tailWord_3440709).sum := by decide
  have hdescent : baseEnd_3440709 < baseStart_3440709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440773 : List Nat := [1, 3, 1, 1, 5, 1, 2, 2, 3, 4]
def baseStart_3440773 : Nat := 118140960795 + 3440773 * 2 ^ 59
def prefixEnd_3440773 : Nat := 4983230072969 + 3 ^ 40 * 3440773 * 2
def baseEnd_3440773 : Nat := 588923457337523897837893

theorem tailTrace_3440773 : CollatzResearch.WordTrace tailWord_3440773 prefixEnd_3440773 588923457337523897837893 := by
  unfold tailWord_3440773
  simp only [CollatzResearch.WordTrace]
  refine ⟨125495301163674533089318973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83663534109116355392879315 125495301163674533089318973)
  ·
    refine ⟨47060737936377949908494615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125495301163674533089318973 47060737936377949908494615)
    ·
      refine ⟨70591106904566924862741923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47060737936377949908494615 70591106904566924862741923)
      ·
        refine ⟨105886660356850387294112885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70591106904566924862741923 105886660356850387294112885)
        ·
          refine ⟨9926874408454723808823083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105886660356850387294112885 9926874408454723808823083)
          ·
            refine ⟨14890311612682085713234625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9926874408454723808823083 14890311612682085713234625)
            ·
              refine ⟨11167733709511564284925969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14890311612682085713234625 11167733709511564284925969)
              ·
                refine ⟨8375800282133673213694477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11167733709511564284925969 8375800282133673213694477)
                ·
                  refine ⟨3140925105800127455135429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8375800282133673213694477 3140925105800127455135429)
                  ·
                    refine ⟨588923457337523897837893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3140925105800127455135429 588923457337523897837893)
                    ·
                      rfl

theorem cell23_3440773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_3440773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440773 prefixEnd_3440773 := by exact prefixLift 3440773
  have htrace : WordTrace (prefixWord ++ tailWord_3440773) baseStart_3440773 baseEnd_3440773 := by
    simpa [prefixWord, tailWord_3440773, baseEnd_3440773] using wordTrace_append hprefix tailTrace_3440773
  have hstable : (prefixWord ++ tailWord_3440773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440773).length < 2 ^ (prefixWord ++ tailWord_3440773).sum := by decide
  have hdescent : baseEnd_3440773 < baseStart_3440773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440779 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 9]
def baseStart_3440779 : Nat := 118140960795 + 3440779 * 2 ^ 59
def prefixEnd_3440779 : Nat := 4983230072969 + 3 ^ 40 * 3440779 * 2
def baseEnd_3440779 : Nat := 1766773452896498670038651

theorem tailTrace_3440779 : CollatzResearch.WordTrace tailWord_3440779 prefixEnd_3440779 1766773452896498670038651 := by
  unfold tailWord_3440779
  simp only [CollatzResearch.WordTrace]
  refine ⟨125495520001652796114037391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83663680001101864076024927 125495520001652796114037391)
  ·
    refine ⟨188243280002479194171056087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125495520001652796114037391 188243280002479194171056087)
    ·
      refine ⟨282364920003718791256584131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188243280002479194171056087 282364920003718791256584131)
      ·
        refine ⟨423547380005578186884876197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282364920003718791256584131 423547380005578186884876197)
        ·
          refine ⟨79415133751045910040914287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 423547380005578186884876197 79415133751045910040914287)
          ·
            refine ⟨119122700626568865061371431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79415133751045910040914287 119122700626568865061371431)
            ·
              refine ⟨178684050939853297592057147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119122700626568865061371431 178684050939853297592057147)
              ·
                refine ⟨268026076409779946388085721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178684050939853297592057147 268026076409779946388085721)
                ·
                  refine ⟨201019557307334959791064291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268026076409779946388085721 201019557307334959791064291)
                  ·
                    refine ⟨301529335961002439686596437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 201019557307334959791064291 301529335961002439686596437)
                    ·
                      refine ⟨1766773452896498670038651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 301529335961002439686596437 1766773452896498670038651)
                      ·
                        rfl

theorem cell23_3440779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 9].length) (baseStart_3440779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440779 prefixEnd_3440779 := by exact prefixLift 3440779
  have htrace : WordTrace (prefixWord ++ tailWord_3440779) baseStart_3440779 baseEnd_3440779 := by
    simpa [prefixWord, tailWord_3440779, baseEnd_3440779] using wordTrace_append hprefix tailTrace_3440779
  have hstable : (prefixWord ++ tailWord_3440779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440779).length < 2 ^ (prefixWord ++ tailWord_3440779).sum := by decide
  have hdescent : baseEnd_3440779 < baseStart_3440779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440786 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 10]
def baseStart_3440786 : Nat := 118140960795 + 3440786 * 2 ^ 59
def prefixEnd_3440786 : Nat := 4983230072969 + 3 ^ 40 * 3440786 * 2
def baseEnd_3440786 : Nat := 196308560806786682516791

theorem tailTrace_3440786 : CollatzResearch.WordTrace tailWord_3440786 prefixEnd_3440786 196308560806786682516791 := by
  unfold tailWord_3440786
  simp only [CollatzResearch.WordTrace]
  refine ⟨31373943828156859077385553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83663850208418290873028141 31373943828156859077385553)
  ·
    refine ⟨23530457871117644308039165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31373943828156859077385553 23530457871117644308039165)
    ·
      refine ⟨8823921701669116615514687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23530457871117644308039165 8823921701669116615514687)
      ·
        refine ⟨13235882552503674923272031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8823921701669116615514687 13235882552503674923272031)
        ·
          refine ⟨19853823828755512384908047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13235882552503674923272031 19853823828755512384908047)
          ·
            refine ⟨29780735743133268577362071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19853823828755512384908047 29780735743133268577362071)
            ·
              refine ⟨44671103614699902866043107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29780735743133268577362071 44671103614699902866043107)
              ·
                refine ⟨67006655422049854299064661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44671103614699902866043107 67006655422049854299064661)
                ·
                  refine ⟨196308560806786682516791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 67006655422049854299064661 196308560806786682516791)
                  ·
                    rfl

theorem cell23_3440786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_3440786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440786 prefixEnd_3440786 := by exact prefixLift 3440786
  have htrace : WordTrace (prefixWord ++ tailWord_3440786) baseStart_3440786 baseEnd_3440786 := by
    simpa [prefixWord, tailWord_3440786, baseEnd_3440786] using wordTrace_append hprefix tailTrace_3440786
  have hstable : (prefixWord ++ tailWord_3440786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440786).length < 2 ^ (prefixWord ++ tailWord_3440786).sum := by decide
  have hdescent : baseEnd_3440786 < baseStart_3440786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440807 : List Nat := [1, 1, 6, 2, 2, 2, 1, 1, 3, 4]
def baseStart_3440807 : Nat := 118140960795 + 3440807 * 2 ^ 59
def prefixEnd_3440807 : Nat := 4983230072969 + 3 ^ 40 * 3440807 * 2
def baseEnd_3440807 : Nat := 588929276784941520162841

theorem tailTrace_3440807 : CollatzResearch.WordTrace tailWord_3440807 prefixEnd_3440807 588929276784941520162841 := by
  unfold tailWord_3440807
  simp only [CollatzResearch.WordTrace]
  refine ⟨125496541245551356896056675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83664360830367571264037783 125496541245551356896056675)
  ·
    refine ⟨188244811868327035344085013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125496541245551356896056675 188244811868327035344085013)
    ·
      refine ⟨8823975556327829781753985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 188244811868327035344085013 8823975556327829781753985)
      ·
        refine ⟨6617981667245872336315489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8823975556327829781753985 6617981667245872336315489)
        ·
          refine ⟨4963486250434404252236617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6617981667245872336315489 4963486250434404252236617)
          ·
            refine ⟨3722614687825803189177463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4963486250434404252236617 3722614687825803189177463)
            ·
              refine ⟨5583922031738704783766195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3722614687825803189177463 5583922031738704783766195)
              ·
                refine ⟨8375883047608057175649293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5583922031738704783766195 8375883047608057175649293)
                ·
                  refine ⟨3140956142853021440868485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8375883047608057175649293 3140956142853021440868485)
                  ·
                    refine ⟨588929276784941520162841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3140956142853021440868485 588929276784941520162841)
                    ·
                      rfl

theorem cell23_3440807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_3440807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440807 prefixEnd_3440807 := by exact prefixLift 3440807
  have htrace : WordTrace (prefixWord ++ tailWord_3440807) baseStart_3440807 baseEnd_3440807 := by
    simpa [prefixWord, tailWord_3440807, baseEnd_3440807] using wordTrace_append hprefix tailTrace_3440807
  have hstable : (prefixWord ++ tailWord_3440807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440807).length < 2 ^ (prefixWord ++ tailWord_3440807).sum := by decide
  have hdescent : baseEnd_3440807 < baseStart_3440807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440834 : List Nat := [3, 5, 1, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_3440834 : Nat := 118140960795 + 3440834 * 2 ^ 59
def prefixEnd_3440834 : Nat := 4983230072969 + 3 ^ 40 * 3440834 * 2
def baseEnd_3440834 : Nat := 1766801694332495954850899

theorem tailTrace_3440834 : CollatzResearch.WordTrace tailWord_3440834 prefixEnd_3440834 1766801694332495954850899 := by
  unfold tailWord_3440834
  simp only [CollatzResearch.WordTrace]
  refine ⟨31374381504113385126822389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83665017344302360338193037 31374381504113385126822389)
  ·
    refine ⟨2941348266010629855639599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31374381504113385126822389 2941348266010629855639599)
    ·
      refine ⟨4412022399015944783459399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2941348266010629855639599 4412022399015944783459399)
      ·
        refine ⟨6618033598523917175189099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4412022399015944783459399 6618033598523917175189099)
        ·
          refine ⟨9927050397785875762783649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6618033598523917175189099 9927050397785875762783649)
          ·
            refine ⟨7445287798339406822087737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9927050397785875762783649 7445287798339406822087737)
            ·
              refine ⟨5583965848754555116565803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7445287798339406822087737 5583965848754555116565803)
              ·
                refine ⟨8375948773131832674848705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5583965848754555116565803 8375948773131832674848705)
                ·
                  refine ⟨6281961579848874506136529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8375948773131832674848705 6281961579848874506136529)
                  ·
                    refine ⟨4711471184886655879602397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6281961579848874506136529 4711471184886655879602397)
                    ·
                      refine ⟨1766801694332495954850899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4711471184886655879602397 1766801694332495954850899)
                      ·
                        rfl

theorem cell23_3440834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_3440834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440834 prefixEnd_3440834 := by exact prefixLift 3440834
  have htrace : WordTrace (prefixWord ++ tailWord_3440834) baseStart_3440834 baseEnd_3440834 := by
    simpa [prefixWord, tailWord_3440834, baseEnd_3440834] using wordTrace_append hprefix tailTrace_3440834
  have hstable : (prefixWord ++ tailWord_3440834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440834).length < 2 ^ (prefixWord ++ tailWord_3440834).sum := by decide
  have hdescent : baseEnd_3440834 < baseStart_3440834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440883 : List Nat := [1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 4]
def baseStart_3440883 : Nat := 118140960795 + 3440883 * 2 ^ 59
def prefixEnd_3440883 : Nat := 4983230072969 + 3 ^ 40 * 3440883 * 2
def baseEnd_3440883 : Nat := 1766826854884566263138173

theorem tailTrace_3440883 : CollatzResearch.WordTrace tailWord_3440883 prefixEnd_3440883 1766826854884566263138173 := by
  unfold tailWord_3440883
  simp only [CollatzResearch.WordTrace]
  refine ⟨125499313193276021875823303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83666208795517347917215535 125499313193276021875823303)
  ·
    refine ⟨188248969789914032813734955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125499313193276021875823303 188248969789914032813734955)
    ·
      refine ⟨282373454684871049220602433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188248969789914032813734955 282373454684871049220602433)
      ·
        refine ⟨211780091013653286915451825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282373454684871049220602433 211780091013653286915451825)
        ·
          refine ⟨158835068260239965186588869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211780091013653286915451825 158835068260239965186588869)
          ·
            refine ⟨29781575298794993472485413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158835068260239965186588869 29781575298794993472485413)
            ·
              refine ⟨5584045368524061276091015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29781575298794993472485413 5584045368524061276091015)
              ·
                refine ⟨8376068052786091914136523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5584045368524061276091015 8376068052786091914136523)
                ·
                  refine ⟨12564102079179137871204785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8376068052786091914136523 12564102079179137871204785)
                  ·
                    refine ⟨9423076559384353403403589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12564102079179137871204785 9423076559384353403403589)
                    ·
                      refine ⟨1766826854884566263138173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9423076559384353403403589 1766826854884566263138173)
                      ·
                        rfl

theorem cell23_3440883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 4].length) (baseStart_3440883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440883 prefixEnd_3440883 := by exact prefixLift 3440883
  have htrace : WordTrace (prefixWord ++ tailWord_3440883) baseStart_3440883 baseEnd_3440883 := by
    simpa [prefixWord, tailWord_3440883, baseEnd_3440883] using wordTrace_append hprefix tailTrace_3440883
  have hstable : (prefixWord ++ tailWord_3440883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440883).length < 2 ^ (prefixWord ++ tailWord_3440883).sum := by decide
  have hdescent : baseEnd_3440883 < baseStart_3440883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440904 : List Nat := [2, 1, 3, 2, 3, 1, 1, 5, 1, 2, 2]
def baseStart_3440904 : Nat := 118140960795 + 3440904 * 2 ^ 59
def prefixEnd_3440904 : Nat := 4983230072969 + 3 ^ 40 * 3440904 * 2
def baseEnd_3440904 : Nat := 1766837637978310680975577

theorem tailTrace_3440904 : CollatzResearch.WordTrace tailWord_3440904 prefixEnd_3440904 1766837637978310680975577 := by
  unfold tailWord_3440904
  simp only [CollatzResearch.WordTrace]
  refine ⟨62750039563099971231168883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83666719417466628308225177 62750039563099971231168883)
  ·
    refine ⟨94125059344649956846753325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62750039563099971231168883 94125059344649956846753325)
    ·
      refine ⟨35296897254243733817532497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94125059344649956846753325 35296897254243733817532497)
      ·
        refine ⟨26472672940682800363149373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35296897254243733817532497 26472672940682800363149373)
        ·
          refine ⟨9927252352756050136181015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26472672940682800363149373 9927252352756050136181015)
          ·
            refine ⟨14890878529134075204271523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9927252352756050136181015 14890878529134075204271523)
            ·
              refine ⟨22336317793701112806407285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14890878529134075204271523 22336317793701112806407285)
              ·
                refine ⟨2094029793159479325600683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22336317793701112806407285 2094029793159479325600683)
                ·
                  refine ⟨3141044689739218988401025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2094029793159479325600683 3141044689739218988401025)
                  ·
                    refine ⟨2355783517304414241300769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3141044689739218988401025 2355783517304414241300769)
                    ·
                      refine ⟨1766837637978310680975577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2355783517304414241300769 1766837637978310680975577)
                      ·
                        rfl

theorem cell23_3440904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_3440904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440904 prefixEnd_3440904 := by exact prefixLift 3440904
  have htrace : WordTrace (prefixWord ++ tailWord_3440904) baseStart_3440904 baseEnd_3440904 := by
    simpa [prefixWord, tailWord_3440904, baseEnd_3440904] using wordTrace_append hprefix tailTrace_3440904
  have hstable : (prefixWord ++ tailWord_3440904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440904).length < 2 ^ (prefixWord ++ tailWord_3440904).sum := by decide
  have hdescent : baseEnd_3440904 < baseStart_3440904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440920 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 4, 1, 3]
def baseStart_3440920 : Nat := 118140960795 + 3440920 * 2 ^ 59
def prefixEnd_3440920 : Nat := 4983230072969 + 3 ^ 40 * 3440920 * 2
def baseEnd_3440920 : Nat := 1766845853668782618375503

theorem tailTrace_3440920 : CollatzResearch.WordTrace tailWord_3440920 prefixEnd_3440920 1766845853668782618375503 := by
  unfold tailWord_3440920
  simp only [CollatzResearch.WordTrace]
  refine ⟨62750331347070988597460107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83667108462761318129946809 62750331347070988597460107)
  ·
    refine ⟨94125497020606482896190161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62750331347070988597460107 94125497020606482896190161)
    ·
      refine ⟨70594122765454862172142621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94125497020606482896190161 70594122765454862172142621)
      ·
        refine ⟨26472796037045573314553483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70594122765454862172142621 26472796037045573314553483)
        ·
          refine ⟨39709194055568359971830225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26472796037045573314553483 39709194055568359971830225)
          ·
            refine ⟨29781895541676269978872669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39709194055568359971830225 29781895541676269978872669)
            ·
              refine ⟨11168210828128601242077251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29781895541676269978872669 11168210828128601242077251)
              ·
                refine ⟨16752316242192901863115877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11168210828128601242077251 16752316242192901863115877)
                ·
                  refine ⟨3141059295411169099334227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16752316242192901863115877 3141059295411169099334227)
                  ·
                    refine ⟨4711588943116753649001341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3141059295411169099334227 4711588943116753649001341)
                    ·
                      refine ⟨1766845853668782618375503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4711588943116753649001341 1766845853668782618375503)
                      ·
                        rfl

theorem cell23_3440920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_3440920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440920 prefixEnd_3440920 := by exact prefixLift 3440920
  have htrace : WordTrace (prefixWord ++ tailWord_3440920) baseStart_3440920 baseEnd_3440920 := by
    simpa [prefixWord, tailWord_3440920, baseEnd_3440920] using wordTrace_append hprefix tailTrace_3440920
  have hstable : (prefixWord ++ tailWord_3440920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440920).length < 2 ^ (prefixWord ++ tailWord_3440920).sum := by decide
  have hdescent : baseEnd_3440920 < baseStart_3440920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440947 : List Nat := [1, 1, 1, 2, 5, 1, 4, 2, 1, 3, 2]
def baseStart_3440947 : Nat := 118140960795 + 3440947 * 2 ^ 59
def prefixEnd_3440947 : Nat := 4983230072969 + 3 ^ 40 * 3440947 * 2
def baseEnd_3440947 : Nat := 1766859717646454012737879

theorem tailTrace_3440947 : CollatzResearch.WordTrace tailWord_3440947 prefixEnd_3440947 1766859717646454012737879 := by
  unfold tailWord_3440947
  simp only [CollatzResearch.WordTrace]
  refine ⟨125501647465044160806153095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83667764976696107204102063 125501647465044160806153095)
  ·
    refine ⟨188252471197566241209229643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125501647465044160806153095 188252471197566241209229643)
    ·
      refine ⟨282378706796349361813844465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188252471197566241209229643 282378706796349361813844465)
      ·
        refine ⟨211784030097262021360383349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282378706796349361813844465 211784030097262021360383349)
        ·
          refine ⟨19854752821618314502535939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 211784030097262021360383349 19854752821618314502535939)
          ·
            refine ⟨29782129232427471753803909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19854752821618314502535939 29782129232427471753803909)
            ·
              refine ⟨5584149231080150953838233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29782129232427471753803909 5584149231080150953838233)
              ·
                refine ⟨4188111923310113215378675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5584149231080150953838233 4188111923310113215378675)
                ·
                  refine ⟨6282167884965169823068013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4188111923310113215378675 6282167884965169823068013)
                  ·
                    refine ⟨2355812956861938683650505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6282167884965169823068013 2355812956861938683650505)
                    ·
                      refine ⟨1766859717646454012737879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2355812956861938683650505 1766859717646454012737879)
                      ·
                        rfl

theorem cell23_3440947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 3, 2].length) (baseStart_3440947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440947 prefixEnd_3440947 := by exact prefixLift 3440947
  have htrace : WordTrace (prefixWord ++ tailWord_3440947) baseStart_3440947 baseEnd_3440947 := by
    simpa [prefixWord, tailWord_3440947, baseEnd_3440947] using wordTrace_append hprefix tailTrace_3440947
  have hstable : (prefixWord ++ tailWord_3440947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440947).length < 2 ^ (prefixWord ++ tailWord_3440947).sum := by decide
  have hdescent : baseEnd_3440947 < baseStart_3440947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440977 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 4, 2, 2]
def baseStart_3440977 : Nat := 118140960795 + 3440977 * 2 ^ 59
def prefixEnd_3440977 : Nat := 4983230072969 + 3 ^ 40 * 3440977 * 2
def baseEnd_3440977 : Nat := 1766875122066088895362741

theorem tailTrace_3440977 : CollatzResearch.WordTrace tailWord_3440977 prefixEnd_3440977 1766875122066088895362741 := by
  unfold tailWord_3440977
  simp only [CollatzResearch.WordTrace]
  refine ⟨125502741654935475929745185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83668494436623650619830123 125502741654935475929745185)
  ·
    refine ⟨94127056241201606947308889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125502741654935475929745185 94127056241201606947308889)
    ·
      refine ⟨70595292180901205210481667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94127056241201606947308889 70595292180901205210481667)
      ·
        refine ⟨105892938271351807815722501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70595292180901205210481667 105892938271351807815722501)
        ·
          refine ⟨19854925925878463965447969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105892938271351807815722501 19854925925878463965447969)
          ·
            refine ⟨14891194444408847974085977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19854925925878463965447969 14891194444408847974085977)
            ·
              refine ⟨11168395833306635980564483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14891194444408847974085977 11168395833306635980564483)
              ·
                refine ⟨16752593749959953970846725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11168395833306635980564483 16752593749959953970846725)
                ·
                  refine ⟨3141111328117491369533761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16752593749959953970846725 3141111328117491369533761)
                  ·
                    refine ⟨2355833496088118527150321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3141111328117491369533761 2355833496088118527150321)
                    ·
                      refine ⟨1766875122066088895362741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2355833496088118527150321 1766875122066088895362741)
                      ·
                        rfl

theorem cell23_3440977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 2, 2].length) (baseStart_3440977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440977 prefixEnd_3440977 := by exact prefixLift 3440977
  have htrace : WordTrace (prefixWord ++ tailWord_3440977) baseStart_3440977 baseEnd_3440977 := by
    simpa [prefixWord, tailWord_3440977, baseEnd_3440977] using wordTrace_append hprefix tailTrace_3440977
  have hstable : (prefixWord ++ tailWord_3440977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440977).length < 2 ^ (prefixWord ++ tailWord_3440977).sum := by decide
  have hdescent : baseEnd_3440977 < baseStart_3440977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440988 : List Nat := [2, 2, 4, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_3440988 : Nat := 118140960795 + 3440988 * 2 ^ 59
def prefixEnd_3440988 : Nat := 4983230072969 + 3 ^ 40 * 3440988 * 2
def baseEnd_3440988 : Nat := 1766880770353288352325191

theorem tailTrace_3440988 : CollatzResearch.WordTrace tailWord_3440988 prefixEnd_3440988 1766880770353288352325191 := by
  unfold tailWord_3440988
  simp only [CollatzResearch.WordTrace]
  refine ⟨62751571428947812404197809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83668761905263749872263745 62751571428947812404197809)
  ·
    refine ⟨47063678571710859303148357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62751571428947812404197809 47063678571710859303148357)
    ·
      refine ⟨8824439732195786119340317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47063678571710859303148357 8824439732195786119340317)
      ·
        refine ⟨3309164899573419794752619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8824439732195786119340317 3309164899573419794752619)
        ·
          refine ⟨4963747349360129692128929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3309164899573419794752619 4963747349360129692128929)
          ·
            refine ⟨3722810512020097269096697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4963747349360129692128929 3722810512020097269096697)
            ·
              refine ⟨2792107884015072951822523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3722810512020097269096697 2792107884015072951822523)
              ·
                refine ⟨4188161826022609427733785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2792107884015072951822523 4188161826022609427733785)
                ·
                  refine ⟨3141121369516957070800339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4188161826022609427733785 3141121369516957070800339)
                  ·
                    refine ⟨4711682054275435606200509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3141121369516957070800339 4711682054275435606200509)
                    ·
                      refine ⟨1766880770353288352325191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4711682054275435606200509 1766880770353288352325191)
                      ·
                        rfl

theorem cell23_3440988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_3440988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3440988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3440988 prefixEnd_3440988 := by exact prefixLift 3440988
  have htrace : WordTrace (prefixWord ++ tailWord_3440988) baseStart_3440988 baseEnd_3440988 := by
    simpa [prefixWord, tailWord_3440988, baseEnd_3440988] using wordTrace_append hprefix tailTrace_3440988
  have hstable : (prefixWord ++ tailWord_3440988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440988).length < 2 ^ (prefixWord ++ tailWord_3440988).sum := by decide
  have hdescent : baseEnd_3440988 < baseStart_3440988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441034 : List Nat := [3, 1, 2, 5, 1, 1, 1, 4, 5]
def baseStart_3441034 : Nat := 118140960795 + 3441034 * 2 ^ 59
def prefixEnd_3441034 : Nat := 4983230072969 + 3 ^ 40 * 3441034 * 2
def baseEnd_3441034 : Nat := 196322710051488352483331

theorem tailTrace_3441034 : CollatzResearch.WordTrace tailWord_3441034 prefixEnd_3441034 196322710051488352483331 := by
  unfold tailWord_3441034
  simp only [CollatzResearch.WordTrace]
  refine ⟨31376205153932243666142539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83669880410485983109713437 31376205153932243666142539)
  ·
    refine ⟨47064307730898365499213809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31376205153932243666142539 47064307730898365499213809)
    ·
      refine ⟨35298230798173774124410357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47064307730898365499213809 35298230798173774124410357)
      ·
        refine ⟨3309209137328791324163471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35298230798173774124410357 3309209137328791324163471)
        ·
          refine ⟨4963813705993186986245207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3309209137328791324163471 4963813705993186986245207)
          ·
            refine ⟨7445720558989780479367811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4963813705993186986245207 7445720558989780479367811)
            ·
              refine ⟨11168580838484670719051717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7445720558989780479367811 11168580838484670719051717)
              ·
                refine ⟨2094108907215875759822197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11168580838484670719051717 2094108907215875759822197)
                ·
                  refine ⟨196322710051488352483331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2094108907215875759822197 196322710051488352483331)
                  ·
                    rfl

theorem cell23_3441034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 5].length) (baseStart_3441034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441034 prefixEnd_3441034 := by exact prefixLift 3441034
  have htrace : WordTrace (prefixWord ++ tailWord_3441034) baseStart_3441034 baseEnd_3441034 := by
    simpa [prefixWord, tailWord_3441034, baseEnd_3441034] using wordTrace_append hprefix tailTrace_3441034
  have hstable : (prefixWord ++ tailWord_3441034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441034).length < 2 ^ (prefixWord ++ tailWord_3441034).sum := by decide
  have hdescent : baseEnd_3441034 < baseStart_3441034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441060 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 5, 4]
def baseStart_3441060 : Nat := 118140960795 + 3441060 * 2 ^ 59
def prefixEnd_3441060 : Nat := 4983230072969 + 3 ^ 40 * 3441060 * 2
def baseEnd_3441060 : Nat := 588972580320137356874953

theorem tailTrace_3441060 : CollatzResearch.WordTrace tailWord_3441060 prefixEnd_3441060 588972580320137356874953 := by
  unfold tailWord_3441060
  simp only [CollatzResearch.WordTrace]
  refine ⟨62752884456817390552508317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83670512609089854070011089 62752884456817390552508317)
  ·
    refine ⟨23532331671306521457190619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62752884456817390552508317 23532331671306521457190619)
    ·
      refine ⟨35298497506959782185785929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23532331671306521457190619 35298497506959782185785929)
      ·
        refine ⟨26473873130219836639339447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35298497506959782185785929 26473873130219836639339447)
        ·
          refine ⟨39710809695329754959009171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26473873130219836639339447 39710809695329754959009171)
          ·
            refine ⟨59566214542994632438513757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39710809695329754959009171 59566214542994632438513757)
            ·
              refine ⟨22337330453622987164442659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59566214542994632438513757 22337330453622987164442659)
              ·
                refine ⟨33505995680434480746663989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22337330453622987164442659 33505995680434480746663989)
                ·
                  refine ⟨3141187095040732569999749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33505995680434480746663989 3141187095040732569999749)
                  ·
                    refine ⟨588972580320137356874953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3141187095040732569999749 588972580320137356874953)
                    ·
                      rfl

theorem cell23_3441060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_3441060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441060 prefixEnd_3441060 := by exact prefixLift 3441060
  have htrace : WordTrace (prefixWord ++ tailWord_3441060) baseStart_3441060 baseEnd_3441060 := by
    simpa [prefixWord, tailWord_3441060, baseEnd_3441060] using wordTrace_append hprefix tailTrace_3441060
  have hstable : (prefixWord ++ tailWord_3441060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441060).length < 2 ^ (prefixWord ++ tailWord_3441060).sum := by decide
  have hdescent : baseEnd_3441060 < baseStart_3441060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441064 : List Nat := [2, 1, 6, 1, 1, 3, 1, 1, 2, 5]
def baseStart_3441064 : Nat := 118140960795 + 3441064 * 2 ^ 59
def prefixEnd_3441064 : Nat := 4983230072969 + 3 ^ 40 * 3441064 * 2
def baseEnd_3441064 : Nat := 588973264961010018324947

theorem tailTrace_3441064 : CollatzResearch.WordTrace tailWord_3441064 prefixEnd_3441064 588973264961010018324947 := by
  unfold tailWord_3441064
  simp only [CollatzResearch.WordTrace]
  refine ⟨62752957402810144894081123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83670609870413526525441497 62752957402810144894081123)
  ·
    refine ⟨94129436104215217341121685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62752957402810144894081123 94129436104215217341121685)
    ·
      refine ⟨4412317317385088312865079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 94129436104215217341121685 4412317317385088312865079)
      ·
        refine ⟨6618475976077632469297619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4412317317385088312865079 6618475976077632469297619)
        ·
          refine ⟨9927713964116448703946429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6618475976077632469297619 9927713964116448703946429)
          ·
            refine ⟨3722892736543668263979911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9927713964116448703946429 3722892736543668263979911)
            ·
              refine ⟨5584339104815502395969867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3722892736543668263979911 5584339104815502395969867)
              ·
                refine ⟨8376508657223253593954801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5584339104815502395969867 8376508657223253593954801)
                ·
                  refine ⟨6282381492917440195466101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8376508657223253593954801 6282381492917440195466101)
                  ·
                    refine ⟨588973264961010018324947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6282381492917440195466101 588973264961010018324947)
                    ·
                      rfl

theorem cell23_3441064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_3441064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441064 prefixEnd_3441064 := by exact prefixLift 3441064
  have htrace : WordTrace (prefixWord ++ tailWord_3441064) baseStart_3441064 baseEnd_3441064 := by
    simpa [prefixWord, tailWord_3441064, baseEnd_3441064] using wordTrace_append hprefix tailTrace_3441064
  have hstable : (prefixWord ++ tailWord_3441064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441064).length < 2 ^ (prefixWord ++ tailWord_3441064).sum := by decide
  have hdescent : baseEnd_3441064 < baseStart_3441064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441127 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 1, 5, 2]
def baseStart_3441127 : Nat := 118140960795 + 3441127 * 2 ^ 59
def prefixEnd_3441127 : Nat := 4983230072969 + 3 ^ 40 * 3441127 * 2
def baseEnd_3441127 : Nat := 1766952144164263308487051

theorem tailTrace_3441127 : CollatzResearch.WordTrace tailWord_3441127 prefixEnd_3441127 1766952144164263308487051 := by
  unfold tailWord_3441127
  simp only [CollatzResearch.WordTrace]
  refine ⟨125508212604392051547705635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83672141736261367698470423 125508212604392051547705635)
  ·
    refine ⟨188262318906588077321558453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125508212604392051547705635 188262318906588077321558453)
    ·
      refine ⟨17649592397492632248896105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188262318906588077321558453 17649592397492632248896105)
      ·
        refine ⟨13237194298119474186672079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17649592397492632248896105 13237194298119474186672079)
        ·
          refine ⟨19855791447179211280008119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13237194298119474186672079 19855791447179211280008119)
          ·
            refine ⟨29783687170768816920012179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19855791447179211280008119 29783687170768816920012179)
            ·
              refine ⟨44675530756153225380018269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29783687170768816920012179 44675530756153225380018269)
              ·
                refine ⟨16753324033557459517506851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44675530756153225380018269 16753324033557459517506851)
                ·
                  refine ⟨25129986050336189276260277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16753324033557459517506851 25129986050336189276260277)
                  ·
                    refine ⟨2355936192219017744649401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25129986050336189276260277 2355936192219017744649401)
                    ·
                      refine ⟨1766952144164263308487051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2355936192219017744649401 1766952144164263308487051)
                      ·
                        rfl

theorem cell23_3441127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_3441127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441127 prefixEnd_3441127 := by exact prefixLift 3441127
  have htrace : WordTrace (prefixWord ++ tailWord_3441127) baseStart_3441127 baseEnd_3441127 := by
    simpa [prefixWord, tailWord_3441127, baseEnd_3441127] using wordTrace_append hprefix tailTrace_3441127
  have hstable : (prefixWord ++ tailWord_3441127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441127).length < 2 ^ (prefixWord ++ tailWord_3441127).sum := by decide
  have hdescent : baseEnd_3441127 < baseStart_3441127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441151 : List Nat := [1, 1, 2, 2, 1, 2, 7, 2, 1, 1, 3]
def baseStart_3441151 : Nat := 118140960795 + 3441151 * 2 ^ 59
def prefixEnd_3441151 : Nat := 4983230072969 + 3 ^ 40 * 3441151 * 2
def baseEnd_3441151 : Nat := 1766964467699971214586941

theorem tailTrace_3441151 : CollatzResearch.WordTrace tailWord_3441151 prefixEnd_3441151 1766964467699971214586941 := by
  unfold tailWord_3441151
  simp only [CollatzResearch.WordTrace]
  refine ⟨125509087956305103646579307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83672725304203402431052871 125509087956305103646579307)
  ·
    refine ⟨188263631934457655469868961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125509087956305103646579307 188263631934457655469868961)
    ·
      refine ⟨141197723950843241602401721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188263631934457655469868961 141197723950843241602401721)
      ·
        refine ⟨105898292963132431201801291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141197723950843241602401721 105898292963132431201801291)
        ·
          refine ⟨158847439444698646802701937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105898292963132431201801291 158847439444698646802701937)
          ·
            refine ⟨119135579583523985102026453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158847439444698646802701937 119135579583523985102026453)
            ·
              refine ⟨2792240146488843400828745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 119135579583523985102026453 2792240146488843400828745)
              ·
                refine ⟨2094180109866632550621559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2792240146488843400828745 2094180109866632550621559)
                ·
                  refine ⟨3141270164799948825932339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2094180109866632550621559 3141270164799948825932339)
                  ·
                    refine ⟨4711905247199923238898509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3141270164799948825932339 4711905247199923238898509)
                    ·
                      refine ⟨1766964467699971214586941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4711905247199923238898509 1766964467699971214586941)
                      ·
                        rfl

theorem cell23_3441151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 1, 1, 3].length) (baseStart_3441151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441151 prefixEnd_3441151 := by exact prefixLift 3441151
  have htrace : WordTrace (prefixWord ++ tailWord_3441151) baseStart_3441151 baseEnd_3441151 := by
    simpa [prefixWord, tailWord_3441151, baseEnd_3441151] using wordTrace_append hprefix tailTrace_3441151
  have hstable : (prefixWord ++ tailWord_3441151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441151).length < 2 ^ (prefixWord ++ tailWord_3441151).sum := by decide
  have hdescent : baseEnd_3441151 < baseStart_3441151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441158 : List Nat := [6, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_3441158 : Nat := 118140960795 + 3441158 * 2 ^ 59
def prefixEnd_3441158 : Nat := 4983230072969 + 3 ^ 40 * 3441158 * 2
def baseEnd_3441158 : Nat := 196329784673839187466601

theorem tailTrace_3441158 : CollatzResearch.WordTrace tailWord_3441158 prefixEnd_3441158 196329784673839187466601 := by
  unfold tailWord_3441158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3922166977102491995065129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83672895511519829228056085 3922166977102491995065129)
  ·
    refine ⟨2941625232826868996298847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3922166977102491995065129 2941625232826868996298847)
    ·
      refine ⟨4412437849240303494448271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2941625232826868996298847 4412437849240303494448271)
      ·
        refine ⟨6618656773860455241672407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4412437849240303494448271 6618656773860455241672407)
        ·
          refine ⟨9927985160790682862508611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6618656773860455241672407 9927985160790682862508611)
          ·
            refine ⟨14891977741186024293762917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9927985160790682862508611 14891977741186024293762917)
            ·
              refine ⟨2792245826472379555080547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14891977741186024293762917 2792245826472379555080547)
              ·
                refine ⟨4188368739708569332620821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2792245826472379555080547 4188368739708569332620821)
                ·
                  refine ⟨196329784673839187466601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4188368739708569332620821 196329784673839187466601)
                  ·
                    rfl

theorem cell23_3441158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_3441158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441158 prefixEnd_3441158 := by exact prefixLift 3441158
  have htrace : WordTrace (prefixWord ++ tailWord_3441158) baseStart_3441158 baseEnd_3441158 := by
    simpa [prefixWord, tailWord_3441158, baseEnd_3441158] using wordTrace_append hprefix tailTrace_3441158
  have hstable : (prefixWord ++ tailWord_3441158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441158).length < 2 ^ (prefixWord ++ tailWord_3441158).sum := by decide
  have hdescent : baseEnd_3441158 < baseStart_3441158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441160 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 2, 6, 3]
def baseStart_3441160 : Nat := 118140960795 + 3441160 * 2 ^ 59
def prefixEnd_3441160 : Nat := 4983230072969 + 3 ^ 40 * 3441160 * 2
def baseEnd_3441160 : Nat := 1766969089025861679374399

theorem tailTrace_3441160 : CollatzResearch.WordTrace tailWord_3441160 prefixEnd_3441160 1766969089025861679374399 := by
  unfold tailWord_3441160
  simp only [CollatzResearch.WordTrace]
  refine ⟨62754708106636249091828467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83672944142181665455771289 62754708106636249091828467)
  ·
    refine ⟨94132062159954373637742701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62754708106636249091828467 94132062159954373637742701)
    ·
      refine ⟨35299523309982890114153513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94132062159954373637742701 35299523309982890114153513)
      ·
        refine ⟨26474642482487167585615135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35299523309982890114153513 26474642482487167585615135)
        ·
          refine ⟨39711963723730751378422703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26474642482487167585615135 39711963723730751378422703)
          ·
            refine ⟨59567945585596127067634055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39711963723730751378422703 59567945585596127067634055)
            ·
              refine ⟨89351918378394190601451083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59567945585596127067634055 89351918378394190601451083)
              ·
                refine ⟨134027877567591285902176625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89351918378394190601451083 134027877567591285902176625)
                ·
                  refine ⟨100520908175693464426632469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134027877567591285902176625 100520908175693464426632469)
                  ·
                    refine ⟨4711917570735631144998397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100520908175693464426632469 4711917570735631144998397)
                    ·
                      refine ⟨1766969089025861679374399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4711917570735631144998397 1766969089025861679374399)
                      ·
                        rfl

theorem cell23_3441160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_3441160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441160 prefixEnd_3441160 := by exact prefixLift 3441160
  have htrace : WordTrace (prefixWord ++ tailWord_3441160) baseStart_3441160 baseEnd_3441160 := by
    simpa [prefixWord, tailWord_3441160, baseEnd_3441160] using wordTrace_append hprefix tailTrace_3441160
  have hstable : (prefixWord ++ tailWord_3441160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441160).length < 2 ^ (prefixWord ++ tailWord_3441160).sum := by decide
  have hdescent : baseEnd_3441160 < baseStart_3441160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441180 : List Nat := [2, 2, 3, 1, 2, 2, 2, 9]
def baseStart_3441180 : Nat := 118140960795 + 3441180 * 2 ^ 59
def prefixEnd_3441180 : Nat := 4983230072969 + 3 ^ 40 * 3441180 * 2
def baseEnd_3441180 : Nat := 65443679949590800041641

theorem tailTrace_3441180 : CollatzResearch.WordTrace tailWord_3441180 prefixEnd_3441180 65443679949590800041641 := by
  unfold tailWord_3441180
  simp only [CollatzResearch.WordTrace]
  refine ⟨62755072836600020799692497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83673430448800027732923329 62755072836600020799692497)
  ·
    refine ⟨47066304627450015599769373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62755072836600020799692497 47066304627450015599769373)
    ·
      refine ⟨17649864235293755849913515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47066304627450015599769373 17649864235293755849913515)
      ·
        refine ⟨26474796352940633774870273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17649864235293755849913515 26474796352940633774870273)
        ·
          refine ⟨19856097264705475331152705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26474796352940633774870273 19856097264705475331152705)
          ·
            refine ⟨14892072948529106498364529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19856097264705475331152705 14892072948529106498364529)
            ·
              refine ⟨11169054711396829873773397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14892072948529106498364529 11169054711396829873773397)
              ·
                refine ⟨65443679949590800041641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11169054711396829873773397 65443679949590800041641)
                ·
                  rfl

theorem cell23_3441180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 9].length) (baseStart_3441180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441180 prefixEnd_3441180 := by exact prefixLift 3441180
  have htrace : WordTrace (prefixWord ++ tailWord_3441180) baseStart_3441180 baseEnd_3441180 := by
    simpa [prefixWord, tailWord_3441180, baseEnd_3441180] using wordTrace_append hprefix tailTrace_3441180
  have hstable : (prefixWord ++ tailWord_3441180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441180).length < 2 ^ (prefixWord ++ tailWord_3441180).sum := by decide
  have hdescent : baseEnd_3441180 < baseStart_3441180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441187 : List Nat := [1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 4]
def baseStart_3441187 : Nat := 118140960795 + 3441187 * 2 ^ 59
def prefixEnd_3441187 : Nat := 4983230072969 + 3 ^ 40 * 3441187 * 2
def baseEnd_3441187 : Nat := 1766982953003533073736775

theorem tailTrace_3441187 : CollatzResearch.WordTrace tailWord_3441187 prefixEnd_3441187 1766982953003533073736775 := by
  unfold tailWord_3441187
  simp only [CollatzResearch.WordTrace]
  refine ⟨125510400984174681794889815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83673600656116454529926543 125510400984174681794889815)
  ·
    refine ⟨188265601476262022692334723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125510400984174681794889815 188265601476262022692334723)
    ·
      refine ⟨282398402214393034038502085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188265601476262022692334723 282398402214393034038502085)
      ·
        refine ⟨52949700415198693882219141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282398402214393034038502085 52949700415198693882219141)
        ·
          refine ⟨9928068827849755102916089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52949700415198693882219141 9928068827849755102916089)
          ·
            refine ⟨7446051620887316327187067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9928068827849755102916089 7446051620887316327187067)
            ·
              refine ⟨11169077431330974490780601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7446051620887316327187067 11169077431330974490780601)
              ·
                refine ⟨8376808073498230868085451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11169077431330974490780601 8376808073498230868085451)
                ·
                  refine ⟨12565212110247346302128177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8376808073498230868085451 12565212110247346302128177)
                  ·
                    refine ⟨9423909082685509726596133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12565212110247346302128177 9423909082685509726596133)
                    ·
                      refine ⟨1766982953003533073736775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9423909082685509726596133 1766982953003533073736775)
                      ·
                        rfl

theorem cell23_3441187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_3441187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441187 prefixEnd_3441187 := by exact prefixLift 3441187
  have htrace : WordTrace (prefixWord ++ tailWord_3441187) baseStart_3441187 baseEnd_3441187 := by
    simpa [prefixWord, tailWord_3441187, baseEnd_3441187] using wordTrace_append hprefix tailTrace_3441187
  have hstable : (prefixWord ++ tailWord_3441187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441187).length < 2 ^ (prefixWord ++ tailWord_3441187).sum := by decide
  have hdescent : baseEnd_3441187 < baseStart_3441187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441194 : List Nat := [3, 1, 4, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_3441194 : Nat := 118140960795 + 3441194 * 2 ^ 59
def prefixEnd_3441194 : Nat := 4983230072969 + 3 ^ 40 * 3441194 * 2
def baseEnd_3441194 : Nat := 1766986547368114546349243

theorem tailTrace_3441194 : CollatzResearch.WordTrace tailWord_3441194 prefixEnd_3441194 1766986547368114546349243 := by
  unfold tailWord_3441194
  simp only [CollatzResearch.WordTrace]
  refine ⟨31377664073787330497598659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83673770863432881326929757 31377664073787330497598659)
  ·
    refine ⟨47066496110680995746397989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31377664073787330497598659 47066496110680995746397989)
    ·
      refine ⟨8824968020752686702449623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47066496110680995746397989 8824968020752686702449623)
      ·
        refine ⟨13237452031129030053674435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8824968020752686702449623 13237452031129030053674435)
        ·
          refine ⟨19856178046693545080511653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13237452031129030053674435 19856178046693545080511653)
          ·
            refine ⟨3723033383755039702595935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19856178046693545080511653 3723033383755039702595935)
            ·
              refine ⟨5584550075632559553893903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3723033383755039702595935 5584550075632559553893903)
              ·
                refine ⟨8376825113448839330840855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5584550075632559553893903 8376825113448839330840855)
                ·
                  refine ⟨12565237670173258996261283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8376825113448839330840855 12565237670173258996261283)
                  ·
                    refine ⟨18847856505259888494391925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12565237670173258996261283 18847856505259888494391925)
                    ·
                      refine ⟨1766986547368114546349243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18847856505259888494391925 1766986547368114546349243)
                      ·
                        rfl

theorem cell23_3441194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_3441194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441194 prefixEnd_3441194 := by exact prefixLift 3441194
  have htrace : WordTrace (prefixWord ++ tailWord_3441194) baseStart_3441194 baseEnd_3441194 := by
    simpa [prefixWord, tailWord_3441194, baseEnd_3441194] using wordTrace_append hprefix tailTrace_3441194
  have hstable : (prefixWord ++ tailWord_3441194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441194).length < 2 ^ (prefixWord ++ tailWord_3441194).sum := by decide
  have hdescent : baseEnd_3441194 < baseStart_3441194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441210 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 2, 7]
def baseStart_3441210 : Nat := 118140960795 + 3441210 * 2 ^ 59
def prefixEnd_3441210 : Nat := 4983230072969 + 3 ^ 40 * 3441210 * 2
def baseEnd_3441210 : Nat := 588998254352862161249723

theorem tailTrace_3441210 : CollatzResearch.WordTrace tailWord_3441210 prefixEnd_3441210 588998254352862161249723 := by
  unfold tailWord_3441210
  simp only [CollatzResearch.WordTrace]
  refine ⟨31377809965772839180744271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83674159908727571148651389 31377809965772839180744271)
  ·
    refine ⟨47066714948659258771116407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31377809965772839180744271 47066714948659258771116407)
    ·
      refine ⟨70600072422988888156674611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47066714948659258771116407 70600072422988888156674611)
      ·
        refine ⟨105900108634483332235011917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70600072422988888156674611 105900108634483332235011917)
        ·
          refine ⟨39712540737931249588129469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105900108634483332235011917 39712540737931249588129469)
          ·
            refine ⟨14892202776724218595548551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39712540737931249588129469 14892202776724218595548551)
            ·
              refine ⟨22338304165086327893322827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14892202776724218595548551 22338304165086327893322827)
              ·
                refine ⟨33507456247629491839984241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22338304165086327893322827 33507456247629491839984241)
                ·
                  refine ⟨25130592185722118879988181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33507456247629491839984241 25130592185722118879988181)
                  ·
                    refine ⟨588998254352862161249723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25130592185722118879988181 588998254352862161249723)
                    ·
                      rfl

theorem cell23_3441210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_3441210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441210 prefixEnd_3441210 := by exact prefixLift 3441210
  have htrace : WordTrace (prefixWord ++ tailWord_3441210) baseStart_3441210 baseEnd_3441210 := by
    simpa [prefixWord, tailWord_3441210, baseEnd_3441210] using wordTrace_append hprefix tailTrace_3441210
  have hstable : (prefixWord ++ tailWord_3441210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441210).length < 2 ^ (prefixWord ++ tailWord_3441210).sum := by decide
  have hdescent : baseEnd_3441210 < baseStart_3441210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441234 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 3, 3, 2]
def baseStart_3441234 : Nat := 118140960795 + 3441234 * 2 ^ 59
def prefixEnd_3441234 : Nat := 4983230072969 + 3 ^ 40 * 3441234 * 2
def baseEnd_3441234 : Nat := 1767007086594294389849059

theorem tailTrace_3441234 : CollatzResearch.WordTrace tailWord_3441234 prefixEnd_3441234 1767007086594294389849059 := by
  unfold tailWord_3441234
  simp only [CollatzResearch.WordTrace]
  refine ⟨31378028803751102205462689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83674743476669605881233837 31378028803751102205462689)
  ·
    refine ⟨23533521602813326654097017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31378028803751102205462689 23533521602813326654097017)
    ·
      refine ⟨17650141202109994990572763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23533521602813326654097017 17650141202109994990572763)
      ·
        refine ⟨26475211803164992485859145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17650141202109994990572763 26475211803164992485859145)
        ·
          refine ⟨19856408852373744364394359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26475211803164992485859145 19856408852373744364394359)
          ·
            refine ⟨29784613278560616546591539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19856408852373744364394359 29784613278560616546591539)
            ·
              refine ⟨44676919917840924819887309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29784613278560616546591539 44676919917840924819887309)
              ·
                refine ⟨16753844969190346807457741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44676919917840924819887309 16753844969190346807457741)
                ·
                  refine ⟨6282691863446380052796653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16753844969190346807457741 6282691863446380052796653)
                  ·
                    refine ⟨2356009448792392519798745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6282691863446380052796653 2356009448792392519798745)
                    ·
                      refine ⟨1767007086594294389849059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2356009448792392519798745 1767007086594294389849059)
                      ·
                        rfl

theorem cell23_3441234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_3441234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441234 prefixEnd_3441234 := by exact prefixLift 3441234
  have htrace : WordTrace (prefixWord ++ tailWord_3441234) baseStart_3441234 baseEnd_3441234 := by
    simpa [prefixWord, tailWord_3441234, baseEnd_3441234] using wordTrace_append hprefix tailTrace_3441234
  have hstable : (prefixWord ++ tailWord_3441234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441234).length < 2 ^ (prefixWord ++ tailWord_3441234).sum := by decide
  have hdescent : baseEnd_3441234 < baseStart_3441234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441327 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 5]
def baseStart_3441327 : Nat := 118140960795 + 3441327 * 2 ^ 59
def prefixEnd_3441327 : Nat := 4983230072969 + 3 ^ 40 * 3441327 * 2
def baseEnd_3441327 : Nat := 1767054840295162525986131

theorem tailTrace_3441327 : CollatzResearch.WordTrace tailWord_3441327 prefixEnd_3441327 1767054840295162525986131 := by
  unfold tailWord_3441327
  simp only [CollatzResearch.WordTrace]
  refine ⟨125515507203667485704986235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83677004802444990469990823 125515507203667485704986235)
  ·
    refine ⟨188273260805501228557479353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125515507203667485704986235 188273260805501228557479353)
    ·
      refine ⟨141204945604125921418109515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188273260805501228557479353 141204945604125921418109515)
      ·
        refine ⟨211807418406188882127164273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141204945604125921418109515 211807418406188882127164273)
        ·
          refine ⟨158855563804641661595373205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211807418406188882127164273 158855563804641661595373205)
          ·
            refine ⟨7446354553342577887283119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 158855563804641661595373205 7446354553342577887283119)
            ·
              refine ⟨11169531830013866830924679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7446354553342577887283119 11169531830013866830924679)
              ·
                refine ⟨16754297745020800246387019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11169531830013866830924679 16754297745020800246387019)
                ·
                  refine ⟨25131446617531200369580529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16754297745020800246387019 25131446617531200369580529)
                  ·
                    refine ⟨18848584963148400277185397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25131446617531200369580529 18848584963148400277185397)
                    ·
                      refine ⟨1767054840295162525986131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18848584963148400277185397 1767054840295162525986131)
                      ·
                        rfl

theorem cell23_3441327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 5].length) (baseStart_3441327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441327 prefixEnd_3441327 := by exact prefixLift 3441327
  have htrace : WordTrace (prefixWord ++ tailWord_3441327) baseStart_3441327 baseEnd_3441327 := by
    simpa [prefixWord, tailWord_3441327, baseEnd_3441327] using wordTrace_append hprefix tailTrace_3441327
  have hstable : (prefixWord ++ tailWord_3441327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441327).length < 2 ^ (prefixWord ++ tailWord_3441327).sum := by decide
  have hdescent : baseEnd_3441327 < baseStart_3441327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441337 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 6, 1, 4]
def baseStart_3441337 : Nat := 118140960795 + 3441337 * 2 ^ 59
def prefixEnd_3441337 : Nat := 4983230072969 + 3 ^ 40 * 3441337 * 2
def baseEnd_3441337 : Nat := 1767059975101707486861085

theorem tailTrace_3441337 : CollatzResearch.WordTrace tailWord_3441337 prefixEnd_3441337 1767059975101707486861085 := by
  unfold tailWord_3441337
  simp only [CollatzResearch.WordTrace]
  refine ⟨125515871933631257412850265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83677247955754171608566843 125515871933631257412850265)
  ·
    refine ⟨94136903950223443059637699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125515871933631257412850265 94136903950223443059637699)
    ·
      refine ⟨141205355925335164589456549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94136903950223443059637699 141205355925335164589456549)
      ·
        refine ⟨26476004236000343360523103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141205355925335164589456549 26476004236000343360523103)
        ·
          refine ⟨39714006354000515040784655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26476004236000343360523103 39714006354000515040784655)
          ·
            refine ⟨59571009531000772561176983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39714006354000515040784655 59571009531000772561176983)
            ·
              refine ⟨89356514296501158841765475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59571009531000772561176983 89356514296501158841765475)
              ·
                refine ⟨134034771444751738262648213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89356514296501158841765475 134034771444751738262648213)
                ·
                  refine ⟨6282879911472737731061635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134034771444751738262648213 6282879911472737731061635)
                  ·
                    refine ⟨9424319867209106596592453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6282879911472737731061635 9424319867209106596592453)
                    ·
                      refine ⟨1767059975101707486861085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9424319867209106596592453 1767059975101707486861085)
                      ·
                        rfl

theorem cell23_3441337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_3441337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441337 prefixEnd_3441337 := by exact prefixLift 3441337
  have htrace : WordTrace (prefixWord ++ tailWord_3441337) baseStart_3441337 baseEnd_3441337 := by
    simpa [prefixWord, tailWord_3441337, baseEnd_3441337] using wordTrace_append hprefix tailTrace_3441337
  have hstable : (prefixWord ++ tailWord_3441337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441337).length < 2 ^ (prefixWord ++ tailWord_3441337).sum := by decide
  have hdescent : baseEnd_3441337 < baseStart_3441337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441354 : List Nat := [3, 1, 2, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_3441354 : Nat := 118140960795 + 3441354 * 2 ^ 59
def prefixEnd_3441354 : Nat := 4983230072969 + 3 ^ 40 * 3441354 * 2
def baseEnd_3441354 : Nat := 1767068704272833920348507

theorem tailTrace_3441354 : CollatzResearch.WordTrace tailWord_3441354 prefixEnd_3441354 1767068704272833920348507 := by
  unfold tailWord_3441354
  simp only [CollatzResearch.WordTrace]
  refine ⟨31379122993642417329054779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83677661316379779544146077 31379122993642417329054779)
  ·
    refine ⟨47068684490463625993582169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31379122993642417329054779 47068684490463625993582169)
    ·
      refine ⟨35301513367847719495186627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47068684490463625993582169 35301513367847719495186627)
      ·
        refine ⟨52952270051771579242779941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35301513367847719495186627 52952270051771579242779941)
        ·
          refine ⟨9928550634707171108021239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52952270051771579242779941 9928550634707171108021239)
          ·
            refine ⟨14892825952060756662031859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9928550634707171108021239 14892825952060756662031859)
            ·
              refine ⟨22339238928091134993047789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14892825952060756662031859 22339238928091134993047789)
              ·
                refine ⟨8377214598034175622392921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22339238928091134993047789 8377214598034175622392921)
                ·
                  refine ⟨6282910948525631716794691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8377214598034175622392921 6282910948525631716794691)
                  ·
                    refine ⟨9424366422788447575192037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6282910948525631716794691 9424366422788447575192037)
                    ·
                      refine ⟨1767068704272833920348507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9424366422788447575192037 1767068704272833920348507)
                      ·
                        rfl

theorem cell23_3441354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_3441354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441354 prefixEnd_3441354 := by exact prefixLift 3441354
  have htrace : WordTrace (prefixWord ++ tailWord_3441354) baseStart_3441354 baseEnd_3441354 := by
    simpa [prefixWord, tailWord_3441354, baseEnd_3441354] using wordTrace_append hprefix tailTrace_3441354
  have hstable : (prefixWord ++ tailWord_3441354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441354).length < 2 ^ (prefixWord ++ tailWord_3441354).sum := by decide
  have hdescent : baseEnd_3441354 < baseStart_3441354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441387 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 3]
def baseStart_3441387 : Nat := 118140960795 + 3441387 * 2 ^ 59
def prefixEnd_3441387 : Nat := 4983230072969 + 3 ^ 40 * 3441387 * 2
def baseEnd_3441387 : Nat := 1767085649134432291235855

theorem tailTrace_3441387 : CollatzResearch.WordTrace tailWord_3441387 prefixEnd_3441387 1767085649134432291235855 := by
  unfold tailWord_3441387
  simp only [CollatzResearch.WordTrace]
  refine ⟨125517695583450115952170415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83678463722300077301446943 125517695583450115952170415)
  ·
    refine ⟨188276543375175173928255623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125517695583450115952170415 188276543375175173928255623)
    ·
      refine ⟨282414815062762760892383435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188276543375175173928255623 282414815062762760892383435)
      ·
        refine ⟨423622222594144141338575153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282414815062762760892383435 423622222594144141338575153)
        ·
          refine ⟨317716666945608106003931365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423622222594144141338575153 317716666945608106003931365)
          ·
            refine ⟨59571875052301519875737131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 317716666945608106003931365 59571875052301519875737131)
            ·
              refine ⟨89357812578452279813605697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59571875052301519875737131 89357812578452279813605697)
              ·
                refine ⟨67018359433839209860204273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89357812578452279813605697 67018359433839209860204273)
                ·
                  refine ⟨50263769575379407395153205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67018359433839209860204273 50263769575379407395153205)
                  ·
                    refine ⟨4712228397691819443295613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50263769575379407395153205 4712228397691819443295613)
                    ·
                      refine ⟨1767085649134432291235855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4712228397691819443295613 1767085649134432291235855)
                      ·
                        rfl

theorem cell23_3441387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 3].length) (baseStart_3441387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441387 prefixEnd_3441387 := by exact prefixLift 3441387
  have htrace : WordTrace (prefixWord ++ tailWord_3441387) baseStart_3441387 baseEnd_3441387 := by
    simpa [prefixWord, tailWord_3441387, baseEnd_3441387] using wordTrace_append hprefix tailTrace_3441387
  have hstable : (prefixWord ++ tailWord_3441387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441387).length < 2 ^ (prefixWord ++ tailWord_3441387).sum := by decide
  have hdescent : baseEnd_3441387 < baseStart_3441387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441394 : List Nat := [3, 2, 1, 3, 1, 2, 2, 3, 6]
def baseStart_3441394 : Nat := 118140960795 + 3441394 * 2 ^ 59
def prefixEnd_3441394 : Nat := 4983230072969 + 3 ^ 40 * 3441394 * 2
def baseEnd_3441394 : Nat := 196343249277668195983147

theorem tailTrace_3441394 : CollatzResearch.WordTrace tailWord_3441394 prefixEnd_3441394 196343249277668195983147 := by
  unfold tailWord_3441394
  simp only [CollatzResearch.WordTrace]
  refine ⟨31379487723606189036918809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83678633929616504098450157 31379487723606189036918809)
  ·
    refine ⟨23534615792704641777689107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31379487723606189036918809 23534615792704641777689107)
    ·
      refine ⟨35301923689056962666533661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23534615792704641777689107 35301923689056962666533661)
      ·
        refine ⟨13238221383396360999950123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35301923689056962666533661 13238221383396360999950123)
        ·
          refine ⟨19857332075094541499925185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13238221383396360999950123 19857332075094541499925185)
          ·
            refine ⟨14892999056320906124943889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19857332075094541499925185 14892999056320906124943889)
            ·
              refine ⟨11169749292240679593707917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14892999056320906124943889 11169749292240679593707917)
              ·
                refine ⟨4188655984590254847640469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11169749292240679593707917 4188655984590254847640469)
                ·
                  refine ⟨196343249277668195983147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4188655984590254847640469 196343249277668195983147)
                  ·
                    rfl

theorem cell23_3441394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_3441394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441394 prefixEnd_3441394 := by exact prefixLift 3441394
  have htrace : WordTrace (prefixWord ++ tailWord_3441394) baseStart_3441394 baseEnd_3441394 := by
    simpa [prefixWord, tailWord_3441394, baseEnd_3441394] using wordTrace_append hprefix tailTrace_3441394
  have hstable : (prefixWord ++ tailWord_3441394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441394).length < 2 ^ (prefixWord ++ tailWord_3441394).sum := by decide
  have hdescent : baseEnd_3441394 < baseStart_3441394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441461 : List Nat := [1, 3, 3, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_3441461 : Nat := 118140960795 + 3441461 * 2 ^ 59
def prefixEnd_3441461 : Nat := 4983230072969 + 3 ^ 40 * 3441461 * 2
def baseEnd_3441461 : Nat := 1767123646702865001710515

theorem tailTrace_3441461 : CollatzResearch.WordTrace tailWord_3441461 prefixEnd_3441461 1767123646702865001710515 := by
  unfold tailWord_3441461
  simp only [CollatzResearch.WordTrace]
  refine ⟨125520394585182026590364237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83680263056788017726909491 125520394585182026590364237)
  ·
    refine ⟨47070147969443259971386589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125520394585182026590364237 47070147969443259971386589)
    ·
      refine ⟨17651305488541222489269971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47070147969443259971386589 17651305488541222489269971)
      ·
        refine ⟨26476958232811833733904957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17651305488541222489269971 26476958232811833733904957)
        ·
          refine ⟨9928859337304437650214359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26476958232811833733904957 9928859337304437650214359)
          ·
            refine ⟨14893289005956656475321539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9928859337304437650214359 14893289005956656475321539)
            ·
              refine ⟨22339933508934984712982309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14893289005956656475321539 22339933508934984712982309)
              ·
                refine ⟨4188737532925309633684183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22339933508934984712982309 4188737532925309633684183)
                ·
                  refine ⟨6283106299387964450526275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4188737532925309633684183 6283106299387964450526275)
                  ·
                    refine ⟨9424659449081946675789413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6283106299387964450526275 9424659449081946675789413)
                    ·
                      refine ⟨1767123646702865001710515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9424659449081946675789413 1767123646702865001710515)
                      ·
                        rfl

theorem cell23_3441461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_3441461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441461 prefixEnd_3441461 := by exact prefixLift 3441461
  have htrace : WordTrace (prefixWord ++ tailWord_3441461) baseStart_3441461 baseEnd_3441461 := by
    simpa [prefixWord, tailWord_3441461, baseEnd_3441461] using wordTrace_append hprefix tailTrace_3441461
  have hstable : (prefixWord ++ tailWord_3441461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441461).length < 2 ^ (prefixWord ++ tailWord_3441461).sum := by decide
  have hdescent : baseEnd_3441461 < baseStart_3441461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441481 : List Nat := [1, 2, 1, 1, 2, 5, 2, 3, 1, 2, 3]
def baseStart_3441481 : Nat := 118140960795 + 3441481 * 2 ^ 59
def prefixEnd_3441481 : Nat := 4983230072969 + 3 ^ 40 * 3441481 * 2
def baseEnd_3441481 : Nat := 1767133916315954923460423

theorem tailTrace_3441481 : CollatzResearch.WordTrace tailWord_3441481 prefixEnd_3441481 1767133916315954923460423 := by
  unfold tailWord_3441481
  simp only [CollatzResearch.WordTrace]
  refine ⟨125521124045109570006092297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83680749363406380004061531 125521124045109570006092297)
  ·
    refine ⟨94140843033832177504569223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125521124045109570006092297 94140843033832177504569223)
    ·
      refine ⟨141211264550748266256853835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94140843033832177504569223 141211264550748266256853835)
      ·
        refine ⟨211816896826122399385280753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141211264550748266256853835 211816896826122399385280753)
        ·
          refine ⟨158862672619591799538960565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211816896826122399385280753 158862672619591799538960565)
          ·
            refine ⟨14893375558086731206777553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158862672619591799538960565 14893375558086731206777553)
            ·
              refine ⟨11170031668565048405083165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14893375558086731206777553 11170031668565048405083165)
              ·
                refine ⟨4188761875711893151906187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11170031668565048405083165 4188761875711893151906187)
                ·
                  refine ⟨6283142813567839727859281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4188761875711893151906187 6283142813567839727859281)
                  ·
                    refine ⟨4712357110175879795894461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6283142813567839727859281 4712357110175879795894461)
                    ·
                      refine ⟨1767133916315954923460423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4712357110175879795894461 1767133916315954923460423)
                      ·
                        rfl

theorem cell23_3441481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 2, 3].length) (baseStart_3441481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441481 prefixEnd_3441481 := by exact prefixLift 3441481
  have htrace : WordTrace (prefixWord ++ tailWord_3441481) baseStart_3441481 baseEnd_3441481 := by
    simpa [prefixWord, tailWord_3441481, baseEnd_3441481] using wordTrace_append hprefix tailTrace_3441481
  have hstable : (prefixWord ++ tailWord_3441481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441481).length < 2 ^ (prefixWord ++ tailWord_3441481).sum := by decide
  have hdescent : baseEnd_3441481 < baseStart_3441481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441484 : List Nat := [2, 2, 1, 3, 3, 3, 9]
def baseStart_3441484 : Nat := 118140960795 + 3441484 * 2 ^ 59
def prefixEnd_3441484 : Nat := 4983230072969 + 3 ^ 40 * 3441484 * 2
def baseEnd_3441484 : Nat := 21816487120468128539789

theorem tailTrace_3441484 : CollatzResearch.WordTrace tailWord_3441484 prefixEnd_3441484 21816487120468128539789 := by
  unfold tailWord_3441484
  simp only [CollatzResearch.WordTrace]
  refine ⟨62760616732049350759225753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83680822309399134345634337 62760616732049350759225753)
  ·
    refine ⟨47070462549037013069419315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62760616732049350759225753 47070462549037013069419315)
    ·
      refine ⟨70605693823555519604128973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47070462549037013069419315 70605693823555519604128973)
      ·
        refine ⟨26477135183833319851548365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70605693823555519604128973 26477135183833319851548365)
        ·
          refine ⟨9928925693937494944330637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26477135183833319851548365 9928925693937494944330637)
          ·
            refine ⟨3723347135226560604123989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9928925693937494944330637 3723347135226560604123989)
            ·
              refine ⟨21816487120468128539789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3723347135226560604123989 21816487120468128539789)
              ·
                rfl

theorem cell23_3441484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 9].length) (baseStart_3441484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441484 prefixEnd_3441484 := by exact prefixLift 3441484
  have htrace : WordTrace (prefixWord ++ tailWord_3441484) baseStart_3441484 baseEnd_3441484 := by
    simpa [prefixWord, tailWord_3441484, baseEnd_3441484] using wordTrace_append hprefix tailTrace_3441484
  have hstable : (prefixWord ++ tailWord_3441484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441484).length < 2 ^ (prefixWord ++ tailWord_3441484).sum := by decide
  have hdescent : baseEnd_3441484 < baseStart_3441484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441495 : List Nat := [1, 1, 3, 2, 4, 3, 1, 1, 3, 2, 2]
def baseStart_3441495 : Nat := 118140960795 + 3441495 * 2 ^ 59
def prefixEnd_3441495 : Nat := 4983230072969 + 3 ^ 40 * 3441495 * 2
def baseEnd_3441495 : Nat := 1767141105045117868685359

theorem tailTrace_3441495 : CollatzResearch.WordTrace tailWord_3441495 prefixEnd_3441495 1767141105045117868685359 := by
  unfold tailWord_3441495
  simp only [CollatzResearch.WordTrace]
  refine ⟨125521634667058850397101939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83681089778039233598067959 125521634667058850397101939)
  ·
    refine ⟨188282452000588275595652909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125521634667058850397101939 188282452000588275595652909)
    ·
      refine ⟨70605919500220603348369841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188282452000588275595652909 70605919500220603348369841)
      ·
        refine ⟨52954439625165452511277381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70605919500220603348369841 52954439625165452511277381)
        ·
          refine ⟨9928957429718522345864509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52954439625165452511277381 9928957429718522345864509)
          ·
            refine ⟨3723359036144445879699191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9928957429718522345864509 3723359036144445879699191)
            ·
              refine ⟨5585038554216668819548787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3723359036144445879699191 5585038554216668819548787)
              ·
                refine ⟨8377557831325003229323181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5585038554216668819548787 8377557831325003229323181)
                ·
                  refine ⟨3141584186746876210996193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8377557831325003229323181 3141584186746876210996193)
                  ·
                    refine ⟨2356188140060157158247145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3141584186746876210996193 2356188140060157158247145)
                    ·
                      refine ⟨1767141105045117868685359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2356188140060157158247145 1767141105045117868685359)
                      ·
                        rfl

theorem cell23_3441495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_3441495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441495 prefixEnd_3441495 := by exact prefixLift 3441495
  have htrace : WordTrace (prefixWord ++ tailWord_3441495) baseStart_3441495 baseEnd_3441495 := by
    simpa [prefixWord, tailWord_3441495, baseEnd_3441495] using wordTrace_append hprefix tailTrace_3441495
  have hstable : (prefixWord ++ tailWord_3441495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441495).length < 2 ^ (prefixWord ++ tailWord_3441495).sum := by decide
  have hdescent : baseEnd_3441495 < baseStart_3441495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441591 : List Nat := [1, 1, 3, 1, 3, 1, 3, 5, 5]
def baseStart_3441591 : Nat := 118140960795 + 3441591 * 2 ^ 59
def prefixEnd_3441591 : Nat := 4983230072969 + 3 ^ 40 * 3441591 * 2
def baseEnd_3441591 : Nat := 196354488798661054787213

theorem tailTrace_3441591 : CollatzResearch.WordTrace tailWord_3441591 prefixEnd_3441591 196354488798661054787213 := by
  unfold tailWord_3441591
  simp only [CollatzResearch.WordTrace]
  refine ⟨125525136074711058792596627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83683424049807372528397751 125525136074711058792596627)
  ·
    refine ⟨188287704112066588188894941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125525136074711058792596627 188287704112066588188894941)
    ·
      refine ⟨70607889042024970570835603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188287704112066588188894941 70607889042024970570835603)
      ·
        refine ⟨105911833563037455856253405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70607889042024970570835603 105911833563037455856253405)
        ·
          refine ⟨39716937586139045946095027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105911833563037455856253405 39716937586139045946095027)
          ·
            refine ⟨59575406379208568919142541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39716937586139045946095027 59575406379208568919142541)
            ·
              refine ⟨22340777392203213344678453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59575406379208568919142541 22340777392203213344678453)
              ·
                refine ⟨2094447880519051251063605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22340777392203213344678453 2094447880519051251063605)
                ·
                  refine ⟨196354488798661054787213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2094447880519051251063605 196354488798661054787213)
                  ·
                    rfl

theorem cell23_3441591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 5].length) (baseStart_3441591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441591 prefixEnd_3441591 := by exact prefixLift 3441591
  have htrace : WordTrace (prefixWord ++ tailWord_3441591) baseStart_3441591 baseEnd_3441591 := by
    simpa [prefixWord, tailWord_3441591, baseEnd_3441591] using wordTrace_append hprefix tailTrace_3441591
  have hstable : (prefixWord ++ tailWord_3441591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441591).length < 2 ^ (prefixWord ++ tailWord_3441591).sum := by decide
  have hdescent : baseEnd_3441591 < baseStart_3441591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441618 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_3441618 : Nat := 118140960795 + 3441618 * 2 ^ 59
def prefixEnd_3441618 : Nat := 4983230072969 + 3 ^ 40 * 3441618 * 2
def baseEnd_3441618 : Nat := 1767204263165620887447293

theorem tailTrace_3441618 : CollatzResearch.WordTrace tailWord_3441618 prefixEnd_3441618 1767204263165620887447293 := by
  unfold tailWord_3441618
  simp only [CollatzResearch.WordTrace]
  refine ⟨31381530211403310600957377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83684080563742161602553005 31381530211403310600957377)
  ·
    refine ⟨23536147658552482950718033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31381530211403310600957377 23536147658552482950718033)
    ·
      refine ⟨17652110743914362213038525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23536147658552482950718033 17652110743914362213038525)
      ·
        refine ⟨6619541528967885829889447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17652110743914362213038525 6619541528967885829889447)
        ·
          refine ⟨9929312293451828744834171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6619541528967885829889447 9929312293451828744834171)
          ·
            refine ⟨14893968440177743117251257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9929312293451828744834171 14893968440177743117251257)
            ·
              refine ⟨11170476330133307337938443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14893968440177743117251257 11170476330133307337938443)
              ·
                refine ⟨16755714495199961006907665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11170476330133307337938443 16755714495199961006907665)
                ·
                  refine ⟨12566785871399970755180749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16755714495199961006907665 12566785871399970755180749)
                  ·
                    refine ⟨4712544701774989033192781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12566785871399970755180749 4712544701774989033192781)
                    ·
                      refine ⟨1767204263165620887447293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4712544701774989033192781 1767204263165620887447293)
                      ·
                        rfl

theorem cell23_3441618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_3441618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441618 prefixEnd_3441618 := by exact prefixLift 3441618
  have htrace : WordTrace (prefixWord ++ tailWord_3441618) baseStart_3441618 baseEnd_3441618 := by
    simpa [prefixWord, tailWord_3441618, baseEnd_3441618] using wordTrace_append hprefix tailTrace_3441618
  have hstable : (prefixWord ++ tailWord_3441618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441618).length < 2 ^ (prefixWord ++ tailWord_3441618).sum := by decide
  have hdescent : baseEnd_3441618 < baseStart_3441618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441644 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 5]
def baseStart_3441644 : Nat := 118140960795 + 3441644 * 2 ^ 59
def prefixEnd_3441644 : Nat := 4983230072969 + 3 ^ 40 * 3441644 * 2
def baseEnd_3441644 : Nat := 1767217613662637785722173

theorem tailTrace_3441644 : CollatzResearch.WordTrace tailWord_3441644 prefixEnd_3441644 1767217613662637785722173 := by
  unfold tailWord_3441644
  simp only [CollatzResearch.WordTrace]
  refine ⟨62763534571759524422137993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83684712762346032562850657 62763534571759524422137993)
  ·
    refine ⟨47072650928819643316603495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62763534571759524422137993 47072650928819643316603495)
    ·
      refine ⟨70608976393229464974905243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47072650928819643316603495 70608976393229464974905243)
      ·
        refine ⟨105913464589844197462357865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70608976393229464974905243 105913464589844197462357865)
        ·
          refine ⟨79435098442383148096768399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105913464589844197462357865 79435098442383148096768399)
          ·
            refine ⟨119152647663574722145152599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79435098442383148096768399 119152647663574722145152599)
            ·
              refine ⟨178728971495362083217728899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119152647663574722145152599 178728971495362083217728899)
              ·
                refine ⟨268093457243043124826593349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178728971495362083217728899 268093457243043124826593349)
                ·
                  refine ⟨50267523233070585904986253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 268093457243043124826593349 50267523233070585904986253)
                  ·
                    refine ⟨18850321212401469714369845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50267523233070585904986253 18850321212401469714369845)
                    ·
                      refine ⟨1767217613662637785722173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18850321212401469714369845 1767217613662637785722173)
                      ·
                        rfl

theorem cell23_3441644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_3441644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441644 prefixEnd_3441644 := by exact prefixLift 3441644
  have htrace : WordTrace (prefixWord ++ tailWord_3441644) baseStart_3441644 baseEnd_3441644 := by
    simpa [prefixWord, tailWord_3441644, baseEnd_3441644] using wordTrace_append hprefix tailTrace_3441644
  have hstable : (prefixWord ++ tailWord_3441644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441644).length < 2 ^ (prefixWord ++ tailWord_3441644).sum := by decide
  have hdescent : baseEnd_3441644 < baseStart_3441644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441731 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 4]
def baseStart_3441731 : Nat := 118140960795 + 3441731 * 2 ^ 59
def prefixEnd_3441731 : Nat := 4983230072969 + 3 ^ 40 * 3441731 * 2
def baseEnd_3441731 : Nat := 1767262286479578945334273

theorem tailTrace_3441731 : CollatzResearch.WordTrace tailWord_3441731 prefixEnd_3441731 1767262286479578945334273 := by
  unfold tailWord_3441731
  simp only [CollatzResearch.WordTrace]
  refine ⟨125530242294203862702693047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83686828196135908468462031 125530242294203862702693047)
  ·
    refine ⟨188295363441305794054039571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125530242294203862702693047 188295363441305794054039571)
    ·
      refine ⟨282443045161958691081059357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188295363441305794054039571 282443045161958691081059357)
      ·
        refine ⟨105916141935734509155397259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282443045161958691081059357 105916141935734509155397259)
        ·
          refine ⟨158874212903601763733095889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105916141935734509155397259 158874212903601763733095889)
          ·
            refine ⟨119155659677701322799821917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158874212903601763733095889 119155659677701322799821917)
            ·
              refine ⟨44683372379137996049933219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119155659677701322799821917 44683372379137996049933219)
              ·
                refine ⟨67025058568706994074899829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44683372379137996049933219 67025058568706994074899829)
                ·
                  refine ⟨6283599240816280694521859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67025058568706994074899829 6283599240816280694521859)
                  ·
                    refine ⟨9425398861224421041782789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6283599240816280694521859 9425398861224421041782789)
                    ·
                      refine ⟨1767262286479578945334273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9425398861224421041782789 1767262286479578945334273)
                      ·
                        rfl

theorem cell23_3441731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_3441731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441731 prefixEnd_3441731 := by exact prefixLift 3441731
  have htrace : WordTrace (prefixWord ++ tailWord_3441731) baseStart_3441731 baseEnd_3441731 := by
    simpa [prefixWord, tailWord_3441731, baseEnd_3441731] using wordTrace_append hprefix tailTrace_3441731
  have hstable : (prefixWord ++ tailWord_3441731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441731).length < 2 ^ (prefixWord ++ tailWord_3441731).sum := by decide
  have hdescent : baseEnd_3441731 < baseStart_3441731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441748 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_3441748 : Nat := 118140960795 + 3441748 * 2 ^ 59
def prefixEnd_3441748 : Nat := 4983230072969 + 3 ^ 40 * 3441748 * 2
def baseEnd_3441748 : Nat := 1767271015650705378821695

theorem tailTrace_3441748 : CollatzResearch.WordTrace tailWord_3441748 prefixEnd_3441748 1767271015650705378821695 := by
  unfold tailWord_3441748
  simp only [CollatzResearch.WordTrace]
  refine ⟨62765431167571137303030949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83687241556761516404041265 62765431167571137303030949)
  ·
    refine ⟨11768518343919588244318303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62765431167571137303030949 11768518343919588244318303)
    ·
      refine ⟨17652777515879382366477455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11768518343919588244318303 17652777515879382366477455)
      ·
        refine ⟨26479166273819073549716183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17652777515879382366477455 26479166273819073549716183)
        ·
          refine ⟨39718749410728610324574275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26479166273819073549716183 39718749410728610324574275)
          ·
            refine ⟨59578124116092915486861413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39718749410728610324574275 59578124116092915486861413)
            ·
              refine ⟨11170898271767421653786515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59578124116092915486861413 11170898271767421653786515)
              ·
                refine ⟨16756347407651132480679773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11170898271767421653786515 16756347407651132480679773)
                ·
                  refine ⟨6283630277869174680254915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16756347407651132480679773 6283630277869174680254915)
                  ·
                    refine ⟨9425445416803762020382373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6283630277869174680254915 9425445416803762020382373)
                    ·
                      refine ⟨1767271015650705378821695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9425445416803762020382373 1767271015650705378821695)
                      ·
                        rfl

theorem cell23_3441748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_3441748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441748 prefixEnd_3441748 := by exact prefixLift 3441748
  have htrace : WordTrace (prefixWord ++ tailWord_3441748) baseStart_3441748 baseEnd_3441748 := by
    simpa [prefixWord, tailWord_3441748, baseEnd_3441748] using wordTrace_append hprefix tailTrace_3441748
  have hstable : (prefixWord ++ tailWord_3441748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441748).length < 2 ^ (prefixWord ++ tailWord_3441748).sum := by decide
  have hdescent : baseEnd_3441748 < baseStart_3441748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441762 : List Nat := [3, 3, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_3441762 : Nat := 118140960795 + 3441762 * 2 ^ 59
def prefixEnd_3441762 : Nat := 4983230072969 + 3 ^ 40 * 3441762 * 2
def baseEnd_3441762 : Nat := 589092734793289441348877

theorem tailTrace_3441762 : CollatzResearch.WordTrace tailWord_3441762 prefixEnd_3441762 589092734793289441348877 := by
  unfold tailWord_3441762
  simp only [CollatzResearch.WordTrace]
  refine ⟨31382843239272888749267885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83687581971394369998047693 31382843239272888749267885)
  ·
    refine ⟨11768566214727333280975457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31382843239272888749267885 11768566214727333280975457)
    ·
      refine ⟨8826424661045499960731593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11768566214727333280975457 8826424661045499960731593)
      ·
        refine ⟨6619818495784124970548695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8826424661045499960731593 6619818495784124970548695)
        ·
          refine ⟨9929727743676187455823043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6619818495784124970548695 9929727743676187455823043)
          ·
            refine ⟨14894591615514281183734565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9929727743676187455823043 14894591615514281183734565)
            ·
              refine ⟨2792735927908927721950231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14894591615514281183734565 2792735927908927721950231)
              ·
                refine ⟨4189103891863391582925347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2792735927908927721950231 4189103891863391582925347)
                ·
                  refine ⟨6283655837795087374388021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4189103891863391582925347 6283655837795087374388021)
                  ·
                    refine ⟨589092734793289441348877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6283655837795087374388021 589092734793289441348877)
                    ·
                      rfl

theorem cell23_3441762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_3441762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441762 prefixEnd_3441762 := by exact prefixLift 3441762
  have htrace : WordTrace (prefixWord ++ tailWord_3441762) baseStart_3441762 baseEnd_3441762 := by
    simpa [prefixWord, tailWord_3441762, baseEnd_3441762] using wordTrace_append hprefix tailTrace_3441762
  have hstable : (prefixWord ++ tailWord_3441762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441762).length < 2 ^ (prefixWord ++ tailWord_3441762).sum := by decide
  have hdescent : baseEnd_3441762 < baseStart_3441762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441765 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 5, 2, 2]
def baseStart_3441765 : Nat := 118140960795 + 3441765 * 2 ^ 59
def prefixEnd_3441765 : Nat := 4983230072969 + 3 ^ 40 * 3441765 * 2
def baseEnd_3441765 : Nat := 1767279744821831812309117

theorem tailTrace_3441765 : CollatzResearch.WordTrace tailWord_3441765 prefixEnd_3441765 1767279744821831812309117 := by
  unfold tailWord_3441765
  simp only [CollatzResearch.WordTrace]
  refine ⟨125531482376080686509430749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83687654917387124339620499 125531482376080686509430749)
  ·
    refine ⟨47074305891030257441036531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125531482376080686509430749 47074305891030257441036531)
    ·
      refine ⟨70611458836545386161554797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47074305891030257441036531 70611458836545386161554797)
      ·
        refine ⟨26479297063704519810583049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70611458836545386161554797 26479297063704519810583049)
        ·
          refine ⟨19859472797778389857937287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26479297063704519810583049 19859472797778389857937287)
          ·
            refine ⟨29789209196667584786905931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19859472797778389857937287 29789209196667584786905931)
            ·
              refine ⟨44683813795001377180358897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29789209196667584786905931 44683813795001377180358897)
              ·
                refine ⟨33512860346251032885269173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44683813795001377180358897 33512860346251032885269173)
                ·
                  refine ⟨3141830657461034332993985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33512860346251032885269173 3141830657461034332993985)
                  ·
                    refine ⟨2356372993095775749745489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3141830657461034332993985 2356372993095775749745489)
                    ·
                      refine ⟨1767279744821831812309117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2356372993095775749745489 1767279744821831812309117)
                      ·
                        rfl

theorem cell23_3441765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_3441765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441765 prefixEnd_3441765 := by exact prefixLift 3441765
  have htrace : WordTrace (prefixWord ++ tailWord_3441765) baseStart_3441765 baseEnd_3441765 := by
    simpa [prefixWord, tailWord_3441765, baseEnd_3441765] using wordTrace_append hprefix tailTrace_3441765
  have hstable : (prefixWord ++ tailWord_3441765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441765).length < 2 ^ (prefixWord ++ tailWord_3441765).sum := by decide
  have hdescent : baseEnd_3441765 < baseStart_3441765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441811 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 5]
def baseStart_3441811 : Nat := 118140960795 + 3441811 * 2 ^ 59
def prefixEnd_3441811 : Nat := 4983230072969 + 3 ^ 40 * 3441811 * 2
def baseEnd_3441811 : Nat := 1767303364931938632333905

theorem tailTrace_3441811 : CollatzResearch.WordTrace tailWord_3441811 prefixEnd_3441811 1767303364931938632333905 := by
  unfold tailWord_3441811
  simp only [CollatzResearch.WordTrace]
  refine ⟨125533160133914036365605287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83688773422609357577070191 125533160133914036365605287)
  ·
    refine ⟨188299740200871054548407931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125533160133914036365605287 188299740200871054548407931)
    ·
      refine ⟨282449610301306581822611897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188299740200871054548407931 282449610301306581822611897)
      ·
        refine ⟨211837207725979936366958923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282449610301306581822611897 211837207725979936366958923)
        ·
          refine ⟨317755811588969904550438385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211837207725979936366958923 317755811588969904550438385)
          ·
            refine ⟨238316858691727428412828789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317755811588969904550438385 238316858691727428412828789)
            ·
              refine ⟨22342205502349446413702699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 238316858691727428412828789 22342205502349446413702699)
              ·
                refine ⟨33513308253524169620554049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22342205502349446413702699 33513308253524169620554049)
                ·
                  refine ⟨25134981190143127215415537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33513308253524169620554049 25134981190143127215415537)
                  ·
                    refine ⟨18851235892607345411561653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25134981190143127215415537 18851235892607345411561653)
                    ·
                      refine ⟨1767303364931938632333905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18851235892607345411561653 1767303364931938632333905)
                      ·
                        rfl

theorem cell23_3441811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_3441811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441811 prefixEnd_3441811 := by exact prefixLift 3441811
  have htrace : WordTrace (prefixWord ++ tailWord_3441811) baseStart_3441811 baseEnd_3441811 := by
    simpa [prefixWord, tailWord_3441811, baseEnd_3441811] using wordTrace_append hprefix tailTrace_3441811
  have hstable : (prefixWord ++ tailWord_3441811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441811).length < 2 ^ (prefixWord ++ tailWord_3441811).sum := by decide
  have hdescent : baseEnd_3441811 < baseStart_3441811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441815 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 4, 1, 3]
def baseStart_3441815 : Nat := 118140960795 + 3441815 * 2 ^ 59
def prefixEnd_3441815 : Nat := 4983230072969 + 3 ^ 40 * 3441815 * 2
def baseEnd_3441815 : Nat := 1767305418854556616683887

theorem tailTrace_3441815 : CollatzResearch.WordTrace tailWord_3441815 prefixEnd_3441815 1767305418854556616683887 := by
  unfold tailWord_3441815
  simp only [CollatzResearch.WordTrace]
  refine ⟨125533306025899545048750899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83688870683933030032500599 125533306025899545048750899)
  ·
    refine ⟨188299959038849317573126349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125533306025899545048750899 188299959038849317573126349)
    ·
      refine ⟨70612484639568494089922381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188299959038849317573126349 70612484639568494089922381)
      ·
        refine ⟨26479681739838185283720893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70612484639568494089922381 26479681739838185283720893)
        ·
          refine ⟨9929880652439319481395335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26479681739838185283720893 9929880652439319481395335)
          ·
            refine ⟨14894820978658979222093003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9929880652439319481395335 14894820978658979222093003)
            ·
              refine ⟨22342231467988468833139505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14894820978658979222093003 22342231467988468833139505)
              ·
                refine ⟨16756673600991351624854629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22342231467988468833139505 16756673600991351624854629)
                ·
                  refine ⟨3141876300185878429660243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16756673600991351624854629 3141876300185878429660243)
                  ·
                    refine ⟨4712814450278817644490365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3141876300185878429660243 4712814450278817644490365)
                    ·
                      refine ⟨1767305418854556616683887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4712814450278817644490365 1767305418854556616683887)
                      ·
                        rfl

theorem cell23_3441815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_3441815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441815 prefixEnd_3441815 := by exact prefixLift 3441815
  have htrace : WordTrace (prefixWord ++ tailWord_3441815) baseStart_3441815 baseEnd_3441815 := by
    simpa [prefixWord, tailWord_3441815, baseEnd_3441815] using wordTrace_append hprefix tailTrace_3441815
  have hstable : (prefixWord ++ tailWord_3441815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441815).length < 2 ^ (prefixWord ++ tailWord_3441815).sum := by decide
  have hdescent : baseEnd_3441815 < baseStart_3441815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441816 : List Nat := [2, 1, 2, 4, 2, 3, 1, 3, 1, 2, 2]
def baseStart_3441816 : Nat := 118140960795 + 3441816 * 2 ^ 59
def prefixEnd_3441816 : Nat := 4983230072969 + 3 ^ 40 * 3441816 * 2
def baseEnd_3441816 : Nat := 1767305932335211112771383

theorem tailTrace_3441816 : CollatzResearch.WordTrace tailWord_3441816 prefixEnd_3441816 1767305932335211112771383 := by
  unfold tailWord_3441816
  simp only [CollatzResearch.WordTrace]
  refine ⟨62766671249447961109768651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83688894999263948146358201 62766671249447961109768651)
  ·
    refine ⟨94150006874171941664652977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62766671249447961109768651 94150006874171941664652977)
    ·
      refine ⟨70612505155628956248489733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94150006874171941664652977 70612505155628956248489733)
      ·
        refine ⟨13239844716680429296591825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70612505155628956248489733 13239844716680429296591825)
        ·
          refine ⟨9929883537510321972443869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13239844716680429296591825 9929883537510321972443869)
          ·
            refine ⟨3723706326566370739666451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9929883537510321972443869 3723706326566370739666451)
            ·
              refine ⟨5585559489849556109499677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3723706326566370739666451 5585559489849556109499677)
              ·
                refine ⟨2094584808693583541062379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5585559489849556109499677 2094584808693583541062379)
                ·
                  refine ⟨3141877213040375311593569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2094584808693583541062379 3141877213040375311593569)
                  ·
                    refine ⟨2356407909780281483695177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3141877213040375311593569 2356407909780281483695177)
                    ·
                      refine ⟨1767305932335211112771383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2356407909780281483695177 1767305932335211112771383)
                      ·
                        rfl

theorem cell23_3441816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_3441816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441816 prefixEnd_3441816 := by exact prefixLift 3441816
  have htrace : WordTrace (prefixWord ++ tailWord_3441816) baseStart_3441816 baseEnd_3441816 := by
    simpa [prefixWord, tailWord_3441816, baseEnd_3441816] using wordTrace_append hprefix tailTrace_3441816
  have hstable : (prefixWord ++ tailWord_3441816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441816).length < 2 ^ (prefixWord ++ tailWord_3441816).sum := by decide
  have hdescent : baseEnd_3441816 < baseStart_3441816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441849 : List Nat := [1, 2, 1, 4, 1, 5, 2, 1, 2, 1, 3]
def baseStart_3441849 : Nat := 118140960795 + 3441849 * 2 ^ 59
def prefixEnd_3441849 : Nat := 4983230072969 + 3 ^ 40 * 3441849 * 2
def baseEnd_3441849 : Nat := 1767322877196809483658731

theorem tailTrace_3441849 : CollatzResearch.WordTrace tailWord_3441849 prefixEnd_3441849 1767322877196809483658731 := by
  unfold tailWord_3441849
  simp only [CollatzResearch.WordTrace]
  refine ⟨125534546107776368855488601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83689697405184245903659067 125534546107776368855488601)
  ·
    refine ⟨94150909580832276641616451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125534546107776368855488601 94150909580832276641616451)
    ·
      refine ⟨141226364371248414962424677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94150909580832276641616451 141226364371248414962424677)
      ·
        refine ⟨26479943319609077805454627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141226364371248414962424677 26479943319609077805454627)
        ·
          refine ⟨39719914979413616708181941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26479943319609077805454627 39719914979413616708181941)
          ·
            refine ⟨3723742029320026566392057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39719914979413616708181941 3723742029320026566392057)
            ·
              refine ⟨2792806521990019924794043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3723742029320026566392057 2792806521990019924794043)
              ·
                refine ⟨4189209782985029887191065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2792806521990019924794043 4189209782985029887191065)
                ·
                  refine ⟨3141907337238772415393299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4189209782985029887191065 3141907337238772415393299)
                  ·
                    refine ⟨4712861005858158623089949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3141907337238772415393299 4712861005858158623089949)
                    ·
                      refine ⟨1767322877196809483658731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4712861005858158623089949 1767322877196809483658731)
                      ·
                        rfl

theorem cell23_3441849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_3441849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441849 prefixEnd_3441849 := by exact prefixLift 3441849
  have htrace : WordTrace (prefixWord ++ tailWord_3441849) baseStart_3441849 baseEnd_3441849 := by
    simpa [prefixWord, tailWord_3441849, baseEnd_3441849] using wordTrace_append hprefix tailTrace_3441849
  have hstable : (prefixWord ++ tailWord_3441849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441849).length < 2 ^ (prefixWord ++ tailWord_3441849).sum := by decide
  have hdescent : baseEnd_3441849 < baseStart_3441849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441861 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 9]
def baseStart_3441861 : Nat := 118140960795 + 3441861 * 2 ^ 59
def prefixEnd_3441861 : Nat := 4983230072969 + 3 ^ 40 * 3441861 * 2
def baseEnd_3441861 : Nat := 196369893218295937412075

theorem tailTrace_3441861 : CollatzResearch.WordTrace tailWord_3441861 prefixEnd_3441861 196369893218295937412075 := by
  unfold tailWord_3441861
  simp only [CollatzResearch.WordTrace]
  refine ⟨125534983783732894904925437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83689989189155263269950291 125534983783732894904925437)
  ·
    refine ⟨47075618918899835589347039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125534983783732894904925437 47075618918899835589347039)
    ·
      refine ⟨70613428378349753384020559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47075618918899835589347039 70613428378349753384020559)
      ·
        refine ⟨105920142567524630076030839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70613428378349753384020559 105920142567524630076030839)
        ·
          refine ⟨158880213851286945114046259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105920142567524630076030839 158880213851286945114046259)
          ·
            refine ⟨238320320776930417671069389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158880213851286945114046259 238320320776930417671069389)
            ·
              refine ⟨89370120291348906626651021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238320320776930417671069389 89370120291348906626651021)
              ·
                refine ⟨33513795109255839984994133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89370120291348906626651021 33513795109255839984994133)
                ·
                  refine ⟨196369893218295937412075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33513795109255839984994133 196369893218295937412075)
                  ·
                    rfl

theorem cell23_3441861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 9].length) (baseStart_3441861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441861 prefixEnd_3441861 := by exact prefixLift 3441861
  have htrace : WordTrace (prefixWord ++ tailWord_3441861) baseStart_3441861 baseEnd_3441861 := by
    simpa [prefixWord, tailWord_3441861, baseEnd_3441861] using wordTrace_append hprefix tailTrace_3441861
  have hstable : (prefixWord ++ tailWord_3441861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441861).length < 2 ^ (prefixWord ++ tailWord_3441861).sum := by decide
  have hdescent : baseEnd_3441861 < baseStart_3441861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441871 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 7]
def baseStart_3441871 : Nat := 118140960795 + 3441871 * 2 ^ 59
def prefixEnd_3441871 : Nat := 4983230072969 + 3 ^ 40 * 3441871 * 2
def baseEnd_3441871 : Nat := 1767334173771208397583629

theorem tailTrace_3441871 : CollatzResearch.WordTrace tailWord_3441871 prefixEnd_3441871 1767334173771208397583629 := by
  unfold tailWord_3441871
  simp only [CollatzResearch.WordTrace]
  refine ⟨125535348513696666612789467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83690232342464444408526311 125535348513696666612789467)
  ·
    refine ⟨188303022770544999919184201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125535348513696666612789467 188303022770544999919184201)
    ·
      refine ⟨141227267077908749939388151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188303022770544999919184201 141227267077908749939388151)
      ·
        refine ⟨211840900616863124909082227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141227267077908749939388151 211840900616863124909082227)
        ·
          refine ⟨317761350925294687363623341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211840900616863124909082227 317761350925294687363623341)
          ·
            refine ⟨119160506596985507761358753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317761350925294687363623341 119160506596985507761358753)
            ·
              refine ⟨89370379947739130821019065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119160506596985507761358753 89370379947739130821019065)
              ·
                refine ⟨67027784960804348115764299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89370379947739130821019065 67027784960804348115764299)
                ·
                  refine ⟨100541677441206522173646449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67027784960804348115764299 100541677441206522173646449)
                  ·
                    refine ⟨75406258080904891630234837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100541677441206522173646449 75406258080904891630234837)
                    ·
                      refine ⟨1767334173771208397583629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 75406258080904891630234837 1767334173771208397583629)
                      ·
                        rfl

theorem cell23_3441871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_3441871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441871 prefixEnd_3441871 := by exact prefixLift 3441871
  have htrace : WordTrace (prefixWord ++ tailWord_3441871) baseStart_3441871 baseEnd_3441871 := by
    simpa [prefixWord, tailWord_3441871, baseEnd_3441871] using wordTrace_append hprefix tailTrace_3441871
  have hstable : (prefixWord ++ tailWord_3441871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441871).length < 2 ^ (prefixWord ++ tailWord_3441871).sum := by decide
  have hdescent : baseEnd_3441871 < baseStart_3441871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441889 : List Nat := [1, 2, 3, 1, 3, 3, 2, 2, 2, 2, 2]
def baseStart_3441889 : Nat := 118140960795 + 3441889 * 2 ^ 59
def prefixEnd_3441889 : Nat := 4983230072969 + 3 ^ 40 * 3441889 * 2
def baseEnd_3441889 : Nat := 1767343416422989327158547

theorem tailTrace_3441889 : CollatzResearch.WordTrace tailWord_3441889 prefixEnd_3441889 1767343416422989327158547 := by
  unfold tailWord_3441889
  simp only [CollatzResearch.WordTrace]
  refine ⟨125536005027631455686944721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83690670018420970457963147 125536005027631455686944721)
  ·
    refine ⟨94152003770723591765208541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125536005027631455686944721 94152003770723591765208541)
    ·
      refine ⟨35307001414021346911953203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94152003770723591765208541 35307001414021346911953203)
      ·
        refine ⟨52960502121032020367929805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35307001414021346911953203 52960502121032020367929805)
        ·
          refine ⟨19860188295387007637973677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52960502121032020367929805 19860188295387007637973677)
          ·
            refine ⟨7447570610770127864240129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19860188295387007637973677 7447570610770127864240129)
            ·
              refine ⟨5585677958077595898180097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7447570610770127864240129 5585677958077595898180097)
              ·
                refine ⟨4189258468558196923635073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5585677958077595898180097 4189258468558196923635073)
                ·
                  refine ⟨3141943851418647692726305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4189258468558196923635073 3141943851418647692726305)
                  ·
                    refine ⟨2356457888563985769544729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3141943851418647692726305 2356457888563985769544729)
                    ·
                      refine ⟨1767343416422989327158547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2356457888563985769544729 1767343416422989327158547)
                      ·
                        rfl

theorem cell23_3441889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_3441889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441889 prefixEnd_3441889 := by exact prefixLift 3441889
  have htrace : WordTrace (prefixWord ++ tailWord_3441889) baseStart_3441889 baseEnd_3441889 := by
    simpa [prefixWord, tailWord_3441889, baseEnd_3441889] using wordTrace_append hprefix tailTrace_3441889
  have hstable : (prefixWord ++ tailWord_3441889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441889).length < 2 ^ (prefixWord ++ tailWord_3441889).sum := by decide
  have hdescent : baseEnd_3441889 < baseStart_3441889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441948 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_3441948 : Nat := 118140960795 + 3441948 * 2 ^ 59
def prefixEnd_3441948 : Nat := 4983230072969 + 3 ^ 40 * 3441948 * 2
def baseEnd_3441948 : Nat := 1767373711781604596320775

theorem tailTrace_3441948 : CollatzResearch.WordTrace tailWord_3441948 prefixEnd_3441948 1767373711781604596320775 := by
  unfold tailWord_3441948
  simp only [CollatzResearch.WordTrace]
  refine ⟨62769078467208854381671249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83692104622945139175561665 62769078467208854381671249)
  ·
    refine ⟨47076808850406640786253437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62769078467208854381671249 47076808850406640786253437)
    ·
      refine ⟨17653803318902490294845039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47076808850406640786253437 17653803318902490294845039)
      ·
        refine ⟨26480704978353735442267559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17653803318902490294845039 26480704978353735442267559)
        ·
          refine ⟨39721057467530603163401339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26480704978353735442267559 39721057467530603163401339)
          ·
            refine ⟨59581586201295904745102009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39721057467530603163401339 59581586201295904745102009)
            ·
              refine ⟨44686189650971928558826507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59581586201295904745102009 44686189650971928558826507)
              ·
                refine ⟨67029284476457892838239761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44686189650971928558826507 67029284476457892838239761)
                ·
                  refine ⟨50271963357343419628679821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67029284476457892838239761 50271963357343419628679821)
                  ·
                    refine ⟨18851986259003782360754933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50271963357343419628679821 18851986259003782360754933)
                    ·
                      refine ⟨1767373711781604596320775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18851986259003782360754933 1767373711781604596320775)
                      ·
                        rfl

theorem cell23_3441948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_3441948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441948 prefixEnd_3441948 := by exact prefixLift 3441948
  have htrace : WordTrace (prefixWord ++ tailWord_3441948) baseStart_3441948 baseEnd_3441948 := by
    simpa [prefixWord, tailWord_3441948, baseEnd_3441948] using wordTrace_append hprefix tailTrace_3441948
  have hstable : (prefixWord ++ tailWord_3441948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441948).length < 2 ^ (prefixWord ++ tailWord_3441948).sum := by decide
  have hdescent : baseEnd_3441948 < baseStart_3441948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441955 : List Nat := [1, 1, 1, 4, 2, 3, 1, 3, 3, 4]
def baseStart_3441955 : Nat := 118140960795 + 3441955 * 2 ^ 59
def prefixEnd_3441955 : Nat := 4983230072969 + 3 ^ 40 * 3441955 * 2
def baseEnd_3441955 : Nat := 589125768715395356311081

theorem tailTrace_3441955 : CollatzResearch.WordTrace tailWord_3441955 prefixEnd_3441955 589125768715395356311081 := by
  unfold tailWord_3441955
  simp only [CollatzResearch.WordTrace]
  refine ⟨125538412245392348958847319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83692274830261565972564879 125538412245392348958847319)
  ·
    refine ⟨188307618368088523438270979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125538412245392348958847319 188307618368088523438270979)
    ·
      refine ⟨282461427552132785157406469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188307618368088523438270979 282461427552132785157406469)
      ·
        refine ⟨52961517666024897217013713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282461427552132785157406469 52961517666024897217013713)
        ·
          refine ⟨39721138249518672912760285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52961517666024897217013713 39721138249518672912760285)
          ·
            refine ⟨14895426843569502342285107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39721138249518672912760285 14895426843569502342285107)
            ·
              refine ⟨22343140265354253513427661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14895426843569502342285107 22343140265354253513427661)
              ·
                refine ⟨8378677599507845067535373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22343140265354253513427661 8378677599507845067535373)
                ·
                  refine ⟨3142004099815441900325765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8378677599507845067535373 3142004099815441900325765)
                  ·
                    refine ⟨589125768715395356311081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3142004099815441900325765 589125768715395356311081)
                    ·
                      rfl

theorem cell23_3441955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 4].length) (baseStart_3441955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441955 prefixEnd_3441955 := by exact prefixLift 3441955
  have htrace : WordTrace (prefixWord ++ tailWord_3441955) baseStart_3441955 baseEnd_3441955 := by
    simpa [prefixWord, tailWord_3441955, baseEnd_3441955] using wordTrace_append hprefix tailTrace_3441955
  have hstable : (prefixWord ++ tailWord_3441955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441955).length < 2 ^ (prefixWord ++ tailWord_3441955).sum := by decide
  have hdescent : baseEnd_3441955 < baseStart_3441955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441972 : List Nat := [2, 5, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_3441972 : Nat := 118140960795 + 3441972 * 2 ^ 59
def prefixEnd_3441972 : Nat := 4983230072969 + 3 ^ 40 * 3441972 * 2
def baseEnd_3441972 : Nat := 589128678439104167473555

theorem tailTrace_3441972 : CollatzResearch.WordTrace tailWord_3441972 prefixEnd_3441972 589128678439104167473555 := by
  unfold tailWord_3441972
  simp only [CollatzResearch.WordTrace]
  refine ⟨62769516143165380431108085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83692688190887173908144113 62769516143165380431108085)
  ·
    refine ⟨5884642138421754415416383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62769516143165380431108085 5884642138421754415416383)
    ·
      refine ⟨8826963207632631623124575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5884642138421754415416383 8826963207632631623124575)
      ·
        refine ⟨13240444811448947434686863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8826963207632631623124575 13240444811448947434686863)
        ·
          refine ⟨19860667217173421152030295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13240444811448947434686863 19860667217173421152030295)
          ·
            refine ⟨29791000825760131728045443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19860667217173421152030295 29791000825760131728045443)
            ·
              refine ⟨44686501238640197592068165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29791000825760131728045443 44686501238640197592068165)
              ·
                refine ⟨8378718982245037048512781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44686501238640197592068165 8378718982245037048512781)
                ·
                  refine ⟨3142019618341888893192293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8378718982245037048512781 3142019618341888893192293)
                  ·
                    refine ⟨589128678439104167473555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3142019618341888893192293 589128678439104167473555)
                    ·
                      rfl

theorem cell23_3441972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_3441972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441972 prefixEnd_3441972 := by exact prefixLift 3441972
  have htrace : WordTrace (prefixWord ++ tailWord_3441972) baseStart_3441972 baseEnd_3441972 := by
    simpa [prefixWord, tailWord_3441972, baseEnd_3441972] using wordTrace_append hprefix tailTrace_3441972
  have hstable : (prefixWord ++ tailWord_3441972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441972).length < 2 ^ (prefixWord ++ tailWord_3441972).sum := by decide
  have hdescent : baseEnd_3441972 < baseStart_3441972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441982 : List Nat := [4, 2, 1, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_3441982 : Nat := 118140960795 + 3441982 * 2 ^ 59
def prefixEnd_3441982 : Nat := 4983230072969 + 3 ^ 40 * 3441982 * 2
def baseEnd_3441982 : Nat := 1767391170123857463295619

theorem tailTrace_3441982 : CollatzResearch.WordTrace tailWord_3441982 prefixEnd_3441982 1767391170123857463295619 := by
  unfold tailWord_3441982
  simp only [CollatzResearch.WordTrace]
  refine ⟨15692424627036816571260025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83692931344196355046720133 15692424627036816571260025)
  ·
    refine ⟨11769318470277612428445019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15692424627036816571260025 11769318470277612428445019)
    ·
      refine ⟨17653977705416418642667529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11769318470277612428445019 17653977705416418642667529)
      ·
        refine ⟨13240483279062313982000647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17653977705416418642667529 13240483279062313982000647)
        ·
          refine ⟨19860724918593470973000971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13240483279062313982000647 19860724918593470973000971)
          ·
            refine ⟨29791087377890206459501457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19860724918593470973000971 29791087377890206459501457)
            ·
              refine ⟨22343315533417654844626093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29791087377890206459501457 22343315533417654844626093)
              ·
                refine ⟨8378743325031620566734785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22343315533417654844626093 8378743325031620566734785)
                ·
                  refine ⟨6284057493773715425051089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8378743325031620566734785 6284057493773715425051089)
                  ·
                    refine ⟨4713043120330286568788317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6284057493773715425051089 4713043120330286568788317)
                    ·
                      refine ⟨1767391170123857463295619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4713043120330286568788317 1767391170123857463295619)
                      ·
                        rfl

theorem cell23_3441982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_3441982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441982 prefixEnd_3441982 := by exact prefixLift 3441982
  have htrace : WordTrace (prefixWord ++ tailWord_3441982) baseStart_3441982 baseEnd_3441982 := by
    simpa [prefixWord, tailWord_3441982, baseEnd_3441982] using wordTrace_append hprefix tailTrace_3441982
  have hstable : (prefixWord ++ tailWord_3441982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441982).length < 2 ^ (prefixWord ++ tailWord_3441982).sum := by decide
  have hdescent : baseEnd_3441982 < baseStart_3441982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441985 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 8]
def baseStart_3441985 : Nat := 118140960795 + 3441985 * 2 ^ 59
def prefixEnd_3441985 : Nat := 4983230072969 + 3 ^ 40 * 3441985 * 2
def baseEnd_3441985 : Nat := 196376967840646772395345

theorem tailTrace_3441985 : CollatzResearch.WordTrace tailWord_3441985 prefixEnd_3441985 196376967840646772395345 := by
  unfold tailWord_3441985
  simp only [CollatzResearch.WordTrace]
  refine ⟨125539506435283664082439409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83693004290189109388292939 125539506435283664082439409)
  ·
    refine ⟨94154629826462748061829557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125539506435283664082439409 94154629826462748061829557)
    ·
      refine ⟨8826996546230882630796521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94154629826462748061829557 8826996546230882630796521)
      ·
        refine ⟨6620247409673161973097391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8826996546230882630796521 6620247409673161973097391)
        ·
          refine ⟨9930371114509742959646087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6620247409673161973097391 9930371114509742959646087)
          ·
            refine ⟨14895556671764614439469131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9930371114509742959646087 14895556671764614439469131)
            ·
              refine ⟨22343335007646921659203697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14895556671764614439469131 22343335007646921659203697)
              ·
                refine ⟨16757501255735191244402773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22343335007646921659203697 16757501255735191244402773)
                ·
                  refine ⟨196376967840646772395345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16757501255735191244402773 196376967840646772395345)
                  ·
                    rfl

theorem cell23_3441985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 8].length) (baseStart_3441985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3441985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3441985 prefixEnd_3441985 := by exact prefixLift 3441985
  have htrace : WordTrace (prefixWord ++ tailWord_3441985) baseStart_3441985 baseEnd_3441985 := by
    simpa [prefixWord, tailWord_3441985, baseEnd_3441985] using wordTrace_append hprefix tailTrace_3441985
  have hstable : (prefixWord ++ tailWord_3441985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441985).length < 2 ^ (prefixWord ++ tailWord_3441985).sum := by decide
  have hdescent : baseEnd_3441985 < baseStart_3441985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442045 : List Nat := [1, 4, 1, 1, 2, 2, 3, 2, 1, 6]
def baseStart_3442045 : Nat := 118140960795 + 3442045 * 2 ^ 59
def prefixEnd_3442045 : Nat := 4983230072969 + 3 ^ 40 * 3442045 * 2
def baseEnd_3442045 : Nat := 589141173135030238935943

theorem tailTrace_3442045 : CollatzResearch.WordTrace tailWord_3442045 prefixEnd_3442045 589141173135030238935943 := by
  unfold tailWord_3442045
  simp only [CollatzResearch.WordTrace]
  refine ⟨125541694815066294329623589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83694463210044196219749059 125541694815066294329623589)
  ·
    refine ⟨23539067777824930186804423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125541694815066294329623589 23539067777824930186804423)
    ·
      refine ⟨35308601666737395280206635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23539067777824930186804423 35308601666737395280206635)
      ·
        refine ⟨52962902500106092920309953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35308601666737395280206635 52962902500106092920309953)
        ·
          refine ⟨39722176875079569690232465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52962902500106092920309953 39722176875079569690232465)
          ·
            refine ⟨29791632656309677267674349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39722176875079569690232465 29791632656309677267674349)
            ·
              refine ⟨11171862246116128975377881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29791632656309677267674349 11171862246116128975377881)
              ·
                refine ⟨8378896684587096731533411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11171862246116128975377881 8378896684587096731533411)
                ·
                  refine ⟨12568345026880645097300117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8378896684587096731533411 12568345026880645097300117)
                  ·
                    refine ⟨589141173135030238935943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12568345026880645097300117 589141173135030238935943)
                    ·
                      rfl

theorem cell23_3442045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_3442045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442045 prefixEnd_3442045 := by exact prefixLift 3442045
  have htrace : WordTrace (prefixWord ++ tailWord_3442045) baseStart_3442045 baseEnd_3442045 := by
    simpa [prefixWord, tailWord_3442045, baseEnd_3442045] using wordTrace_append hprefix tailTrace_3442045
  have hstable : (prefixWord ++ tailWord_3442045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442045).length < 2 ^ (prefixWord ++ tailWord_3442045).sum := by decide
  have hdescent : baseEnd_3442045 < baseStart_3442045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442058 : List Nat := [3, 1, 2, 17]
def baseStart_3442058 : Nat := 118140960795 + 3442058 * 2 ^ 59
def prefixEnd_3442058 : Nat := 4983230072969 + 3 ^ 40 * 3442058 * 2
def baseEnd_3442058 : Nat := 808152809626702865087

theorem tailTrace_3442058 : CollatzResearch.WordTrace tailWord_3442058 prefixEnd_3442058 808152809626702865087 := by
  unfold tailWord_3442058
  simp only [CollatzResearch.WordTrace]
  refine ⟨31385542241004799387461707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83694779309346131699897885 31385542241004799387461707)
  ·
    refine ⟨47078313361507199081192561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31385542241004799387461707 47078313361507199081192561)
    ·
      refine ⟨35308735021130399310894421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47078313361507199081192561 35308735021130399310894421)
      ·
        refine ⟨808152809626702865087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 17 35308735021130399310894421 808152809626702865087)
        ·
          rfl

theorem cell23_3442058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 17].length) (baseStart_3442058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442058 prefixEnd_3442058 := by exact prefixLift 3442058
  have htrace : WordTrace (prefixWord ++ tailWord_3442058) baseStart_3442058 baseEnd_3442058 := by
    simpa [prefixWord, tailWord_3442058, baseEnd_3442058] using wordTrace_append hprefix tailTrace_3442058
  have hstable : (prefixWord ++ tailWord_3442058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442058).length < 2 ^ (prefixWord ++ tailWord_3442058).sum := by decide
  have hdescent : baseEnd_3442058 < baseStart_3442058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442082 : List Nat := [3, 3, 1, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_3442082 : Nat := 118140960795 + 3442082 * 2 ^ 59
def prefixEnd_3442082 : Nat := 4983230072969 + 3 ^ 40 * 3442082 * 2
def baseEnd_3442082 : Nat := 1767442518189307072045159

theorem tailTrace_3442082 : CollatzResearch.WordTrace tailWord_3442082 prefixEnd_3442082 1767442518189307072045159 := by
  unfold tailWord_3442082
  simp only [CollatzResearch.WordTrace]
  refine ⟨31385761078983062412180125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83695362877288166432480333 31385761078983062412180125)
  ·
    refine ⟨11769660404618648404567547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31385761078983062412180125 11769660404618648404567547)
    ·
      refine ⟨17654490606927972606851321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11769660404618648404567547 17654490606927972606851321)
      ·
        refine ⟨13240867955195979455138491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17654490606927972606851321 13240867955195979455138491)
        ·
          refine ⟨19861301932793969182707737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13240867955195979455138491 19861301932793969182707737)
          ·
            refine ⟨14895976449595476887030803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19861301932793969182707737 14895976449595476887030803)
            ·
              refine ⟨22343964674393215330546205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14895976449595476887030803 22343964674393215330546205)
              ·
                refine ⟨8378986752897455748954827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22343964674393215330546205 8378986752897455748954827)
                ·
                  refine ⟨12568480129346183623432241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8378986752897455748954827 12568480129346183623432241)
                  ·
                    refine ⟨9426360097009637717574181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12568480129346183623432241 9426360097009637717574181)
                    ·
                      refine ⟨1767442518189307072045159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9426360097009637717574181 1767442518189307072045159)
                      ·
                        rfl

theorem cell23_3442082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_3442082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442082 prefixEnd_3442082 := by exact prefixLift 3442082
  have htrace : WordTrace (prefixWord ++ tailWord_3442082) baseStart_3442082 baseEnd_3442082 := by
    simpa [prefixWord, tailWord_3442082, baseEnd_3442082] using wordTrace_append hprefix tailTrace_3442082
  have hstable : (prefixWord ++ tailWord_3442082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442082).length < 2 ^ (prefixWord ++ tailWord_3442082).sum := by decide
  have hdescent : baseEnd_3442082 < baseStart_3442082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442155 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 4]
def baseStart_3442155 : Nat := 118140960795 + 3442155 * 2 ^ 59
def prefixEnd_3442155 : Nat := 4983230072969 + 3 ^ 40 * 3442155 * 2
def baseEnd_3442155 : Nat := 1767480002277085286432323

theorem tailTrace_3442155 : CollatzResearch.WordTrace tailWord_3442155 prefixEnd_3442155 1767480002277085286432323 := by
  unfold tailWord_3442155
  simp only [CollatzResearch.WordTrace]
  refine ⟨125545706844667783116127919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83697137896445188744085279 125545706844667783116127919)
  ·
    refine ⟨188318560267001674674191879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125545706844667783116127919 188318560267001674674191879)
    ·
      refine ⟨282477840400502512011287819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188318560267001674674191879 282477840400502512011287819)
      ·
        refine ⟨423716760600753768016931729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282477840400502512011287819 423716760600753768016931729)
        ·
          refine ⟨317787570450565326012698797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423716760600753768016931729 317787570450565326012698797)
          ·
            refine ⟨119170338918961997254762049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317787570450565326012698797 119170338918961997254762049)
            ·
              refine ⟨89377754189221497941071537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119170338918961997254762049 89377754189221497941071537)
              ·
                refine ⟨67033315641916123455803653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89377754189221497941071537 67033315641916123455803653)
                ·
                  refine ⟨12568746682859273147963185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67033315641916123455803653 12568746682859273147963185)
                  ·
                    refine ⟨9426560012144454860972389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12568746682859273147963185 9426560012144454860972389)
                    ·
                      refine ⟨1767480002277085286432323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9426560012144454860972389 1767480002277085286432323)
                      ·
                        rfl

theorem cell23_3442155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 4].length) (baseStart_3442155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442155 prefixEnd_3442155 := by exact prefixLift 3442155
  have htrace : WordTrace (prefixWord ++ tailWord_3442155) baseStart_3442155 baseEnd_3442155 := by
    simpa [prefixWord, tailWord_3442155, baseEnd_3442155] using wordTrace_append hprefix tailTrace_3442155
  have hstable : (prefixWord ++ tailWord_3442155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442155).length < 2 ^ (prefixWord ++ tailWord_3442155).sum := by decide
  have hdescent : baseEnd_3442155 < baseStart_3442155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442159 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 4, 2, 2]
def baseStart_3442159 : Nat := 118140960795 + 3442159 * 2 ^ 59
def prefixEnd_3442159 : Nat := 4983230072969 + 3 ^ 40 * 3442159 * 2
def baseEnd_3442159 : Nat := 1767482056199703270782305

theorem tailTrace_3442159 : CollatzResearch.WordTrace tailWord_3442159 prefixEnd_3442159 1767482056199703270782305 := by
  unfold tailWord_3442159
  simp only [CollatzResearch.WordTrace]
  refine ⟨125545852736653291799273531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83697235157768861199515687 125545852736653291799273531)
  ·
    refine ⟨188318779104979937698910297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125545852736653291799273531 188318779104979937698910297)
    ·
      refine ⟨141239084328734953274182723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188318779104979937698910297 141239084328734953274182723)
      ·
        refine ⟨211858626493102429911274085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141239084328734953274182723 211858626493102429911274085)
        ·
          refine ⟨39723492467456705608363891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211858626493102429911274085 39723492467456705608363891)
          ·
            refine ⟨59585238701185058412545837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39723492467456705608363891 59585238701185058412545837)
            ·
              refine ⟨22344464512944396904704689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59585238701185058412545837 22344464512944396904704689)
              ·
                refine ⟨16758348384708297678528517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22344464512944396904704689 16758348384708297678528517)
                ·
                  refine ⟨3142190322132805814724097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16758348384708297678528517 3142190322132805814724097)
                  ·
                    refine ⟨2356642741599604361043073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3142190322132805814724097 2356642741599604361043073)
                    ·
                      refine ⟨1767482056199703270782305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2356642741599604361043073 1767482056199703270782305)
                      ·
                        rfl

theorem cell23_3442159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 2, 2].length) (baseStart_3442159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3442159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3442159 prefixEnd_3442159 := by exact prefixLift 3442159
  have htrace : WordTrace (prefixWord ++ tailWord_3442159) baseStart_3442159 baseEnd_3442159 := by
    simpa [prefixWord, tailWord_3442159, baseEnd_3442159] using wordTrace_append hprefix tailTrace_3442159
  have hstable : (prefixWord ++ tailWord_3442159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442159).length < 2 ^ (prefixWord ++ tailWord_3442159).sum := by decide
  have hdescent : baseEnd_3442159 < baseStart_3442159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
