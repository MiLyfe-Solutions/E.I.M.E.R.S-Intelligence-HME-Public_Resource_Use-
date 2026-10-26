import V185TrunkScan23Chunk0502

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2975165 : List Nat := [1, 4, 1, 2, 2, 1, 4, 8]
def baseStart_2975165 : Nat := 118140960795 + 2975165 * 2 ^ 59
def prefixEnd_2975165 : Nat := 4983230072969 + 3 ^ 40 * 2975165 * 2
def baseEnd_2975165 : Nat := 56581098941998421739073

theorem tailTrace_2975165 : CollatzResearch.WordTrace tailWord_2975165 prefixEnd_2975165 56581098941998421739073 := by
  unfold tailWord_2975165
  simp only [CollatzResearch.WordTrace]
  refine ⟨108513182266492797573790949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72342121510995198382527299 108513182266492797573790949)
  ·
    refine ⟨20346221674967399545085803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108513182266492797573790949 20346221674967399545085803)
    ·
      refine ⟨30519332512451099317628705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20346221674967399545085803 30519332512451099317628705)
      ·
        refine ⟨22889499384338324488221529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30519332512451099317628705 22889499384338324488221529)
        ·
          refine ⟨17167124538253743366166147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22889499384338324488221529 17167124538253743366166147)
          ·
            refine ⟨25750686807380615049249221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17167124538253743366166147 25750686807380615049249221)
            ·
              refine ⟨4828253776383865321734229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25750686807380615049249221 4828253776383865321734229)
              ·
                refine ⟨56581098941998421739073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4828253776383865321734229 56581098941998421739073)
                ·
                  rfl

theorem cell23_2975165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 8].length) (baseStart_2975165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975165 prefixEnd_2975165 := by exact prefixLift 2975165
  have htrace : WordTrace (prefixWord ++ tailWord_2975165) baseStart_2975165 baseEnd_2975165 := by
    simpa [prefixWord, tailWord_2975165, baseEnd_2975165] using wordTrace_append hprefix tailTrace_2975165
  have hstable : (prefixWord ++ tailWord_2975165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975165).length < 2 ^ (prefixWord ++ tailWord_2975165).sum := by decide
  have hdescent : baseEnd_2975165 < baseStart_2975165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975172 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_2975172 : Nat := 118140960795 + 2975172 * 2 ^ 59
def prefixEnd_2975172 : Nat := 4983230072969 + 3 ^ 40 * 2975172 * 2
def baseEnd_2975172 : Nat := 1527693265798538859567439

theorem tailTrace_2975172 : CollatzResearch.WordTrace tailWord_2975172 prefixEnd_2975172 1527693265798538859567439 := by
  unfold tailWord_2975172
  simp only [CollatzResearch.WordTrace]
  refine ⟨54256718788733718884647885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72342291718311625179530513 54256718788733718884647885)
  ·
    refine ⟨20346269545775144581742957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54256718788733718884647885 20346269545775144581742957)
    ·
      refine ⟨7629851079665679218153609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20346269545775144581742957 7629851079665679218153609)
      ·
        refine ⟨5722388309749259413615207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7629851079665679218153609 5722388309749259413615207)
        ·
          refine ⟨8583582464623889120422811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5722388309749259413615207 8583582464623889120422811)
          ·
            refine ⟨12875373696935833680634217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8583582464623889120422811 12875373696935833680634217)
            ·
              refine ⟨9656530272701875260475663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12875373696935833680634217 9656530272701875260475663)
              ·
                refine ⟨14484795409052812890713495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9656530272701875260475663 14484795409052812890713495)
                ·
                  refine ⟨21727193113579219336070243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14484795409052812890713495 21727193113579219336070243)
                  ·
                    refine ⟨32590789670368829004105365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21727193113579219336070243 32590789670368829004105365)
                    ·
                      refine ⟨1527693265798538859567439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32590789670368829004105365 1527693265798538859567439)
                      ·
                        rfl

theorem cell23_2975172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_2975172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975172 prefixEnd_2975172 := by exact prefixLift 2975172
  have htrace : WordTrace (prefixWord ++ tailWord_2975172) baseStart_2975172 baseEnd_2975172 := by
    simpa [prefixWord, tailWord_2975172, baseEnd_2975172] using wordTrace_append hprefix tailTrace_2975172
  have hstable : (prefixWord ++ tailWord_2975172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975172).length < 2 ^ (prefixWord ++ tailWord_2975172).sum := by decide
  have hdescent : baseEnd_2975172 < baseStart_2975172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975192 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 6, 1, 3]
def baseStart_2975192 : Nat := 118140960795 + 2975192 * 2 ^ 59
def prefixEnd_2975192 : Nat := 4983230072969 + 3 ^ 40 * 2975192 * 2
def baseEnd_2975192 : Nat := 1527703535411628781317347

theorem tailTrace_2975192 : CollatzResearch.WordTrace tailWord_2975192 prefixEnd_2975192 1527703535411628781317347 := by
  unfold tailWord_2975192
  simp only [CollatzResearch.WordTrace]
  refine ⟨54257083518697490592511915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72342778024929987456682553 54257083518697490592511915)
  ·
    refine ⟨81385625278046235888767873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54257083518697490592511915 81385625278046235888767873)
    ·
      refine ⟨61039218958534676916575905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81385625278046235888767873 61039218958534676916575905)
      ·
        refine ⟨45779414218901007687431929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61039218958534676916575905 45779414218901007687431929)
        ·
          refine ⟨34334560664175755765573947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45779414218901007687431929 34334560664175755765573947)
          ·
            refine ⟨51501840996263633648360921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34334560664175755765573947 51501840996263633648360921)
            ·
              refine ⟨38626380747197725236270691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51501840996263633648360921 38626380747197725236270691)
              ·
                refine ⟨57939571120796587854406037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38626380747197725236270691 57939571120796587854406037)
                ·
                  refine ⟨2715917396287340055675283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57939571120796587854406037 2715917396287340055675283)
                  ·
                    refine ⟨4073876094431010083512925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2715917396287340055675283 4073876094431010083512925)
                    ·
                      refine ⟨1527703535411628781317347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4073876094431010083512925 1527703535411628781317347)
                      ·
                        rfl

theorem cell23_2975192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_2975192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975192 prefixEnd_2975192 := by exact prefixLift 2975192
  have htrace : WordTrace (prefixWord ++ tailWord_2975192) baseStart_2975192 baseEnd_2975192 := by
    simpa [prefixWord, tailWord_2975192, baseEnd_2975192] using wordTrace_append hprefix tailTrace_2975192
  have hstable : (prefixWord ++ tailWord_2975192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975192).length < 2 ^ (prefixWord ++ tailWord_2975192).sum := by decide
  have hdescent : baseEnd_2975192 < baseStart_2975192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975215 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 4]
def baseStart_2975215 : Nat := 118140960795 + 2975215 * 2 ^ 59
def prefixEnd_2975215 : Nat := 4983230072969 + 3 ^ 40 * 2975215 * 2
def baseEnd_2975215 : Nat := 1527715345466682191329741

theorem tailTrace_2975215 : CollatzResearch.WordTrace tailWord_2975215 prefixEnd_2975215 1527715345466682191329741 := by
  unfold tailWord_2975215
  simp only [CollatzResearch.WordTrace]
  refine ⟨108515005916311656113111099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72343337277541104075407399 108515005916311656113111099)
  ·
    refine ⟨162772508874467484169666649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108515005916311656113111099 162772508874467484169666649)
    ·
      refine ⟨122079381655850613127249987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162772508874467484169666649 122079381655850613127249987)
      ·
        refine ⟨183119072483775919690874981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122079381655850613127249987 183119072483775919690874981)
        ·
          refine ⟨34334826090707984942039059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183119072483775919690874981 34334826090707984942039059)
          ·
            refine ⟨51502239136061977413058589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34334826090707984942039059 51502239136061977413058589)
            ·
              refine ⟨19313339676023241529896971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51502239136061977413058589 19313339676023241529896971)
              ·
                refine ⟨28970009514034862294845457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19313339676023241529896971 28970009514034862294845457)
                ·
                  refine ⟨21727507135526146721134093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28970009514034862294845457 21727507135526146721134093)
                  ·
                    refine ⟨8147815175822305020425285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21727507135526146721134093 8147815175822305020425285)
                    ·
                      refine ⟨1527715345466682191329741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8147815175822305020425285 1527715345466682191329741)
                      ·
                        rfl

theorem cell23_2975215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_2975215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975215 prefixEnd_2975215 := by exact prefixLift 2975215
  have htrace : WordTrace (prefixWord ++ tailWord_2975215) baseStart_2975215 baseEnd_2975215 := by
    simpa [prefixWord, tailWord_2975215, baseEnd_2975215] using wordTrace_append hprefix tailTrace_2975215
  have hstable : (prefixWord ++ tailWord_2975215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975215).length < 2 ^ (prefixWord ++ tailWord_2975215).sum := by decide
  have hdescent : baseEnd_2975215 < baseStart_2975215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975235 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 5]
def baseStart_2975235 : Nat := 118140960795 + 2975235 * 2 ^ 59
def prefixEnd_2975235 : Nat := 4983230072969 + 3 ^ 40 * 2975235 * 2
def baseEnd_2975235 : Nat := 1527725615079772113079649

theorem tailTrace_2975235 : CollatzResearch.WordTrace tailWord_2975235 prefixEnd_2975235 1527725615079772113079649 := by
  unfold tailWord_2975235
  simp only [CollatzResearch.WordTrace]
  refine ⟨108515735376239199528839159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72343823584159466352559439 108515735376239199528839159)
  ·
    refine ⟨162773603064358799293258739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108515735376239199528839159 162773603064358799293258739)
    ·
      refine ⟨244160404596538198939888109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162773603064358799293258739 244160404596538198939888109)
      ·
        refine ⟨91560151723701824602458041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244160404596538198939888109 91560151723701824602458041)
        ·
          refine ⟨68670113792776368451843531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91560151723701824602458041 68670113792776368451843531)
          ·
            refine ⟨103005170689164552677765297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68670113792776368451843531 103005170689164552677765297)
            ·
              refine ⟨77253878016873414508323973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103005170689164552677765297 77253878016873414508323973)
              ·
                refine ⟨14485102128163765220310745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77253878016873414508323973 14485102128163765220310745)
                ·
                  refine ⟨10863826596122823915233059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14485102128163765220310745 10863826596122823915233059)
                  ·
                    refine ⟨16295739894184235872849589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10863826596122823915233059 16295739894184235872849589)
                    ·
                      refine ⟨1527725615079772113079649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16295739894184235872849589 1527725615079772113079649)
                      ·
                        rfl

theorem cell23_2975235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_2975235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975235 prefixEnd_2975235 := by exact prefixLift 2975235
  have htrace : WordTrace (prefixWord ++ tailWord_2975235) baseStart_2975235 baseEnd_2975235 := by
    simpa [prefixWord, tailWord_2975235, baseEnd_2975235] using wordTrace_append hprefix tailTrace_2975235
  have hstable : (prefixWord ++ tailWord_2975235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975235).length < 2 ^ (prefixWord ++ tailWord_2975235).sum := by decide
  have hdescent : baseEnd_2975235 < baseStart_2975235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975249 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 4, 2, 2]
def baseStart_2975249 : Nat := 118140960795 + 2975249 * 2 ^ 59
def prefixEnd_2975249 : Nat := 4983230072969 + 3 ^ 40 * 2975249 * 2
def baseEnd_2975249 : Nat := 1527732803808935058304585

theorem tailTrace_2975249 : CollatzResearch.WordTrace tailWord_2975249 prefixEnd_2975249 1527732803808935058304585 := by
  unfold tailWord_2975249
  simp only [CollatzResearch.WordTrace]
  refine ⟨108516245998188479919848801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72344163998792319946565867 108516245998188479919848801)
  ·
    refine ⟨81387184498641359939886601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108516245998188479919848801 81387184498641359939886601)
    ·
      refine ⟨61040388373981019954914951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81387184498641359939886601 61040388373981019954914951)
      ·
        refine ⟨91560582560971529932372427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61040388373981019954914951 91560582560971529932372427)
        ·
          refine ⟨137340873841457294898558641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91560582560971529932372427 137340873841457294898558641)
          ·
            refine ⟨103005655381092971173918981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137340873841457294898558641 103005655381092971173918981)
            ·
              refine ⟨19313560383954932095109809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103005655381092971173918981 19313560383954932095109809)
              ·
                refine ⟨14485170287966199071332357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19313560383954932095109809 14485170287966199071332357)
                ·
                  refine ⟨2715969428993662325874817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14485170287966199071332357 2715969428993662325874817)
                  ·
                    refine ⟨2036977071745246744406113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2715969428993662325874817 2036977071745246744406113)
                    ·
                      refine ⟨1527732803808935058304585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2036977071745246744406113 1527732803808935058304585)
                      ·
                        rfl

theorem cell23_2975249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 2, 2].length) (baseStart_2975249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975249 prefixEnd_2975249 := by exact prefixLift 2975249
  have htrace : WordTrace (prefixWord ++ tailWord_2975249) baseStart_2975249 baseEnd_2975249 := by
    simpa [prefixWord, tailWord_2975249, baseEnd_2975249] using wordTrace_append hprefix tailTrace_2975249
  have hstable : (prefixWord ++ tailWord_2975249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975249).length < 2 ^ (prefixWord ++ tailWord_2975249).sum := by decide
  have hdescent : baseEnd_2975249 < baseStart_2975249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975253 : List Nat := [1, 3, 2, 1, 3, 4, 2, 1, 1, 3, 2]
def baseStart_2975253 : Nat := 118140960795 + 2975253 * 2 ^ 59
def prefixEnd_2975253 : Nat := 4983230072969 + 3 ^ 40 * 2975253 * 2
def baseEnd_2975253 : Nat := 1527734857731553042654567

theorem tailTrace_2975253 : CollatzResearch.WordTrace tailWord_2975253 prefixEnd_2975253 1527734857731553042654567 := by
  unfold tailWord_2975253
  simp only [CollatzResearch.WordTrace]
  refine ⟨108516391890173988602994413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72344261260115992401996275 108516391890173988602994413)
  ·
    refine ⟨40693646958815245726122905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108516391890173988602994413 40693646958815245726122905)
    ·
      refine ⟨30520235219111434294592179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40693646958815245726122905 30520235219111434294592179)
      ·
        refine ⟨45780352828667151441888269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30520235219111434294592179 45780352828667151441888269)
        ·
          refine ⟨17167632310750181790708101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45780352828667151441888269 17167632310750181790708101)
          ·
            refine ⟨3218931058265659085757769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17167632310750181790708101 3218931058265659085757769)
            ·
              refine ⟨2414198293699244314318327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3218931058265659085757769 2414198293699244314318327)
              ·
                refine ⟨3621297440548866471477491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2414198293699244314318327 3621297440548866471477491)
                ·
                  refine ⟨5431946160823299707216237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3621297440548866471477491 5431946160823299707216237)
                  ·
                    refine ⟨2036979810308737390206089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5431946160823299707216237 2036979810308737390206089)
                    ·
                      refine ⟨1527734857731553042654567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2036979810308737390206089 1527734857731553042654567)
                      ·
                        rfl

theorem cell23_2975253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_2975253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975253 prefixEnd_2975253 := by exact prefixLift 2975253
  have htrace : WordTrace (prefixWord ++ tailWord_2975253) baseStart_2975253 baseEnd_2975253 := by
    simpa [prefixWord, tailWord_2975253, baseEnd_2975253] using wordTrace_append hprefix tailTrace_2975253
  have hstable : (prefixWord ++ tailWord_2975253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975253).length < 2 ^ (prefixWord ++ tailWord_2975253).sum := by decide
  have hdescent : baseEnd_2975253 < baseStart_2975253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975283 : List Nat := [1, 1, 1, 2, 4, 4, 3, 1, 2, 2, 2]
def baseStart_2975283 : Nat := 118140960795 + 2975283 * 2 ^ 59
def prefixEnd_2975283 : Nat := 4983230072969 + 3 ^ 40 * 2975283 * 2
def baseEnd_2975283 : Nat := 1527750262151187925279429

theorem tailTrace_2975283 : CollatzResearch.WordTrace tailWord_2975283 prefixEnd_2975283 1527750262151187925279429 := by
  unfold tailWord_2975283
  simp only [CollatzResearch.WordTrace]
  refine ⟨108517486080065303726586503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72344990720043535817724335 108517486080065303726586503)
  ·
    refine ⟨162776229120097955589879755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108517486080065303726586503 162776229120097955589879755)
    ·
      refine ⟨244164343680146933384819633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162776229120097955589879755 244164343680146933384819633)
      ·
        refine ⟨183123257760110200038614725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244164343680146933384819633 183123257760110200038614725)
        ·
          refine ⟨34335610830020662507240261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183123257760110200038614725 34335610830020662507240261)
          ·
            refine ⟨6437927030628874220107549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34335610830020662507240261 6437927030628874220107549)
            ·
              refine ⟨2414222636485827832540331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6437927030628874220107549 2414222636485827832540331)
              ·
                refine ⟨3621333954728741748810497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2414222636485827832540331 3621333954728741748810497)
                ·
                  refine ⟨2716000466046556311607873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3621333954728741748810497 2716000466046556311607873)
                  ·
                    refine ⟨2037000349534917233705905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2716000466046556311607873 2037000349534917233705905)
                    ·
                      refine ⟨1527750262151187925279429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2037000349534917233705905 1527750262151187925279429)
                      ·
                        rfl

theorem cell23_2975283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 2, 2, 2].length) (baseStart_2975283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975283 prefixEnd_2975283 := by exact prefixLift 2975283
  have htrace : WordTrace (prefixWord ++ tailWord_2975283) baseStart_2975283 baseEnd_2975283 := by
    simpa [prefixWord, tailWord_2975283, baseEnd_2975283] using wordTrace_append hprefix tailTrace_2975283
  have hstable : (prefixWord ++ tailWord_2975283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975283).length < 2 ^ (prefixWord ++ tailWord_2975283).sum := by decide
  have hdescent : baseEnd_2975283 < baseStart_2975283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975383 : List Nat := [1, 1, 3, 3, 2, 2, 4, 2, 1, 4]
def baseStart_2975383 : Nat := 118140960795 + 2975383 * 2 ^ 59
def prefixEnd_2975383 : Nat := 4983230072969 + 3 ^ 40 * 2975383 * 2
def baseEnd_2975383 : Nat := 509267203405545844676323

theorem tailTrace_2975383 : CollatzResearch.WordTrace tailWord_2975383 prefixEnd_2975383 509267203405545844676323 := by
  unfold tailWord_2975383
  simp only [CollatzResearch.WordTrace]
  refine ⟨108521133379703020805226803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72347422253135347203484535 108521133379703020805226803)
  ·
    refine ⟨162781700069554531207840205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108521133379703020805226803 162781700069554531207840205)
    ·
      refine ⟨61043137526082949202940077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162781700069554531207840205 61043137526082949202940077)
      ·
        refine ⟨22891176572281105951102529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61043137526082949202940077 22891176572281105951102529)
        ·
          refine ⟨17168382429210829463326897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22891176572281105951102529 17168382429210829463326897)
          ·
            refine ⟨12876286821908122097495173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17168382429210829463326897 12876286821908122097495173)
            ·
              refine ⟨2414303779107772893280345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12876286821908122097495173 2414303779107772893280345)
              ·
                refine ⟨1810727834330829669960259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2414303779107772893280345 1810727834330829669960259)
                ·
                  refine ⟨2716091751496244504940389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1810727834330829669960259 2716091751496244504940389)
                  ·
                    refine ⟨509267203405545844676323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2716091751496244504940389 509267203405545844676323)
                    ·
                      rfl

theorem cell23_2975383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 1, 4].length) (baseStart_2975383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975383 prefixEnd_2975383 := by exact prefixLift 2975383
  have htrace : WordTrace (prefixWord ++ tailWord_2975383) baseStart_2975383 baseEnd_2975383 := by
    simpa [prefixWord, tailWord_2975383, baseEnd_2975383] using wordTrace_append hprefix tailTrace_2975383
  have hstable : (prefixWord ++ tailWord_2975383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975383).length < 2 ^ (prefixWord ++ tailWord_2975383).sum := by decide
  have hdescent : baseEnd_2975383 < baseStart_2975383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975400 : List Nat := [2, 1, 7, 1, 1, 1, 1, 2, 3, 4]
def baseStart_2975400 : Nat := 118140960795 + 2975400 * 2 ^ 59
def prefixEnd_2975400 : Nat := 4983230072969 + 3 ^ 40 * 2975400 * 2
def baseEnd_2975400 : Nat := 509270113129254655838797

theorem tailTrace_2975400 : CollatzResearch.WordTrace tailWord_2975400 prefixEnd_2975400 509270113129254655838797 := by
  unfold tailWord_2975400
  simp only [CollatzResearch.WordTrace]
  refine ⟨54260876710320716354297827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72347835613760955139063769 54260876710320716354297827)
  ·
    refine ⟨81391315065481074531446741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54260876710320716354297827 81391315065481074531446741)
    ·
      refine ⟨1907608946847212684330783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 81391315065481074531446741 1907608946847212684330783)
      ·
        refine ⟨2861413420270819026496175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1907608946847212684330783 2861413420270819026496175)
        ·
          refine ⟨4292120130406228539744263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2861413420270819026496175 4292120130406228539744263)
          ·
            refine ⟨6438180195609342809616395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4292120130406228539744263 6438180195609342809616395)
            ·
              refine ⟨9657270293414014214424593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6438180195609342809616395 9657270293414014214424593)
              ·
                refine ⟨7242952720060510660818445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9657270293414014214424593 7242952720060510660818445)
                ·
                  refine ⟨2716107270022691497806917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7242952720060510660818445 2716107270022691497806917)
                  ·
                    refine ⟨509270113129254655838797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2716107270022691497806917 509270113129254655838797)
                    ·
                      rfl

theorem cell23_2975400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_2975400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975400 prefixEnd_2975400 := by exact prefixLift 2975400
  have htrace : WordTrace (prefixWord ++ tailWord_2975400) baseStart_2975400 baseEnd_2975400 := by
    simpa [prefixWord, tailWord_2975400, baseEnd_2975400] using wordTrace_append hprefix tailTrace_2975400
  have hstable : (prefixWord ++ tailWord_2975400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975400).length < 2 ^ (prefixWord ++ tailWord_2975400).sum := by decide
  have hdescent : baseEnd_2975400 < baseStart_2975400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975423 : List Nat := [1, 1, 2, 2, 2, 3, 4, 3, 1, 1, 3]
def baseStart_2975423 : Nat := 118140960795 + 2975423 * 2 ^ 59
def prefixEnd_2975423 : Nat := 4983230072969 + 3 ^ 40 * 2975423 * 2
def baseEnd_2975423 : Nat := 1527822149442817377528785

theorem tailTrace_2975423 : CollatzResearch.WordTrace tailWord_2975423 prefixEnd_2975423 1527822149442817377528785 := by
  unfold tailWord_2975423
  simp only [CollatzResearch.WordTrace]
  refine ⟨108522592299558107636682923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72348394866372071757788615 108522592299558107636682923)
  ·
    refine ⟨162783888449337161455024385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108522592299558107636682923 162783888449337161455024385)
    ·
      refine ⟨122087916337002871091268289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162783888449337161455024385 122087916337002871091268289)
      ·
        refine ⟨91565937252752153318451217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122087916337002871091268289 91565937252752153318451217)
        ·
          refine ⟨68674452939564114988838413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91565937252752153318451217 68674452939564114988838413)
          ·
            refine ⟨25752919852336543120814405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68674452939564114988838413 25752919852336543120814405)
            ·
              refine ⟨4828672472313101835152701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25752919852336543120814405 4828672472313101835152701)
              ·
                refine ⟨1810752177117413188182263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4828672472313101835152701 1810752177117413188182263)
                ·
                  refine ⟨2716128265676119782273395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1810752177117413188182263 2716128265676119782273395)
                  ·
                    refine ⟨4074192398514179673410093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2716128265676119782273395 4074192398514179673410093)
                    ·
                      refine ⟨1527822149442817377528785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4074192398514179673410093 1527822149442817377528785)
                      ·
                        rfl

theorem cell23_2975423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 1, 1, 3].length) (baseStart_2975423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975423 prefixEnd_2975423 := by exact prefixLift 2975423
  have htrace : WordTrace (prefixWord ++ tailWord_2975423) baseStart_2975423 baseEnd_2975423 := by
    simpa [prefixWord, tailWord_2975423, baseEnd_2975423] using wordTrace_append hprefix tailTrace_2975423
  have hstable : (prefixWord ++ tailWord_2975423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975423).length < 2 ^ (prefixWord ++ tailWord_2975423).sum := by decide
  have hdescent : baseEnd_2975423 < baseStart_2975423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975429 : List Nat := [1, 3, 1, 1, 1, 1, 2, 7, 1, 1, 4]
def baseStart_2975429 : Nat := 118140960795 + 2975429 * 2 ^ 59
def prefixEnd_2975429 : Nat := 4983230072969 + 3 ^ 40 * 2975429 * 2
def baseEnd_2975429 : Nat := 1527825230326744354053757

theorem tailTrace_2975429 : CollatzResearch.WordTrace tailWord_2975429 prefixEnd_2975429 1527825230326744354053757 := by
  unfold tailWord_2975429
  simp only [CollatzResearch.WordTrace]
  refine ⟨108522811137536370661401341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72348540758357580440934227 108522811137536370661401341)
  ·
    refine ⟨40696054176576138998025503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108522811137536370661401341 40696054176576138998025503)
    ·
      refine ⟨61044081264864208497038255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40696054176576138998025503 61044081264864208497038255)
      ·
        refine ⟨91566121897296312745557383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61044081264864208497038255 91566121897296312745557383)
        ·
          refine ⟨137349182845944469118336075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91566121897296312745557383 137349182845944469118336075)
          ·
            refine ⟨206023774268916703677504113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137349182845944469118336075 206023774268916703677504113)
            ·
              refine ⟨154517830701687527758128085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206023774268916703677504113 154517830701687527758128085)
              ·
                refine ⟨3621511657070801431831127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 154517830701687527758128085 3621511657070801431831127)
                ·
                  refine ⟨5432267485606202147746691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3621511657070801431831127 5432267485606202147746691)
                  ·
                    refine ⟨8148401228409303221620037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5432267485606202147746691 8148401228409303221620037)
                    ·
                      refine ⟨1527825230326744354053757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8148401228409303221620037 1527825230326744354053757)
                      ·
                        rfl

theorem cell23_2975429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 1, 4].length) (baseStart_2975429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975429 prefixEnd_2975429 := by exact prefixLift 2975429
  have htrace : WordTrace (prefixWord ++ tailWord_2975429) baseStart_2975429 baseEnd_2975429 := by
    simpa [prefixWord, tailWord_2975429, baseEnd_2975429] using wordTrace_append hprefix tailTrace_2975429
  have hstable : (prefixWord ++ tailWord_2975429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975429).length < 2 ^ (prefixWord ++ tailWord_2975429).sum := by decide
  have hdescent : baseEnd_2975429 < baseStart_2975429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975430 : List Nat := [6, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_2975430 : Nat := 118140960795 + 2975430 * 2 ^ 59
def prefixEnd_2975430 : Nat := 4983230072969 + 3 ^ 40 * 2975430 * 2
def baseEnd_2975430 : Nat := 169758415978599872237917

theorem tailTrace_2975430 : CollatzResearch.WordTrace tailWord_2975430 prefixEnd_2975430 169758415978599872237917 := by
  unfold tailWord_2975430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3391338987829148369755867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72348565073688498554791829 3391338987829148369755867)
  ·
    refine ⟨5087008481743722554633801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3391338987829148369755867 5087008481743722554633801)
    ·
      refine ⟨3815256361307791915975351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5087008481743722554633801 3815256361307791915975351)
      ·
        refine ⟨5722884541961687873963027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3815256361307791915975351 5722884541961687873963027)
        ·
          refine ⟨8584326812942531810944541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5722884541961687873963027 8584326812942531810944541)
          ·
            refine ⟨3219122554853449429104203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8584326812942531810944541 3219122554853449429104203)
            ·
              refine ⟨4828683832280174143656305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3219122554853449429104203 4828683832280174143656305)
              ·
                refine ⟨3621512874210130607742229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4828683832280174143656305 3621512874210130607742229)
                ·
                  refine ⟨169758415978599872237917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3621512874210130607742229 169758415978599872237917)
                  ·
                    rfl

theorem cell23_2975430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_2975430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975430 prefixEnd_2975430 := by exact prefixLift 2975430
  have htrace : WordTrace (prefixWord ++ tailWord_2975430) baseStart_2975430 baseEnd_2975430 := by
    simpa [prefixWord, tailWord_2975430, baseEnd_2975430] using wordTrace_append hprefix tailTrace_2975430
  have hstable : (prefixWord ++ tailWord_2975430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975430).length < 2 ^ (prefixWord ++ tailWord_2975430).sum := by decide
  have hdescent : baseEnd_2975430 < baseStart_2975430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975449 : List Nat := [1, 2, 1, 2, 3, 4, 1, 2, 1, 1, 5]
def baseStart_2975449 : Nat := 118140960795 + 2975449 * 2 ^ 59
def prefixEnd_2975449 : Nat := 4983230072969 + 3 ^ 40 * 2975449 * 2
def baseEnd_2975449 : Nat := 1527835499939834275803665

theorem tailTrace_2975449 : CollatzResearch.WordTrace tailWord_2975449 prefixEnd_2975449 1527835499939834275803665 := by
  unfold tailWord_2975449
  simp only [CollatzResearch.WordTrace]
  refine ⟨108523540597463914077129401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72349027064975942718086267 108523540597463914077129401)
  ·
    refine ⟨81392655448097935557847051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108523540597463914077129401 81392655448097935557847051)
    ·
      refine ⟨122088983172146903336770577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81392655448097935557847051 122088983172146903336770577)
      ·
        refine ⟨91566737379110177502577933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122088983172146903336770577 91566737379110177502577933)
        ·
          refine ⟨34337526517166316563466725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91566737379110177502577933 34337526517166316563466725)
          ·
            refine ⟨6438286221968684355650011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34337526517166316563466725 6438286221968684355650011)
            ·
              refine ⟨9657429332953026533475017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6438286221968684355650011 9657429332953026533475017)
              ·
                refine ⟨7243071999714769900106263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9657429332953026533475017 7243071999714769900106263)
                ·
                  refine ⟨10864607999572154850159395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7243071999714769900106263 10864607999572154850159395)
                  ·
                    refine ⟨16296911999358232275239093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10864607999572154850159395 16296911999358232275239093)
                    ·
                      refine ⟨1527835499939834275803665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16296911999358232275239093 1527835499939834275803665)
                      ·
                        rfl

theorem cell23_2975449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_2975449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975449 prefixEnd_2975449 := by exact prefixLift 2975449
  have htrace : WordTrace (prefixWord ++ tailWord_2975449) baseStart_2975449 baseEnd_2975449 := by
    simpa [prefixWord, tailWord_2975449, baseEnd_2975449] using wordTrace_append hprefix tailTrace_2975449
  have hstable : (prefixWord ++ tailWord_2975449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975449).length < 2 ^ (prefixWord ++ tailWord_2975449).sum := by decide
  have hdescent : baseEnd_2975449 < baseStart_2975449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975466 : List Nat := [3, 1, 3, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_2975466 : Nat := 118140960795 + 2975466 * 2 ^ 59
def prefixEnd_2975466 : Nat := 4983230072969 + 3 ^ 40 * 2975466 * 2
def baseEnd_2975466 : Nat := 1527844229110960709291087

theorem tailTrace_2975466 : CollatzResearch.WordTrace tailWord_2975466 prefixEnd_2975466 1527844229110960709291087 := by
  unfold tailWord_2975466
  simp only [CollatzResearch.WordTrace]
  refine ⟨27131040159600581495124563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72349440425601550653665501 27131040159600581495124563)
  ·
    refine ⟨40696560239400872242686845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27131040159600581495124563 40696560239400872242686845)
    ·
      refine ⟨15261210089775327091007567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40696560239400872242686845 15261210089775327091007567)
      ·
        refine ⟨22891815134662990636511351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15261210089775327091007567 22891815134662990636511351)
        ·
          refine ⟨34337722701994485954767027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22891815134662990636511351 34337722701994485954767027)
          ·
            refine ⟨51506584052991728932150541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34337722701994485954767027 51506584052991728932150541)
            ·
              refine ⟨19314969019871898349556453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51506584052991728932150541 19314969019871898349556453)
              ·
                refine ⟨3621556691225980940541835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19314969019871898349556453 3621556691225980940541835)
                ·
                  refine ⟨5432335036838971410812753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3621556691225980940541835 5432335036838971410812753)
                  ·
                    refine ⟨4074251277629228558109565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5432335036838971410812753 4074251277629228558109565)
                    ·
                      refine ⟨1527844229110960709291087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4074251277629228558109565 1527844229110960709291087)
                      ·
                        rfl

theorem cell23_2975466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_2975466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975466 prefixEnd_2975466 := by exact prefixLift 2975466
  have htrace : WordTrace (prefixWord ++ tailWord_2975466) baseStart_2975466 baseEnd_2975466 := by
    simpa [prefixWord, tailWord_2975466, baseEnd_2975466] using wordTrace_append hprefix tailTrace_2975466
  have hstable : (prefixWord ++ tailWord_2975466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975466).length < 2 ^ (prefixWord ++ tailWord_2975466).sum := by decide
  have hdescent : baseEnd_2975466 < baseStart_2975466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975469 : List Nat := [1, 5, 1, 2, 1, 3, 1, 9]
def baseStart_2975469 : Nat := 118140960795 + 2975469 * 2 ^ 59
def prefixEnd_2975469 : Nat := 4983230072969 + 3 ^ 40 * 2975469 * 2
def baseEnd_2975469 : Nat := 56586880353812007316799

theorem tailTrace_2975469 : CollatzResearch.WordTrace tailWord_2975469 prefixEnd_2975469 56586880353812007316799 := by
  unfold tailWord_2975469
  simp only [CollatzResearch.WordTrace]
  refine ⟨108524270057391457492857461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72349513371594304995238307 108524270057391457492857461)
  ·
    refine ⟨10174150317880449139955387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108524270057391457492857461 10174150317880449139955387)
    ·
      refine ⟨15261225476820673709933081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10174150317880449139955387 15261225476820673709933081)
      ·
        refine ⟨11445919107615505282449811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15261225476820673709933081 11445919107615505282449811)
        ·
          refine ⟨17168878661423257923674717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11445919107615505282449811 17168878661423257923674717)
          ·
            refine ⟨6438329498033721721378019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17168878661423257923674717 6438329498033721721378019)
            ·
              refine ⟨9657494247050582582067029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6438329498033721721378019 9657494247050582582067029)
              ·
                refine ⟨56586880353812007316799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9657494247050582582067029 56586880353812007316799)
                ·
                  rfl

theorem cell23_2975469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 9].length) (baseStart_2975469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975469 prefixEnd_2975469 := by exact prefixLift 2975469
  have htrace : WordTrace (prefixWord ++ tailWord_2975469) baseStart_2975469 baseEnd_2975469 := by
    simpa [prefixWord, tailWord_2975469, baseEnd_2975469] using wordTrace_append hprefix tailTrace_2975469
  have hstable : (prefixWord ++ tailWord_2975469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975469).length < 2 ^ (prefixWord ++ tailWord_2975469).sum := by decide
  have hdescent : baseEnd_2975469 < baseStart_2975469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975479 : List Nat := [1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 3]
def baseStart_2975479 : Nat := 118140960795 + 2975479 * 2 ^ 59
def prefixEnd_2975479 : Nat := 4983230072969 + 3 ^ 40 * 2975479 * 2
def baseEnd_2975479 : Nat := 1527850904359469158428527

theorem tailTrace_2975479 : CollatzResearch.WordTrace tailWord_2975479 prefixEnd_2975479 1527850904359469158428527 := by
  unfold tailWord_2975479
  simp only [CollatzResearch.WordTrace]
  refine ⟨108524634787355229200721491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72349756524903486133814327 108524634787355229200721491)
  ·
    refine ⟨162786952181032843801082237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108524634787355229200721491 162786952181032843801082237)
    ·
      refine ⟨61045107067887316425405839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162786952181032843801082237 61045107067887316425405839)
      ·
        refine ⟨91567660601830974638108759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61045107067887316425405839 91567660601830974638108759)
        ·
          refine ⟨137351490902746461957163139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91567660601830974638108759 137351490902746461957163139)
          ·
            refine ⟨206027236354119692935744709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137351490902746461957163139 206027236354119692935744709)
            ·
              refine ⟨38630106816397442425452133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206027236354119692935744709 38630106816397442425452133)
              ·
                refine ⟨7243145028074520454772275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38630106816397442425452133 7243145028074520454772275)
                ·
                  refine ⟨10864717542111780682158413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7243145028074520454772275 10864717542111780682158413)
                  ·
                    refine ⟨4074269078291917755809405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10864717542111780682158413 4074269078291917755809405)
                    ·
                      refine ⟨1527850904359469158428527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4074269078291917755809405 1527850904359469158428527)
                      ·
                        rfl

theorem cell23_2975479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_2975479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975479 prefixEnd_2975479 := by exact prefixLift 2975479
  have htrace : WordTrace (prefixWord ++ tailWord_2975479) baseStart_2975479 baseEnd_2975479 := by
    simpa [prefixWord, tailWord_2975479, baseEnd_2975479] using wordTrace_append hprefix tailTrace_2975479
  have hstable : (prefixWord ++ tailWord_2975479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975479).length < 2 ^ (prefixWord ++ tailWord_2975479).sum := by decide
  have hdescent : baseEnd_2975479 < baseStart_2975479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975482 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 1, 9]
def baseStart_2975482 : Nat := 118140960795 + 2975482 * 2 ^ 59
def prefixEnd_2975482 : Nat := 4983230072969 + 3 ^ 40 * 2975482 * 2
def baseEnd_2975482 : Nat := 509284148267144215563671

theorem tailTrace_2975482 : CollatzResearch.WordTrace tailWord_2975482 prefixEnd_2975482 509284148267144215563671 := by
  unfold tailWord_2975482
  simp only [CollatzResearch.WordTrace]
  refine ⟨27131186051586090178270175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72349829470896240475387133 27131186051586090178270175)
  ·
    refine ⟨40696779077379135267405263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27131186051586090178270175 40696779077379135267405263)
    ·
      refine ⟨61045168616068702901107895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40696779077379135267405263 61045168616068702901107895)
      ·
        refine ⟨91567752924103054351661843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61045168616068702901107895 91567752924103054351661843)
        ·
          refine ⟨137351629386154581527492765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91567752924103054351661843 137351629386154581527492765)
          ·
            refine ⟨51506861019807968072809787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137351629386154581527492765 51506861019807968072809787)
            ·
              refine ⟨77260291529711952109214681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51506861019807968072809787 77260291529711952109214681)
              ·
                refine ⟨57945218647283964081911011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77260291529711952109214681 57945218647283964081911011)
                ·
                  refine ⟨86917827970925946122866517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57945218647283964081911011 86917827970925946122866517)
                  ·
                    refine ⟨509284148267144215563671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 86917827970925946122866517 509284148267144215563671)
                    ·
                      rfl

theorem cell23_2975482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_2975482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975482 prefixEnd_2975482 := by exact prefixLift 2975482
  have htrace : WordTrace (prefixWord ++ tailWord_2975482) baseStart_2975482 baseEnd_2975482 := by
    simpa [prefixWord, tailWord_2975482, baseEnd_2975482] using wordTrace_append hprefix tailTrace_2975482
  have hstable : (prefixWord ++ tailWord_2975482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975482).length < 2 ^ (prefixWord ++ tailWord_2975482).sum := by decide
  have hdescent : baseEnd_2975482 < baseStart_2975482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975486 : List Nat := [4, 2, 2, 1, 3, 2, 9]
def baseStart_2975486 : Nat := 118140960795 + 2975486 * 2 ^ 59
def prefixEnd_2975486 : Nat := 4983230072969 + 3 ^ 40 * 2975486 * 2
def baseEnd_2975486 : Nat := 18862401218815439889395

theorem tailTrace_2975486 : CollatzResearch.WordTrace tailWord_2975486 prefixEnd_2975486 18862401218815439889395 := by
  unfold tailWord_2975486
  simp only [CollatzResearch.WordTrace]
  refine ⟨13565611262291233674528289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72349926732219912930817541 13565611262291233674528289)
  ·
    refine ⟨10174208446718425255896217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13565611262291233674528289 10174208446718425255896217)
    ·
      refine ⟨7630656335038818941922163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10174208446718425255896217 7630656335038818941922163)
      ·
        refine ⟨11445984502558228412883245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7630656335038818941922163 11445984502558228412883245)
        ·
          refine ⟨4292244188459335654831217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11445984502558228412883245 4292244188459335654831217)
          ·
            refine ⟨3219183141344501741123413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4292244188459335654831217 3219183141344501741123413)
            ·
              refine ⟨18862401218815439889395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3219183141344501741123413 18862401218815439889395)
              ·
                rfl

theorem cell23_2975486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 9].length) (baseStart_2975486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975486 prefixEnd_2975486 := by exact prefixLift 2975486
  have htrace : WordTrace (prefixWord ++ tailWord_2975486) baseStart_2975486 baseEnd_2975486 := by
    simpa [prefixWord, tailWord_2975486, baseEnd_2975486] using wordTrace_append hprefix tailTrace_2975486
  have hstable : (prefixWord ++ tailWord_2975486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975486).length < 2 ^ (prefixWord ++ tailWord_2975486).sum := by decide
  have hdescent : baseEnd_2975486 < baseStart_2975486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975496 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 4, 1, 3]
def baseStart_2975496 : Nat := 118140960795 + 2975496 * 2 ^ 59
def prefixEnd_2975496 : Nat := 4983230072969 + 3 ^ 40 * 2975496 * 2
def baseEnd_2975496 : Nat := 1527859633530595591915949

theorem tailTrace_2975496 : CollatzResearch.WordTrace tailWord_2975496 prefixEnd_2975496 1527859633530595591915949 := by
  unfold tailWord_2975496
  simp only [CollatzResearch.WordTrace]
  refine ⟨54262627414146820552045171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72350169885529094069393561 54262627414146820552045171)
  ·
    refine ⟨81393941121220230828067757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54262627414146820552045171 81393941121220230828067757)
    ·
      refine ⟨30522727920457586560525409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81393941121220230828067757 30522727920457586560525409)
      ·
        refine ⟨22892045940343189920394057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30522727920457586560525409 22892045940343189920394057)
        ·
          refine ⟨17169034455257392440295543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22892045940343189920394057 17169034455257392440295543)
          ·
            refine ⟨25753551682886088660443315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17169034455257392440295543 25753551682886088660443315)
            ·
              refine ⟨38630327524329132990664973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25753551682886088660443315 38630327524329132990664973)
              ·
                refine ⟨14486372821623424871499365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38630327524329132990664973 14486372821623424871499365)
                ·
                  refine ⟨2716194904054392163406131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14486372821623424871499365 2716194904054392163406131)
                  ·
                    refine ⟨4074292356081588245109197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2716194904054392163406131 4074292356081588245109197)
                    ·
                      refine ⟨1527859633530595591915949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4074292356081588245109197 1527859633530595591915949)
                      ·
                        rfl

theorem cell23_2975496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_2975496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975496 prefixEnd_2975496 := by exact prefixLift 2975496
  have htrace : WordTrace (prefixWord ++ tailWord_2975496) baseStart_2975496 baseEnd_2975496 := by
    simpa [prefixWord, tailWord_2975496, baseEnd_2975496] using wordTrace_append hprefix tailTrace_2975496
  have hstable : (prefixWord ++ tailWord_2975496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975496).length < 2 ^ (prefixWord ++ tailWord_2975496).sum := by decide
  have hdescent : baseEnd_2975496 < baseStart_2975496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975523 : List Nat := [1, 1, 1, 4, 2, 1, 5, 2, 1, 3, 2]
def baseStart_2975523 : Nat := 118140960795 + 2975523 * 2 ^ 59
def prefixEnd_2975523 : Nat := 4983230072969 + 3 ^ 40 * 2975523 * 2
def baseEnd_2975523 : Nat := 1527873497508266986278325

theorem tailTrace_2975523 : CollatzResearch.WordTrace tailWord_2975523 prefixEnd_2975523 1527873497508266986278325 := by
  unfold tailWord_2975523
  simp only [CollatzResearch.WordTrace]
  refine ⟨108526239599195824715323223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72350826399463883143548815 108526239599195824715323223)
  ·
    refine ⟨162789359398793737072984835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108526239599195824715323223 162789359398793737072984835)
    ·
      refine ⟨244184039098190605609477253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162789359398793737072984835 244184039098190605609477253)
      ·
        refine ⟨45784507330910738551776985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244184039098190605609477253 45784507330910738551776985)
        ·
          refine ⟨34338380498183053913832739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45784507330910738551776985 34338380498183053913832739)
          ·
            refine ⟨51507570747274580870749109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34338380498183053913832739 51507570747274580870749109)
            ·
              refine ⟨4828834757556991956632729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51507570747274580870749109 4828834757556991956632729)
              ·
                refine ⟨3621626068167743967474547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4828834757556991956632729 3621626068167743967474547)
                ·
                  refine ⟨5432439102251615951211821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3621626068167743967474547 5432439102251615951211821)
                  ·
                    refine ⟨2037164663344355981704433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5432439102251615951211821 2037164663344355981704433)
                    ·
                      refine ⟨1527873497508266986278325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2037164663344355981704433 1527873497508266986278325)
                      ·
                        rfl

theorem cell23_2975523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_2975523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975523 prefixEnd_2975523 := by exact prefixLift 2975523
  have htrace : WordTrace (prefixWord ++ tailWord_2975523) baseStart_2975523 baseEnd_2975523 := by
    simpa [prefixWord, tailWord_2975523, baseEnd_2975523] using wordTrace_append hprefix tailTrace_2975523
  have hstable : (prefixWord ++ tailWord_2975523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975523).length < 2 ^ (prefixWord ++ tailWord_2975523).sum := by decide
  have hdescent : baseEnd_2975523 < baseStart_2975523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975570 : List Nat := [3, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2]
def baseStart_2975570 : Nat := 118140960795 + 2975570 * 2 ^ 59
def prefixEnd_2975570 : Nat := 4983230072969 + 3 ^ 40 * 2975570 * 2
def baseEnd_2975570 : Nat := 1527897631099028302390609

theorem tailTrace_2975570 : CollatzResearch.WordTrace tailWord_2975570 prefixEnd_2975570 1527897631099028302390609 := by
  unfold tailWord_2975570
  simp only [CollatzResearch.WordTrace]
  refine ⟨27131988457506387935571041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72351969220017034494856109 27131988457506387935571041)
  ·
    refine ⟨20348991343129790951678281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27131988457506387935571041 20348991343129790951678281)
    ·
      refine ⟨15261743507347343213758711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20348991343129790951678281 15261743507347343213758711)
      ·
        refine ⟨22892615261021014820638067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15261743507347343213758711 22892615261021014820638067)
        ·
          refine ⟨34338922891531522230957101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22892615261021014820638067 34338922891531522230957101)
          ·
            refine ⟨12877096084324320836608913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34338922891531522230957101 12877096084324320836608913)
            ·
              refine ⟨9657822063243240627456685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12877096084324320836608913 9657822063243240627456685)
              ·
                refine ⟨3621683273716215235296257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9657822063243240627456685 3621683273716215235296257)
                ·
                  refine ⟨2716262455287161426472193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3621683273716215235296257 2716262455287161426472193)
                  ·
                    refine ⟨2037196841465371069854145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2716262455287161426472193 2037196841465371069854145)
                    ·
                      refine ⟨1527897631099028302390609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2037196841465371069854145 1527897631099028302390609)
                      ·
                        rfl

theorem cell23_2975570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_2975570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975570 prefixEnd_2975570 := by exact prefixLift 2975570
  have htrace : WordTrace (prefixWord ++ tailWord_2975570) baseStart_2975570 baseEnd_2975570 := by
    simpa [prefixWord, tailWord_2975570, baseEnd_2975570] using wordTrace_append hprefix tailTrace_2975570
  have hstable : (prefixWord ++ tailWord_2975570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975570).length < 2 ^ (prefixWord ++ tailWord_2975570).sum := by decide
  have hdescent : baseEnd_2975570 < baseStart_2975570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975689 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 7]
def baseStart_2975689 : Nat := 118140960795 + 2975689 * 2 ^ 59
def prefixEnd_2975689 : Nat := 4983230072969 + 3 ^ 40 * 2975689 * 2
def baseEnd_2975689 : Nat := 1527958735296913336802561

theorem tailTrace_2975689 : CollatzResearch.WordTrace tailWord_2975689 prefixEnd_2975689 1527958735296913336802561 := by
  unfold tailWord_2975689
  simp only [CollatzResearch.WordTrace]
  refine ⟨108532294116594435065866121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72354862744396290043910747 108532294116594435065866121)
  ·
    refine ⟨81399220587445826299399591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108532294116594435065866121 81399220587445826299399591)
    ·
      refine ⟨122098830881168739449099387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81399220587445826299399591 122098830881168739449099387)
      ·
        refine ⟨183148246321753109173649081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122098830881168739449099387 183148246321753109173649081)
        ·
          refine ⟨137361184741314831880236811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183148246321753109173649081 137361184741314831880236811)
          ·
            refine ⟨206041777111972247820355217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137361184741314831880236811 206041777111972247820355217)
            ·
              refine ⟨154531332833979185865266413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206041777111972247820355217 154531332833979185865266413)
              ·
                refine ⟨57949249812742194699474905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154531332833979185865266413 57949249812742194699474905)
                ·
                  refine ⟨43461937359556646024606179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57949249812742194699474905 43461937359556646024606179)
                  ·
                    refine ⟨65192906039334969036909269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43461937359556646024606179 65192906039334969036909269)
                    ·
                      refine ⟨1527958735296913336802561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65192906039334969036909269 1527958735296913336802561)
                      ·
                        rfl

theorem cell23_2975689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_2975689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975689 prefixEnd_2975689 := by exact prefixLift 2975689
  have htrace : WordTrace (prefixWord ++ tailWord_2975689) baseStart_2975689 baseEnd_2975689 := by
    simpa [prefixWord, tailWord_2975689, baseEnd_2975689] using wordTrace_append hprefix tailTrace_2975689
  have hstable : (prefixWord ++ tailWord_2975689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975689).length < 2 ^ (prefixWord ++ tailWord_2975689).sum := by decide
  have hdescent : baseEnd_2975689 < baseStart_2975689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975736 : List Nat := [2, 1, 2, 1, 1, 3, 2, 4, 1, 1, 5]
def baseStart_2975736 : Nat := 118140960795 + 2975736 * 2 ^ 59
def prefixEnd_2975736 : Nat := 4983230072969 + 3 ^ 40 * 2975736 * 2
def baseEnd_2975736 : Nat := 1527982868887674652914845

theorem tailTrace_2975736 : CollatzResearch.WordTrace tailWord_2975736 prefixEnd_2975736 1527982868887674652914845 := by
  unfold tailWord_2975736
  simp only [CollatzResearch.WordTrace]
  refine ⟨54267004173712081046413531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72356005564949441395218041 54267004173712081046413531)
  ·
    refine ⟨81400506260568121569620297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54267004173712081046413531 81400506260568121569620297)
    ·
      refine ⟨61050379695426091177215223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81400506260568121569620297 61050379695426091177215223)
      ·
        refine ⟨91575569543139136765822835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61050379695426091177215223 91575569543139136765822835)
        ·
          refine ⟨137363354314708705148734253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91575569543139136765822835 137363354314708705148734253)
          ·
            refine ⟨51511257868015764430775345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137363354314708705148734253 51511257868015764430775345)
            ·
              refine ⟨38633443401011823323081509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51511257868015764430775345 38633443401011823323081509)
              ·
                refine ⟨7243770637689716873077783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38633443401011823323081509 7243770637689716873077783)
                ·
                  refine ⟨10865655956534575309616675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7243770637689716873077783 10865655956534575309616675)
                  ·
                    refine ⟨16298483934801862964425013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10865655956534575309616675 16298483934801862964425013)
                    ·
                      refine ⟨1527982868887674652914845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16298483934801862964425013 1527982868887674652914845)
                      ·
                        rfl

theorem cell23_2975736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_2975736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975736 prefixEnd_2975736 := by exact prefixLift 2975736
  have htrace : WordTrace (prefixWord ++ tailWord_2975736) baseStart_2975736 baseEnd_2975736 := by
    simpa [prefixWord, tailWord_2975736, baseEnd_2975736] using wordTrace_append hprefix tailTrace_2975736
  have hstable : (prefixWord ++ tailWord_2975736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975736).length < 2 ^ (prefixWord ++ tailWord_2975736).sum := by decide
  have hdescent : baseEnd_2975736 < baseStart_2975736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975754 : List Nat := [3, 1, 2, 2, 5, 1, 1, 1, 2, 3, 2]
def baseStart_2975754 : Nat := 118140960795 + 2975754 * 2 ^ 59
def prefixEnd_2975754 : Nat := 4983230072969 + 3 ^ 40 * 2975754 * 2
def baseEnd_2975754 : Nat := 1527992111539455582489763

theorem tailTrace_2975754 : CollatzResearch.WordTrace tailWord_2975754 prefixEnd_2975754 1527992111539455582489763 := by
  unfold tailWord_2975754
  simp only [CollatzResearch.WordTrace]
  refine ⟨27133666215339737791745579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72356443240905967444654877 27133666215339737791745579)
  ·
    refine ⟨40700499323009606687618369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27133666215339737791745579 40700499323009606687618369)
    ·
      refine ⟨30525374492257205015713777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40700499323009606687618369 30525374492257205015713777)
      ·
        refine ⟨22894030869192903761785333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30525374492257205015713777 22894030869192903761785333)
        ·
          refine ⟨2146315393986834727667375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22894030869192903761785333 2146315393986834727667375)
          ·
            refine ⟨3219473090980252091501063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2146315393986834727667375 3219473090980252091501063)
            ·
              refine ⟨4829209636470378137251595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3219473090980252091501063 4829209636470378137251595)
              ·
                refine ⟨7243814454705567205877393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4829209636470378137251595 7243814454705567205877393)
                ·
                  refine ⟨5432860841029175404408045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7243814454705567205877393 5432860841029175404408045)
                  ·
                    refine ⟨2037322815385940776653017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5432860841029175404408045 2037322815385940776653017)
                    ·
                      refine ⟨1527992111539455582489763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2037322815385940776653017 1527992111539455582489763)
                      ·
                        rfl

theorem cell23_2975754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_2975754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975754 prefixEnd_2975754 := by exact prefixLift 2975754
  have htrace : WordTrace (prefixWord ++ tailWord_2975754) baseStart_2975754 baseEnd_2975754 := by
    simpa [prefixWord, tailWord_2975754, baseEnd_2975754] using wordTrace_append hprefix tailTrace_2975754
  have hstable : (prefixWord ++ tailWord_2975754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975754).length < 2 ^ (prefixWord ++ tailWord_2975754).sum := by decide
  have hdescent : baseEnd_2975754 < baseStart_2975754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975770 : List Nat := [3, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3]
def baseStart_2975770 : Nat := 118140960795 + 2975770 * 2 ^ 59
def prefixEnd_2975770 : Nat := 4983230072969 + 3 ^ 40 * 2975770 * 2
def baseEnd_2975770 : Nat := 1528000327229927519889689

theorem tailTrace_2975770 : CollatzResearch.WordTrace tailWord_2975770 prefixEnd_2975770 1528000327229927519889689 := by
  unfold tailWord_2975770
  simp only [CollatzResearch.WordTrace]
  refine ⟨27133812107325246474891191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72356832286200657266376509 27133812107325246474891191)
  ·
    refine ⟨40700718160987869712336787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27133812107325246474891191 40700718160987869712336787)
    ·
      refine ⟨61051077241481804568505181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40700718160987869712336787 61051077241481804568505181)
      ·
        refine ⟨22894153965555676713189443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61051077241481804568505181 22894153965555676713189443)
        ·
          refine ⟨34341230948333515069784165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22894153965555676713189443 34341230948333515069784165)
          ·
            refine ⟨6438980802812534075584531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34341230948333515069784165 6438980802812534075584531)
            ·
              refine ⟨9658471204218801113376797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6438980802812534075584531 9658471204218801113376797)
              ·
                refine ⟨3621926701582050417516299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9658471204218801113376797 3621926701582050417516299)
                ·
                  refine ⟨5432890052373075626274449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3621926701582050417516299 5432890052373075626274449)
                  ·
                    refine ⟨4074667539279806719705837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5432890052373075626274449 4074667539279806719705837)
                    ·
                      refine ⟨1528000327229927519889689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4074667539279806719705837 1528000327229927519889689)
                      ·
                        rfl

theorem cell23_2975770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_2975770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975770 prefixEnd_2975770 := by exact prefixLift 2975770
  have htrace : WordTrace (prefixWord ++ tailWord_2975770) baseStart_2975770 baseEnd_2975770 := by
    simpa [prefixWord, tailWord_2975770, baseEnd_2975770] using wordTrace_append hprefix tailTrace_2975770
  have hstable : (prefixWord ++ tailWord_2975770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975770).length < 2 ^ (prefixWord ++ tailWord_2975770).sum := by decide
  have hdescent : baseEnd_2975770 < baseStart_2975770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975777 : List Nat := [1, 2, 3, 2, 4, 2, 1, 2, 2, 4]
def baseStart_2975777 : Nat := 118140960795 + 2975777 * 2 ^ 59
def prefixEnd_2975777 : Nat := 4983230072969 + 3 ^ 40 * 2975777 * 2
def baseEnd_2975777 : Nat := 509334640531502997500719

theorem tailTrace_2975777 : CollatzResearch.WordTrace tailWord_2975777 prefixEnd_2975777 509334640531502997500719 := by
  unfold tailWord_2975777
  simp only [CollatzResearch.WordTrace]
  refine ⟨108535503740275626095069585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72357002493517084063379723 108535503740275626095069585)
  ·
    refine ⟨81401627805206719571302189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108535503740275626095069585 81401627805206719571302189)
    ·
      refine ⟨30525610426952519839238321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81401627805206719571302189 30525610426952519839238321)
      ·
        refine ⟨22894207820214389879428741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30525610426952519839238321 22894207820214389879428741)
        ·
          refine ⟨4292663966290198102392889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22894207820214389879428741 4292663966290198102392889)
          ·
            refine ⟨3219497974717648576794667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4292663966290198102392889 3219497974717648576794667)
            ·
              refine ⟨4829246962076472865192001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3219497974717648576794667 4829246962076472865192001)
              ·
                refine ⟨3621935221557354648894001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4829246962076472865192001 3621935221557354648894001)
                ·
                  refine ⟨2716451416168015986670501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3621935221557354648894001 2716451416168015986670501)
                  ·
                    refine ⟨509334640531502997500719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2716451416168015986670501 509334640531502997500719)
                    ·
                      rfl

theorem cell23_2975777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_2975777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975777 prefixEnd_2975777 := by exact prefixLift 2975777
  have htrace : WordTrace (prefixWord ++ tailWord_2975777) baseStart_2975777 baseEnd_2975777 := by
    simpa [prefixWord, tailWord_2975777, baseEnd_2975777] using wordTrace_append hprefix tailTrace_2975777
  have hstable : (prefixWord ++ tailWord_2975777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975777).length < 2 ^ (prefixWord ++ tailWord_2975777).sum := by decide
  have hdescent : baseEnd_2975777 < baseStart_2975777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975816 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 4, 6]
def baseStart_2975816 : Nat := 118140960795 + 2975816 * 2 ^ 59
def prefixEnd_2975816 : Nat := 4983230072969 + 3 ^ 40 * 2975816 * 2
def baseEnd_2975816 : Nat := 509341315780011446638159

theorem tailTrace_2975816 : CollatzResearch.WordTrace tailWord_2975816 prefixEnd_2975816 509341315780011446638159 := by
  unfold tailWord_2975816
  simp only [CollatzResearch.WordTrace]
  refine ⟨54268463093567167877869651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72357950791422890503826201 54268463093567167877869651)
  ·
    refine ⟨81402694640350751816804477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54268463093567167877869651 81402694640350751816804477)
    ·
      refine ⟨30526010490131531931301679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81402694640350751816804477 30526010490131531931301679)
      ·
        refine ⟨45789015735197297896952519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30526010490131531931301679 45789015735197297896952519)
        ·
          refine ⟨68683523602795946845428779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45789015735197297896952519 68683523602795946845428779)
          ·
            refine ⟨103025285404193920268143169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68683523602795946845428779 103025285404193920268143169)
            ·
              refine ⟨77268964053145440201107377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103025285404193920268143169 77268964053145440201107377)
              ·
                refine ⟨57951723039859080150830533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77268964053145440201107377 57951723039859080150830533)
                ·
                  refine ⟨10865948069973577528280725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57951723039859080150830533 10865948069973577528280725)
                  ·
                    refine ⟨509341315780011446638159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10865948069973577528280725 509341315780011446638159)
                    ·
                      rfl

theorem cell23_2975816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_2975816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975816 prefixEnd_2975816 := by exact prefixLift 2975816
  have htrace : WordTrace (prefixWord ++ tailWord_2975816) baseStart_2975816 baseEnd_2975816 := by
    simpa [prefixWord, tailWord_2975816, baseEnd_2975816] using wordTrace_append hprefix tailTrace_2975816
  have hstable : (prefixWord ++ tailWord_2975816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975816).length < 2 ^ (prefixWord ++ tailWord_2975816).sum := by decide
  have hdescent : baseEnd_2975816 < baseStart_2975816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975853 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_2975853 : Nat := 118140960795 + 2975853 * 2 ^ 59
def prefixEnd_2975853 : Nat := 4983230072969 + 3 ^ 40 * 2975853 * 2
def baseEnd_2975853 : Nat := 1528042946124250695151807

theorem tailTrace_2975853 : CollatzResearch.WordTrace tailWord_2975853 prefixEnd_2975853 1528042946124250695151807 := by
  unfold tailWord_2975853
  simp only [CollatzResearch.WordTrace]
  refine ⟨108538275688000291074836213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72358850458666860716557475 108538275688000291074836213)
  ·
    refine ⟨10175463345750027288265895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108538275688000291074836213 10175463345750027288265895)
    ·
      refine ⟨15263195018625040932398843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10175463345750027288265895 15263195018625040932398843)
      ·
        refine ⟨22894792527937561398598265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15263195018625040932398843 22894792527937561398598265)
        ·
          refine ⟨17171094395953171048948699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22894792527937561398598265 17171094395953171048948699)
          ·
            refine ⟨25756641593929756573423049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17171094395953171048948699 25756641593929756573423049)
            ·
              refine ⟨19317481195447317430067287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25756641593929756573423049 19317481195447317430067287)
              ·
                refine ⟨28976221793170976145100931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19317481195447317430067287 28976221793170976145100931)
                ·
                  refine ⟨43464332689756464217651397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28976221793170976145100931 43464332689756464217651397)
                  ·
                    refine ⟨8149562379329337040809637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43464332689756464217651397 8149562379329337040809637)
                    ·
                      refine ⟨1528042946124250695151807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8149562379329337040809637 1528042946124250695151807)
                      ·
                        rfl

theorem cell23_2975853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_2975853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975853 prefixEnd_2975853 := by exact prefixLift 2975853
  have htrace : WordTrace (prefixWord ++ tailWord_2975853) baseStart_2975853 baseEnd_2975853 := by
    simpa [prefixWord, tailWord_2975853, baseEnd_2975853] using wordTrace_append hprefix tailTrace_2975853
  have hstable : (prefixWord ++ tailWord_2975853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975853).length < 2 ^ (prefixWord ++ tailWord_2975853).sum := by decide
  have hdescent : baseEnd_2975853 < baseStart_2975853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975857 : List Nat := [1, 2, 2, 2, 1, 1, 5, 3, 2, 2, 2]
def baseStart_2975857 : Nat := 118140960795 + 2975857 * 2 ^ 59
def prefixEnd_2975857 : Nat := 4983230072969 + 3 ^ 40 * 2975857 * 2
def baseEnd_2975857 : Nat := 1528045000046868679501789

theorem tailTrace_2975857 : CollatzResearch.WordTrace tailWord_2975857 prefixEnd_2975857 1528045000046868679501789 := by
  unfold tailWord_2975857
  simp only [CollatzResearch.WordTrace]
  refine ⟨108538421579985799757981825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72358947719990533171987883 108538421579985799757981825)
  ·
    refine ⟨81403816184989349818486369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108538421579985799757981825 81403816184989349818486369)
    ·
      refine ⟨61052862138742012363864777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81403816184989349818486369 61052862138742012363864777)
      ·
        refine ⟨45789646604056509272898583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61052862138742012363864777 45789646604056509272898583)
        ·
          refine ⟨68684469906084763909347875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45789646604056509272898583 68684469906084763909347875)
          ·
            refine ⟨103026704859127145864021813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68684469906084763909347875 103026704859127145864021813)
            ·
              refine ⟨9658753580543169924752045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103026704859127145864021813 9658753580543169924752045)
              ·
                refine ⟨3622032592703688721782017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9658753580543169924752045 3622032592703688721782017)
                ·
                  refine ⟨2716524444527766541336513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3622032592703688721782017 2716524444527766541336513)
                  ·
                    refine ⟨2037393333395824906002385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2716524444527766541336513 2037393333395824906002385)
                    ·
                      refine ⟨1528045000046868679501789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2037393333395824906002385 1528045000046868679501789)
                      ·
                        rfl

theorem cell23_2975857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_2975857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975857 prefixEnd_2975857 := by exact prefixLift 2975857
  have htrace : WordTrace (prefixWord ++ tailWord_2975857) baseStart_2975857 baseEnd_2975857 := by
    simpa [prefixWord, tailWord_2975857, baseEnd_2975857] using wordTrace_append hprefix tailTrace_2975857
  have hstable : (prefixWord ++ tailWord_2975857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975857).length < 2 ^ (prefixWord ++ tailWord_2975857).sum := by decide
  have hdescent : baseEnd_2975857 < baseStart_2975857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975866 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8]
def baseStart_2975866 : Nat := 118140960795 + 2975866 * 2 ^ 59
def prefixEnd_2975866 : Nat := 4983230072969 + 3 ^ 40 * 2975866 * 2
def baseEnd_2975866 : Nat := 1528049621372759144289247

theorem tailTrace_2975866 : CollatzResearch.WordTrace tailWord_2975866 prefixEnd_2975866 1528049621372759144289247 := by
  unfold tailWord_2975866
  simp only [CollatzResearch.WordTrace]
  refine ⟨27134687459238298573764863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72359166557968796196706301 27134687459238298573764863)
  ·
    refine ⟨40702031188857447860647295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27134687459238298573764863 40702031188857447860647295)
    ·
      refine ⟨61053046783286171790970943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40702031188857447860647295 61053046783286171790970943)
      ·
        refine ⟨91579570174929257686456415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61053046783286171790970943 91579570174929257686456415)
        ·
          refine ⟨137369355262393886529684623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91579570174929257686456415 137369355262393886529684623)
          ·
            refine ⟨206054032893590829794526935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137369355262393886529684623 206054032893590829794526935)
            ·
              refine ⟨309081049340386244691790403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206054032893590829794526935 309081049340386244691790403)
              ·
                refine ⟨463621574010579367037685605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309081049340386244691790403 463621574010579367037685605)
                ·
                  refine ⟨86929045126983631319566051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 463621574010579367037685605 86929045126983631319566051)
                  ·
                    refine ⟨130393567690475446979349077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86929045126983631319566051 130393567690475446979349077)
                    ·
                      refine ⟨1528049621372759144289247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 130393567690475446979349077 1528049621372759144289247)
                      ·
                        rfl

theorem cell23_2975866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_2975866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975866 prefixEnd_2975866 := by exact prefixLift 2975866
  have htrace : WordTrace (prefixWord ++ tailWord_2975866) baseStart_2975866 baseEnd_2975866 := by
    simpa [prefixWord, tailWord_2975866, baseEnd_2975866] using wordTrace_append hprefix tailTrace_2975866
  have hstable : (prefixWord ++ tailWord_2975866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975866).length < 2 ^ (prefixWord ++ tailWord_2975866).sum := by decide
  have hdescent : baseEnd_2975866 < baseStart_2975866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975890 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_2975890 : Nat := 118140960795 + 2975890 * 2 ^ 59
def prefixEnd_2975890 : Nat := 4983230072969 + 3 ^ 40 * 2975890 * 2
def baseEnd_2975890 : Nat := 1528061944908467050389137

theorem tailTrace_2975890 : CollatzResearch.WordTrace tailWord_2975890 prefixEnd_2975890 1528061944908467050389137 := by
  unfold tailWord_2975890
  simp only [CollatzResearch.WordTrace]
  refine ⟨27134906297216561598483281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72359750125910830929288749 27134906297216561598483281)
  ·
    refine ⟨20351179722912421198862461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27134906297216561598483281 20351179722912421198862461)
    ·
      refine ⟨7631692396092157949573423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20351179722912421198862461 7631692396092157949573423)
      ·
        refine ⟨11447538594138236924360135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7631692396092157949573423 11447538594138236924360135)
        ·
          refine ⟨17171307891207355386540203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11447538594138236924360135 17171307891207355386540203)
          ·
            refine ⟨25756961836811033079810305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17171307891207355386540203 25756961836811033079810305)
            ·
              refine ⟨19317721377608274809857729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25756961836811033079810305 19317721377608274809857729)
              ·
                refine ⟨14488291033206206107393297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19317721377608274809857729 14488291033206206107393297)
                ·
                  refine ⟨10866218274904654580544973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14488291033206206107393297 10866218274904654580544973)
                  ·
                    refine ⟨4074831853089245467704365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10866218274904654580544973 4074831853089245467704365)
                    ·
                      refine ⟨1528061944908467050389137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4074831853089245467704365 1528061944908467050389137)
                      ·
                        rfl

theorem cell23_2975890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_2975890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975890 prefixEnd_2975890 := by exact prefixLift 2975890
  have htrace : WordTrace (prefixWord ++ tailWord_2975890) baseStart_2975890 baseEnd_2975890 := by
    simpa [prefixWord, tailWord_2975890, baseEnd_2975890] using wordTrace_append hprefix tailTrace_2975890
  have hstable : (prefixWord ++ tailWord_2975890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975890).length < 2 ^ (prefixWord ++ tailWord_2975890).sum := by decide
  have hdescent : baseEnd_2975890 < baseStart_2975890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975893 : List Nat := [1, 3, 2, 1, 1, 1, 3, 4, 2, 5]
def baseStart_2975893 : Nat := 118140960795 + 2975893 * 2 ^ 59
def prefixEnd_2975893 : Nat := 4983230072969 + 3 ^ 40 * 2975893 * 2
def baseEnd_2975893 : Nat := 509354495116810179550541

theorem tailTrace_2975893 : CollatzResearch.WordTrace tailWord_2975893 prefixEnd_2975893 509354495116810179550541 := by
  unfold tailWord_2975893
  simp only [CollatzResearch.WordTrace]
  refine ⟨108539734607855377906292333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72359823071903585270861555 108539734607855377906292333)
  ·
    refine ⟨40702400477945766714859625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108539734607855377906292333 40702400477945766714859625)
    ·
      refine ⟨30526800358459325036144719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40702400477945766714859625 30526800358459325036144719)
      ·
        refine ⟨45790200537688987554217079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30526800358459325036144719 45790200537688987554217079)
        ·
          refine ⟨68685300806533481331325619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45790200537688987554217079 68685300806533481331325619)
          ·
            refine ⟨103027951209800221996988429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68685300806533481331325619 103027951209800221996988429)
            ·
              refine ⟨38635481703675083248870661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103027951209800221996988429 38635481703675083248870661)
              ·
                refine ⟨7244152819439078109163249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38635481703675083248870661 7244152819439078109163249)
                ·
                  refine ⟨5433114614579308581872437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7244152819439078109163249 5433114614579308581872437)
                  ·
                    refine ⟨509354495116810179550541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5433114614579308581872437 509354495116810179550541)
                    ·
                      rfl

theorem cell23_2975893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_2975893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975893 prefixEnd_2975893 := by exact prefixLift 2975893
  have htrace : WordTrace (prefixWord ++ tailWord_2975893) baseStart_2975893 baseEnd_2975893 := by
    simpa [prefixWord, tailWord_2975893, baseEnd_2975893] using wordTrace_append hprefix tailTrace_2975893
  have hstable : (prefixWord ++ tailWord_2975893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975893).length < 2 ^ (prefixWord ++ tailWord_2975893).sum := by decide
  have hdescent : baseEnd_2975893 < baseStart_2975893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975900 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 1, 7, 2]
def baseStart_2975900 : Nat := 118140960795 + 2975900 * 2 ^ 59
def prefixEnd_2975900 : Nat := 4983230072969 + 3 ^ 40 * 2975900 * 2
def baseEnd_2975900 : Nat := 1528067079715012011264091

theorem tailTrace_2975900 : CollatzResearch.WordTrace tailWord_2975900 prefixEnd_2975900 1528067079715012011264091 := by
  unfold tailWord_2975900
  simp only [CollatzResearch.WordTrace]
  refine ⟨54269994959415009050898577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72359993279220012067864769 54269994959415009050898577)
  ·
    refine ⟨40702496219561256788173933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54269994959415009050898577 40702496219561256788173933)
    ·
      refine ⟨15263436082335471295565225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40702496219561256788173933 15263436082335471295565225)
      ·
        refine ⟨11447577061751603471673919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15263436082335471295565225 11447577061751603471673919)
        ·
          refine ⟨17171365592627405207510879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11447577061751603471673919 17171365592627405207510879)
          ·
            refine ⟨25757048388941107811266319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17171365592627405207510879 25757048388941107811266319)
            ·
              refine ⟨38635572583411661716899479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25757048388941107811266319 38635572583411661716899479)
              ·
                refine ⟨57953358875117492575349219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38635572583411661716899479 57953358875117492575349219)
                ·
                  refine ⟨86930038312676238863023829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57953358875117492575349219 86930038312676238863023829)
                  ·
                    refine ⟨2037422772953349348352121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 86930038312676238863023829 2037422772953349348352121)
                    ·
                      refine ⟨1528067079715012011264091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2037422772953349348352121 1528067079715012011264091)
                      ·
                        rfl

theorem cell23_2975900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_2975900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975900 prefixEnd_2975900 := by exact prefixLift 2975900
  have htrace : WordTrace (prefixWord ++ tailWord_2975900) baseStart_2975900 baseEnd_2975900 := by
    simpa [prefixWord, tailWord_2975900, baseEnd_2975900] using wordTrace_append hprefix tailTrace_2975900
  have hstable : (prefixWord ++ tailWord_2975900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975900).length < 2 ^ (prefixWord ++ tailWord_2975900).sum := by decide
  have hdescent : baseEnd_2975900 < baseStart_2975900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975930 : List Nat := [3, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4]
def baseStart_2975930 : Nat := 118140960795 + 2975930 * 2 ^ 59
def prefixEnd_2975930 : Nat := 4983230072969 + 3 ^ 40 * 2975930 * 2
def baseEnd_2975930 : Nat := 1528082484134646893888953

theorem tailTrace_2975930 : CollatzResearch.WordTrace tailWord_2975930 prefixEnd_2975930 1528082484134646893888953 := by
  unfold tailWord_2975930
  simp only [CollatzResearch.WordTrace]
  refine ⟨27135271027180333306347311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72360722739147555483592829 27135271027180333306347311)
  ·
    refine ⟨40702906540770499959520967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27135271027180333306347311 40702906540770499959520967)
    ·
      refine ⟨61054359811155749939281451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40702906540770499959520967 61054359811155749939281451)
      ·
        refine ⟨91581539716733624908922177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61054359811155749939281451 91581539716733624908922177)
        ·
          refine ⟨68686154787550218681691633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91581539716733624908922177 68686154787550218681691633)
          ·
            refine ⟨51514616090662664011268725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68686154787550218681691633 51514616090662664011268725)
            ·
              refine ⟨4829495258499624751056443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51514616090662664011268725 4829495258499624751056443)
              ·
                refine ⟨7244242887749437126584665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4829495258499624751056443 7244242887749437126584665)
                ·
                  refine ⟨5433182165812077844938499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7244242887749437126584665 5433182165812077844938499)
                  ·
                    refine ⟨8149773248718116767407749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5433182165812077844938499 8149773248718116767407749)
                    ·
                      refine ⟨1528082484134646893888953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8149773248718116767407749 1528082484134646893888953)
                      ·
                        rfl

theorem cell23_2975930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_2975930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975930 prefixEnd_2975930 := by exact prefixLift 2975930
  have htrace : WordTrace (prefixWord ++ tailWord_2975930) baseStart_2975930 baseEnd_2975930 := by
    simpa [prefixWord, tailWord_2975930, baseEnd_2975930] using wordTrace_append hprefix tailTrace_2975930
  have hstable : (prefixWord ++ tailWord_2975930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975930).length < 2 ^ (prefixWord ++ tailWord_2975930).sum := by decide
  have hdescent : baseEnd_2975930 < baseStart_2975930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975963 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 3]
def baseStart_2975963 : Nat := 118140960795 + 2975963 * 2 ^ 59
def prefixEnd_2975963 : Nat := 4983230072969 + 3 ^ 40 * 2975963 * 2
def baseEnd_2975963 : Nat := 1528099428996245264776301

theorem tailTrace_2975963 : CollatzResearch.WordTrace tailWord_2975963 prefixEnd_2975963 1528099428996245264776301 := by
  unfold tailWord_2975963
  simp only [CollatzResearch.WordTrace]
  refine ⟨108542287717601779861340543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72361525145067853240893695 108542287717601779861340543)
  ·
    refine ⟨162813431576402669792010815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108542287717601779861340543 162813431576402669792010815)
    ·
      refine ⟨244220147364604004688016223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162813431576402669792010815 244220147364604004688016223)
      ·
        refine ⟨366330221046906007032024335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244220147364604004688016223 366330221046906007032024335)
        ·
          refine ⟨549495331570359010548036503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366330221046906007032024335 549495331570359010548036503)
          ·
            refine ⟨824242997355538515822054755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549495331570359010548036503 824242997355538515822054755)
            ·
              refine ⟨1236364496033307773733082133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824242997355538515822054755 1236364496033307773733082133)
              ·
                refine ⟨57954585751561301893738225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1236364496033307773733082133 57954585751561301893738225)
                ·
                  refine ⟨43465939313670976420303669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57954585751561301893738225 43465939313670976420303669)
                  ·
                    refine ⟨4074931810656654039403469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43465939313670976420303669 4074931810656654039403469)
                    ·
                      refine ⟨1528099428996245264776301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4074931810656654039403469 1528099428996245264776301)
                      ·
                        rfl

theorem cell23_2975963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 3].length) (baseStart_2975963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975963 prefixEnd_2975963 := by exact prefixLift 2975963
  have htrace : WordTrace (prefixWord ++ tailWord_2975963) baseStart_2975963 baseEnd_2975963 := by
    simpa [prefixWord, tailWord_2975963, baseEnd_2975963] using wordTrace_append hprefix tailTrace_2975963
  have hstable : (prefixWord ++ tailWord_2975963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975963).length < 2 ^ (prefixWord ++ tailWord_2975963).sum := by decide
  have hdescent : baseEnd_2975963 < baseStart_2975963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976000 : List Nat := [2, 1, 1, 2, 1, 1, 6, 3, 1, 5]
def baseStart_2976000 : Nat := 118140960795 + 2976000 * 2 ^ 59
def prefixEnd_2976000 : Nat := 4983230072969 + 3 ^ 40 * 2976000 * 2
def baseEnd_2976000 : Nat := 509372809260153873337877

theorem tailTrace_2976000 : CollatzResearch.WordTrace tailWord_2976000 prefixEnd_2976000 509372809260153873337877 := by
  unfold tailWord_2976000
  simp only [CollatzResearch.WordTrace]
  refine ⟨54271818609233867590218727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72362424812311823453624969 54271818609233867590218727)
  ·
    refine ⟨81407727913850801385328091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54271818609233867590218727 81407727913850801385328091)
    ·
      refine ⟨122111591870776202077992137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81407727913850801385328091 122111591870776202077992137)
      ·
        refine ⟨91583693903082151558494103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122111591870776202077992137 91583693903082151558494103)
        ·
          refine ⟨137375540854623227337741155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91583693903082151558494103 137375540854623227337741155)
          ·
            refine ⟨206063311281934841006611733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137375540854623227337741155 206063311281934841006611733)
            ·
              refine ⟨9659217716340695672184925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 206063311281934841006611733 9659217716340695672184925)
              ·
                refine ⟨3622206643627760877069347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9659217716340695672184925 3622206643627760877069347)
                ·
                  refine ⟨5433309965441641315604021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3622206643627760877069347 5433309965441641315604021)
                  ·
                    refine ⟨509372809260153873337877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5433309965441641315604021 509372809260153873337877)
                    ·
                      rfl

theorem cell23_2976000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 1, 5].length) (baseStart_2976000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976000 prefixEnd_2976000 := by exact prefixLift 2976000
  have htrace : WordTrace (prefixWord ++ tailWord_2976000) baseStart_2976000 baseEnd_2976000 := by
    simpa [prefixWord, tailWord_2976000, baseEnd_2976000] using wordTrace_append hprefix tailTrace_2976000
  have hstable : (prefixWord ++ tailWord_2976000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976000).length < 2 ^ (prefixWord ++ tailWord_2976000).sum := by decide
  have hdescent : baseEnd_2976000 < baseStart_2976000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976034 : List Nat := [3, 3, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_2976034 : Nat := 118140960795 + 2976034 * 2 ^ 59
def prefixEnd_2976034 : Nat := 4983230072969 + 3 ^ 40 * 2976034 * 2
def baseEnd_2976034 : Nat := 509378628707571495662825

theorem tailTrace_2976034 : CollatzResearch.WordTrace tailWord_2976034 prefixEnd_2976034 509378628707571495662825 := by
  unfold tailWord_2976034
  simp only [CollatzResearch.WordTrace]
  refine ⟨27136219325086139746793789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72363251533563039324783437 27136219325086139746793789)
  ·
    refine ⟨10176082246907302405047671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27136219325086139746793789 10176082246907302405047671)
    ·
      refine ⟨15264123370360953607571507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10176082246907302405047671 15264123370360953607571507)
      ·
        refine ⟨22896185055541430411357261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15264123370360953607571507 22896185055541430411357261)
        ·
          refine ⟨8586069395828036404258973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22896185055541430411357261 8586069395828036404258973)
          ·
            refine ⟨3219776023435513651597115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8586069395828036404258973 3219776023435513651597115)
            ·
              refine ⟨4829664035153270477395673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3219776023435513651597115 4829664035153270477395673)
              ·
                refine ⟨3622248026364952858046755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4829664035153270477395673 3622248026364952858046755)
                ·
                  refine ⟨5433372039547429287070133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3622248026364952858046755 5433372039547429287070133)
                  ·
                    refine ⟨509378628707571495662825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5433372039547429287070133 509378628707571495662825)
                    ·
                      rfl

theorem cell23_2976034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_2976034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976034 prefixEnd_2976034 := by exact prefixLift 2976034
  have htrace : WordTrace (prefixWord ++ tailWord_2976034) baseStart_2976034 baseEnd_2976034 := by
    simpa [prefixWord, tailWord_2976034, baseEnd_2976034] using wordTrace_append hprefix tailTrace_2976034
  have hstable : (prefixWord ++ tailWord_2976034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976034).length < 2 ^ (prefixWord ++ tailWord_2976034).sum := by decide
  have hdescent : baseEnd_2976034 < baseStart_2976034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976037 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 3, 1, 4]
def baseStart_2976037 : Nat := 118140960795 + 2976037 * 2 ^ 59
def prefixEnd_2976037 : Nat := 4983230072969 + 3 ^ 40 * 2976037 * 2
def baseEnd_2976037 : Nat := 1528137426564677975250961

theorem tailTrace_2976037 : CollatzResearch.WordTrace tailWord_2976037 prefixEnd_2976037 1528137426564677975250961 := by
  unfold tailWord_2976037
  simp only [CollatzResearch.WordTrace]
  refine ⟨108544986719333690499534365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72363324479555793666356243 108544986719333690499534365)
  ·
    refine ⟨40704370019750133937325387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108544986719333690499534365 40704370019750133937325387)
    ·
      refine ⟨61056555029625200905988081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40704370019750133937325387 61056555029625200905988081)
      ·
        refine ⟨45792416272218900679491061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61056555029625200905988081 45792416272218900679491061)
        ·
          refine ⟨4293039025520521938702287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45792416272218900679491061 4293039025520521938702287)
          ·
            refine ⟨6439558538280782908053431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4293039025520521938702287 6439558538280782908053431)
            ·
              refine ⟨9659337807421174362080147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6439558538280782908053431 9659337807421174362080147)
              ·
                refine ⟨14489006711131761543120221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9659337807421174362080147 14489006711131761543120221)
                ·
                  refine ⟨5433377516674410578670083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14489006711131761543120221 5433377516674410578670083)
                  ·
                    refine ⟨8150066275011615868005125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5433377516674410578670083 8150066275011615868005125)
                    ·
                      refine ⟨1528137426564677975250961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8150066275011615868005125 1528137426564677975250961)
                      ·
                        rfl

theorem cell23_2976037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_2976037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976037 prefixEnd_2976037 := by exact prefixLift 2976037
  have htrace : WordTrace (prefixWord ++ tailWord_2976037) baseStart_2976037 baseEnd_2976037 := by
    simpa [prefixWord, tailWord_2976037, baseEnd_2976037] using wordTrace_append hprefix tailTrace_2976037
  have hstable : (prefixWord ++ tailWord_2976037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976037).length < 2 ^ (prefixWord ++ tailWord_2976037).sum := by decide
  have hdescent : baseEnd_2976037 < baseStart_2976037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976057 : List Nat := [1, 2, 1, 6, 1, 1, 3, 1, 1, 1, 5]
def baseStart_2976057 : Nat := 118140960795 + 2976057 * 2 ^ 59
def prefixEnd_2976057 : Nat := 4983230072969 + 3 ^ 40 * 2976057 * 2
def baseEnd_2976057 : Nat := 1528147696177767897000869

theorem tailTrace_2976057 : CollatzResearch.WordTrace tailWord_2976057 prefixEnd_2976057 1528147696177767897000869 := by
  unfold tailWord_2976057
  simp only [CollatzResearch.WordTrace]
  refine ⟨108545716179261233915262425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72363810786174155943508283 108545716179261233915262425)
  ·
    refine ⟨81409287134445925436446819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108545716179261233915262425 81409287134445925436446819)
    ·
      refine ⟨122113930701668888154670229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81409287134445925436446819 122113930701668888154670229)
      ·
        refine ⟨5724090501640729132250167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122113930701668888154670229 5724090501640729132250167)
        ·
          refine ⟨8586135752461093698375251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5724090501640729132250167 8586135752461093698375251)
          ·
            refine ⟨12879203628691640547562877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8586135752461093698375251 12879203628691640547562877)
            ·
              refine ⟨4829701360759365205336079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12879203628691640547562877 4829701360759365205336079)
              ·
                refine ⟨7244552041139047808004119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4829701360759365205336079 7244552041139047808004119)
                ·
                  refine ⟨10866828061708571712006179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7244552041139047808004119 10866828061708571712006179)
                  ·
                    refine ⟨16300242092562857568009269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10866828061708571712006179 16300242092562857568009269)
                    ·
                      refine ⟨1528147696177767897000869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16300242092562857568009269 1528147696177767897000869)
                      ·
                        rfl

theorem cell23_2976057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_2976057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976057 prefixEnd_2976057 := by exact prefixLift 2976057
  have htrace : WordTrace (prefixWord ++ tailWord_2976057) baseStart_2976057 baseEnd_2976057 := by
    simpa [prefixWord, tailWord_2976057, baseEnd_2976057] using wordTrace_append hprefix tailTrace_2976057
  have hstable : (prefixWord ++ tailWord_2976057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976057).length < 2 ^ (prefixWord ++ tailWord_2976057).sum := by decide
  have hdescent : baseEnd_2976057 < baseStart_2976057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976065 : List Nat := [1, 2, 5, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_2976065 : Nat := 118140960795 + 2976065 * 2 ^ 59
def prefixEnd_2976065 : Nat := 4983230072969 + 3 ^ 40 * 2976065 * 2
def baseEnd_2976065 : Nat := 1528151804023003865700833

theorem tailTrace_2976065 : CollatzResearch.WordTrace tailWord_2976065 prefixEnd_2976065 1528151804023003865700833 := by
  unfold tailWord_2976065
  simp only [CollatzResearch.WordTrace]
  refine ⟨108546007963232251281553649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72364005308821500854369099 108546007963232251281553649)
  ·
    refine ⟨81409505972424188461165237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108546007963232251281553649 81409505972424188461165237)
    ·
      refine ⟨7632141184914767668234241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81409505972424188461165237 7632141184914767668234241)
      ·
        refine ⟨5724105888686075751175681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7632141184914767668234241 5724105888686075751175681)
        ·
          refine ⟨4293079416514556813381761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5724105888686075751175681 4293079416514556813381761)
          ·
            refine ⟨3219809562385917610036321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4293079416514556813381761 3219809562385917610036321)
            ·
              refine ⟨2414857171789438207527241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3219809562385917610036321 2414857171789438207527241)
              ·
                refine ⟨1811142878842078655645431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2414857171789438207527241 1811142878842078655645431)
                ·
                  refine ⟨2716714318263117983468147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811142878842078655645431 2716714318263117983468147)
                  ·
                    refine ⟨4075071477394676975202221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2716714318263117983468147 4075071477394676975202221)
                    ·
                      refine ⟨1528151804023003865700833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4075071477394676975202221 1528151804023003865700833)
                      ·
                        rfl

theorem cell23_2976065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_2976065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976065 prefixEnd_2976065 := by exact prefixLift 2976065
  have htrace : WordTrace (prefixWord ++ tailWord_2976065) baseStart_2976065 baseEnd_2976065 := by
    simpa [prefixWord, tailWord_2976065, baseEnd_2976065] using wordTrace_append hprefix tailTrace_2976065
  have hstable : (prefixWord ++ tailWord_2976065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976065).length < 2 ^ (prefixWord ++ tailWord_2976065).sum := by decide
  have hdescent : baseEnd_2976065 < baseStart_2976065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976071 : List Nat := [1, 1, 4, 1, 2, 2, 3, 4, 1, 2, 2]
def baseStart_2976071 : Nat := 118140960795 + 2976071 * 2 ^ 59
def prefixEnd_2976071 : Nat := 4983230072969 + 3 ^ 40 * 2976071 * 2
def baseEnd_2976071 : Nat := 1528154884906930842225805

theorem tailTrace_2976071 : CollatzResearch.WordTrace tailWord_2976071 prefixEnd_2976071 1528154884906930842225805 := by
  unfold tailWord_2976071
  simp only [CollatzResearch.WordTrace]
  refine ⟨108546226801210514306272067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72364151200807009537514711 108546226801210514306272067)
  ·
    refine ⟨162819340201815771459408101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108546226801210514306272067 162819340201815771459408101)
    ·
      refine ⟨30528626287840457148639019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162819340201815771459408101 30528626287840457148639019)
      ·
        refine ⟨45792939431760685722958529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30528626287840457148639019 45792939431760685722958529)
        ·
          refine ⟨34344704573820514292218897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45792939431760685722958529 34344704573820514292218897)
          ·
            refine ⟨25758528430365385719164173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34344704573820514292218897 25758528430365385719164173)
            ·
              refine ⟨9659448161387019644686565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25758528430365385719164173 9659448161387019644686565)
              ·
                refine ⟨1811146530260066183378731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9659448161387019644686565 1811146530260066183378731)
                ·
                  refine ⟨2716719795390099275068097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811146530260066183378731 2716719795390099275068097)
                  ·
                    refine ⟨2037539846542574456301073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2716719795390099275068097 2037539846542574456301073)
                    ·
                      refine ⟨1528154884906930842225805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2037539846542574456301073 1528154884906930842225805)
                      ·
                        rfl

theorem cell23_2976071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 1, 2, 2].length) (baseStart_2976071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976071 prefixEnd_2976071 := by exact prefixLift 2976071
  have htrace : WordTrace (prefixWord ++ tailWord_2976071) baseStart_2976071 baseEnd_2976071 := by
    simpa [prefixWord, tailWord_2976071, baseEnd_2976071] using wordTrace_append hprefix tailTrace_2976071
  have hstable : (prefixWord ++ tailWord_2976071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976071).length < 2 ^ (prefixWord ++ tailWord_2976071).sum := by decide
  have hdescent : baseEnd_2976071 < baseStart_2976071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976087 : List Nat := [1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 3]
def baseStart_2976087 : Nat := 118140960795 + 2976087 * 2 ^ 59
def prefixEnd_2976087 : Nat := 4983230072969 + 3 ^ 40 * 2976087 * 2
def baseEnd_2976087 : Nat := 1528163100597402779625731

theorem tailTrace_2976087 : CollatzResearch.WordTrace tailWord_2976087 prefixEnd_2976087 1528163100597402779625731 := by
  unfold tailWord_2976087
  simp only [CollatzResearch.WordTrace]
  refine ⟨108546810369152549038854515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72364540246101699359236343 108546810369152549038854515)
  ·
    refine ⟨162820215553728823558281773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108546810369152549038854515 162820215553728823558281773)
    ·
      refine ⟨61057580832648308834355665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162820215553728823558281773 61057580832648308834355665)
      ·
        refine ⟨45793185624486231625766749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61057580832648308834355665 45793185624486231625766749)
        ·
          refine ⟨17172444609182336859662531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45793185624486231625766749 17172444609182336859662531)
          ·
            refine ⟨25758666913773505289493797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17172444609182336859662531 25758666913773505289493797)
            ·
              refine ⟨4829750046332532241780087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25758666913773505289493797 4829750046332532241780087)
              ·
                refine ⟨7244625069498798362670131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4829750046332532241780087 7244625069498798362670131)
                ·
                  refine ⟨10866937604248197544005197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7244625069498798362670131 10866937604248197544005197)
                  ·
                    refine ⟨4075101601593074079001949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10866937604248197544005197 4075101601593074079001949)
                    ·
                      refine ⟨1528163100597402779625731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4075101601593074079001949 1528163100597402779625731)
                      ·
                        rfl

theorem cell23_2976087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_2976087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976087 prefixEnd_2976087 := by exact prefixLift 2976087
  have htrace : WordTrace (prefixWord ++ tailWord_2976087) baseStart_2976087 baseEnd_2976087 := by
    simpa [prefixWord, tailWord_2976087, baseEnd_2976087] using wordTrace_append hprefix tailTrace_2976087
  have hstable : (prefixWord ++ tailWord_2976087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976087).length < 2 ^ (prefixWord ++ tailWord_2976087).sum := by decide
  have hdescent : baseEnd_2976087 < baseStart_2976087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976100 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_2976100 : Nat := 118140960795 + 2976100 * 2 ^ 59
def prefixEnd_2976100 : Nat := 4983230072969 + 3 ^ 40 * 2976100 * 2
def baseEnd_2976100 : Nat := 1528169775845911228763171

theorem tailTrace_2976100 : CollatzResearch.WordTrace tailWord_2976100 prefixEnd_2976100 1528169775845911228763171 := by
  unfold tailWord_2976100
  simp only [CollatzResearch.WordTrace]
  refine ⟨54273642259052726129538877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72364856345403634839385169 54273642259052726129538877)
  ·
    refine ⟨20352615847144772298577079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54273642259052726129538877 20352615847144772298577079)
    ·
      refine ⟨30528923770717158447865619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20352615847144772298577079 30528923770717158447865619)
      ·
        refine ⟨45793385656075737671798429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30528923770717158447865619 45793385656075737671798429)
        ·
          refine ⟨17172519621028401626924411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45793385656075737671798429 17172519621028401626924411)
          ·
            refine ⟨25758779431542602440386617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17172519621028401626924411 25758779431542602440386617)
            ·
              refine ⟨19319084573656951830289963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25758779431542602440386617 19319084573656951830289963)
              ·
                refine ⟨28978626860485427745434945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19319084573656951830289963 28978626860485427745434945)
                ·
                  refine ⟨21733970145364070809076209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28978626860485427745434945 21733970145364070809076209)
                  ·
                    refine ⟨16300477609023053106807157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21733970145364070809076209 16300477609023053106807157)
                    ·
                      refine ⟨1528169775845911228763171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16300477609023053106807157 1528169775845911228763171)
                      ·
                        rfl

theorem cell23_2976100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_2976100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976100 prefixEnd_2976100 := by exact prefixLift 2976100
  have htrace : WordTrace (prefixWord ++ tailWord_2976100) baseStart_2976100 baseEnd_2976100 := by
    simpa [prefixWord, tailWord_2976100, baseEnd_2976100] using wordTrace_append hprefix tailTrace_2976100
  have hstable : (prefixWord ++ tailWord_2976100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976100).length < 2 ^ (prefixWord ++ tailWord_2976100).sum := by decide
  have hdescent : baseEnd_2976100 < baseStart_2976100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976108 : List Nat := [2, 2, 1, 1, 7, 1, 2, 1, 1, 2, 3]
def baseStart_2976108 : Nat := 118140960795 + 2976108 * 2 ^ 59
def prefixEnd_2976108 : Nat := 4983230072969 + 3 ^ 40 * 2976108 * 2
def baseEnd_2976108 : Nat := 1528173883691147197463135

theorem tailTrace_2976108 : CollatzResearch.WordTrace tailWord_2976108 prefixEnd_2976108 1528173883691147197463135 := by
  unfold tailWord_2976108
  simp only [CollatzResearch.WordTrace]
  refine ⟨54273788151038234812684489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72365050868050979750245985 54273788151038234812684489)
  ·
    refine ⟨40705341113278676109513367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54273788151038234812684489 40705341113278676109513367)
    ·
      refine ⟨61058011669918014164270051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40705341113278676109513367 61058011669918014164270051)
      ·
        refine ⟨91587017504877021246405077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61058011669918014164270051 91587017504877021246405077)
        ·
          refine ⟨2146570722770555185462619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 91587017504877021246405077 2146570722770555185462619)
          ·
            refine ⟨3219856084155832778193929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2146570722770555185462619 3219856084155832778193929)
            ·
              refine ⟨2414892063116874583645447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3219856084155832778193929 2414892063116874583645447)
              ·
                refine ⟨3622338094675311875468171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2414892063116874583645447 3622338094675311875468171)
                ·
                  refine ⟨5433507142012967813202257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3622338094675311875468171 5433507142012967813202257)
                  ·
                    refine ⟨4075130356509725859901693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5433507142012967813202257 4075130356509725859901693)
                    ·
                      refine ⟨1528173883691147197463135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4075130356509725859901693 1528173883691147197463135)
                      ·
                        rfl

theorem cell23_2976108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 1, 2, 3].length) (baseStart_2976108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976108 prefixEnd_2976108 := by exact prefixLift 2976108
  have htrace : WordTrace (prefixWord ++ tailWord_2976108) baseStart_2976108 baseEnd_2976108 := by
    simpa [prefixWord, tailWord_2976108, baseEnd_2976108] using wordTrace_append hprefix tailTrace_2976108
  have hstable : (prefixWord ++ tailWord_2976108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976108).length < 2 ^ (prefixWord ++ tailWord_2976108).sum := by decide
  have hdescent : baseEnd_2976108 < baseStart_2976108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976138 : List Nat := [3, 1, 2, 5, 2, 1, 1, 1, 1, 3, 3]
def baseStart_2976138 : Nat := 118140960795 + 2976138 * 2 ^ 59
def prefixEnd_2976138 : Nat := 4983230072969 + 3 ^ 40 * 2976138 * 2
def baseEnd_2976138 : Nat := 1528189288110782080087997

theorem tailTrace_2976138 : CollatzResearch.WordTrace tailWord_2976138 prefixEnd_2976138 1528189288110782080087997 := by
  unfold tailWord_2976138
  simp only [CollatzResearch.WordTrace]
  refine ⟨27137167622991946187240267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72365780327978523165974045 27137167622991946187240267)
  ·
    refine ⟨40705751434487919280860401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27137167622991946187240267 40705751434487919280860401)
    ·
      refine ⟨30529313575865939460645301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40705751434487919280860401 30529313575865939460645301)
      ·
        refine ⟨2862123147737431824435497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30529313575865939460645301 2862123147737431824435497)
        ·
          refine ⟨2146592360803073868326623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2862123147737431824435497 2146592360803073868326623)
          ·
            refine ⟨3219888541204610802489935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2146592360803073868326623 3219888541204610802489935)
            ·
              refine ⟨4829832811806916203734903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3219888541204610802489935 4829832811806916203734903)
              ·
                refine ⟨7244749217710374305602355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4829832811806916203734903 7244749217710374305602355)
                ·
                  refine ⟨10867123826565561458403533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7244749217710374305602355 10867123826565561458403533)
                  ·
                    refine ⟨4075171434962085546901325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10867123826565561458403533 4075171434962085546901325)
                    ·
                      refine ⟨1528189288110782080087997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4075171434962085546901325 1528189288110782080087997)
                      ·
                        rfl

theorem cell23_2976138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_2976138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976138 prefixEnd_2976138 := by exact prefixLift 2976138
  have htrace : WordTrace (prefixWord ++ tailWord_2976138) baseStart_2976138 baseEnd_2976138 := by
    simpa [prefixWord, tailWord_2976138, baseEnd_2976138] using wordTrace_append hprefix tailTrace_2976138
  have hstable : (prefixWord ++ tailWord_2976138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976138).length < 2 ^ (prefixWord ++ tailWord_2976138).sum := by decide
  have hdescent : baseEnd_2976138 < baseStart_2976138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976148 : List Nat := [2, 4, 2, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_2976148 : Nat := 118140960795 + 2976148 * 2 ^ 59
def prefixEnd_2976148 : Nat := 4983230072969 + 3 ^ 40 * 2976148 * 2
def baseEnd_2976148 : Nat := 1528194422917327040962951

theorem tailTrace_2976148 : CollatzResearch.WordTrace tailWord_2976148 prefixEnd_2976148 1528194422917327040962951 := by
  unfold tailWord_2976148
  simp only [CollatzResearch.WordTrace]
  refine ⟨54274517610965778228412549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72366023481287704304550065 54274517610965778228412549)
  ·
    refine ⟨10176472052056083417827353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54274517610965778228412549 10176472052056083417827353)
    ·
      refine ⟨7632354039042062563370515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10176472052056083417827353 7632354039042062563370515)
      ·
        refine ⟨11448531058563093845055773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7632354039042062563370515 11448531058563093845055773)
        ·
          refine ⟨4293199146961160191895915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11448531058563093845055773 4293199146961160191895915)
          ·
            refine ⟨6439798720441740287843873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4293199146961160191895915 6439798720441740287843873)
            ·
              refine ⟨4829849040331305215882905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6439798720441740287843873 4829849040331305215882905)
              ·
                refine ⟨3622386780248478911912179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4829849040331305215882905 3622386780248478911912179)
                ·
                  refine ⟨5433580170372718367868269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3622386780248478911912179 5433580170372718367868269)
                  ·
                    refine ⟨2037592563889769387950601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5433580170372718367868269 2037592563889769387950601)
                    ·
                      refine ⟨1528194422917327040962951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2037592563889769387950601 1528194422917327040962951)
                      ·
                        rfl

theorem cell23_2976148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_2976148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976148 prefixEnd_2976148 := by exact prefixLift 2976148
  have htrace : WordTrace (prefixWord ++ tailWord_2976148) baseStart_2976148 baseEnd_2976148 := by
    simpa [prefixWord, tailWord_2976148, baseEnd_2976148] using wordTrace_append hprefix tailTrace_2976148
  have hstable : (prefixWord ++ tailWord_2976148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976148).length < 2 ^ (prefixWord ++ tailWord_2976148).sum := by decide
  have hdescent : baseEnd_2976148 < baseStart_2976148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976234 : List Nat := [3, 1, 3, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_2976234 : Nat := 118140960795 + 2976234 * 2 ^ 59
def prefixEnd_2976234 : Nat := 4983230072969 + 3 ^ 40 * 2976234 * 2
def baseEnd_2976234 : Nat := 1528238582253613704487555

theorem tailTrace_2976234 : CollatzResearch.WordTrace tailWord_2976234 prefixEnd_2976234 1528238582253613704487555 := by
  unfold tailWord_2976234
  simp only [CollatzResearch.WordTrace]
  refine ⟨27138042974904998286113939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72368114599746662096303837 27138042974904998286113939)
  ·
    refine ⟨40707064462357497429170909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27138042974904998286113939 40707064462357497429170909)
    ·
      refine ⟨15265149173384061535939091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40707064462357497429170909 15265149173384061535939091)
      ·
        refine ⟨22897723760076092303908637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15265149173384061535939091 22897723760076092303908637)
        ·
          refine ⟨8586646410028534613965739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22897723760076092303908637 8586646410028534613965739)
          ·
            refine ⟨12879969615042801920948609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8586646410028534613965739 12879969615042801920948609)
            ·
              refine ⟨9659977211282101440711457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12879969615042801920948609 9659977211282101440711457)
              ·
                refine ⟨7244982908461576080533593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9659977211282101440711457 7244982908461576080533593)
                ·
                  refine ⟨5433737181346182060400195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7244982908461576080533593 5433737181346182060400195)
                  ·
                    refine ⟨8150605772019273090600293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5433737181346182060400195 8150605772019273090600293)
                    ·
                      refine ⟨1528238582253613704487555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8150605772019273090600293 1528238582253613704487555)
                      ·
                        rfl

theorem cell23_2976234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_2976234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976234 prefixEnd_2976234 := by exact prefixLift 2976234
  have htrace : WordTrace (prefixWord ++ tailWord_2976234) baseStart_2976234 baseEnd_2976234 := by
    simpa [prefixWord, tailWord_2976234, baseEnd_2976234] using wordTrace_append hprefix tailTrace_2976234
  have hstable : (prefixWord ++ tailWord_2976234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976234).length < 2 ^ (prefixWord ++ tailWord_2976234).sum := by decide
  have hdescent : baseEnd_2976234 < baseStart_2976234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976321 : List Nat := [1, 2, 5, 1, 1, 3, 2, 2, 1, 5]
def baseStart_2976321 : Nat := 118140960795 + 2976321 * 2 ^ 59
def prefixEnd_2976321 : Nat := 4983230072969 + 3 ^ 40 * 2976321 * 2
def baseEnd_2976321 : Nat := 509427751690184954699885

theorem tailTrace_2976321 : CollatzResearch.WordTrace tailWord_2976321 prefixEnd_2976321 509427751690184954699885 := by
  unfold tailWord_2976321
  simp only [CollatzResearch.WordTrace]
  refine ⟨108555345050304807002872817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72370230033536538001915211 108555345050304807002872817)
  ·
    refine ⟨81416508787728605252154613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108555345050304807002872817 81416508787728605252154613)
    ·
      refine ⟨7632797698849556742389495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81416508787728605252154613 7632797698849556742389495)
      ·
        refine ⟨11449196548274335113584243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7632797698849556742389495 11449196548274335113584243)
        ·
          refine ⟨17173794822411502670376365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11449196548274335113584243 17173794822411502670376365)
          ·
            refine ⟨6440173058404313501391137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17173794822411502670376365 6440173058404313501391137)
            ·
              refine ⟨4830129793803235126043353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6440173058404313501391137 4830129793803235126043353)
              ·
                refine ⟨3622597345352426344532515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4830129793803235126043353 3622597345352426344532515)
                ·
                  refine ⟨5433896018028639516798773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3622597345352426344532515 5433896018028639516798773)
                  ·
                    refine ⟨509427751690184954699885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5433896018028639516798773 509427751690184954699885)
                    ·
                      rfl

theorem cell23_2976321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_2976321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976321 prefixEnd_2976321 := by exact prefixLift 2976321
  have htrace : WordTrace (prefixWord ++ tailWord_2976321) baseStart_2976321 baseEnd_2976321 := by
    simpa [prefixWord, tailWord_2976321, baseEnd_2976321] using wordTrace_append hprefix tailTrace_2976321
  have hstable : (prefixWord ++ tailWord_2976321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976321).length < 2 ^ (prefixWord ++ tailWord_2976321).sum := by decide
  have hdescent : baseEnd_2976321 < baseStart_2976321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976334 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 4, 4]
def baseStart_2976334 : Nat := 118140960795 + 2976334 * 2 ^ 59
def prefixEnd_2976334 : Nat := 4983230072969 + 3 ^ 40 * 2976334 * 2
def baseEnd_2976334 : Nat := 509429976773021104412365

theorem tailTrace_2976334 : CollatzResearch.WordTrace tailWord_2976334 prefixEnd_2976334 509429976773021104412365 := by
  unfold tailWord_2976334
  simp only [CollatzResearch.WordTrace]
  refine ⟨13569477399907213777887007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72370546132838473482064037 13569477399907213777887007)
  ·
    refine ⟨20354216099860820666830511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13569477399907213777887007 20354216099860820666830511)
    ·
      refine ⟨30531324149791231000245767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20354216099860820666830511 30531324149791231000245767)
      ·
        refine ⟨45796986224686846500368651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30531324149791231000245767 45796986224686846500368651)
        ·
          refine ⟨68695479337030269750552977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45796986224686846500368651 68695479337030269750552977)
          ·
            refine ⟨51521609502772702312914733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68695479337030269750552977 51521609502772702312914733)
            ·
              refine ⟨19320603563539763367343025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51521609502772702312914733 19320603563539763367343025)
              ·
                refine ⟨14490452672654822525507269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19320603563539763367343025 14490452672654822525507269)
                ·
                  refine ⟨2716959876122779223532613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14490452672654822525507269 2716959876122779223532613)
                  ·
                    refine ⟨509429976773021104412365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2716959876122779223532613 509429976773021104412365)
                    ·
                      rfl

theorem cell23_2976334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_2976334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976334 prefixEnd_2976334 := by exact prefixLift 2976334
  have htrace : WordTrace (prefixWord ++ tailWord_2976334) baseStart_2976334 baseEnd_2976334 := by
    simpa [prefixWord, tailWord_2976334, baseEnd_2976334] using wordTrace_append hprefix tailTrace_2976334
  have hstable : (prefixWord ++ tailWord_2976334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976334).length < 2 ^ (prefixWord ++ tailWord_2976334).sum := by decide
  have hdescent : baseEnd_2976334 < baseStart_2976334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976341 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 5, 2, 2]
def baseStart_2976341 : Nat := 118140960795 + 2976341 * 2 ^ 59
def prefixEnd_2976341 : Nat := 4983230072969 + 3 ^ 40 * 2976341 * 2
def baseEnd_2976341 : Nat := 1528293524683644785849563

theorem tailTrace_2976341 : CollatzResearch.WordTrace tailWord_2976341 prefixEnd_2976341 1528293524683644785849563 := by
  unfold tailWord_2976341
  simp only [CollatzResearch.WordTrace]
  refine ⟨108556074510232350418600877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72370716340154900279067251 108556074510232350418600877)
  ·
    refine ⟨40708527941337131406975329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108556074510232350418600877 40708527941337131406975329)
    ·
      refine ⟨30531395956002848555231497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40708527941337131406975329 30531395956002848555231497)
      ·
        refine ⟨22898546967002136416423623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30531395956002848555231497 22898546967002136416423623)
        ·
          refine ⟨34347820450503204624635435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22898546967002136416423623 34347820450503204624635435)
          ·
            refine ⟨51521730675754806936953153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34347820450503204624635435 51521730675754806936953153)
            ·
              refine ⟨38641298006816105202714865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51521730675754806936953153 38641298006816105202714865)
              ·
                refine ⟨28980973505112078902036149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38641298006816105202714865 28980973505112078902036149)
                ·
                  refine ⟨2716966266104257397065889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28980973505112078902036149 2716966266104257397065889)
                  ·
                    refine ⟨2037724699578193047799417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2716966266104257397065889 2037724699578193047799417)
                    ·
                      refine ⟨1528293524683644785849563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2037724699578193047799417 1528293524683644785849563)
                      ·
                        rfl

theorem cell23_2976341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_2976341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976341 prefixEnd_2976341 := by exact prefixLift 2976341
  have htrace : WordTrace (prefixWord ++ tailWord_2976341) baseStart_2976341 baseEnd_2976341 := by
    simpa [prefixWord, tailWord_2976341, baseEnd_2976341] using wordTrace_append hprefix tailTrace_2976341
  have hstable : (prefixWord ++ tailWord_2976341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976341).length < 2 ^ (prefixWord ++ tailWord_2976341).sum := by decide
  have hdescent : baseEnd_2976341 < baseStart_2976341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976387 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 5]
def baseStart_2976387 : Nat := 118140960795 + 2976387 * 2 ^ 59
def prefixEnd_2976387 : Nat := 4983230072969 + 3 ^ 40 * 2976387 * 2
def baseEnd_2976387 : Nat := 1528317144793751605874351

theorem tailTrace_2976387 : CollatzResearch.WordTrace tailWord_2976387 prefixEnd_2976387 1528317144793751605874351 := by
  unfold tailWord_2976387
  simp only [CollatzResearch.WordTrace]
  refine ⟨108557752268065700274775415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72371834845377133516516943 108557752268065700274775415)
  ·
    refine ⟨162836628402098550412163123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108557752268065700274775415 162836628402098550412163123)
    ·
      refine ⟨244254942603147825618244685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162836628402098550412163123 244254942603147825618244685)
      ·
        refine ⟨91595603476180434606841757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244254942603147825618244685 91595603476180434606841757)
        ·
          refine ⟨34348351303567662977565659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91595603476180434606841757 34348351303567662977565659)
          ·
            refine ⟨51522526955351494466348489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34348351303567662977565659 51522526955351494466348489)
            ·
              refine ⟨38641895216513620849761367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51522526955351494466348489 38641895216513620849761367)
              ·
                refine ⟨57962842824770431274642051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38641895216513620849761367 57962842824770431274642051)
                ·
                  refine ⟨86944264237155646911963077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57962842824770431274642051 86944264237155646911963077)
                  ·
                    refine ⟨16302049544466683795993077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86944264237155646911963077 16302049544466683795993077)
                    ·
                      refine ⟨1528317144793751605874351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16302049544466683795993077 1528317144793751605874351)
                      ·
                        rfl

theorem cell23_2976387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_2976387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976387 prefixEnd_2976387 := by exact prefixLift 2976387
  have htrace : WordTrace (prefixWord ++ tailWord_2976387) baseStart_2976387 baseEnd_2976387 := by
    simpa [prefixWord, tailWord_2976387, baseEnd_2976387] using wordTrace_append hprefix tailTrace_2976387
  have hstable : (prefixWord ++ tailWord_2976387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976387).length < 2 ^ (prefixWord ++ tailWord_2976387).sum := by decide
  have hdescent : baseEnd_2976387 < baseStart_2976387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976408 : List Nat := [2, 1, 2, 4, 1, 1, 4, 2, 2, 1, 3]
def baseStart_2976408 : Nat := 118140960795 + 2976408 * 2 ^ 59
def prefixEnd_2976408 : Nat := 4983230072969 + 3 ^ 40 * 2976408 * 2
def baseEnd_2976408 : Nat := 1528327927887496023711755

theorem tailTrace_2976408 : CollatzResearch.WordTrace tailWord_2976408 prefixEnd_2976408 1528327927887496023711755 := by
  unfold tailWord_2976408
  simp only [CollatzResearch.WordTrace]
  refine ⟨54279259100494810430644939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72372345467326413907526585 54279259100494810430644939)
  ·
    refine ⟨81418888650742215645967409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54279259100494810430644939 81418888650742215645967409)
    ·
      refine ⟨61064166488056661734475557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81418888650742215645967409 61064166488056661734475557)
      ·
        refine ⟨11449531216510624075214167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61064166488056661734475557 11449531216510624075214167)
        ·
          refine ⟨17174296824765936112821251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11449531216510624075214167 17174296824765936112821251)
          ·
            refine ⟨25761445237148904169231877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17174296824765936112821251 25761445237148904169231877)
            ·
              refine ⟨4830270981965419531730977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25761445237148904169231877 4830270981965419531730977)
              ·
                refine ⟨3622703236474064648798233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4830270981965419531730977 3622703236474064648798233)
                ·
                  refine ⟨2717027427355548486598675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3622703236474064648798233 2717027427355548486598675)
                  ·
                    refine ⟨4075541141033322729898013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2717027427355548486598675 4075541141033322729898013)
                    ·
                      refine ⟨1528327927887496023711755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4075541141033322729898013 1528327927887496023711755)
                      ·
                        rfl

theorem cell23_2976408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_2976408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976408 prefixEnd_2976408 := by exact prefixLift 2976408
  have htrace : WordTrace (prefixWord ++ tailWord_2976408) baseStart_2976408 baseEnd_2976408 := by
    simpa [prefixWord, tailWord_2976408, baseEnd_2976408] using wordTrace_append hprefix tailTrace_2976408
  have hstable : (prefixWord ++ tailWord_2976408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976408).length < 2 ^ (prefixWord ++ tailWord_2976408).sum := by decide
  have hdescent : baseEnd_2976408 < baseStart_2976408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976431 : List Nat := [1, 1, 2, 1, 2, 5, 1, 3, 1, 4, 2]
def baseStart_2976431 : Nat := 118140960795 + 2976431 * 2 ^ 59
def prefixEnd_2976431 : Nat := 4983230072969 + 3 ^ 40 * 2976431 * 2
def baseEnd_2976431 : Nat := 1528339737942549433724149

theorem tailTrace_2976431 : CollatzResearch.WordTrace tailWord_2976431 prefixEnd_2976431 1528339737942549433724149 := by
  unfold tailWord_2976431
  simp only [CollatzResearch.WordTrace]
  refine ⟨108559357079906295789377147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72372904719937530526251431 108559357079906295789377147)
  ·
    refine ⟨162839035619859443684065721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108559357079906295789377147 162839035619859443684065721)
    ·
      refine ⟨122129276714894582763049291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162839035619859443684065721 122129276714894582763049291)
      ·
        refine ⟨183193915072341874144573937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122129276714894582763049291 183193915072341874144573937)
        ·
          refine ⟨137395436304256405608430453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183193915072341874144573937 137395436304256405608430453)
          ·
            refine ⟨12880822153524038025790355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137395436304256405608430453 12880822153524038025790355)
            ·
              refine ⟨19321233230286057038685533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12880822153524038025790355 19321233230286057038685533)
              ·
                refine ⟨7245462461357271389507075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19321233230286057038685533 7245462461357271389507075)
                ·
                  refine ⟨10868193692035907084260613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7245462461357271389507075 10868193692035907084260613)
                  ·
                    refine ⟨2037786317256732578298865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10868193692035907084260613 2037786317256732578298865)
                    ·
                      refine ⟨1528339737942549433724149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2037786317256732578298865 1528339737942549433724149)
                      ·
                        rfl

theorem cell23_2976431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 4, 2].length) (baseStart_2976431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976431 prefixEnd_2976431 := by exact prefixLift 2976431
  have htrace : WordTrace (prefixWord ++ tailWord_2976431) baseStart_2976431 baseEnd_2976431 := by
    simpa [prefixWord, tailWord_2976431, baseEnd_2976431] using wordTrace_append hprefix tailTrace_2976431
  have hstable : (prefixWord ++ tailWord_2976431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976431).length < 2 ^ (prefixWord ++ tailWord_2976431).sum := by decide
  have hdescent : baseEnd_2976431 < baseStart_2976431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976434 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3]
def baseStart_2976434 : Nat := 118140960795 + 2976434 * 2 ^ 59
def prefixEnd_2976434 : Nat := 4983230072969 + 3 ^ 40 * 2976434 * 2
def baseEnd_2976434 : Nat := 1528341278384512921986635

theorem tailTrace_2976434 : CollatzResearch.WordTrace tailWord_2976434 prefixEnd_2976434 1528341278384512921986635 := by
  unfold tailWord_2976434
  simp only [CollatzResearch.WordTrace]
  refine ⟨27139866624723856825434089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72372977665930284867824237 27139866624723856825434089)
  ·
    refine ⟨20354899968542892619075567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27139866624723856825434089 20354899968542892619075567)
    ·
      refine ⟨30532349952814338928613351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20354899968542892619075567 30532349952814338928613351)
      ·
        refine ⟨45798524929221508392920027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30532349952814338928613351 45798524929221508392920027)
        ·
          refine ⟨68697787393832262589380041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45798524929221508392920027 68697787393832262589380041)
          ·
            refine ⟨51523340545374196942035031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68697787393832262589380041 51523340545374196942035031)
            ·
              refine ⟨77285010818061295413052547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51523340545374196942035031 77285010818061295413052547)
              ·
                refine ⟨115927516227091943119578821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77285010818061295413052547 115927516227091943119578821)
                ·
                  refine ⟨21736409292579739334921029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115927516227091943119578821 21736409292579739334921029)
                  ·
                    refine ⟨4075576742358701125297693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21736409292579739334921029 4075576742358701125297693)
                    ·
                      refine ⟨1528341278384512921986635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4075576742358701125297693 1528341278384512921986635)
                      ·
                        rfl

theorem cell23_2976434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_2976434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976434 prefixEnd_2976434 := by exact prefixLift 2976434
  have htrace : WordTrace (prefixWord ++ tailWord_2976434) baseStart_2976434 baseEnd_2976434 := by
    simpa [prefixWord, tailWord_2976434, baseEnd_2976434] using wordTrace_append hprefix tailTrace_2976434
  have hstable : (prefixWord ++ tailWord_2976434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976434).length < 2 ^ (prefixWord ++ tailWord_2976434).sum := by decide
  have hdescent : baseEnd_2976434 < baseStart_2976434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976444 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2976444 : Nat := 118140960795 + 2976444 * 2 ^ 59
def prefixEnd_2976444 : Nat := 4983230072969 + 3 ^ 40 * 2976444 * 2
def baseEnd_2976444 : Nat := 1528346413191057882861589

theorem tailTrace_2976444 : CollatzResearch.WordTrace tailWord_2976444 prefixEnd_2976444 1528346413191057882861589 := by
  unfold tailWord_2976444
  simp only [CollatzResearch.WordTrace]
  refine ⟨54279915614429599504800193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72373220819239466006400257 54279915614429599504800193)
  ·
    refine ⟨40709936710822199628600145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54279915614429599504800193 40709936710822199628600145)
    ·
      refine ⟨30532452533116649721450109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40709936710822199628600145 30532452533116649721450109)
      ·
        refine ⟨11449669699918743645543791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30532452533116649721450109 11449669699918743645543791)
        ·
          refine ⟨17174504549878115468315687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11449669699918743645543791 17174504549878115468315687)
          ·
            refine ⟨25761756824817173202473531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17174504549878115468315687 25761756824817173202473531)
            ·
              refine ⟨38642635237225759803710297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25761756824817173202473531 38642635237225759803710297)
              ·
                refine ⟨28981976427919319852782723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38642635237225759803710297 28981976427919319852782723)
                ·
                  refine ⟨43472964641878979779174085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28981976427919319852782723 43472964641878979779174085)
                  ·
                    refine ⟨8151180870352308708595141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43472964641878979779174085 8151180870352308708595141)
                    ·
                      refine ⟨1528346413191057882861589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8151180870352308708595141 1528346413191057882861589)
                      ·
                        rfl

theorem cell23_2976444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2976444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976444 prefixEnd_2976444 := by exact prefixLift 2976444
  have htrace : WordTrace (prefixWord ++ tailWord_2976444) baseStart_2976444 baseEnd_2976444 := by
    simpa [prefixWord, tailWord_2976444, baseEnd_2976444] using wordTrace_append hprefix tailTrace_2976444
  have hstable : (prefixWord ++ tailWord_2976444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976444).length < 2 ^ (prefixWord ++ tailWord_2976444).sum := by decide
  have hdescent : baseEnd_2976444 < baseStart_2976444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976452 : List Nat := [2, 3, 3, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_2976452 : Nat := 118140960795 + 2976452 * 2 ^ 59
def prefixEnd_2976452 : Nat := 4983230072969 + 3 ^ 40 * 2976452 * 2
def baseEnd_2976452 : Nat := 1528350521036293851561553

theorem tailTrace_2976452 : CollatzResearch.WordTrace tailWord_2976452 prefixEnd_2976452 1528350521036293851561553 := by
  unfold tailWord_2976452
  simp only [CollatzResearch.WordTrace]
  refine ⟨54280061506415108187945805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72373415341886810917261073 54280061506415108187945805)
  ·
    refine ⟨20355023064905665570479677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54280061506415108187945805 20355023064905665570479677)
    ·
      refine ⟨7633133649339624588929879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20355023064905665570479677 7633133649339624588929879)
      ·
        refine ⟨11449700474009436883394819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7633133649339624588929879 11449700474009436883394819)
        ·
          refine ⟨17174550711014155325092229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11449700474009436883394819 17174550711014155325092229)
          ·
            refine ⟨3220228258315154123454793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17174550711014155325092229 3220228258315154123454793)
            ·
              refine ⟨2415171193736365592591095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3220228258315154123454793 2415171193736365592591095)
              ·
                refine ⟨3622756790604548388886643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2415171193736365592591095 3622756790604548388886643)
                ·
                  refine ⟨5434135185906822583329965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3622756790604548388886643 5434135185906822583329965)
                  ·
                    refine ⟨2037800694715058468748737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5434135185906822583329965 2037800694715058468748737)
                    ·
                      refine ⟨1528350521036293851561553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2037800694715058468748737 1528350521036293851561553)
                      ·
                        rfl

theorem cell23_2976452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_2976452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976452 prefixEnd_2976452 := by exact prefixLift 2976452
  have htrace : WordTrace (prefixWord ++ tailWord_2976452) baseStart_2976452 baseEnd_2976452 := by
    simpa [prefixWord, tailWord_2976452, baseEnd_2976452] using wordTrace_append hprefix tailTrace_2976452
  have hstable : (prefixWord ++ tailWord_2976452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976452).length < 2 ^ (prefixWord ++ tailWord_2976452).sum := by decide
  have hdescent : baseEnd_2976452 < baseStart_2976452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976471 : List Nat := [1, 1, 3, 2, 1, 4, 2, 4, 5]
def baseStart_2976471 : Nat := 118140960795 + 2976471 * 2 ^ 59
def prefixEnd_2976471 : Nat := 4983230072969 + 3 ^ 40 * 2976471 * 2
def baseEnd_2976471 : Nat := 169817808574303253024885

theorem tailTrace_2976471 : CollatzResearch.WordTrace tailWord_2976471 prefixEnd_2976471 169817808574303253024885 := by
  unfold tailWord_2976471
  simp only [CollatzResearch.WordTrace]
  refine ⟨108560815999761382620833267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72373877333174255080555511 108560815999761382620833267)
  ·
    refine ⟨162841223999642073931249901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108560815999761382620833267 162841223999642073931249901)
    ·
      refine ⟨61065458999865777724218713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162841223999642073931249901 61065458999865777724218713)
      ·
        refine ⟨45799094249899333293164035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61065458999865777724218713 45799094249899333293164035)
        ·
          refine ⟨68698641374848999939746053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45799094249899333293164035 68698641374848999939746053)
          ·
            refine ⟨12880995257784187488702385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68698641374848999939746053 12880995257784187488702385)
            ·
              refine ⟨9660746443338140616526789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12880995257784187488702385 9660746443338140616526789)
              ·
                refine ⟨1811389958125901365598773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9660746443338140616526789 1811389958125901365598773)
                ·
                  refine ⟨169817808574303253024885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1811389958125901365598773 169817808574303253024885)
                  ·
                    rfl

theorem cell23_2976471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 5].length) (baseStart_2976471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976471 prefixEnd_2976471 := by exact prefixLift 2976471
  have htrace : WordTrace (prefixWord ++ tailWord_2976471) baseStart_2976471 baseEnd_2976471 := by
    simpa [prefixWord, tailWord_2976471, baseEnd_2976471] using wordTrace_append hprefix tailTrace_2976471
  have hstable : (prefixWord ++ tailWord_2976471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976471).length < 2 ^ (prefixWord ++ tailWord_2976471).sum := by decide
  have hdescent : baseEnd_2976471 < baseStart_2976471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976481 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 2, 3, 3]
def baseStart_2976481 : Nat := 118140960795 + 2976481 * 2 ^ 59
def prefixEnd_2976481 : Nat := 4983230072969 + 3 ^ 40 * 2976481 * 2
def baseEnd_2976481 : Nat := 1528365411975274238098919

theorem tailTrace_2976481 : CollatzResearch.WordTrace tailWord_2976481 prefixEnd_2976481 1528365411975274238098919 := by
  unfold tailWord_2976481
  simp only [CollatzResearch.WordTrace]
  refine ⟨108561180729725154328697297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72374120486483436219131531 108561180729725154328697297)
  ·
    refine ⟨81420885547293865746522973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108561180729725154328697297 81420885547293865746522973)
    ·
      refine ⟨30532832080235199654946115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81420885547293865746522973 30532832080235199654946115)
      ·
        refine ⟨45799248120352799482419173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30532832080235199654946115 45799248120352799482419173)
        ·
          refine ⟨8587359022566149902953595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45799248120352799482419173 8587359022566149902953595)
          ·
            refine ⟨12881038533849224854430393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8587359022566149902953595 12881038533849224854430393)
            ·
              refine ⟨9660778900386918640822795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12881038533849224854430393 9660778900386918640822795)
              ·
                refine ⟨14491168350580377961234193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9660778900386918640822795 14491168350580377961234193)
                ·
                  refine ⟨10868376262935283470925645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14491168350580377961234193 10868376262935283470925645)
                  ·
                    refine ⟨4075641098600731301597117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10868376262935283470925645 4075641098600731301597117)
                    ·
                      refine ⟨1528365411975274238098919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4075641098600731301597117 1528365411975274238098919)
                      ·
                        rfl

theorem cell23_2976481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_2976481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976481 prefixEnd_2976481 := by exact prefixLift 2976481
  have htrace : WordTrace (prefixWord ++ tailWord_2976481) baseStart_2976481 baseEnd_2976481 := by
    simpa [prefixWord, tailWord_2976481, baseEnd_2976481] using wordTrace_append hprefix tailTrace_2976481
  have hstable : (prefixWord ++ tailWord_2976481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976481).length < 2 ^ (prefixWord ++ tailWord_2976481).sum := by decide
  have hdescent : baseEnd_2976481 < baseStart_2976481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976484 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 1, 7]
def baseStart_2976484 : Nat := 118140960795 + 2976484 * 2 ^ 59
def prefixEnd_2976484 : Nat := 4983230072969 + 3 ^ 40 * 2976484 * 2
def baseEnd_2976484 : Nat := 509455650805745908787135

theorem tailTrace_2976484 : CollatzResearch.WordTrace tailWord_2976484 prefixEnd_2976484 509455650805745908787135 := by
  unfold tailWord_2976484
  simp only [CollatzResearch.WordTrace]
  refine ⟨54280645074357142920528253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72374193432476190560704337 54280645074357142920528253)
  ·
    refine ⟨20355241902883928595198095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54280645074357142920528253 20355241902883928595198095)
    ·
      refine ⟨30532862854325892892797143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20355241902883928595198095 30532862854325892892797143)
      ·
        refine ⟨45799294281488839339195715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30532862854325892892797143 45799294281488839339195715)
        ·
          refine ⟨68698941422233259008793573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45799294281488839339195715 68698941422233259008793573)
          ·
            refine ⟨12881051516668736064148795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68698941422233259008793573 12881051516668736064148795)
            ·
              refine ⟨19321577275003104096223193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12881051516668736064148795 19321577275003104096223193)
              ·
                refine ⟨14491182956252328072167395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19321577275003104096223193 14491182956252328072167395)
                ·
                  refine ⟨21736774434378492108251093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14491182956252328072167395 21736774434378492108251093)
                  ·
                    refine ⟨509455650805745908787135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21736774434378492108251093 509455650805745908787135)
                    ·
                      rfl

theorem cell23_2976484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_2976484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976484 prefixEnd_2976484 := by exact prefixLift 2976484
  have htrace : WordTrace (prefixWord ++ tailWord_2976484) baseStart_2976484 baseEnd_2976484 := by
    simpa [prefixWord, tailWord_2976484, baseEnd_2976484] using wordTrace_append hprefix tailTrace_2976484
  have hstable : (prefixWord ++ tailWord_2976484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976484).length < 2 ^ (prefixWord ++ tailWord_2976484).sum := by decide
  have hdescent : baseEnd_2976484 < baseStart_2976484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976504 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 1, 3, 4]
def baseStart_2976504 : Nat := 118140960795 + 2976504 * 2 ^ 59
def prefixEnd_2976504 : Nat := 4983230072969 + 3 ^ 40 * 2976504 * 2
def baseEnd_2976504 : Nat := 1528377222030327648111313

theorem tailTrace_2976504 : CollatzResearch.WordTrace tailWord_2976504 prefixEnd_2976504 1528377222030327648111313 := by
  unfold tailWord_2976504
  simp only [CollatzResearch.WordTrace]
  refine ⟨54281009804320914628392283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72374679739094552837856377 54281009804320914628392283)
  ·
    refine ⟨81421514706481371942588425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54281009804320914628392283 81421514706481371942588425)
    ·
      refine ⟨61066136029861028956941319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81421514706481371942588425 61066136029861028956941319)
      ·
        refine ⟨91599204044791543435411979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61066136029861028956941319 91599204044791543435411979)
        ·
          refine ⟨137398806067187315153117969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91599204044791543435411979 137398806067187315153117969)
          ·
            refine ⟨103049104550390486364838477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137398806067187315153117969 103049104550390486364838477)
            ·
              refine ⟨38643414206396432386814429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103049104550390486364838477 38643414206396432386814429)
              ·
                refine ⟨14491280327398662145055411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38643414206396432386814429 14491280327398662145055411)
                ·
                  refine ⟨21736920491097993217583117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14491280327398662145055411 21736920491097993217583117)
                  ·
                    refine ⟨8151345184161747456593669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21736920491097993217583117 8151345184161747456593669)
                    ·
                      refine ⟨1528377222030327648111313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8151345184161747456593669 1528377222030327648111313)
                      ·
                        rfl

theorem cell23_2976504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_2976504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976504 prefixEnd_2976504 := by exact prefixLift 2976504
  have htrace : WordTrace (prefixWord ++ tailWord_2976504) baseStart_2976504 baseEnd_2976504 := by
    simpa [prefixWord, tailWord_2976504, baseEnd_2976504] using wordTrace_append hprefix tailTrace_2976504
  have hstable : (prefixWord ++ tailWord_2976504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976504).length < 2 ^ (prefixWord ++ tailWord_2976504).sum := by decide
  have hdescent : baseEnd_2976504 < baseStart_2976504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976521 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 4, 4, 2]
def baseStart_2976521 : Nat := 118140960795 + 2976521 * 2 ^ 59
def prefixEnd_2976521 : Nat := 4983230072969 + 3 ^ 40 * 2976521 * 2
def baseEnd_2976521 : Nat := 1528385951201454081598735

theorem tailTrace_2976521 : CollatzResearch.WordTrace tailWord_2976521 prefixEnd_2976521 1528385951201454081598735 := by
  unfold tailWord_2976521
  simp only [CollatzResearch.WordTrace]
  refine ⟨108562639649580241160153417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72375093099720160773435611 108562639649580241160153417)
  ·
    refine ⟨81421979737185180870115063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108562639649580241160153417 81421979737185180870115063)
    ·
      refine ⟨122132969605777771305172595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81421979737185180870115063 122132969605777771305172595)
      ·
        refine ⟨183199454408666656957758893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122132969605777771305172595 183199454408666656957758893)
        ·
          refine ⟨68699795403249996359159585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183199454408666656957758893 68699795403249996359159585)
          ·
            refine ⟨51524846552437497269369689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68699795403249996359159585 51524846552437497269369689)
            ·
              refine ⟨38643634914328122952027267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51524846552437497269369689 38643634914328122952027267)
              ·
                refine ⟨57965452371492184428040901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38643634914328122952027267 57965452371492184428040901)
                ·
                  refine ⟨10868522319654784580257669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57965452371492184428040901 10868522319654784580257669)
                  ·
                    refine ⟨2037847934935272108798313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10868522319654784580257669 2037847934935272108798313)
                    ·
                      refine ⟨1528385951201454081598735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2037847934935272108798313 1528385951201454081598735)
                      ·
                        rfl

theorem cell23_2976521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 4, 2].length) (baseStart_2976521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976521 prefixEnd_2976521 := by exact prefixLift 2976521
  have htrace : WordTrace (prefixWord ++ tailWord_2976521) baseStart_2976521 baseEnd_2976521 := by
    simpa [prefixWord, tailWord_2976521, baseEnd_2976521] using wordTrace_append hprefix tailTrace_2976521
  have hstable : (prefixWord ++ tailWord_2976521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976521).length < 2 ^ (prefixWord ++ tailWord_2976521).sum := by decide
  have hdescent : baseEnd_2976521 < baseStart_2976521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976615 : List Nat := [1, 1, 5, 1, 2, 2, 3, 1, 2, 3, 2]
def baseStart_2976615 : Nat := 118140960795 + 2976615 * 2 ^ 59
def prefixEnd_2976615 : Nat := 4983230072969 + 3 ^ 40 * 2976615 * 2
def baseEnd_2976615 : Nat := 1528434218382976713823303

theorem tailTrace_2976615 : CollatzResearch.WordTrace tailWord_2976615 prefixEnd_2976615 1528434218382976713823303 := by
  unfold tailWord_2976615
  simp only [CollatzResearch.WordTrace]
  refine ⟨108566068111239695214075299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72377378740826463476050199 108566068111239695214075299)
  ·
    refine ⟨162849102166859542821112949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108566068111239695214075299 162849102166859542821112949)
    ·
      refine ⟨15267103328143082139479339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162849102166859542821112949 15267103328143082139479339)
      ·
        refine ⟨22900654992214623209219009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15267103328143082139479339 22900654992214623209219009)
        ·
          refine ⟨17175491244160967406914257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22900654992214623209219009 17175491244160967406914257)
          ·
            refine ⟨12881618433120725555185693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17175491244160967406914257 12881618433120725555185693)
            ·
              refine ⟨4830606912420272083194635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12881618433120725555185693 4830606912420272083194635)
              ·
                refine ⟨7245910368630408124791953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4830606912420272083194635 7245910368630408124791953)
                ·
                  refine ⟨5434432776472806093593965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7245910368630408124791953 5434432776472806093593965)
                  ·
                    refine ⟨2037912291177302285097737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5434432776472806093593965 2037912291177302285097737)
                    ·
                      refine ⟨1528434218382976713823303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2037912291177302285097737 1528434218382976713823303)
                      ·
                        rfl

theorem cell23_2976615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_2976615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976615 prefixEnd_2976615 := by exact prefixLift 2976615
  have htrace : WordTrace (prefixWord ++ tailWord_2976615) baseStart_2976615 baseEnd_2976615 := by
    simpa [prefixWord, tailWord_2976615, baseEnd_2976615] using wordTrace_append hprefix tailTrace_2976615
  have hstable : (prefixWord ++ tailWord_2976615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976615).length < 2 ^ (prefixWord ++ tailWord_2976615).sum := by decide
  have hdescent : baseEnd_2976615 < baseStart_2976615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976625 : List Nat := [1, 2, 2, 2, 1, 6, 2, 1, 1, 5]
def baseStart_2976625 : Nat := 118140960795 + 2976625 * 2 ^ 59
def prefixEnd_2976625 : Nat := 4983230072969 + 3 ^ 40 * 2976625 * 2
def baseEnd_2976625 : Nat := 509479784396507224899419

theorem tailTrace_2976625 : CollatzResearch.WordTrace tailWord_2976625 prefixEnd_2976625 509479784396507224899419 := by
  unfold tailWord_2976625
  simp only [CollatzResearch.WordTrace]
  refine ⟨108566432841203466921939329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72377621894135644614626219 108566432841203466921939329)
  ·
    refine ⟨81424824630902600191454497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108566432841203466921939329 81424824630902600191454497)
    ·
      refine ⟨61068618473176950143590873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81424824630902600191454497 61068618473176950143590873)
      ·
        refine ⟨45801463854882712607693155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61068618473176950143590873 45801463854882712607693155)
        ·
          refine ⟨68702195782324068911539733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45801463854882712607693155 68702195782324068911539733)
          ·
            refine ⟨3220415427296440730228425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68702195782324068911539733 3220415427296440730228425)
            ·
              refine ⟨2415311570472330547671319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3220415427296440730228425 2415311570472330547671319)
              ·
                refine ⟨3622967355708495821506979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2415311570472330547671319 3622967355708495821506979)
                ·
                  refine ⟨5434451033562743732260469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3622967355708495821506979 5434451033562743732260469)
                  ·
                    refine ⟨509479784396507224899419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5434451033562743732260469 509479784396507224899419)
                    ·
                      rfl

theorem cell23_2976625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 1, 5].length) (baseStart_2976625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976625 prefixEnd_2976625 := by exact prefixLift 2976625
  have htrace : WordTrace (prefixWord ++ tailWord_2976625) baseStart_2976625 baseEnd_2976625 := by
    simpa [prefixWord, tailWord_2976625, baseEnd_2976625] using wordTrace_append hprefix tailTrace_2976625
  have hstable : (prefixWord ++ tailWord_2976625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976625).length < 2 ^ (prefixWord ++ tailWord_2976625).sum := by decide
  have hdescent : baseEnd_2976625 < baseStart_2976625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976645 : List Nat := [1, 3, 1, 1, 3, 3, 1, 3, 3, 2, 2]
def baseStart_2976645 : Nat := 118140960795 + 2976645 * 2 ^ 59
def prefixEnd_2976645 : Nat := 4983230072969 + 3 ^ 40 * 2976645 * 2
def baseEnd_2976645 : Nat := 1528449622802611596448165

theorem tailTrace_2976645 : CollatzResearch.WordTrace tailWord_2976645 prefixEnd_2976645 1528449622802611596448165 := by
  unfold tailWord_2976645
  simp only [CollatzResearch.WordTrace]
  refine ⟨108567162301131010337667389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72378108200754006891778259 108567162301131010337667389)
  ·
    refine ⟨40712685862924128876625271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108567162301131010337667389 40712685862924128876625271)
    ·
      refine ⟨61069028794386193314937907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40712685862924128876625271 61069028794386193314937907)
      ·
        refine ⟨91603543191579289972406861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61069028794386193314937907 91603543191579289972406861)
        ·
          refine ⟨34351328696842233739652573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91603543191579289972406861 34351328696842233739652573)
          ·
            refine ⟨12881748261315837652369715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34351328696842233739652573 12881748261315837652369715)
            ·
              refine ⟨19322622391973756478554573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12881748261315837652369715 19322622391973756478554573)
              ·
                refine ⟨7245983396990158679457965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19322622391973756478554573 7245983396990158679457965)
                ·
                  refine ⟨2717243773871309504796737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7245983396990158679457965 2717243773871309504796737)
                  ·
                    refine ⟨2037932830403482128597553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2717243773871309504796737 2037932830403482128597553)
                    ·
                      refine ⟨1528449622802611596448165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2037932830403482128597553 1528449622802611596448165)
                      ·
                        rfl

theorem cell23_2976645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 2, 2].length) (baseStart_2976645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976645 prefixEnd_2976645 := by exact prefixLift 2976645
  have htrace : WordTrace (prefixWord ++ tailWord_2976645) baseStart_2976645 baseEnd_2976645 := by
    simpa [prefixWord, tailWord_2976645, baseEnd_2976645] using wordTrace_append hprefix tailTrace_2976645
  have hstable : (prefixWord ++ tailWord_2976645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976645).length < 2 ^ (prefixWord ++ tailWord_2976645).sum := by decide
  have hdescent : baseEnd_2976645 < baseStart_2976645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976648 : List Nat := [2, 1, 3, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_2976648 : Nat := 118140960795 + 2976648 * 2 ^ 59
def prefixEnd_2976648 : Nat := 4983230072969 + 3 ^ 40 * 2976648 * 2
def baseEnd_2976648 : Nat := 1528451163244575084710651

theorem tailTrace_2976648 : CollatzResearch.WordTrace tailWord_2976648 prefixEnd_2976648 1528451163244575084710651 := by
  unfold tailWord_2976648
  simp only [CollatzResearch.WordTrace]
  refine ⟨54283635860060070925013299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72378181146746761233351065 54283635860060070925013299)
  ·
    refine ⟨81425453790090106387519949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54283635860060070925013299 81425453790090106387519949)
    ·
      refine ⟨30534545171283789895319981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81425453790090106387519949 30534545171283789895319981)
      ·
        refine ⟨11450454439231421210744993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30534545171283789895319981 11450454439231421210744993)
        ·
          refine ⟨8587840829423565908058745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11450454439231421210744993 8587840829423565908058745)
          ·
            refine ⟨6440880622067674431044059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8587840829423565908058745 6440880622067674431044059)
            ·
              refine ⟨9661320933101511646566089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6440880622067674431044059 9661320933101511646566089)
              ·
                refine ⟨7245990699826133734924567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9661320933101511646566089 7245990699826133734924567)
                ·
                  refine ⟨10868986049739200602386851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7245990699826133734924567 10868986049739200602386851)
                  ·
                    refine ⟨16303479074608800903580277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10868986049739200602386851 16303479074608800903580277)
                    ·
                      refine ⟨1528451163244575084710651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16303479074608800903580277 1528451163244575084710651)
                      ·
                        rfl

theorem cell23_2976648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_2976648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976648 prefixEnd_2976648 := by exact prefixLift 2976648
  have htrace : WordTrace (prefixWord ++ tailWord_2976648) baseStart_2976648 baseEnd_2976648 := by
    simpa [prefixWord, tailWord_2976648, baseEnd_2976648] using wordTrace_append hprefix tailTrace_2976648
  have hstable : (prefixWord ++ tailWord_2976648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976648).length < 2 ^ (prefixWord ++ tailWord_2976648).sum := by decide
  have hdescent : baseEnd_2976648 < baseStart_2976648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976668 : List Nat := [2, 2, 3, 3, 2, 1, 1, 9]
def baseStart_2976668 : Nat := 118140960795 + 2976668 * 2 ^ 59
def prefixEnd_2976668 : Nat := 4983230072969 + 3 ^ 40 * 2976668 * 2
def baseEnd_2976668 : Nat := 56609682698432037276317

theorem tailTrace_2976668 : CollatzResearch.WordTrace tailWord_2976668 prefixEnd_2976668 56609682698432037276317 := by
  unfold tailWord_2976668
  simp only [CollatzResearch.WordTrace]
  refine ⟨54284000590023842632877329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72378667453365123510503105 54284000590023842632877329)
  ·
    refine ⟨40713000442517881974657997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54284000590023842632877329 40713000442517881974657997)
    ·
      refine ⟨15267375165944205740496749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40713000442517881974657997 15267375165944205740496749)
      ·
        refine ⟨5725265687229077152686281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15267375165944205740496749 5725265687229077152686281)
        ·
          refine ⟨4293949265421807864514711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5725265687229077152686281 4293949265421807864514711)
          ·
            refine ⟨6440923898132711796772067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4293949265421807864514711 6440923898132711796772067)
            ·
              refine ⟨9661385847199067695158101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6440923898132711796772067 9661385847199067695158101)
              ·
                refine ⟨56609682698432037276317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9661385847199067695158101 56609682698432037276317)
                ·
                  rfl

theorem cell23_2976668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 9].length) (baseStart_2976668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976668 prefixEnd_2976668 := by exact prefixLift 2976668
  have htrace : WordTrace (prefixWord ++ tailWord_2976668) baseStart_2976668 baseEnd_2976668 := by
    simpa [prefixWord, tailWord_2976668, baseEnd_2976668] using wordTrace_append hprefix tailTrace_2976668
  have hstable : (prefixWord ++ tailWord_2976668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976668).length < 2 ^ (prefixWord ++ tailWord_2976668).sum := by decide
  have hdescent : baseEnd_2976668 < baseStart_2976668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976685 : List Nat := [1, 5, 2, 3, 1, 2, 9]
def baseStart_2976685 : Nat := 118140960795 + 2976685 * 2 ^ 59
def prefixEnd_2976685 : Nat := 4983230072969 + 3 ^ 40 * 2976685 * 2
def baseEnd_2976685 : Nat := 18870002000355449875901

theorem tailTrace_2976685 : CollatzResearch.WordTrace tailWord_2976685 prefixEnd_2976685 18870002000355449875901 := by
  unfold tailWord_2976685
  simp only [CollatzResearch.WordTrace]
  refine ⟨108568621220986097169123509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72379080813990731446082339 108568621220986097169123509)
  ·
    refine ⟨10178308239467446609605329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108568621220986097169123509 10178308239467446609605329)
    ·
      refine ⟨7633731179600584957203997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10178308239467446609605329 7633731179600584957203997)
      ·
        refine ⟨2862649192350219358951499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7633731179600584957203997 2862649192350219358951499)
        ·
          refine ⟨4293973788525329038427249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2862649192350219358951499 4293973788525329038427249)
          ·
            refine ⟨3220480341393996778820437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4293973788525329038427249 3220480341393996778820437)
            ·
              refine ⟨18870002000355449875901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3220480341393996778820437 18870002000355449875901)
              ·
                rfl

theorem cell23_2976685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 9].length) (baseStart_2976685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976685 prefixEnd_2976685 := by exact prefixLift 2976685
  have htrace : WordTrace (prefixWord ++ tailWord_2976685) baseStart_2976685 baseEnd_2976685 := by
    simpa [prefixWord, tailWord_2976685, baseEnd_2976685] using wordTrace_append hprefix tailTrace_2976685
  have hstable : (prefixWord ++ tailWord_2976685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976685).length < 2 ^ (prefixWord ++ tailWord_2976685).sum := by decide
  have hdescent : baseEnd_2976685 < baseStart_2976685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976711 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 2, 6]
def baseStart_2976711 : Nat := 118140960795 + 2976711 * 2 ^ 59
def prefixEnd_2976711 : Nat := 4983230072969 + 3 ^ 40 * 2976711 * 2
def baseEnd_2976711 : Nat := 509494504175269446074287

theorem tailTrace_2976711 : CollatzResearch.WordTrace tailWord_2976711 prefixEnd_2976711 509494504175269446074287 := by
  unfold tailWord_2976711
  simp only [CollatzResearch.WordTrace]
  refine ⟨108569569518891903609569987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72379713012594602406379991 108569569518891903609569987)
  ·
    refine ⟨162854354278337855414354981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108569569518891903609569987 162854354278337855414354981)
    ·
      refine ⟨30535191427188347890191559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162854354278337855414354981 30535191427188347890191559)
      ·
        refine ⟨45802787140782521835287339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30535191427188347890191559 45802787140782521835287339)
        ·
          refine ⟨68704180711173782752931009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45802787140782521835287339 68704180711173782752931009)
          ·
            refine ⟨51528135533380337064698257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68704180711173782752931009 51528135533380337064698257)
            ·
              refine ⟨38646101650035252798523693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51528135533380337064698257 38646101650035252798523693)
              ·
                refine ⟨14492288118763219799446385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38646101650035252798523693 14492288118763219799446385)
                ·
                  refine ⟨10869216089072414849584789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14492288118763219799446385 10869216089072414849584789)
                  ·
                    refine ⟨509494504175269446074287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10869216089072414849584789 509494504175269446074287)
                    ·
                      rfl

theorem cell23_2976711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_2976711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976711 prefixEnd_2976711 := by exact prefixLift 2976711
  have htrace : WordTrace (prefixWord ++ tailWord_2976711) baseStart_2976711 baseEnd_2976711 := by
    simpa [prefixWord, tailWord_2976711, baseEnd_2976711] using wordTrace_append hprefix tailTrace_2976711
  have hstable : (prefixWord ++ tailWord_2976711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976711).length < 2 ^ (prefixWord ++ tailWord_2976711).sum := by decide
  have hdescent : baseEnd_2976711 < baseStart_2976711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976712 : List Nat := [2, 1, 3, 1, 5, 1, 1, 3, 2, 1, 3]
def baseStart_2976712 : Nat := 118140960795 + 2976712 * 2 ^ 59
def prefixEnd_2976712 : Nat := 4983230072969 + 3 ^ 40 * 2976712 * 2
def baseEnd_2976712 : Nat := 1528484026006462834310357

theorem tailTrace_2976712 : CollatzResearch.WordTrace tailWord_2976712 prefixEnd_2976712 1528484026006462834310357 := by
  unfold tailWord_2976712
  simp only [CollatzResearch.WordTrace]
  refine ⟨54284802995944140390178195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72379737327925520520237593 54284802995944140390178195)
  ·
    refine ⟨81427204493916210585267293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54284802995944140390178195 81427204493916210585267293)
    ·
      refine ⟨30535201685218578969475235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81427204493916210585267293 30535201685218578969475235)
      ·
        refine ⟨45802802527827868454212853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30535201685218578969475235 45802802527827868454212853)
        ·
          refine ⟨4294012736983862667582455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45802802527827868454212853 4294012736983862667582455)
          ·
            refine ⟨6441019105475794001373683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4294012736983862667582455 6441019105475794001373683)
            ·
              refine ⟨9661528658213691002060525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6441019105475794001373683 9661528658213691002060525)
              ·
                refine ⟨3623073246830134125772697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9661528658213691002060525 3623073246830134125772697)
                ·
                  refine ⟨2717304935122600594329523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3623073246830134125772697 2717304935122600594329523)
                  ·
                    refine ⟨4075957402683900891494285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2717304935122600594329523 4075957402683900891494285)
                    ·
                      refine ⟨1528484026006462834310357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4075957402683900891494285 1528484026006462834310357)
                      ·
                        rfl

theorem cell23_2976712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_2976712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976712 prefixEnd_2976712 := by exact prefixLift 2976712
  have htrace : WordTrace (prefixWord ++ tailWord_2976712) baseStart_2976712 baseEnd_2976712 := by
    simpa [prefixWord, tailWord_2976712, baseEnd_2976712] using wordTrace_append hprefix tailTrace_2976712
  have hstable : (prefixWord ++ tailWord_2976712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976712).length < 2 ^ (prefixWord ++ tailWord_2976712).sum := by decide
  have hdescent : baseEnd_2976712 < baseStart_2976712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976721 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 4, 1, 5]
def baseStart_2976721 : Nat := 118140960795 + 2976721 * 2 ^ 59
def prefixEnd_2976721 : Nat := 4983230072969 + 3 ^ 40 * 2976721 * 2
def baseEnd_2976721 : Nat := 1528488647332353299097815

theorem tailTrace_2976721 : CollatzResearch.WordTrace tailWord_2976721 prefixEnd_2976721 1528488647332353299097815 := by
  unfold tailWord_2976721
  simp only [CollatzResearch.WordTrace]
  refine ⟨108569934248855675317434017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72379956165903783544956011 108569934248855675317434017)
  ·
    refine ⟨81427450686641756488075513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108569934248855675317434017 81427450686641756488075513)
    ·
      refine ⟨61070588014981317366056635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81427450686641756488075513 61070588014981317366056635)
      ·
        refine ⟨91605882022471976049084953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61070588014981317366056635 91605882022471976049084953)
        ·
          refine ⟨68704411516853982036813715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91605882022471976049084953 68704411516853982036813715)
          ·
            refine ⟨103056617275280973055220573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68704411516853982036813715 103056617275280973055220573)
            ·
              refine ⟨38646231478230364895707715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103056617275280973055220573 38646231478230364895707715)
              ·
                refine ⟨57969347217345547343561573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38646231478230364895707715 57969347217345547343561573)
                ·
                  refine ⟨10869252603252290126917795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57969347217345547343561573 10869252603252290126917795)
                  ·
                    refine ⟨16303878904878435190376693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10869252603252290126917795 16303878904878435190376693)
                    ·
                      refine ⟨1528488647332353299097815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16303878904878435190376693 1528488647332353299097815)
                      ·
                        rfl

theorem cell23_2976721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_2976721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976721 prefixEnd_2976721 := by exact prefixLift 2976721
  have htrace : WordTrace (prefixWord ++ tailWord_2976721) baseStart_2976721 baseEnd_2976721 := by
    simpa [prefixWord, tailWord_2976721, baseEnd_2976721] using wordTrace_append hprefix tailTrace_2976721
  have hstable : (prefixWord ++ tailWord_2976721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976721).length < 2 ^ (prefixWord ++ tailWord_2976721).sum := by decide
  have hdescent : baseEnd_2976721 < baseStart_2976721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976722 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 3, 3, 2]
def baseStart_2976722 : Nat := 118140960795 + 2976722 * 2 ^ 59
def prefixEnd_2976722 : Nat := 4983230072969 + 3 ^ 40 * 2976722 * 2
def baseEnd_2976722 : Nat := 1528489160813007795185311

theorem tailTrace_2976722 : CollatzResearch.WordTrace tailWord_2976722 prefixEnd_2976722 1528489160813007795185311 := by
  unfold tailWord_2976722
  simp only [CollatzResearch.WordTrace]
  refine ⟨27142492680463013122055105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72379980481234701658813613 27142492680463013122055105)
  ·
    refine ⟨20356869510347259841541329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27142492680463013122055105 20356869510347259841541329)
    ·
      refine ⟨15267652132760444881155997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20356869510347259841541329 15267652132760444881155997)
      ·
        refine ⟨5725369549785166830433499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15267652132760444881155997 5725369549785166830433499)
        ·
          refine ⟨8588054324677750245650249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5725369549785166830433499 8588054324677750245650249)
          ·
            refine ⟨6441040743508312684237687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8588054324677750245650249 6441040743508312684237687)
            ·
              refine ⟨9661561115262469026356531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6441040743508312684237687 9661561115262469026356531)
              ·
                refine ⟨14492341672893703539534797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9661561115262469026356531 14492341672893703539534797)
                ·
                  refine ⟨5434628127335138827325549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14492341672893703539534797 5434628127335138827325549)
                  ·
                    refine ⟨2037985547750677060247081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5434628127335138827325549 2037985547750677060247081)
                    ·
                      refine ⟨1528489160813007795185311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2037985547750677060247081 1528489160813007795185311)
                      ·
                        rfl

theorem cell23_2976722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_2976722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976722 prefixEnd_2976722 := by exact prefixLift 2976722
  have htrace : WordTrace (prefixWord ++ tailWord_2976722) baseStart_2976722 baseEnd_2976722 := by
    simpa [prefixWord, tailWord_2976722, baseEnd_2976722] using wordTrace_append hprefix tailTrace_2976722
  have hstable : (prefixWord ++ tailWord_2976722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976722).length < 2 ^ (prefixWord ++ tailWord_2976722).sum := by decide
  have hdescent : baseEnd_2976722 < baseStart_2976722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976869 : List Nat := [1, 3, 1, 3, 2, 1, 5, 2, 1, 4]
def baseStart_2976869 : Nat := 118140960795 + 2976869 * 2 ^ 59
def prefixEnd_2976869 : Nat := 4983230072969 + 3 ^ 40 * 2976869 * 2
def baseEnd_2976869 : Nat := 509521547489739573349045

theorem tailTrace_2976869 : CollatzResearch.WordTrace tailWord_2976869 prefixEnd_2976869 509521547489739573349045 := by
  unfold tailWord_2976869
  simp only [CollatzResearch.WordTrace]
  refine ⟨108575332252319496593821661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72383554834879664395881107 108575332252319496593821661)
  ·
    refine ⟨40715749594619811222683123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108575332252319496593821661 40715749594619811222683123)
    ·
      refine ⟨61073624391929716834024685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40715749594619811222683123 61073624391929716834024685)
      ·
        refine ⟨22902609146973643812759257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61073624391929716834024685 22902609146973643812759257)
        ·
          refine ⟨17176956860230232859569443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22902609146973643812759257 17176956860230232859569443)
          ·
            refine ⟨25765435290345349289354165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17176956860230232859569443 25765435290345349289354165)
            ·
              refine ⟨2415509558469876495876953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25765435290345349289354165 2415509558469876495876953)
              ·
                refine ⟨1811632168852407371907715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2415509558469876495876953 1811632168852407371907715)
                ·
                  refine ⟨2717448253278611057861573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811632168852407371907715 2717448253278611057861573)
                  ·
                    refine ⟨509521547489739573349045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2717448253278611057861573 509521547489739573349045)
                    ·
                      rfl

theorem cell23_2976869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 1, 4].length) (baseStart_2976869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976869 prefixEnd_2976869 := by exact prefixLift 2976869
  have htrace : WordTrace (prefixWord ++ tailWord_2976869) baseStart_2976869 baseEnd_2976869 := by
    simpa [prefixWord, tailWord_2976869, baseEnd_2976869] using wordTrace_append hprefix tailTrace_2976869
  have hstable : (prefixWord ++ tailWord_2976869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976869).length < 2 ^ (prefixWord ++ tailWord_2976869).sum := by decide
  have hdescent : baseEnd_2976869 < baseStart_2976869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2976915 : List Nat := [1, 1, 1, 2, 1, 2, 4, 5, 1, 1, 4]
def baseStart_2976915 : Nat := 118140960795 + 2976915 * 2 ^ 59
def prefixEnd_2976915 : Nat := 4983230072969 + 3 ^ 40 * 2976915 * 2
def baseEnd_2976915 : Nat := 1528588262579325540071923

theorem tailTrace_2976915 : CollatzResearch.WordTrace tailWord_2976915 prefixEnd_2976915 1528588262579325540071923 := by
  unfold tailWord_2976915
  simp only [CollatzResearch.WordTrace]
  refine ⟨108577010010152846449996199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72384673340101897633330799 108577010010152846449996199)
  ·
    refine ⟨162865515015229269674994299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108577010010152846449996199 162865515015229269674994299)
    ·
      refine ⟨244298272522843904512491449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162865515015229269674994299 244298272522843904512491449)
      ·
        refine ⟨183223704392132928384368587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244298272522843904512491449 183223704392132928384368587)
        ·
          refine ⟨274835556588199392576552881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183223704392132928384368587 274835556588199392576552881)
          ·
            refine ⟨206126667441149544432414661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274835556588199392576552881 206126667441149544432414661)
            ·
              refine ⟨38648750145215539581077749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206126667441149544432414661 38648750145215539581077749)
              ·
                refine ⟨3623320326113956835726039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38648750145215539581077749 3623320326113956835726039)
                ·
                  refine ⟨5434980489170935253589059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3623320326113956835726039 5434980489170935253589059)
                  ·
                    refine ⟨8152470733756402880383589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5434980489170935253589059 8152470733756402880383589)
                    ·
                      refine ⟨1528588262579325540071923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8152470733756402880383589 1528588262579325540071923)
                      ·
                        rfl

theorem cell23_2976915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 1, 4].length) (baseStart_2976915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2976915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2976915 prefixEnd_2976915 := by exact prefixLift 2976915
  have htrace : WordTrace (prefixWord ++ tailWord_2976915) baseStart_2976915 baseEnd_2976915 := by
    simpa [prefixWord, tailWord_2976915, baseEnd_2976915] using wordTrace_append hprefix tailTrace_2976915
  have hstable : (prefixWord ++ tailWord_2976915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2976915).length < 2 ^ (prefixWord ++ tailWord_2976915).sum := by decide
  have hdescent : baseEnd_2976915 < baseStart_2976915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2976915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977025 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_2977025 : Nat := 118140960795 + 2977025 * 2 ^ 59
def prefixEnd_2977025 : Nat := 4983230072969 + 3 ^ 40 * 2977025 * 2
def baseEnd_2977025 : Nat := 1528644745451320109696417

theorem tailTrace_2977025 : CollatzResearch.WordTrace tailWord_2977025 prefixEnd_2977025 1528644745451320109696417 := by
  unfold tailWord_2977025
  simp only [CollatzResearch.WordTrace]
  refine ⟨108581022039754335236500529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72387348026502890157667019 108581022039754335236500529)
  ·
    refine ⟨81435766529815751427375397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108581022039754335236500529 81435766529815751427375397)
    ·
      refine ⟨15269206224340453392632887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81435766529815751427375397 15269206224340453392632887)
      ·
        refine ⟨22903809336510680088949331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15269206224340453392632887 22903809336510680088949331)
        ·
          refine ⟨34355714004766020133423997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22903809336510680088949331 34355714004766020133423997)
          ·
            refine ⟨12883392751787257550033999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34355714004766020133423997 12883392751787257550033999)
            ·
              refine ⟨19325089127680886325050999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12883392751787257550033999 19325089127680886325050999)
              ·
                refine ⟨28987633691521329487576499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19325089127680886325050999 28987633691521329487576499)
                ·
                  refine ⟨43481450537281994231364749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28987633691521329487576499 43481450537281994231364749)
                  ·
                    refine ⟨16305543951480747836761781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43481450537281994231364749 16305543951480747836761781)
                    ·
                      refine ⟨1528644745451320109696417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16305543951480747836761781 1528644745451320109696417)
                      ·
                        rfl

theorem cell23_2977025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_2977025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977025 prefixEnd_2977025 := by exact prefixLift 2977025
  have htrace : WordTrace (prefixWord ++ tailWord_2977025) baseStart_2977025 baseEnd_2977025 := by
    simpa [prefixWord, tailWord_2977025, baseEnd_2977025] using wordTrace_append hprefix tailTrace_2977025
  have hstable : (prefixWord ++ tailWord_2977025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977025).length < 2 ^ (prefixWord ++ tailWord_2977025).sum := by decide
  have hdescent : baseEnd_2977025 < baseStart_2977025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977135 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 8]
def baseStart_2977135 : Nat := 118140960795 + 2977135 * 2 ^ 59
def prefixEnd_2977135 : Nat := 4983230072969 + 3 ^ 40 * 2977135 * 2
def baseEnd_2977135 : Nat := 169855692035923853257879

theorem tailTrace_2977135 : CollatzResearch.WordTrace tailWord_2977135 prefixEnd_2977135 169855692035923853257879 := by
  unfold tailWord_2977135
  simp only [CollatzResearch.WordTrace]
  refine ⟨108585034069355824023004859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72390022712903882682003239 108585034069355824023004859)
  ·
    refine ⟨162877551104033736034507289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108585034069355824023004859 162877551104033736034507289)
    ·
      refine ⟨122158163328025302025880467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162877551104033736034507289 122158163328025302025880467)
      ·
        refine ⟨183237244992037953038820701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122158163328025302025880467 183237244992037953038820701)
        ·
          refine ⟨68713966872014232389557763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183237244992037953038820701 68713966872014232389557763)
          ·
            refine ⟨103070950308021348584336645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68713966872014232389557763 103070950308021348584336645)
            ·
              refine ⟨19325803182754002859563121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103070950308021348584336645 19325803182754002859563121)
              ·
                refine ⟨14494352387065502144672341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19325803182754002859563121 14494352387065502144672341)
                ·
                  refine ⟨169855692035923853257879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14494352387065502144672341 169855692035923853257879)
                  ·
                    rfl

theorem cell23_2977135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 8].length) (baseStart_2977135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977135 prefixEnd_2977135 := by exact prefixLift 2977135
  have htrace : WordTrace (prefixWord ++ tailWord_2977135) baseStart_2977135 baseEnd_2977135 := by
    simpa [prefixWord, tailWord_2977135, baseEnd_2977135] using wordTrace_append hprefix tailTrace_2977135
  have hstable : (prefixWord ++ tailWord_2977135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977135).length < 2 ^ (prefixWord ++ tailWord_2977135).sum := by decide
  have hdescent : baseEnd_2977135 < baseStart_2977135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977156 : List Nat := [2, 3, 2, 1, 1, 3, 2, 4, 1, 4]
def baseStart_2977156 : Nat := 118140960795 + 2977156 * 2 ^ 59
def prefixEnd_2977156 : Nat := 4983230072969 + 3 ^ 40 * 2977156 * 2
def baseEnd_2977156 : Nat := 509570670472353032386105

theorem tailTrace_2977156 : CollatzResearch.WordTrace tailWord_2977156 prefixEnd_2977156 509570670472353032386105 := by
  unfold tailWord_2977156
  simp only [CollatzResearch.WordTrace]
  refine ⟨54292900001139872304759661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72390533334853163073012881 54292900001139872304759661)
  ·
    refine ⟨20359837500427452114284873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54292900001139872304759661 20359837500427452114284873)
    ·
      refine ⟨15269878125320589085713655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20359837500427452114284873 15269878125320589085713655)
      ·
        refine ⟨22904817187980883628570483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15269878125320589085713655 22904817187980883628570483)
        ·
          refine ⟨34357225781971325442855725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22904817187980883628570483 34357225781971325442855725)
          ·
            refine ⟨12883959668239247041070897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34357225781971325442855725 12883959668239247041070897)
            ·
              refine ⟨9662969751179435280803173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12883959668239247041070897 9662969751179435280803173)
              ·
                refine ⟨1811806828346144115150595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9662969751179435280803173 1811806828346144115150595)
                ·
                  refine ⟨2717710242519216172725893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811806828346144115150595 2717710242519216172725893)
                  ·
                    refine ⟨509570670472353032386105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2717710242519216172725893 509570670472353032386105)
                    ·
                      rfl

theorem cell23_2977156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_2977156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977156 prefixEnd_2977156 := by exact prefixLift 2977156
  have htrace : WordTrace (prefixWord ++ tailWord_2977156) baseStart_2977156 baseEnd_2977156 := by
    simpa [prefixWord, tailWord_2977156, baseEnd_2977156] using wordTrace_append hprefix tailTrace_2977156
  have hstable : (prefixWord ++ tailWord_2977156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977156).length < 2 ^ (prefixWord ++ tailWord_2977156).sum := by decide
  have hdescent : baseEnd_2977156 < baseStart_2977156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977236 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_2977236 : Nat := 118140960795 + 2977236 * 2 ^ 59
def prefixEnd_2977236 : Nat := 4983230072969 + 3 ^ 40 * 2977236 * 2
def baseEnd_2977236 : Nat := 1528753089869418784157947

theorem tailTrace_2977236 : CollatzResearch.WordTrace tailWord_2977236 prefixEnd_2977236 1528753089869418784157947 := by
  unfold tailWord_2977236
  simp only [CollatzResearch.WordTrace]
  refine ⟨54294358920994959136215781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72392478561326612181621041 54294358920994959136215781)
  ·
    refine ⟨10180192297686554838040459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54294358920994959136215781 10180192297686554838040459)
    ·
      refine ⟨15270288446529832257060689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10180192297686554838040459 15270288446529832257060689)
      ·
        refine ⟨11452716334897374192795517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15270288446529832257060689 11452716334897374192795517)
        ·
          refine ⟨4294768625586515322298319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11452716334897374192795517 4294768625586515322298319)
          ·
            refine ⟨6442152938379772983447479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4294768625586515322298319 6442152938379772983447479)
            ·
              refine ⟨9663229407569659475171219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6442152938379772983447479 9663229407569659475171219)
              ·
                refine ⟨14494844111354489212756829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9663229407569659475171219 14494844111354489212756829)
                ·
                  refine ⟨5435566541757933454783811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14494844111354489212756829 5435566541757933454783811)
                  ·
                    refine ⟨8153349812636900182175717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5435566541757933454783811 8153349812636900182175717)
                    ·
                      refine ⟨1528753089869418784157947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8153349812636900182175717 1528753089869418784157947)
                      ·
                        rfl

theorem cell23_2977236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_2977236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977236 prefixEnd_2977236 := by exact prefixLift 2977236
  have htrace : WordTrace (prefixWord ++ tailWord_2977236) baseStart_2977236 baseEnd_2977236 := by
    simpa [prefixWord, tailWord_2977236, baseEnd_2977236] using wordTrace_append hprefix tailTrace_2977236
  have hstable : (prefixWord ++ tailWord_2977236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977236).length < 2 ^ (prefixWord ++ tailWord_2977236).sum := by decide
  have hdescent : baseEnd_2977236 < baseStart_2977236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977242 : List Nat := [3, 1, 1, 2, 3, 2, 2, 9]
def baseStart_2977242 : Nat := 118140960795 + 2977242 * 2 ^ 59
def prefixEnd_2977242 : Nat := 4983230072969 + 3 ^ 40 * 2977242 * 2
def baseEnd_2977242 : Nat := 56620598916790583728997

theorem tailTrace_2977242 : CollatzResearch.WordTrace tailWord_2977242 prefixEnd_2977242 56620598916790583728997 := by
  unfold tailWord_2977242
  simp only [CollatzResearch.WordTrace]
  refine ⟨27147234169992045324287495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72392624453312120864766653 27147234169992045324287495)
  ·
    refine ⟨40720851254988067986431243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27147234169992045324287495 40720851254988067986431243)
    ·
      refine ⟨61081276882482101979646865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40720851254988067986431243 61081276882482101979646865)
      ·
        refine ⟨45810957661861576484735149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61081276882482101979646865 45810957661861576484735149)
        ·
          refine ⟨17179109123198091181775681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45810957661861576484735149 17179109123198091181775681)
          ·
            refine ⟨12884331842398568386331761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17179109123198091181775681 12884331842398568386331761)
            ·
              refine ⟨9663248881798926289748821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12884331842398568386331761 9663248881798926289748821)
              ·
                refine ⟨56620598916790583728997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9663248881798926289748821 56620598916790583728997)
                ·
                  rfl

theorem cell23_2977242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 9].length) (baseStart_2977242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977242 prefixEnd_2977242 := by exact prefixLift 2977242
  have htrace : WordTrace (prefixWord ++ tailWord_2977242) baseStart_2977242 baseEnd_2977242 := by
    simpa [prefixWord, tailWord_2977242, baseEnd_2977242] using wordTrace_append hprefix tailTrace_2977242
  have hstable : (prefixWord ++ tailWord_2977242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977242).length < 2 ^ (prefixWord ++ tailWord_2977242).sum := by decide
  have hdescent : baseEnd_2977242 < baseStart_2977242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977249 : List Nat := [1, 2, 3, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_2977249 : Nat := 118140960795 + 2977249 * 2 ^ 59
def prefixEnd_2977249 : Nat := 4983230072969 + 3 ^ 40 * 2977249 * 2
def baseEnd_2977249 : Nat := 1528759765117927233295387

theorem tailTrace_2977249 : CollatzResearch.WordTrace tailWord_2977249 prefixEnd_2977249 1528759765117927233295387 := by
  unfold tailWord_2977249
  simp only [CollatzResearch.WordTrace]
  refine ⟨108589191990942821492654801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72392794660628547661769867 108589191990942821492654801)
  ·
    refine ⟨81441893993207116119491101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108589191990942821492654801 81441893993207116119491101)
    ·
      refine ⟨30540710247452668544809163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81441893993207116119491101 30540710247452668544809163)
      ·
        refine ⟨45811065371179002817213745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30540710247452668544809163 45811065371179002817213745)
        ·
          refine ⟨34358299028384252112910309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45811065371179002817213745 34358299028384252112910309)
          ·
            refine ⟨6442181067822047271170683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34358299028384252112910309 6442181067822047271170683)
            ·
              refine ⟨9663271601733070906756025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6442181067822047271170683 9663271601733070906756025)
              ·
                refine ⟨7247453701299803180067019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9663271601733070906756025 7247453701299803180067019)
                ·
                  refine ⟨10871180551949704770100529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7247453701299803180067019 10871180551949704770100529)
                  ·
                    refine ⟨8153385413962278577575397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10871180551949704770100529 8153385413962278577575397)
                    ·
                      refine ⟨1528759765117927233295387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8153385413962278577575397 1528759765117927233295387)
                      ·
                        rfl

theorem cell23_2977249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_2977249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977249 prefixEnd_2977249 := by exact prefixLift 2977249
  have htrace : WordTrace (prefixWord ++ tailWord_2977249) baseStart_2977249 baseEnd_2977249 := by
    simpa [prefixWord, tailWord_2977249, baseEnd_2977249] using wordTrace_append hprefix tailTrace_2977249
  have hstable : (prefixWord ++ tailWord_2977249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977249).length < 2 ^ (prefixWord ++ tailWord_2977249).sum := by decide
  have hdescent : baseEnd_2977249 < baseStart_2977249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977253 : List Nat := [1, 3, 1, 5, 1, 2, 3, 1, 1, 1, 4]
def baseStart_2977253 : Nat := 118140960795 + 2977253 * 2 ^ 59
def prefixEnd_2977253 : Nat := 4983230072969 + 3 ^ 40 * 2977253 * 2
def baseEnd_2977253 : Nat := 1528761819040545217645369

theorem tailTrace_2977253 : CollatzResearch.WordTrace tailWord_2977253 prefixEnd_2977253 1528761819040545217645369 := by
  unfold tailWord_2977253
  simp only [CollatzResearch.WordTrace]
  refine ⟨108589337882928330175800413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72392891921952220117200275 108589337882928330175800413)
  ·
    refine ⟨40721001706098123815925155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108589337882928330175800413 40721001706098123815925155)
    ·
      refine ⟨61081502559147185723887733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40721001706098123815925155 61081502559147185723887733)
      ·
        refine ⟨5726390864920048661614475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61081502559147185723887733 5726390864920048661614475)
        ·
          refine ⟨8589586297380072992421713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5726390864920048661614475 8589586297380072992421713)
          ·
            refine ⟨6442189723035054744316285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8589586297380072992421713 6442189723035054744316285)
            ·
              refine ⟨2415821146138145529118607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6442189723035054744316285 2415821146138145529118607)
              ·
                refine ⟨3623731719207218293677911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2415821146138145529118607 3623731719207218293677911)
                ·
                  refine ⟨5435597578810827440516867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3623731719207218293677911 5435597578810827440516867)
                  ·
                    refine ⟨8153396368216241160775301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5435597578810827440516867 8153396368216241160775301)
                    ·
                      refine ⟨1528761819040545217645369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8153396368216241160775301 1528761819040545217645369)
                      ·
                        rfl

theorem cell23_2977253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_2977253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977253 prefixEnd_2977253 := by exact prefixLift 2977253
  have htrace : WordTrace (prefixWord ++ tailWord_2977253) baseStart_2977253 baseEnd_2977253 := by
    simpa [prefixWord, tailWord_2977253, baseEnd_2977253] using wordTrace_append hprefix tailTrace_2977253
  have hstable : (prefixWord ++ tailWord_2977253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977253).length < 2 ^ (prefixWord ++ tailWord_2977253).sum := by decide
  have hdescent : baseEnd_2977253 < baseStart_2977253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977272 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 2, 7]
def baseStart_2977272 : Nat := 118140960795 + 2977272 * 2 ^ 59
def prefixEnd_2977272 : Nat := 4983230072969 + 3 ^ 40 * 2977272 * 2
def baseEnd_2977272 : Nat := 509590525057660214435927

theorem tailTrace_2977272 : CollatzResearch.WordTrace tailWord_2977272 prefixEnd_2977272 509590525057660214435927 := by
  unfold tailWord_2977272
  simp only [CollatzResearch.WordTrace]
  refine ⟨54295015434929748210371035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72393353913239664280494713 54295015434929748210371035)
  ·
    refine ⟨81442523152394622315556553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54295015434929748210371035 81442523152394622315556553)
    ·
      refine ⟨61081892364295966736667415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81442523152394622315556553 61081892364295966736667415)
      ·
        refine ⟨91622838546443950105001123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61081892364295966736667415 91622838546443950105001123)
        ·
          refine ⟨137434257819665925157501685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91622838546443950105001123 137434257819665925157501685)
          ·
            refine ⟨12884461670593680483515783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137434257819665925157501685 12884461670593680483515783)
            ·
              refine ⟨19326692505890520725273675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12884461670593680483515783 19326692505890520725273675)
              ·
                refine ⟨28990038758835781087910513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19326692505890520725273675 28990038758835781087910513)
                ·
                  refine ⟨21742529069126835815932885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28990038758835781087910513 21742529069126835815932885)
                  ·
                    refine ⟨509590525057660214435927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21742529069126835815932885 509590525057660214435927)
                    ·
                      rfl

theorem cell23_2977272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_2977272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977272 prefixEnd_2977272 := by exact prefixLift 2977272
  have htrace : WordTrace (prefixWord ++ tailWord_2977272) baseStart_2977272 baseEnd_2977272 := by
    simpa [prefixWord, tailWord_2977272, baseEnd_2977272] using wordTrace_append hprefix tailTrace_2977272
  have hstable : (prefixWord ++ tailWord_2977272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977272).length < 2 ^ (prefixWord ++ tailWord_2977272).sum := by decide
  have hdescent : baseEnd_2977272 < baseStart_2977272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977313 : List Nat := [1, 2, 3, 2, 2, 3, 1, 3, 1, 3, 2]
def baseStart_2977313 : Nat := 118140960795 + 2977313 * 2 ^ 59
def prefixEnd_2977313 : Nat := 4983230072969 + 3 ^ 40 * 2977313 * 2
def baseEnd_2977313 : Nat := 1528792627879814982895093

theorem tailTrace_2977313 : CollatzResearch.WordTrace tailWord_2977313 prefixEnd_2977313 1528792627879814982895093 := by
  unfold tailWord_2977313
  simp only [CollatzResearch.WordTrace]
  refine ⟨108591526262710960422984593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72394350841807306948656395 108591526262710960422984593)
  ·
    refine ⟨81443644697033220317238445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108591526262710960422984593 81443644697033220317238445)
    ·
      refine ⟨30541366761387457618964417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81443644697033220317238445 30541366761387457618964417)
      ·
        refine ⟨22906025071040593214223313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30541366761387457618964417 22906025071040593214223313)
        ·
          refine ⟨17179518803280444910667485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22906025071040593214223313 17179518803280444910667485)
          ·
            refine ⟨6442319551230166841500307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17179518803280444910667485 6442319551230166841500307)
            ·
              refine ⟨9663479326845250262250461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6442319551230166841500307 9663479326845250262250461)
              ·
                refine ⟨3623804747566968848343923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9663479326845250262250461 3623804747566968848343923)
                ·
                  refine ⟨5435707121350453272515885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3623804747566968848343923 5435707121350453272515885)
                  ·
                    refine ⟨2038390170506419977193457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5435707121350453272515885 2038390170506419977193457)
                    ·
                      refine ⟨1528792627879814982895093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2038390170506419977193457 1528792627879814982895093)
                      ·
                        rfl

theorem cell23_2977313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_2977313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977313 prefixEnd_2977313 := by exact prefixLift 2977313
  have htrace : WordTrace (prefixWord ++ tailWord_2977313) baseStart_2977313 baseEnd_2977313 := by
    simpa [prefixWord, tailWord_2977313, baseEnd_2977313] using wordTrace_append hprefix tailTrace_2977313
  have hstable : (prefixWord ++ tailWord_2977313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977313).length < 2 ^ (prefixWord ++ tailWord_2977313).sum := by decide
  have hdescent : baseEnd_2977313 < baseStart_2977313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977343 : List Nat := [1, 1, 2, 2, 3, 5, 1, 1, 1, 4, 2]
def baseStart_2977343 : Nat := 118140960795 + 2977343 * 2 ^ 59
def prefixEnd_2977343 : Nat := 4983230072969 + 3 ^ 40 * 2977343 * 2
def baseEnd_2977343 : Nat := 1528808032299449865519955

theorem tailTrace_2977343 : CollatzResearch.WordTrace tailWord_2977343 prefixEnd_2977343 1528808032299449865519955 := by
  unfold tailWord_2977343
  simp only [CollatzResearch.WordTrace]
  refine ⟨108592620452602275546576683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72395080301734850364384455 108592620452602275546576683)
  ·
    refine ⟨162888930678903413319865025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108592620452602275546576683 162888930678903413319865025)
    ·
      refine ⟨122166698009177559989898769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162888930678903413319865025 122166698009177559989898769)
      ·
        refine ⟨91625023506883169992424077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122166698009177559989898769 91625023506883169992424077)
        ·
          refine ⟨34359383815081188747159029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91625023506883169992424077 34359383815081188747159029)
          ·
            refine ⟨3221192232663861445046159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34359383815081188747159029 3221192232663861445046159)
            ·
              refine ⟨4831788348995792167569239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3221192232663861445046159 4831788348995792167569239)
              ·
                refine ⟨7247682523493688251353859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4831788348995792167569239 7247682523493688251353859)
                ·
                  refine ⟨10871523785240532377030789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7247682523493688251353859 10871523785240532377030789)
                  ·
                    refine ⟨2038410709732599820693273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10871523785240532377030789 2038410709732599820693273)
                    ·
                      refine ⟨1528808032299449865519955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2038410709732599820693273 1528808032299449865519955)
                      ·
                        rfl

theorem cell23_2977343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 4, 2].length) (baseStart_2977343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977343 prefixEnd_2977343 := by exact prefixLift 2977343
  have htrace : WordTrace (prefixWord ++ tailWord_2977343) baseStart_2977343 baseEnd_2977343 := by
    simpa [prefixWord, tailWord_2977343, baseEnd_2977343] using wordTrace_append hprefix tailTrace_2977343
  have hstable : (prefixWord ++ tailWord_2977343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977343).length < 2 ^ (prefixWord ++ tailWord_2977343).sum := by decide
  have hdescent : baseEnd_2977343 < baseStart_2977343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977379 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 4, 5]
def baseStart_2977379 : Nat := 118140960795 + 2977379 * 2 ^ 59
def prefixEnd_2977379 : Nat := 4983230072969 + 3 ^ 40 * 2977379 * 2
def baseEnd_2977379 : Nat := 509608839201003908223263

theorem tailTrace_2977379 : CollatzResearch.WordTrace tailWord_2977379 prefixEnd_2977379 509608839201003908223263 := by
  unfold tailWord_2977379
  simp only [CollatzResearch.WordTrace]
  refine ⟨108593933480471853694887191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72395955653647902463258127 108593933480471853694887191)
  ·
    refine ⟨162890900220707780542330787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108593933480471853694887191 162890900220707780542330787)
    ·
      refine ⟨244336350331061670813496181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162890900220707780542330787 244336350331061670813496181)
      ·
        refine ⟨22906532843537031638765267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 244336350331061670813496181 22906532843537031638765267)
        ·
          refine ⟨34359799265305547458147901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22906532843537031638765267 34359799265305547458147901)
          ·
            refine ⟨12884924724489580296805463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34359799265305547458147901 12884924724489580296805463)
            ·
              refine ⟨19327387086734370445208195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12884924724489580296805463 19327387086734370445208195)
              ·
                refine ⟨28991080630101555667812293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19327387086734370445208195 28991080630101555667812293)
                ·
                  refine ⟨5435827618144041687714805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28991080630101555667812293 5435827618144041687714805)
                  ·
                    refine ⟨509608839201003908223263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5435827618144041687714805 509608839201003908223263)
                    ·
                      rfl

theorem cell23_2977379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 5].length) (baseStart_2977379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977379 prefixEnd_2977379 := by exact prefixLift 2977379
  have htrace : WordTrace (prefixWord ++ tailWord_2977379) baseStart_2977379 baseEnd_2977379 := by
    simpa [prefixWord, tailWord_2977379, baseEnd_2977379] using wordTrace_append hprefix tailTrace_2977379
  have hstable : (prefixWord ++ tailWord_2977379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977379).length < 2 ^ (prefixWord ++ tailWord_2977379).sum := by decide
  have hdescent : baseEnd_2977379 < baseStart_2977379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977399 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 4]
def baseStart_2977399 : Nat := 118140960795 + 2977399 * 2 ^ 59
def prefixEnd_2977399 : Nat := 4983230072969 + 3 ^ 40 * 2977399 * 2
def baseEnd_2977399 : Nat := 1528836787216101646419697

theorem tailTrace_2977399 : CollatzResearch.WordTrace tailWord_2977399 prefixEnd_2977399 1528836787216101646419697 := by
  unfold tailWord_2977399
  simp only [CollatzResearch.WordTrace]
  refine ⟨108594662940399397110615251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72396441960266264740410167 108594662940399397110615251)
  ·
    refine ⟨162891994410599095665922877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108594662940399397110615251 162891994410599095665922877)
    ·
      refine ⟨61084497903974660874721079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162891994410599095665922877 61084497903974660874721079)
      ·
        refine ⟨91626746855961991312081619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61084497903974660874721079 91626746855961991312081619)
        ·
          refine ⟨137440120283942986968122429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91626746855961991312081619 137440120283942986968122429)
          ·
            refine ⟨51540045106478620113045911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137440120283942986968122429 51540045106478620113045911)
            ·
              refine ⟨77310067659717930169568867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51540045106478620113045911 77310067659717930169568867)
              ·
                refine ⟨115965101489576895254353301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77310067659717930169568867 115965101489576895254353301)
                ·
                  refine ⟨5435864132323916965047811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115965101489576895254353301 5435864132323916965047811)
                  ·
                    refine ⟨8153796198485875447571717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5435864132323916965047811 8153796198485875447571717)
                    ·
                      refine ⟨1528836787216101646419697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8153796198485875447571717 1528836787216101646419697)
                      ·
                        rfl

theorem cell23_2977399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_2977399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977399 prefixEnd_2977399 := by exact prefixLift 2977399
  have htrace : WordTrace (prefixWord ++ tailWord_2977399) baseStart_2977399 baseEnd_2977399 := by
    simpa [prefixWord, tailWord_2977399, baseEnd_2977399] using wordTrace_append hprefix tailTrace_2977399
  have hstable : (prefixWord ++ tailWord_2977399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977399).length < 2 ^ (prefixWord ++ tailWord_2977399).sum := by decide
  have hdescent : baseEnd_2977399 < baseStart_2977399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977443 : List Nat := [1, 1, 1, 4, 1, 1, 5, 4, 1, 4]
def baseStart_2977443 : Nat := 118140960795 + 2977443 * 2 ^ 59
def prefixEnd_2977443 : Nat := 4983230072969 + 3 ^ 40 * 2977443 * 2
def baseEnd_2977443 : Nat := 509619793454966491423165

theorem tailTrace_2977443 : CollatzResearch.WordTrace tailWord_2977443 prefixEnd_2977443 509619793454966491423165 := by
  unfold tailWord_2977443
  simp only [CollatzResearch.WordTrace]
  refine ⟨108596267752239992625216983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72397511834826661750144655 108596267752239992625216983)
  ·
    refine ⟨162894401628359988937825475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108596267752239992625216983 162894401628359988937825475)
    ·
      refine ⟨244341602442539983406738213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162894401628359988937825475 244341602442539983406738213)
      ·
        refine ⟨45814050457976246888763415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244341602442539983406738213 45814050457976246888763415)
        ·
          refine ⟨68721075686964370333145123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45814050457976246888763415 68721075686964370333145123)
          ·
            refine ⟨103081613530446555499717685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68721075686964370333145123 103081613530446555499717685)
            ·
              refine ⟨9663901268479364578098533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103081613530446555499717685 9663901268479364578098533)
              ·
                refine ⟨1811981487839880858393475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9663901268479364578098533 1811981487839880858393475)
                ·
                  refine ⟨2717972231759821287590213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811981487839880858393475 2717972231759821287590213)
                  ·
                    refine ⟨509619793454966491423165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2717972231759821287590213 509619793454966491423165)
                    ·
                      rfl

theorem cell23_2977443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 1, 4].length) (baseStart_2977443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977443 prefixEnd_2977443 := by exact prefixLift 2977443
  have htrace : WordTrace (prefixWord ++ tailWord_2977443) baseStart_2977443 baseEnd_2977443 := by
    simpa [prefixWord, tailWord_2977443, baseEnd_2977443] using wordTrace_append hprefix tailTrace_2977443
  have hstable : (prefixWord ++ tailWord_2977443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977443).length < 2 ^ (prefixWord ++ tailWord_2977443).sum := by decide
  have hdescent : baseEnd_2977443 < baseStart_2977443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977470 : List Nat := [4, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_2977470 : Nat := 118140960795 + 2977470 * 2 ^ 59
def prefixEnd_2977470 : Nat := 4983230072969 + 3 ^ 40 * 2977470 * 2
def baseEnd_2977470 : Nat := 1528873244342570868631871

theorem tailTrace_2977470 : CollatzResearch.WordTrace tailWord_2977470 prefixEnd_2977470 1528873244342570868631871 := by
  unfold tailWord_2977470
  simp only [CollatzResearch.WordTrace]
  refine ⟨13574656565392772029556233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72398168348761450824299909 13574656565392772029556233)
  ·
    refine ⟨10180992424044579022167175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13574656565392772029556233 10180992424044579022167175)
    ·
      refine ⟨15271488636066868533250763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10180992424044579022167175 15271488636066868533250763)
      ·
        refine ⟨22907232954100302799876145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15271488636066868533250763 22907232954100302799876145)
        ·
          refine ⟨17180424715575227099907109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22907232954100302799876145 17180424715575227099907109)
          ·
            refine ⟨3221329634170355081232583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17180424715575227099907109 3221329634170355081232583)
            ·
              refine ⟨4831994451255532621848875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3221329634170355081232583 4831994451255532621848875)
              ·
                refine ⟨7247991676883298932773313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4831994451255532621848875 7247991676883298932773313)
                ·
                  refine ⟨5435993757662474199579985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7247991676883298932773313 5435993757662474199579985)
                  ·
                    refine ⟨4076995318246855649684989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5435993757662474199579985 4076995318246855649684989)
                    ·
                      refine ⟨1528873244342570868631871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4076995318246855649684989 1528873244342570868631871)
                      ·
                        rfl

theorem cell23_2977470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_2977470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977470 prefixEnd_2977470 := by exact prefixLift 2977470
  have htrace : WordTrace (prefixWord ++ tailWord_2977470) baseStart_2977470 baseEnd_2977470 := by
    simpa [prefixWord, tailWord_2977470, baseEnd_2977470] using wordTrace_append hprefix tailTrace_2977470
  have hstable : (prefixWord ++ tailWord_2977470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977470).length < 2 ^ (prefixWord ++ tailWord_2977470).sum := by decide
  have hdescent : baseEnd_2977470 < baseStart_2977470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977516 : List Nat := [2, 2, 1, 1, 2, 2, 5, 1, 1, 6]
def baseStart_2977516 : Nat := 118140960795 + 2977516 * 2 ^ 59
def prefixEnd_2977516 : Nat := 4983230072969 + 3 ^ 40 * 2977516 * 2
def baseEnd_2977516 : Nat := 509632288150892562885553

theorem tailTrace_2977516 : CollatzResearch.WordTrace tailWord_2977516 prefixEnd_2977516 509632288150892562885553 := by
  unfold tailWord_2977516
  simp only [CollatzResearch.WordTrace]
  refine ⟨54299465140487763046312201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72399286853983684061749601 54299465140487763046312201)
  ·
    refine ⟨40724598855365822284734151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54299465140487763046312201 40724598855365822284734151)
    ·
      refine ⟨61086898283048733427101227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40724598855365822284734151 61086898283048733427101227)
      ·
        refine ⟨91630347424573100140651841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61086898283048733427101227 91630347424573100140651841)
        ·
          refine ⟨68722760568429825105488881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91630347424573100140651841 68722760568429825105488881)
          ·
            refine ⟨51542070426322368829116661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68722760568429825105488881 51542070426322368829116661)
            ·
              refine ⟨4832069102467722077729687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51542070426322368829116661 4832069102467722077729687)
              ·
                refine ⟨7248103653701583116594531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4832069102467722077729687 7248103653701583116594531)
                ·
                  refine ⟨10872155480552374674891797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7248103653701583116594531 10872155480552374674891797)
                  ·
                    refine ⟨509632288150892562885553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10872155480552374674891797 509632288150892562885553)
                    ·
                      rfl

theorem cell23_2977516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_2977516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977516 prefixEnd_2977516 := by exact prefixLift 2977516
  have htrace : WordTrace (prefixWord ++ tailWord_2977516) baseStart_2977516 baseEnd_2977516 := by
    simpa [prefixWord, tailWord_2977516, baseEnd_2977516] using wordTrace_append hprefix tailTrace_2977516
  have hstable : (prefixWord ++ tailWord_2977516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977516).length < 2 ^ (prefixWord ++ tailWord_2977516).sum := by decide
  have hdescent : baseEnd_2977516 < baseStart_2977516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977546 : List Nat := [3, 1, 2, 2, 1, 5, 9]
def baseStart_2977546 : Nat := 118140960795 + 2977546 * 2 ^ 59
def prefixEnd_2977546 : Nat := 4983230072969 + 3 ^ 40 * 2977546 * 2
def baseEnd_2977546 : Nat := 18875460109534723102241

theorem tailTrace_2977546 : CollatzResearch.WordTrace tailWord_2977546 prefixEnd_2977546 18875460109534723102241 := by
  unfold tailWord_2977546
  simp only [CollatzResearch.WordTrace]
  refine ⟨27150006117716710304054123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72400016313911227477477661 27150006117716710304054123)
  ·
    refine ⟨40725009176575065456081185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27150006117716710304054123 40725009176575065456081185)
    ·
      refine ⟨30543756882431299092060889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40725009176575065456081185 30543756882431299092060889)
      ·
        refine ⟨22907817661823474319045667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30543756882431299092060889 22907817661823474319045667)
        ·
          refine ⟨34361726492735211478568501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22907817661823474319045667 34361726492735211478568501)
          ·
            refine ⟨3221411858693926076115797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34361726492735211478568501 3221411858693926076115797)
            ·
              refine ⟨18875460109534723102241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3221411858693926076115797 18875460109534723102241)
              ·
                rfl

theorem cell23_2977546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 9].length) (baseStart_2977546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977546 prefixEnd_2977546 := by exact prefixLift 2977546
  have htrace : WordTrace (prefixWord ++ tailWord_2977546) baseStart_2977546 baseEnd_2977546 := by
    simpa [prefixWord, tailWord_2977546, baseEnd_2977546] using wordTrace_append hprefix tailTrace_2977546
  have hstable : (prefixWord ++ tailWord_2977546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977546).length < 2 ^ (prefixWord ++ tailWord_2977546).sum := by decide
  have hdescent : baseEnd_2977546 < baseStart_2977546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977557 : List Nat := [1, 3, 2, 1, 2, 5, 1, 1, 3, 2, 2]
def baseStart_2977557 : Nat := 118140960795 + 2977557 * 2 ^ 59
def prefixEnd_2977557 : Nat := 4983230072969 + 3 ^ 40 * 2977557 * 2
def baseEnd_2977557 : Nat := 1528917917159512028243971

theorem tailTrace_2977557 : CollatzResearch.WordTrace tailWord_2977557 prefixEnd_2977557 1528917917159512028243971 := by
  unfold tailWord_2977557
  simp only [CollatzResearch.WordTrace]
  refine ⟨108600425673826990094866925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72400283782551326729911283 108600425673826990094866925)
  ·
    refine ⟨40725159627685121285575097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108600425673826990094866925 40725159627685121285575097)
    ·
      refine ⟨30543869720763840964181323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40725159627685121285575097 30543869720763840964181323)
      ·
        refine ⟨45815804581145761446271985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30543869720763840964181323 45815804581145761446271985)
        ·
          refine ⟨34361853435859321084703989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45815804581145761446271985 34361853435859321084703989)
          ·
            refine ⟨3221423759611811351690999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34361853435859321084703989 3221423759611811351690999)
            ·
              refine ⟨4832135639417717027536499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3221423759611811351690999 4832135639417717027536499)
              ·
                refine ⟨7248203459126575541304749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4832135639417717027536499 7248203459126575541304749)
                ·
                  refine ⟨2718076297172465827989281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7248203459126575541304749 2718076297172465827989281)
                  ·
                    refine ⟨2038557222879349370991961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2718076297172465827989281 2038557222879349370991961)
                    ·
                      refine ⟨1528917917159512028243971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2038557222879349370991961 1528917917159512028243971)
                      ·
                        rfl

theorem cell23_2977557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_2977557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977557 prefixEnd_2977557 := by exact prefixLift 2977557
  have htrace : WordTrace (prefixWord ++ tailWord_2977557) baseStart_2977557 baseEnd_2977557 := by
    simpa [prefixWord, tailWord_2977557, baseEnd_2977557] using wordTrace_append hprefix tailTrace_2977557
  have hstable : (prefixWord ++ tailWord_2977557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977557).length < 2 ^ (prefixWord ++ tailWord_2977557).sum := by decide
  have hdescent : baseEnd_2977557 < baseStart_2977557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977583 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 3, 3, 2]
def baseStart_2977583 : Nat := 118140960795 + 2977583 * 2 ^ 59
def prefixEnd_2977583 : Nat := 4983230072969 + 3 ^ 40 * 2977583 * 2
def baseEnd_2977583 : Nat := 1528931267656528926518851

theorem tailTrace_2977583 : CollatzResearch.WordTrace tailWord_2977583 prefixEnd_2977583 1528931267656528926518851 := by
  unfold tailWord_2977583
  simp only [CollatzResearch.WordTrace]
  refine ⟨108601373971732796535313403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72400915981155197690208935 108601373971732796535313403)
  ·
    refine ⟨162902060957599194802970105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108601373971732796535313403 162902060957599194802970105)
    ·
      refine ⟨122176545718199396102227579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162902060957599194802970105 122176545718199396102227579)
      ·
        refine ⟨183264818577299094153341369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122176545718199396102227579 183264818577299094153341369)
        ·
          refine ⟨137448613932974320615006027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183264818577299094153341369 137448613932974320615006027)
          ·
            refine ⟨206172920899461480922509041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137448613932974320615006027 206172920899461480922509041)
            ·
              refine ⟨154629690674596110691881781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206172920899461480922509041 154629690674596110691881781)
              ·
                refine ⟨14496533500743385377363917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 154629690674596110691881781 14496533500743385377363917)
                ·
                  refine ⟨5436200062778769516511469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14496533500743385377363917 5436200062778769516511469)
                  ·
                    refine ⟨2038575023542038568691801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5436200062778769516511469 2038575023542038568691801)
                    ·
                      refine ⟨1528931267656528926518851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2038575023542038568691801 1528931267656528926518851)
                      ·
                        rfl

theorem cell23_2977583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 3, 2].length) (baseStart_2977583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977583 prefixEnd_2977583 := by exact prefixLift 2977583
  have htrace : WordTrace (prefixWord ++ tailWord_2977583) baseStart_2977583 baseEnd_2977583 := by
    simpa [prefixWord, tailWord_2977583, baseEnd_2977583] using wordTrace_append hprefix tailTrace_2977583
  have hstable : (prefixWord ++ tailWord_2977583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977583).length < 2 ^ (prefixWord ++ tailWord_2977583).sum := by decide
  have hdescent : baseEnd_2977583 < baseStart_2977583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977590 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_2977590 : Nat := 118140960795 + 2977590 * 2 ^ 59
def prefixEnd_2977590 : Nat := 4983230072969 + 3 ^ 40 * 2977590 * 2
def baseEnd_2977590 : Nat := 1528934862021110399131319

theorem tailTrace_2977590 : CollatzResearch.WordTrace tailWord_2977590 prefixEnd_2977590 1528934862021110399131319 := by
  unfold tailWord_2977590
  simp only [CollatzResearch.WordTrace]
  refine ⟨6787601830169214795676139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72401086188471624487212149 6787601830169214795676139)
  ·
    refine ⟨10181402745253822193514209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6787601830169214795676139 10181402745253822193514209)
    ·
      refine ⟨7636052058940366645135657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10181402745253822193514209 7636052058940366645135657)
      ·
        refine ⟨5727039044205274983851743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7636052058940366645135657 5727039044205274983851743)
        ·
          refine ⟨8590558566307912475777615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5727039044205274983851743 8590558566307912475777615)
          ·
            refine ⟨12885837849461868713666423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8590558566307912475777615 12885837849461868713666423)
            ·
              refine ⟨19328756774192803070499635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12885837849461868713666423 19328756774192803070499635)
              ·
                refine ⟨28993135161289204605749453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19328756774192803070499635 28993135161289204605749453)
                ·
                  refine ⟨10872425685483451727156045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28993135161289204605749453 10872425685483451727156045)
                  ·
                    refine ⟨4077159632056294397683517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10872425685483451727156045 4077159632056294397683517)
                    ·
                      refine ⟨1528934862021110399131319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4077159632056294397683517 1528934862021110399131319)
                      ·
                        rfl

theorem cell23_2977590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_2977590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977590 prefixEnd_2977590 := by exact prefixLift 2977590
  have htrace : WordTrace (prefixWord ++ tailWord_2977590) baseStart_2977590 baseEnd_2977590 := by
    simpa [prefixWord, tailWord_2977590, baseEnd_2977590] using wordTrace_append hprefix tailTrace_2977590
  have hstable : (prefixWord ++ tailWord_2977590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977590).length < 2 ^ (prefixWord ++ tailWord_2977590).sum := by decide
  have hdescent : baseEnd_2977590 < baseStart_2977590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977623 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 2, 6]
def baseStart_2977623 : Nat := 118140960795 + 2977623 * 2 ^ 59
def prefixEnd_2977623 : Nat := 4983230072969 + 3 ^ 40 * 2977623 * 2
def baseEnd_2977623 : Nat := 509650602294236256672889

theorem tailTrace_2977623 : CollatzResearch.WordTrace tailWord_2977623 prefixEnd_2977623 509650602294236256672889 := by
  unfold tailWord_2977623
  simp only [CollatzResearch.WordTrace]
  refine ⟨108602832891587883366769523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72401888594391922244513015 108602832891587883366769523)
  ·
    refine ⟨162904249337381825050154285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108602832891587883366769523 162904249337381825050154285)
    ·
      refine ⟨61089093501518184393807857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162904249337381825050154285 61089093501518184393807857)
      ·
        refine ⟨45816820126138638295355893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61089093501518184393807857 45816820126138638295355893)
        ·
          refine ⟨4295326886825497340189615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45816820126138638295355893 4295326886825497340189615)
          ·
            refine ⟨6442990330238246010284423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4295326886825497340189615 6442990330238246010284423)
            ·
              refine ⟨9664485495357369015426635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6442990330238246010284423 9664485495357369015426635)
              ·
                refine ⟨14496728243036053523139953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9664485495357369015426635 14496728243036053523139953)
                ·
                  refine ⟨10872546182277040142354965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14496728243036053523139953 10872546182277040142354965)
                  ·
                    refine ⟨509650602294236256672889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10872546182277040142354965 509650602294236256672889)
                    ·
                      rfl

theorem cell23_2977623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_2977623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977623 prefixEnd_2977623 := by exact prefixLift 2977623
  have htrace : WordTrace (prefixWord ++ tailWord_2977623) baseStart_2977623 baseEnd_2977623 := by
    simpa [prefixWord, tailWord_2977623, baseEnd_2977623] using wordTrace_append hprefix tailTrace_2977623
  have hstable : (prefixWord ++ tailWord_2977623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977623).length < 2 ^ (prefixWord ++ tailWord_2977623).sum := by decide
  have hdescent : baseEnd_2977623 < baseStart_2977623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977676 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 1, 1, 7]
def baseStart_2977676 : Nat := 118140960795 + 2977676 * 2 ^ 59
def prefixEnd_2977676 : Nat := 4983230072969 + 3 ^ 40 * 2977676 * 2
def baseEnd_2977676 : Nat := 1528979021357397062655923

theorem tailTrace_2977676 : CollatzResearch.WordTrace tailWord_2977676 prefixEnd_2977676 1528979021357397062655923 := by
  unfold tailWord_2977676
  simp only [CollatzResearch.WordTrace]
  refine ⟨54302382980197936709224441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72403177306930582278965921 54302382980197936709224441)
  ·
    refine ⟨40726787235148452531918331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54302382980197936709224441 40726787235148452531918331)
    ·
      refine ⟨61090180852722678797877497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40726787235148452531918331 61090180852722678797877497)
      ·
        refine ⟨45817635639542009098408123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61090180852722678797877497 45817635639542009098408123)
        ·
          refine ⟨68726453459313013647612185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45817635639542009098408123 68726453459313013647612185)
          ·
            refine ⟨51544840094484760235709139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68726453459313013647612185 51544840094484760235709139)
            ·
              refine ⟨77317260141727140353563709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51544840094484760235709139 77317260141727140353563709)
              ·
                refine ⟨28993972553147677632586391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77317260141727140353563709 28993972553147677632586391)
                ·
                  refine ⟨43490958829721516448879587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28993972553147677632586391 43490958829721516448879587)
                  ·
                    refine ⟨65236438244582274673319381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43490958829721516448879587 65236438244582274673319381)
                    ·
                      refine ⟨1528979021357397062655923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65236438244582274673319381 1528979021357397062655923)
                      ·
                        rfl

theorem cell23_2977676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_2977676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977676 prefixEnd_2977676 := by exact prefixLift 2977676
  have htrace : WordTrace (prefixWord ++ tailWord_2977676) baseStart_2977676 baseEnd_2977676 := by
    simpa [prefixWord, tailWord_2977676, baseEnd_2977676] using wordTrace_append hprefix tailTrace_2977676
  have hstable : (prefixWord ++ tailWord_2977676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977676).length < 2 ^ (prefixWord ++ tailWord_2977676).sum := by decide
  have hdescent : baseEnd_2977676 < baseStart_2977676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977696 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 1, 10]
def baseStart_2977696 : Nat := 118140960795 + 2977696 * 2 ^ 59
def prefixEnd_2977696 : Nat := 4983230072969 + 3 ^ 40 * 2977696 * 2
def baseEnd_2977696 : Nat := 509663096990162328135277

theorem tailTrace_2977696 : CollatzResearch.WordTrace tailWord_2977696 prefixEnd_2977696 509663096990162328135277 := by
  unfold tailWord_2977696
  simp only [CollatzResearch.WordTrace]
  refine ⟨54302747710161708417088471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72403663613548944556117961 54302747710161708417088471)
  ·
    refine ⟨81454121565242562625632707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54302747710161708417088471 81454121565242562625632707)
    ·
      refine ⟨122181182347863843938449061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81454121565242562625632707 122181182347863843938449061)
      ·
        refine ⟨22908971690224470738459199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122181182347863843938449061 22908971690224470738459199)
        ·
          refine ⟨34363457535336706107688799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22908971690224470738459199 34363457535336706107688799)
          ·
            refine ⟨51545186303005059161533199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34363457535336706107688799 51545186303005059161533199)
            ·
              refine ⟨77317779454507588742299799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51545186303005059161533199 77317779454507588742299799)
              ·
                refine ⟨115976669181761383113449699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77317779454507588742299799 115976669181761383113449699)
                ·
                  refine ⟨173965003772642074670174549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115976669181761383113449699 173965003772642074670174549)
                  ·
                    refine ⟨509663096990162328135277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 173965003772642074670174549 509663096990162328135277)
                    ·
                      rfl

theorem cell23_2977696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 10].length) (baseStart_2977696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977696 prefixEnd_2977696 := by exact prefixLift 2977696
  have htrace : WordTrace (prefixWord ++ tailWord_2977696) baseStart_2977696 baseEnd_2977696 := by
    simpa [prefixWord, tailWord_2977696, baseEnd_2977696] using wordTrace_append hprefix tailTrace_2977696
  have hstable : (prefixWord ++ tailWord_2977696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977696).length < 2 ^ (prefixWord ++ tailWord_2977696).sum := by decide
  have hdescent : baseEnd_2977696 < baseStart_2977696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977723 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 3]
def baseStart_2977723 : Nat := 118140960795 + 2977723 * 2 ^ 59
def prefixEnd_2977723 : Nat := 4983230072969 + 3 ^ 40 * 2977723 * 2
def baseEnd_2977723 : Nat := 1529003154948158378768207

theorem tailTrace_2977723 : CollatzResearch.WordTrace tailWord_2977723 prefixEnd_2977723 1529003154948158378768207 := by
  unfold tailWord_2977723
  simp only [CollatzResearch.WordTrace]
  refine ⟨108606480191225600445409823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72404320127483733630273215 108606480191225600445409823)
  ·
    refine ⟨162909720286838400668114735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108606480191225600445409823 162909720286838400668114735)
    ·
      refine ⟨244364580430257601002172103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162909720286838400668114735 244364580430257601002172103)
      ·
        refine ⟨366546870645386401503258155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244364580430257601002172103 366546870645386401503258155)
        ·
          refine ⟨549820305968079602254887233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366546870645386401503258155 549820305968079602254887233)
          ·
            refine ⟨412365229476059701691165425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 549820305968079602254887233 412365229476059701691165425)
            ·
              refine ⟨309273922107044776268374069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412365229476059701691165425 309273922107044776268374069)
              ·
                refine ⟨28994430197535447775160069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 309273922107044776268374069 28994430197535447775160069)
                ·
                  refine ⟨5436455662037896457842513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28994430197535447775160069 5436455662037896457842513)
                  ·
                    refine ⟨4077341746528422343381885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5436455662037896457842513 4077341746528422343381885)
                    ·
                      refine ⟨1529003154948158378768207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4077341746528422343381885 1529003154948158378768207)
                      ·
                        rfl

theorem cell23_2977723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 3].length) (baseStart_2977723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977723 prefixEnd_2977723 := by exact prefixLift 2977723
  have htrace : WordTrace (prefixWord ++ tailWord_2977723) baseStart_2977723 baseEnd_2977723 := by
    simpa [prefixWord, tailWord_2977723, baseEnd_2977723] using wordTrace_append hprefix tailTrace_2977723
  have hstable : (prefixWord ++ tailWord_2977723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977723).length < 2 ^ (prefixWord ++ tailWord_2977723).sum := by decide
  have hdescent : baseEnd_2977723 < baseStart_2977723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977743 : List Nat := [1, 1, 2, 1, 1, 5, 3, 3, 6]
def baseStart_2977743 : Nat := 118140960795 + 2977743 * 2 ^ 59
def prefixEnd_2977743 : Nat := 4983230072969 + 3 ^ 40 * 2977743 * 2
def baseEnd_2977743 : Nat := 169890380506805366724235

theorem tailTrace_2977743 : CollatzResearch.WordTrace tailWord_2977743 prefixEnd_2977743 169890380506805366724235 := by
  unfold tailWord_2977743
  simp only [CollatzResearch.WordTrace]
  refine ⟨108607209651153143861137883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72404806434102095907425255 108607209651153143861137883)
  ·
    refine ⟨162910814476729715791706825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108607209651153143861137883 162910814476729715791706825)
    ·
      refine ⟨122183110857547286843780119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162910814476729715791706825 122183110857547286843780119)
      ·
        refine ⟨183274666286320930265670179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122183110857547286843780119 183274666286320930265670179)
        ·
          refine ⟨274911999429481395398505269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183274666286320930265670179 274911999429481395398505269)
          ·
            refine ⟨25772999946513880818609869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 274911999429481395398505269 25772999946513880818609869)
            ·
              refine ⟨9664874979942705306978701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25772999946513880818609869 9664874979942705306978701)
              ·
                refine ⟨3624328117478514490117013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9664874979942705306978701 3624328117478514490117013)
                ·
                  refine ⟨169890380506805366724235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3624328117478514490117013 169890380506805366724235)
                  ·
                    rfl

theorem cell23_2977743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 6].length) (baseStart_2977743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977743 prefixEnd_2977743 := by exact prefixLift 2977743
  have htrace : WordTrace (prefixWord ++ tailWord_2977743) baseStart_2977743 baseEnd_2977743 := by
    simpa [prefixWord, tailWord_2977743, baseEnd_2977743] using wordTrace_append hprefix tailTrace_2977743
  have hstable : (prefixWord ++ tailWord_2977743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977743).length < 2 ^ (prefixWord ++ tailWord_2977743).sum := by decide
  have hdescent : baseEnd_2977743 < baseStart_2977743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977798 : List Nat := [6, 2, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_2977798 : Nat := 118140960795 + 2977798 * 2 ^ 59
def prefixEnd_2977798 : Nat := 4983230072969 + 3 ^ 40 * 2977798 * 2
def baseEnd_2977798 : Nat := 509680555332415195110121

theorem tailTrace_2977798 : CollatzResearch.WordTrace tailWord_2977798 prefixEnd_2977798 509680555332415195110121 := by
  unfold tailWord_2977798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3394037989561059007949689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72406143777302592169593365 3394037989561059007949689)
  ·
    refine ⟨2545528492170794255962267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3394037989561059007949689 2545528492170794255962267)
    ·
      refine ⟨3818292738256191383943401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2545528492170794255962267 3818292738256191383943401)
      ·
        refine ⟨2863719553692143537957551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3818292738256191383943401 2863719553692143537957551)
        ·
          refine ⟨4295579330538215306936327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2863719553692143537957551 4295579330538215306936327)
          ·
            refine ⟨6443368995807322960404491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4295579330538215306936327 6443368995807322960404491)
            ·
              refine ⟨9665053493710984440606737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6443368995807322960404491 9665053493710984440606737)
              ·
                refine ⟨7248790120283238330455053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9665053493710984440606737 7248790120283238330455053)
                ·
                  refine ⟨2718296295106214373920645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7248790120283238330455053 2718296295106214373920645)
                  ·
                    refine ⟨509680555332415195110121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2718296295106214373920645 509680555332415195110121)
                    ·
                      rfl

theorem cell23_2977798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_2977798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977798 prefixEnd_2977798 := by exact prefixLift 2977798
  have htrace : WordTrace (prefixWord ++ tailWord_2977798) baseStart_2977798 baseEnd_2977798 := by
    simpa [prefixWord, tailWord_2977798, baseEnd_2977798] using wordTrace_append hprefix tailTrace_2977798
  have hstable : (prefixWord ++ tailWord_2977798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977798).length < 2 ^ (prefixWord ++ tailWord_2977798).sum := by decide
  have hdescent : baseEnd_2977798 < baseStart_2977798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977820 : List Nat := [2, 2, 3, 1, 3, 1, 2, 2, 1, 6]
def baseStart_2977820 : Nat := 118140960795 + 2977820 * 2 ^ 59
def prefixEnd_2977820 : Nat := 4983230072969 + 3 ^ 40 * 2977820 * 2
def baseEnd_2977820 : Nat := 509684320857214833085087

theorem tailTrace_2977820 : CollatzResearch.WordTrace tailWord_2977820 prefixEnd_2977820 509684320857214833085087 := by
  unfold tailWord_2977820
  simp only [CollatzResearch.WordTrace]
  refine ⟨54305009035937093005845457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72406678714582790674460609 54305009035937093005845457)
  ·
    refine ⟨40728756776952819754384093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54305009035937093005845457 40728756776952819754384093)
    ·
      refine ⟨15273283791357307407894035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40728756776952819754384093 15273283791357307407894035)
      ·
        refine ⟨22909925687035961111841053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15273283791357307407894035 22909925687035961111841053)
        ·
          refine ⟨8591222132638485416940395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22909925687035961111841053 8591222132638485416940395)
          ·
            refine ⟨12886833198957728125410593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8591222132638485416940395 12886833198957728125410593)
            ·
              refine ⟨9665124899218296094057945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12886833198957728125410593 9665124899218296094057945)
              ·
                refine ⟨7248843674413722070543459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9665124899218296094057945 7248843674413722070543459)
                ·
                  refine ⟨10873265511620583105815189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7248843674413722070543459 10873265511620583105815189)
                  ·
                    refine ⟨509684320857214833085087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10873265511620583105815189 509684320857214833085087)
                    ·
                      rfl

theorem cell23_2977820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_2977820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977820 prefixEnd_2977820 := by exact prefixLift 2977820
  have htrace : WordTrace (prefixWord ++ tailWord_2977820) baseStart_2977820 baseEnd_2977820 := by
    simpa [prefixWord, tailWord_2977820, baseEnd_2977820] using wordTrace_append hprefix tailTrace_2977820
  have hstable : (prefixWord ++ tailWord_2977820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977820).length < 2 ^ (prefixWord ++ tailWord_2977820).sum := by decide
  have hdescent : baseEnd_2977820 < baseStart_2977820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977821 : List Nat := [1, 4, 2, 2, 2, 2, 2, 3, 1, 1, 3]
def baseStart_2977821 : Nat := 118140960795 + 2977821 * 2 ^ 59
def prefixEnd_2977821 : Nat := 4983230072969 + 3 ^ 40 * 2977821 * 2
def baseEnd_2977821 : Nat := 1529053476052298995342757

theorem tailTrace_2977821 : CollatzResearch.WordTrace tailWord_2977821 prefixEnd_2977821 1529053476052298995342757 := by
  unfold tailWord_2977821
  simp only [CollatzResearch.WordTrace]
  refine ⟨108610054544870563182477317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72406703029913708788318211 108610054544870563182477317)
  ·
    refine ⟨20364385227163230596714497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108610054544870563182477317 20364385227163230596714497)
    ·
      refine ⟨15273288920372422947535873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20364385227163230596714497 15273288920372422947535873)
      ·
        refine ⟨11454966690279317210651905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15273288920372422947535873 11454966690279317210651905)
        ·
          refine ⟨8591225017709487907988929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11454966690279317210651905 8591225017709487907988929)
          ·
            refine ⟨6443418763282115930991697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8591225017709487907988929 6443418763282115930991697)
            ·
              refine ⟨4832564072461586948243773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6443418763282115930991697 4832564072461586948243773)
              ·
                refine ⟨1812211527173095105591415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4832564072461586948243773 1812211527173095105591415)
                ·
                  refine ⟨2718317290759642658387123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1812211527173095105591415 2718317290759642658387123)
                  ·
                    refine ⟨4077475936139463987580685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2718317290759642658387123 4077475936139463987580685)
                    ·
                      refine ⟨1529053476052298995342757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4077475936139463987580685 1529053476052298995342757)
                      ·
                        rfl

theorem cell23_2977821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_2977821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977821 prefixEnd_2977821 := by exact prefixLift 2977821
  have htrace : WordTrace (prefixWord ++ tailWord_2977821) baseStart_2977821 baseEnd_2977821 := by
    simpa [prefixWord, tailWord_2977821, baseEnd_2977821] using wordTrace_append hprefix tailTrace_2977821
  have hstable : (prefixWord ++ tailWord_2977821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977821).length < 2 ^ (prefixWord ++ tailWord_2977821).sum := by decide
  have hdescent : baseEnd_2977821 < baseStart_2977821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977827 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 5, 2, 2]
def baseStart_2977827 : Nat := 118140960795 + 2977827 * 2 ^ 59
def prefixEnd_2977827 : Nat := 4983230072969 + 3 ^ 40 * 2977827 * 2
def baseEnd_2977827 : Nat := 1529056556936225971867729

theorem tailTrace_2977827 : CollatzResearch.WordTrace tailWord_2977827 prefixEnd_2977827 1529056556936225971867729 := by
  unfold tailWord_2977827
  simp only [CollatzResearch.WordTrace]
  refine ⟨108610273382848826207195735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72406848921899217471463823 108610273382848826207195735)
  ·
    refine ⟨162915410074273239310793603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108610273382848826207195735 162915410074273239310793603)
    ·
      refine ⟨244373115111409858966190405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162915410074273239310793603 244373115111409858966190405)
      ·
        refine ⟨45819959083389348556160701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244373115111409858966190405 45819959083389348556160701)
        ·
          refine ⟨17182484656271005708560263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45819959083389348556160701 17182484656271005708560263)
          ·
            refine ⟨25773726984406508562840395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17182484656271005708560263 25773726984406508562840395)
            ·
              refine ⟨38660590476609762844260593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25773726984406508562840395 38660590476609762844260593)
              ·
                refine ⟨28995442857457322133195445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38660590476609762844260593 28995442857457322133195445)
                ·
                  refine ⟨2718322767886623949987073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28995442857457322133195445 2718322767886623949987073)
                  ·
                    refine ⟨2038742075914967962490305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2718322767886623949987073 2038742075914967962490305)
                    ·
                      refine ⟨1529056556936225971867729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2038742075914967962490305 1529056556936225971867729)
                      ·
                        rfl

theorem cell23_2977827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_2977827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977827 prefixEnd_2977827 := by exact prefixLift 2977827
  have htrace : WordTrace (prefixWord ++ tailWord_2977827) baseStart_2977827 baseEnd_2977827 := by
    simpa [prefixWord, tailWord_2977827, baseEnd_2977827] using wordTrace_append hprefix tailTrace_2977827
  have hstable : (prefixWord ++ tailWord_2977827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977827).length < 2 ^ (prefixWord ++ tailWord_2977827).sum := by decide
  have hdescent : baseEnd_2977827 < baseStart_2977827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977854 : List Nat := [4, 2, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_2977854 : Nat := 118140960795 + 2977854 * 2 ^ 59
def prefixEnd_2977854 : Nat := 4983230072969 + 3 ^ 40 * 2977854 * 2
def baseEnd_2977854 : Nat := 509690140304632455410035

theorem tailTrace_2977854 : CollatzResearch.WordTrace tailWord_2977854 prefixEnd_2977854 509690140304632455410035 := by
  unfold tailWord_2977854
  simp only [CollatzResearch.WordTrace]
  refine ⟨13576407269218876227303577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72407505435834006545619077 13576407269218876227303577)
  ·
    refine ⟨10182305451914157170477683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13576407269218876227303577 10182305451914157170477683)
    ·
      refine ⟨15273458177871235755716525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10182305451914157170477683 15273458177871235755716525)
      ·
        refine ⟨5727546816701713408393697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15273458177871235755716525 5727546816701713408393697)
        ·
          refine ⟨4295660112526285056295273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5727546816701713408393697 4295660112526285056295273)
          ·
            refine ⟨3221745084394713792221455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4295660112526285056295273 3221745084394713792221455)
            ·
              refine ⟨4832617626592070688332183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3221745084394713792221455 4832617626592070688332183)
              ·
                refine ⟨7248926439888106032498275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4832617626592070688332183 7248926439888106032498275)
                ·
                  refine ⟨10873389659832159048747413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7248926439888106032498275 10873389659832159048747413)
                  ·
                    refine ⟨509690140304632455410035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10873389659832159048747413 509690140304632455410035)
                    ·
                      rfl

theorem cell23_2977854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_2977854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977854 prefixEnd_2977854 := by exact prefixLift 2977854
  have htrace : WordTrace (prefixWord ++ tailWord_2977854) baseStart_2977854 baseEnd_2977854 := by
    simpa [prefixWord, tailWord_2977854, baseEnd_2977854] using wordTrace_append hprefix tailTrace_2977854
  have hstable : (prefixWord ++ tailWord_2977854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977854).length < 2 ^ (prefixWord ++ tailWord_2977854).sum := by decide
  have hdescent : baseEnd_2977854 < baseStart_2977854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977857 : List Nat := [1, 2, 5, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_2977857 : Nat := 118140960795 + 2977857 * 2 ^ 59
def prefixEnd_2977857 : Nat := 4983230072969 + 3 ^ 40 * 2977857 * 2
def baseEnd_2977857 : Nat := 1529071961355860854492591

theorem tailTrace_2977857 : CollatzResearch.WordTrace tailWord_2977857 prefixEnd_2977857 1529071961355860854492591 := by
  unfold tailWord_2977857
  simp only [CollatzResearch.WordTrace]
  refine ⟨108611367572740141330787825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72407578381826760887191883 108611367572740141330787825)
  ·
    refine ⟨81458525679555105998090869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108611367572740141330787825 81458525679555105998090869)
    ·
      refine ⟨7636736782458291187321019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81458525679555105998090869 7636736782458291187321019)
      ·
        refine ⟨11455105173687436780981529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7636736782458291187321019 11455105173687436780981529)
        ·
          refine ⟨8591328880265577585736147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11455105173687436780981529 8591328880265577585736147)
          ·
            refine ⟨12886993320398366378604221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8591328880265577585736147 12886993320398366378604221)
            ·
              refine ⟨4832622495149387391976583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12886993320398366378604221 4832622495149387391976583)
              ·
                refine ⟨7248933742724081087964875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4832622495149387391976583 7248933742724081087964875)
                ·
                  refine ⟨10873400614086121631947313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7248933742724081087964875 10873400614086121631947313)
                  ·
                    refine ⟨8155050460564591223960485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10873400614086121631947313 8155050460564591223960485)
                    ·
                      refine ⟨1529071961355860854492591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8155050460564591223960485 1529071961355860854492591)
                      ·
                        rfl

theorem cell23_2977857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_2977857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977857 prefixEnd_2977857 := by exact prefixLift 2977857
  have htrace : WordTrace (prefixWord ++ tailWord_2977857) baseStart_2977857 baseEnd_2977857 := by
    simpa [prefixWord, tailWord_2977857, baseEnd_2977857] using wordTrace_append hprefix tailTrace_2977857
  have hstable : (prefixWord ++ tailWord_2977857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977857).length < 2 ^ (prefixWord ++ tailWord_2977857).sum := by decide
  have hdescent : baseEnd_2977857 < baseStart_2977857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977877 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 4, 1, 3]
def baseStart_2977877 : Nat := 118140960795 + 2977877 * 2 ^ 59
def prefixEnd_2977877 : Nat := 4983230072969 + 3 ^ 40 * 2977877 * 2
def baseEnd_2977877 : Nat := 1529082230968950776242499

theorem tailTrace_2977877 : CollatzResearch.WordTrace tailWord_2977877 prefixEnd_2977877 1529082230968950776242499 := by
  unfold tailWord_2977877
  simp only [CollatzResearch.WordTrace]
  refine ⟨108612097032667684746515885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72408064688445123164343923 108612097032667684746515885)
  ·
    refine ⟨40729536387250381779943457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108612097032667684746515885 40729536387250381779943457)
    ·
      refine ⟨30547152290437786334957593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40729536387250381779943457 30547152290437786334957593)
      ·
        refine ⟨22910364217828339751218195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30547152290437786334957593 22910364217828339751218195)
        ·
          refine ⟨34365546326742509626827293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22910364217828339751218195 34365546326742509626827293)
          ·
            refine ⟨12887079872528441110060235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34365546326742509626827293 12887079872528441110060235)
            ·
              refine ⟨19330619808792661665090353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12887079872528441110060235 19330619808792661665090353)
              ·
                refine ⟨14497964856594496248817765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19330619808792661665090353 14497964856594496248817765)
                ·
                  refine ⟨2718368410611468046653331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14497964856594496248817765 2718368410611468046653331)
                  ·
                    refine ⟨4077552615917202069979997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2718368410611468046653331 4077552615917202069979997)
                    ·
                      refine ⟨1529082230968950776242499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4077552615917202069979997 1529082230968950776242499)
                      ·
                        rfl

theorem cell23_2977877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_2977877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977877 prefixEnd_2977877 := by exact prefixLift 2977877
  have htrace : WordTrace (prefixWord ++ tailWord_2977877) baseStart_2977877 baseEnd_2977877 := by
    simpa [prefixWord, tailWord_2977877, baseEnd_2977877] using wordTrace_append hprefix tailTrace_2977877
  have hstable : (prefixWord ++ tailWord_2977877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977877).length < 2 ^ (prefixWord ++ tailWord_2977877).sum := by decide
  have hdescent : baseEnd_2977877 < baseStart_2977877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977911 : List Nat := [1, 1, 3, 1, 1, 7, 2, 1, 2, 1, 3]
def baseStart_2977911 : Nat := 118140960795 + 2977911 * 2 ^ 59
def prefixEnd_2977911 : Nat := 4983230072969 + 3 ^ 40 * 2977911 * 2
def baseEnd_2977911 : Nat := 1529099689311203643217343

theorem tailTrace_2977911 : CollatzResearch.WordTrace tailWord_2977911 prefixEnd_2977911 1529099689311203643217343 := by
  unfold tailWord_2977911
  simp only [CollatzResearch.WordTrace]
  refine ⟨108613337114544508553253587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72408891409696339035502391 108613337114544508553253587)
  ·
    refine ⟨162920005671816762829880381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108613337114544508553253587 162920005671816762829880381)
    ·
      refine ⟨61095002126931286061205143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162920005671816762829880381 61095002126931286061205143)
      ·
        refine ⟨91642503190396929091807715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61095002126931286061205143 91642503190396929091807715)
        ·
          refine ⟨137463754785595393637711573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91642503190396929091807715 137463754785595393637711573)
          ·
            refine ⟨3221806752787392038383865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 137463754785595393637711573 3221806752787392038383865)
            ·
              refine ⟨2416355064590544028787899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3221806752787392038383865 2416355064590544028787899)
              ·
                refine ⟨3624532596885816043181849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2416355064590544028787899 3624532596885816043181849)
                ·
                  refine ⟨2718399447664362032386387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3624532596885816043181849 2718399447664362032386387)
                  ·
                    refine ⟨4077599171496543048579581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2718399447664362032386387 4077599171496543048579581)
                    ·
                      refine ⟨1529099689311203643217343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4077599171496543048579581 1529099689311203643217343)
                      ·
                        rfl

theorem cell23_2977911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 2, 1, 3].length) (baseStart_2977911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977911 prefixEnd_2977911 := by exact prefixLift 2977911
  have htrace : WordTrace (prefixWord ++ tailWord_2977911) baseStart_2977911 baseEnd_2977911 := by
    simpa [prefixWord, tailWord_2977911, baseEnd_2977911] using wordTrace_append hprefix tailTrace_2977911
  have hstable : (prefixWord ++ tailWord_2977911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977911).length < 2 ^ (prefixWord ++ tailWord_2977911).sum := by decide
  have hdescent : baseEnd_2977911 < baseStart_2977911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977951 : List Nat := [1, 1, 2, 6, 1, 1, 1, 4, 2, 2, 2]
def baseStart_2977951 : Nat := 118140960795 + 2977951 * 2 ^ 59
def prefixEnd_2977951 : Nat := 4983230072969 + 3 ^ 40 * 2977951 * 2
def baseEnd_2977951 : Nat := 1529120228537383486717159

theorem tailTrace_2977951 : CollatzResearch.WordTrace tailWord_2977951 prefixEnd_2977951 1529120228537383486717159 := by
  unfold tailWord_2977951
  simp only [CollatzResearch.WordTrace]
  refine ⟨108614796034399595384709707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72409864022933063589806471 108614796034399595384709707)
  ·
    refine ⟨162922194051599393077064561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108614796034399595384709707 162922194051599393077064561)
    ·
      refine ⟨122191645538699544807798421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162922194051599393077064561 122191645538699544807798421)
      ·
        refine ⟨5727733384626541162865551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122191645538699544807798421 5727733384626541162865551)
        ·
          refine ⟨8591600076939811744298327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5727733384626541162865551 8591600076939811744298327)
          ·
            refine ⟨12887400115409717616447491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8591600076939811744298327 12887400115409717616447491)
            ·
              refine ⟨19331100173114576424671237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12887400115409717616447491 19331100173114576424671237)
              ·
                refine ⟨3624581282458983079625857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19331100173114576424671237 3624581282458983079625857)
                ·
                  refine ⟨2718435961844237309719393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3624581282458983079625857 2718435961844237309719393)
                  ·
                    refine ⟨2038826971383177982289545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2718435961844237309719393 2038826971383177982289545)
                    ·
                      refine ⟨1529120228537383486717159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2038826971383177982289545 1529120228537383486717159)
                      ·
                        rfl

theorem cell23_2977951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_2977951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977951 prefixEnd_2977951 := by exact prefixLift 2977951
  have htrace : WordTrace (prefixWord ++ tailWord_2977951) baseStart_2977951 baseEnd_2977951 := by
    simpa [prefixWord, tailWord_2977951, baseEnd_2977951] using wordTrace_append hprefix tailTrace_2977951
  have hstable : (prefixWord ++ tailWord_2977951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977951).length < 2 ^ (prefixWord ++ tailWord_2977951).sum := by decide
  have hdescent : baseEnd_2977951 < baseStart_2977951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977957 : List Nat := [1, 3, 1, 2, 1, 3, 3, 4, 5]
def baseStart_2977957 : Nat := 118140960795 + 2977957 * 2 ^ 59
def prefixEnd_2977957 : Nat := 4983230072969 + 3 ^ 40 * 2977957 * 2
def baseEnd_2977957 : Nat := 169902589935701162582459

theorem tailTrace_2977957 : CollatzResearch.WordTrace tailWord_2977957 prefixEnd_2977957 169902589935701162582459 := by
  unfold tailWord_2977957
  simp only [CollatzResearch.WordTrace]
  refine ⟨108615014872377858409428125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72410009914918572272952083 108615014872377858409428125)
  ·
    refine ⟨40730630577141696903535547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108615014872377858409428125 40730630577141696903535547)
    ·
      refine ⟨61095945865712545355303321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40730630577141696903535547 61095945865712545355303321)
      ·
        refine ⟨45821959399284409016477491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61095945865712545355303321 45821959399284409016477491)
        ·
          refine ⟨68732939098926613524716237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45821959399284409016477491 68732939098926613524716237)
          ·
            refine ⟨25774852162097480071768589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68732939098926613524716237 25774852162097480071768589)
            ·
              refine ⟨9665569560786555026913221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25774852162097480071768589 9665569560786555026913221)
              ·
                refine ⟨1812294292647479067546229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9665569560786555026913221 1812294292647479067546229)
                ·
                  refine ⟨169902589935701162582459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1812294292647479067546229 169902589935701162582459)
                  ·
                    rfl

theorem cell23_2977957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 5].length) (baseStart_2977957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977957 prefixEnd_2977957 := by exact prefixLift 2977957
  have htrace : WordTrace (prefixWord ++ tailWord_2977957) baseStart_2977957 baseEnd_2977957 := by
    simpa [prefixWord, tailWord_2977957, baseEnd_2977957] using wordTrace_append hprefix tailTrace_2977957
  have hstable : (prefixWord ++ tailWord_2977957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977957).length < 2 ^ (prefixWord ++ tailWord_2977957).sum := by decide
  have hdescent : baseEnd_2977957 < baseStart_2977957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977970 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 1, 7]
def baseStart_2977970 : Nat := 118140960795 + 2977970 * 2 ^ 59
def prefixEnd_2977970 : Nat := 4983230072969 + 3 ^ 40 * 2977970 * 2
def baseEnd_2977970 : Nat := 509709994889939637459857

theorem tailTrace_2977970 : CollatzResearch.WordTrace tailWord_2977970 prefixEnd_2977970 509709994889939637459857 := by
  unfold tailWord_2977970
  simp only [CollatzResearch.WordTrace]
  refine ⟨27153872255332690407412841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72410326014220507753100909 27153872255332690407412841)
  ·
    refine ⟨20365404191499517805559631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27153872255332690407412841 20365404191499517805559631)
    ·
      refine ⟨30548106287249276708339447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20365404191499517805559631 30548106287249276708339447)
      ·
        refine ⟨45822159430873915062509171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30548106287249276708339447 45822159430873915062509171)
        ·
          refine ⟨68733239146310872593763757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45822159430873915062509171 68733239146310872593763757)
          ·
            refine ⟨25774964679866577222661409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68733239146310872593763757 25774964679866577222661409)
            ·
              refine ⟨19331223509899932916996057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25774964679866577222661409 19331223509899932916996057)
              ·
                refine ⟨14498417632424949687747043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19331223509899932916996057 14498417632424949687747043)
                ·
                  refine ⟨21747626448637424531620565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14498417632424949687747043 21747626448637424531620565)
                  ·
                    refine ⟨509709994889939637459857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21747626448637424531620565 509709994889939637459857)
                    ·
                      rfl

theorem cell23_2977970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_2977970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977970 prefixEnd_2977970 := by exact prefixLift 2977970
  have htrace : WordTrace (prefixWord ++ tailWord_2977970) baseStart_2977970 baseEnd_2977970 := by
    simpa [prefixWord, tailWord_2977970, baseEnd_2977970] using wordTrace_append hprefix tailTrace_2977970
  have hstable : (prefixWord ++ tailWord_2977970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977970).length < 2 ^ (prefixWord ++ tailWord_2977970).sum := by decide
  have hdescent : baseEnd_2977970 < baseStart_2977970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2977977 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 2, 5, 2]
def baseStart_2977977 : Nat := 118140960795 + 2977977 * 2 ^ 59
def prefixEnd_2977977 : Nat := 4983230072969 + 3 ^ 40 * 2977977 * 2
def baseEnd_2977977 : Nat := 1529133579034400384992039

theorem tailTrace_2977977 : CollatzResearch.WordTrace tailWord_2977977 prefixEnd_2977977 1529133579034400384992039 := by
  unfold tailWord_2977977
  simp only [CollatzResearch.WordTrace]
  refine ⟨108615744332305401825156185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72410496221536934550104123 108615744332305401825156185)
  ·
    refine ⟨81461808249229051368867139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108615744332305401825156185 81461808249229051368867139)
    ·
      refine ⟨122192712373843577053300709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81461808249229051368867139 122192712373843577053300709)
      ·
        refine ⟨22911133570095670697493883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122192712373843577053300709 22911133570095670697493883)
        ·
          refine ⟨34366700355143506046240825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22911133570095670697493883 34366700355143506046240825)
          ·
            refine ⟨25775025266357629534680619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34366700355143506046240825 25775025266357629534680619)
            ·
              refine ⟨38662537899536444302020929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25775025266357629534680619 38662537899536444302020929)
              ·
                refine ⟨28996903424652333226515697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38662537899536444302020929 28996903424652333226515697)
                ·
                  refine ⟨21747677568489249919886773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28996903424652333226515697 21747677568489249919886773)
                  ·
                    refine ⟨2038844772045867179989385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21747677568489249919886773 2038844772045867179989385)
                    ·
                      refine ⟨1529133579034400384992039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2038844772045867179989385 1529133579034400384992039)
                      ·
                        rfl

theorem cell23_2977977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_2977977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2977977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2977977 prefixEnd_2977977 := by exact prefixLift 2977977
  have htrace : WordTrace (prefixWord ++ tailWord_2977977) baseStart_2977977 baseEnd_2977977 := by
    simpa [prefixWord, tailWord_2977977, baseEnd_2977977] using wordTrace_append hprefix tailTrace_2977977
  have hstable : (prefixWord ++ tailWord_2977977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2977977).length < 2 ^ (prefixWord ++ tailWord_2977977).sum := by decide
  have hdescent : baseEnd_2977977 < baseStart_2977977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2977977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978010 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5]
def baseStart_2978010 : Nat := 118140960795 + 2978010 * 2 ^ 59
def prefixEnd_2978010 : Nat := 4983230072969 + 3 ^ 40 * 2978010 * 2
def baseEnd_2978010 : Nat := 1529150523895998755879387

theorem tailTrace_2978010 : CollatzResearch.WordTrace tailWord_2978010 prefixEnd_2978010 1529150523895998755879387 := by
  unfold tailWord_2978010
  simp only [CollatzResearch.WordTrace]
  refine ⟨27154236985296462115276871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72411298627457232307404989 27154236985296462115276871)
  ·
    refine ⟨40731355477944693172915307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27154236985296462115276871 40731355477944693172915307)
    ·
      refine ⟨61097033216917039759372961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40731355477944693172915307 61097033216917039759372961)
      ·
        refine ⟨45822774912687779819529721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61097033216917039759372961 45822774912687779819529721)
        ·
          refine ⟨34367081184515834864647291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45822774912687779819529721 34367081184515834864647291)
          ·
            refine ⟨51550621776773752296970937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34367081184515834864647291 51550621776773752296970937)
            ·
              refine ⟨38662966332580314222728203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51550621776773752296970937 38662966332580314222728203)
              ·
                refine ⟨57994449498870471334092305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38662966332580314222728203 57994449498870471334092305)
                ·
                  refine ⟨43495837124152853500569229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57994449498870471334092305 43495837124152853500569229)
                  ·
                    refine ⟨16310938921557320062713461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43495837124152853500569229 16310938921557320062713461)
                    ·
                      refine ⟨1529150523895998755879387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16310938921557320062713461 1529150523895998755879387)
                      ·
                        rfl

theorem cell23_2978010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_2978010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978010 prefixEnd_2978010 := by exact prefixLift 2978010
  have htrace : WordTrace (prefixWord ++ tailWord_2978010) baseStart_2978010 baseEnd_2978010 := by
    simpa [prefixWord, tailWord_2978010, baseEnd_2978010] using wordTrace_append hprefix tailTrace_2978010
  have hstable : (prefixWord ++ tailWord_2978010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978010).length < 2 ^ (prefixWord ++ tailWord_2978010).sum := by decide
  have hdescent : baseEnd_2978010 < baseStart_2978010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978020 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_2978020 : Nat := 118140960795 + 2978020 * 2 ^ 59
def prefixEnd_2978020 : Nat := 4983230072969 + 3 ^ 40 * 2978020 * 2
def baseEnd_2978020 : Nat := 1529155658702543716754341

theorem tailTrace_2978020 : CollatzResearch.WordTrace tailWord_2978020 prefixEnd_2978020 1529155658702543716754341 := by
  unfold tailWord_2978020
  simp only [CollatzResearch.WordTrace]
  refine ⟨54308656335574810084485757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72411541780766413445981009 54308656335574810084485757)
  ·
    refine ⟨20365746125840553781682159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54308656335574810084485757 20365746125840553781682159)
    ·
      refine ⟨30548619188760830672523239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20365746125840553781682159 30548619188760830672523239)
      ·
        refine ⟨45822928783141246008784859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30548619188760830672523239 45822928783141246008784859)
        ·
          refine ⟨68734393174711869013177289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45822928783141246008784859 68734393174711869013177289)
          ·
            refine ⟨51550794881033901759882967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68734393174711869013177289 51550794881033901759882967)
            ·
              refine ⟨77326192321550852639824451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51550794881033901759882967 77326192321550852639824451)
              ·
                refine ⟨115989288482326278959736677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77326192321550852639824451 115989288482326278959736677)
                ·
                  refine ⟨21747991590436177304950627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115989288482326278959736677 21747991590436177304950627)
                  ·
                    refine ⟨32621987385654265957425941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21747991590436177304950627 32621987385654265957425941)
                    ·
                      refine ⟨1529155658702543716754341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32621987385654265957425941 1529155658702543716754341)
                      ·
                        rfl

theorem cell23_2978020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_2978020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978020 prefixEnd_2978020 := by exact prefixLift 2978020
  have htrace : WordTrace (prefixWord ++ tailWord_2978020) baseStart_2978020 baseEnd_2978020 := by
    simpa [prefixWord, tailWord_2978020, baseEnd_2978020] using wordTrace_append hprefix tailTrace_2978020
  have hstable : (prefixWord ++ tailWord_2978020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978020).length < 2 ^ (prefixWord ++ tailWord_2978020).sum := by decide
  have hdescent : baseEnd_2978020 < baseStart_2978020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978024 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 2, 4, 2]
def baseStart_2978024 : Nat := 118140960795 + 2978024 * 2 ^ 59
def prefixEnd_2978024 : Nat := 4983230072969 + 3 ^ 40 * 2978024 * 2
def baseEnd_2978024 : Nat := 1529157712625161701104323

theorem tailTrace_2978024 : CollatzResearch.WordTrace tailWord_2978024 prefixEnd_2978024 1529157712625161701104323 := by
  unfold tailWord_2978024
  simp only [CollatzResearch.WordTrace]
  refine ⟨54308729281567564426058563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72411639042090085901411417 54308729281567564426058563)
  ·
    refine ⟨81463093922351346639087845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54308729281567564426058563 81463093922351346639087845)
    ·
      refine ⟨15274330110440877494828971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81463093922351346639087845 15274330110440877494828971)
      ·
        refine ⟨22911495165661316242243457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15274330110440877494828971 22911495165661316242243457)
        ·
          refine ⟨17183621374245987181682593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22911495165661316242243457 17183621374245987181682593)
          ·
            refine ⟨12887716030684490386261945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17183621374245987181682593 12887716030684490386261945)
            ·
              refine ⟨9665787023013367789696459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12887716030684490386261945 9665787023013367789696459)
              ·
                refine ⟨14498680534520051684544689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9665787023013367789696459 14498680534520051684544689)
                ·
                  refine ⟨10874010400890038763408517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14498680534520051684544689 10874010400890038763408517)
                  ·
                    refine ⟨2038876950166882268139097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10874010400890038763408517 2038876950166882268139097)
                    ·
                      refine ⟨1529157712625161701104323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2038876950166882268139097 1529157712625161701104323)
                      ·
                        rfl

theorem cell23_2978024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_2978024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978024 prefixEnd_2978024 := by exact prefixLift 2978024
  have htrace : WordTrace (prefixWord ++ tailWord_2978024) baseStart_2978024 baseEnd_2978024 := by
    simpa [prefixWord, tailWord_2978024, baseEnd_2978024] using wordTrace_append hprefix tailTrace_2978024
  have hstable : (prefixWord ++ tailWord_2978024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978024).length < 2 ^ (prefixWord ++ tailWord_2978024).sum := by decide
  have hdescent : baseEnd_2978024 < baseStart_2978024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978034 : List Nat := [3, 2, 1, 3, 2, 1, 2, 2, 3, 4]
def baseStart_2978034 : Nat := 118140960795 + 2978034 * 2 ^ 59
def prefixEnd_2978034 : Nat := 4983230072969 + 3 ^ 40 * 2978034 * 2
def baseEnd_2978034 : Nat := 509720949143902220659759

theorem tailTrace_2978034 : CollatzResearch.WordTrace tailWord_2978034 prefixEnd_2978034 509720949143902220659759 := by
  unfold tailWord_2978034
  simp only [CollatzResearch.WordTrace]
  refine ⟨27154455823274725139995289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72411882195399267039987437 27154455823274725139995289)
  ·
    refine ⟨20365841867456043854996467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27154455823274725139995289 20365841867456043854996467)
    ·
      refine ⟨30548762801184065782494701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20365841867456043854996467 30548762801184065782494701)
      ·
        refine ⟨11455786050444024668435513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30548762801184065782494701 11455786050444024668435513)
        ·
          refine ⟨8591839537833018501326635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11455786050444024668435513 8591839537833018501326635)
          ·
            refine ⟨12887759306749527751989953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8591839537833018501326635 12887759306749527751989953)
            ·
              refine ⟨9665819480062145813992465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12887759306749527751989953 9665819480062145813992465)
              ·
                refine ⟨7249364610046609360494349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9665819480062145813992465 7249364610046609360494349)
                ·
                  refine ⟨2718511728767478510185381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7249364610046609360494349 2718511728767478510185381)
                  ·
                    refine ⟨509720949143902220659759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2718511728767478510185381 509720949143902220659759)
                    ·
                      rfl

theorem cell23_2978034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_2978034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978034 prefixEnd_2978034 := by exact prefixLift 2978034
  have htrace : WordTrace (prefixWord ++ tailWord_2978034) baseStart_2978034 baseEnd_2978034 := by
    simpa [prefixWord, tailWord_2978034, baseEnd_2978034] using wordTrace_append hprefix tailTrace_2978034
  have hstable : (prefixWord ++ tailWord_2978034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978034).length < 2 ^ (prefixWord ++ tailWord_2978034).sum := by decide
  have hdescent : baseEnd_2978034 < baseStart_2978034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978101 : List Nat := [1, 3, 3, 1, 2, 1, 4, 1, 2, 3, 2]
def baseStart_2978101 : Nat := 118140960795 + 2978101 * 2 ^ 59
def prefixEnd_2978101 : Nat := 4983230072969 + 3 ^ 40 * 2978101 * 2
def baseEnd_2978101 : Nat := 1529197250635557899841469

theorem tailTrace_2978101 : CollatzResearch.WordTrace tailWord_2978101 prefixEnd_2978101 1529197250635557899841469 := by
  unfold tailWord_2978101
  simp only [CollatzResearch.WordTrace]
  refine ⟨108620266983856171002670157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72413511322570780668446771 108620266983856171002670157)
  ·
    refine ⟨40732600118946064126001309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108620266983856171002670157 40732600118946064126001309)
    ·
      refine ⟨15274725044604774047250491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40732600118946064126001309 15274725044604774047250491)
      ·
        refine ⟨22912087566907161070875737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15274725044604774047250491 22912087566907161070875737)
        ·
          refine ⟨17184065675180370803156803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22912087566907161070875737 17184065675180370803156803)
          ·
            refine ⟨25776098512770556204735205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17184065675180370803156803 25776098512770556204735205)
            ·
              refine ⟨4833018471144479288387851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25776098512770556204735205 4833018471144479288387851)
              ·
                refine ⟨7249527706716718932581777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4833018471144479288387851 7249527706716718932581777)
                ·
                  refine ⟨5437145780037539199436333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7249527706716718932581777 5437145780037539199436333)
                  ·
                    refine ⟨2038929667514077199788625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5437145780037539199436333 2038929667514077199788625)
                    ·
                      refine ⟨1529197250635557899841469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2038929667514077199788625 1529197250635557899841469)
                      ·
                        rfl

theorem cell23_2978101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_2978101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978101 prefixEnd_2978101 := by exact prefixLift 2978101
  have htrace : WordTrace (prefixWord ++ tailWord_2978101) baseStart_2978101 baseEnd_2978101 := by
    simpa [prefixWord, tailWord_2978101, baseEnd_2978101] using wordTrace_append hprefix tailTrace_2978101
  have hstable : (prefixWord ++ tailWord_2978101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978101).length < 2 ^ (prefixWord ++ tailWord_2978101).sum := by decide
  have hdescent : baseEnd_2978101 < baseStart_2978101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978165 : List Nat := [1, 3, 4, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_2978165 : Nat := 118140960795 + 2978165 * 2 ^ 59
def prefixEnd_2978165 : Nat := 4983230072969 + 3 ^ 40 * 2978165 * 2
def baseEnd_2978165 : Nat := 1529230113397445649441175

theorem tailTrace_2978165 : CollatzResearch.WordTrace tailWord_2978165 prefixEnd_2978165 1529230113397445649441175 := by
  unfold tailWord_2978165
  simp only [CollatzResearch.WordTrace]
  refine ⟨108622601255624309932999949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72415067503749539955333299 108622601255624309932999949)
  ·
    refine ⟨40733475470859116224874981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108622601255624309932999949 40733475470859116224874981)
    ·
      refine ⟨7637526650786084292164059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40733475470859116224874981 7637526650786084292164059)
      ·
        refine ⟨11456289976179126438246089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7637526650786084292164059 11456289976179126438246089)
        ·
          refine ⟨8592217482134344828684567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11456289976179126438246089 8592217482134344828684567)
          ·
            refine ⟨12888326223201517243026851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8592217482134344828684567 12888326223201517243026851)
            ·
              refine ⟨19332489334802275864540277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12888326223201517243026851 19332489334802275864540277)
              ·
                refine ⟨1812420875137713362300651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19332489334802275864540277 1812420875137713362300651)
                ·
                  refine ⟨2718631312706570043450977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1812420875137713362300651 2718631312706570043450977)
                  ·
                    refine ⟨2038973484529927532588233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2718631312706570043450977 2038973484529927532588233)
                    ·
                      refine ⟨1529230113397445649441175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2038973484529927532588233 1529230113397445649441175)
                      ·
                        rfl

theorem cell23_2978165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_2978165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978165 prefixEnd_2978165 := by exact prefixLift 2978165
  have htrace : WordTrace (prefixWord ++ tailWord_2978165) baseStart_2978165 baseEnd_2978165 := by
    simpa [prefixWord, tailWord_2978165, baseEnd_2978165] using wordTrace_append hprefix tailTrace_2978165
  have hstable : (prefixWord ++ tailWord_2978165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978165).length < 2 ^ (prefixWord ++ tailWord_2978165).sum := by decide
  have hdescent : baseEnd_2978165 < baseStart_2978165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978208 : List Nat := [2, 1, 1, 4, 1, 4, 2, 2, 1, 3, 2]
def baseStart_2978208 : Nat := 118140960795 + 2978208 * 2 ^ 59
def prefixEnd_2978208 : Nat := 4983230072969 + 3 ^ 40 * 2978208 * 2
def baseEnd_2978208 : Nat := 1529252193065588981203477

theorem tailTrace_2978208 : CollatzResearch.WordTrace tailWord_2978208 prefixEnd_2978208 1529252193065588981203477 := by
  unfold tailWord_2978208
  simp only [CollatzResearch.WordTrace]
  refine ⟨54312084797234264138407639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72416113062979018851210185 54312084797234264138407639)
  ·
    refine ⟨81468127195851396207611459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54312084797234264138407639 81468127195851396207611459)
    ·
      refine ⟨122202190793777094311417189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81468127195851396207611459 122202190793777094311417189)
      ·
        refine ⟨22912910773833205183390723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122202190793777094311417189 22912910773833205183390723)
        ·
          refine ⟨34369366160749807775086085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22912910773833205183390723 34369366160749807775086085)
          ·
            refine ⟨6444256155140588957828641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34369366160749807775086085 6444256155140588957828641)
            ·
              refine ⟨4833192116355441718371481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6444256155140588957828641 4833192116355441718371481)
              ·
                refine ⟨3624894087266581288778611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4833192116355441718371481 3624894087266581288778611)
                ·
                  refine ⟨5437341130899871933167917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3624894087266581288778611 5437341130899871933167917)
                  ·
                    refine ⟨2039002924087451974937969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5437341130899871933167917 2039002924087451974937969)
                    ·
                      refine ⟨1529252193065588981203477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2039002924087451974937969 1529252193065588981203477)
                      ·
                        rfl

theorem cell23_2978208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_2978208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978208 prefixEnd_2978208 := by exact prefixLift 2978208
  have htrace : WordTrace (prefixWord ++ tailWord_2978208) baseStart_2978208 baseEnd_2978208 := by
    simpa [prefixWord, tailWord_2978208, baseEnd_2978208] using wordTrace_append hprefix tailTrace_2978208
  have hstable : (prefixWord ++ tailWord_2978208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978208).length < 2 ^ (prefixWord ++ tailWord_2978208).sum := by decide
  have hdescent : baseEnd_2978208 < baseStart_2978208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978217 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 1, 4, 4]
def baseStart_2978217 : Nat := 118140960795 + 2978217 * 2 ^ 59
def prefixEnd_2978217 : Nat := 4983230072969 + 3 ^ 40 * 2978217 * 2
def baseEnd_2978217 : Nat := 1529256814391479445990935

theorem tailTrace_2978217 : CollatzResearch.WordTrace tailWord_2978217 prefixEnd_2978217 1529256814391479445990935 := by
  unfold tailWord_2978217
  simp only [CollatzResearch.WordTrace]
  refine ⟨108624497851435922813892905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72416331900957281875928603 108624497851435922813892905)
  ·
    refine ⟨81468373388576942110419679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108624497851435922813892905 81468373388576942110419679)
    ·
      refine ⟨122202560082865413165629519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81468373388576942110419679 122202560082865413165629519)
      ·
        refine ⟨183303840124298119748444279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122202560082865413165629519 183303840124298119748444279)
        ·
          refine ⟨274955760186447179622666419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183303840124298119748444279 274955760186447179622666419)
          ·
            refine ⟨412433640279670769433999629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274955760186447179622666419 412433640279670769433999629)
            ·
              refine ⟨154662615104876538537749861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 412433640279670769433999629 154662615104876538537749861)
              ·
                refine ⟨28999240332164350975828099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154662615104876538537749861 28999240332164350975828099)
                ·
                  refine ⟨43498860498246526463742149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28999240332164350975828099 43498860498246526463742149)
                  ·
                    refine ⟨8156036343421223711951653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43498860498246526463742149 8156036343421223711951653)
                    ·
                      refine ⟨1529256814391479445990935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8156036343421223711951653 1529256814391479445990935)
                      ·
                        rfl

theorem cell23_2978217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_2978217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978217 prefixEnd_2978217 := by exact prefixLift 2978217
  have htrace : WordTrace (prefixWord ++ tailWord_2978217) baseStart_2978217 baseEnd_2978217 := by
    simpa [prefixWord, tailWord_2978217, baseEnd_2978217] using wordTrace_append hprefix tailTrace_2978217
  have hstable : (prefixWord ++ tailWord_2978217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978217).length < 2 ^ (prefixWord ++ tailWord_2978217).sum := by decide
  have hdescent : baseEnd_2978217 < baseStart_2978217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978238 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2]
def baseStart_2978238 : Nat := 118140960795 + 2978238 * 2 ^ 59
def prefixEnd_2978238 : Nat := 4983230072969 + 3 ^ 40 * 2978238 * 2
def baseEnd_2978238 : Nat := 1529267597485223863828339

theorem tailTrace_2978238 : CollatzResearch.WordTrace tailWord_2978238 prefixEnd_2978238 1529267597485223863828339 := by
  unfold tailWord_2978238
  simp only [CollatzResearch.WordTrace]
  refine ⟨13578157973044980425050921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72416842522906562266938245 13578157973044980425050921)
  ·
    refine ⟨10183618479783735318788191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13578157973044980425050921 10183618479783735318788191)
    ·
      refine ⟨15275427719675602978182287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10183618479783735318788191 15275427719675602978182287)
      ·
        refine ⟨22913141579513404467273431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15275427719675602978182287 22913141579513404467273431)
        ·
          refine ⟨34369712369270106700910147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22913141579513404467273431 34369712369270106700910147)
          ·
            refine ⟨51554568553905160051365221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34369712369270106700910147 51554568553905160051365221)
            ·
              refine ⟨9666481603857217509630979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51554568553905160051365221 9666481603857217509630979)
              ·
                refine ⟨14499722405785826264446469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9666481603857217509630979 14499722405785826264446469)
                ·
                  refine ⟨2718697951084842424583713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14499722405785826264446469 2718697951084842424583713)
                  ·
                    refine ⟨2039023463313631818437785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2718697951084842424583713 2039023463313631818437785)
                    ·
                      refine ⟨1529267597485223863828339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2039023463313631818437785 1529267597485223863828339)
                      ·
                        rfl

theorem cell23_2978238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_2978238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978238 prefixEnd_2978238 := by exact prefixLift 2978238
  have htrace : WordTrace (prefixWord ++ tailWord_2978238) baseStart_2978238 baseEnd_2978238 := by
    simpa [prefixWord, tailWord_2978238, baseEnd_2978238] using wordTrace_append hprefix tailTrace_2978238
  have hstable : (prefixWord ++ tailWord_2978238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978238).length < 2 ^ (prefixWord ++ tailWord_2978238).sum := by decide
  have hdescent : baseEnd_2978238 < baseStart_2978238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978254 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3]
def baseStart_2978254 : Nat := 118140960795 + 2978254 * 2 ^ 59
def prefixEnd_2978254 : Nat := 4983230072969 + 3 ^ 40 * 2978254 * 2
def baseEnd_2978254 : Nat := 1529275813175695801228265

theorem tailTrace_2978254 : CollatzResearch.WordTrace tailWord_2978254 prefixEnd_2978254 1529275813175695801228265 := by
  unfold tailWord_2978254
  simp only [CollatzResearch.WordTrace]
  refine ⟨13578230919037734766623727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72417231568201252088659877 13578230919037734766623727)
  ·
    refine ⟨20367346378556602149935591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13578230919037734766623727 20367346378556602149935591)
    ·
      refine ⟨30551019567834903224903387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20367346378556602149935591 30551019567834903224903387)
      ·
        refine ⟨45826529351752354837355081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30551019567834903224903387 45826529351752354837355081)
        ·
          refine ⟨34369897013814266128016311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45826529351752354837355081 34369897013814266128016311)
          ·
            refine ⟨51554845520721399192024467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34369897013814266128016311 51554845520721399192024467)
            ·
              refine ⟨77332268281082098788036701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51554845520721399192024467 77332268281082098788036701)
              ·
                refine ⟨28999600605405787045513763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77332268281082098788036701 28999600605405787045513763)
                ·
                  refine ⟨43499400908108680568270645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28999600605405787045513763 43499400908108680568270645)
                  ·
                    refine ⟨4078068835135188803275373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43499400908108680568270645 4078068835135188803275373)
                    ·
                      refine ⟨1529275813175695801228265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4078068835135188803275373 1529275813175695801228265)
                      ·
                        rfl

theorem cell23_2978254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_2978254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978254 prefixEnd_2978254 := by exact prefixLift 2978254
  have htrace : WordTrace (prefixWord ++ tailWord_2978254) baseStart_2978254 baseEnd_2978254 := by
    simpa [prefixWord, tailWord_2978254, baseEnd_2978254] using wordTrace_append hprefix tailTrace_2978254
  have hstable : (prefixWord ++ tailWord_2978254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978254).length < 2 ^ (prefixWord ++ tailWord_2978254).sum := by decide
  have hdescent : baseEnd_2978254 < baseStart_2978254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978257 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 3, 7]
def baseStart_2978257 : Nat := 118140960795 + 2978257 * 2 ^ 59
def prefixEnd_2978257 : Nat := 4983230072969 + 3 ^ 40 * 2978257 * 2
def baseEnd_2978257 : Nat := 509759117872553096496917

theorem tailTrace_2978257 : CollatzResearch.WordTrace tailWord_2978257 prefixEnd_2978257 509759117872553096496917 := by
  unfold tailWord_2978257
  simp only [CollatzResearch.WordTrace]
  refine ⟨108625956771291009645349025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72417304514194006430232683 108625956771291009645349025)
  ·
    refine ⟨81469467578468257234011769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108625956771291009645349025 81469467578468257234011769)
    ·
      refine ⟨61102100683851192925508827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81469467578468257234011769 61102100683851192925508827)
      ·
        refine ⟨91653151025776789388263241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61102100683851192925508827 91653151025776789388263241)
        ·
          refine ⟨68739863269332592041197431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91653151025776789388263241 68739863269332592041197431)
          ·
            refine ⟨103109794903998888061796147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68739863269332592041197431 103109794903998888061796147)
            ·
              refine ⟨154664692355998332092694221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103109794903998888061796147 154664692355998332092694221)
              ·
                refine ⟨57999259633499374534760333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154664692355998332092694221 57999259633499374534760333)
                ·
                  refine ⟨21749722362562265450535125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57999259633499374534760333 21749722362562265450535125)
                  ·
                    refine ⟨509759117872553096496917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21749722362562265450535125 509759117872553096496917)
                    ·
                      rfl

theorem cell23_2978257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_2978257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978257 prefixEnd_2978257 := by exact prefixLift 2978257
  have htrace : WordTrace (prefixWord ++ tailWord_2978257) baseStart_2978257 baseEnd_2978257 := by
    simpa [prefixWord, tailWord_2978257, baseEnd_2978257] using wordTrace_append hprefix tailTrace_2978257
  have hstable : (prefixWord ++ tailWord_2978257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978257).length < 2 ^ (prefixWord ++ tailWord_2978257).sum := by decide
  have hdescent : baseEnd_2978257 < baseStart_2978257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978304 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 9, 4]
def baseStart_2978304 : Nat := 118140960795 + 2978304 * 2 ^ 59
def prefixEnd_2978304 : Nat := 4983230072969 + 3 ^ 40 * 2978304 * 2
def baseEnd_2978304 : Nat := 509767162402806868534345

theorem tailTrace_2978304 : CollatzResearch.WordTrace tailWord_2978304 prefixEnd_2978304 509767162402806868534345 := by
  unfold tailWord_2978304
  simp only [CollatzResearch.WordTrace]
  refine ⟨54313835501060368336154983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72418447334747157781539977 54313835501060368336154983)
  ·
    refine ⟨81470753251590552504232475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54313835501060368336154983 81470753251590552504232475)
    ·
      refine ⟨122206129877385828756348713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81470753251590552504232475 122206129877385828756348713)
      ·
        refine ⟨91654597408039371567261535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122206129877385828756348713 91654597408039371567261535)
        ·
          refine ⟨137481896112059057350892303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91654597408039371567261535 137481896112059057350892303)
          ·
            refine ⟨206222844168088586026338455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137481896112059057350892303 206222844168088586026338455)
            ·
              refine ⟨309334266252132879039507683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206222844168088586026338455 309334266252132879039507683)
              ·
                refine ⟨464001399378199318559261525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309334266252132879039507683 464001399378199318559261525)
                ·
                  refine ⟨2718758199481636632183173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 464001399378199318559261525 2718758199481636632183173)
                  ·
                    refine ⟨509767162402806868534345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2718758199481636632183173 509767162402806868534345)
                    ·
                      rfl

theorem cell23_2978304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 9, 4].length) (baseStart_2978304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978304 prefixEnd_2978304 := by exact prefixLift 2978304
  have htrace : WordTrace (prefixWord ++ tailWord_2978304) baseStart_2978304 baseEnd_2978304 := by
    simpa [prefixWord, tailWord_2978304, baseEnd_2978304] using wordTrace_append hprefix tailTrace_2978304
  have hstable : (prefixWord ++ tailWord_2978304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978304).length < 2 ^ (prefixWord ++ tailWord_2978304).sum := by decide
  have hdescent : baseEnd_2978304 < baseStart_2978304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978328 : List Nat := [2, 1, 2, 3, 3, 3, 1, 1, 2, 1, 4]
def baseStart_2978328 : Nat := 118140960795 + 2978328 * 2 ^ 59
def prefixEnd_2978328 : Nat := 4983230072969 + 3 ^ 40 * 2978328 * 2
def baseEnd_2978328 : Nat := 1529313810744128511702925

theorem tailTrace_2978328 : CollatzResearch.WordTrace tailWord_2978328 prefixEnd_2978328 1529313810744128511702925 := by
  unfold tailWord_2978328
  simp only [CollatzResearch.WordTrace]
  refine ⟨54314273177016894385591819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72419030902689192514122425 54314273177016894385591819)
  ·
    refine ⟨81471409765525341578387729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54314273177016894385591819 81471409765525341578387729)
    ·
      refine ⟨61103557324144006183790797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81471409765525341578387729 61103557324144006183790797)
      ·
        refine ⟨22913833996554002318921549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61103557324144006183790797 22913833996554002318921549)
        ·
          refine ⟨8592687748707750869595581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22913833996554002318921549 8592687748707750869595581)
          ·
            refine ⟨3222257905765406576098343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8592687748707750869595581 3222257905765406576098343)
            ·
              refine ⟨4833386858648109864147515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3222257905765406576098343 4833386858648109864147515)
              ·
                refine ⟨7250080287972164796221273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4833386858648109864147515 7250080287972164796221273)
                ·
                  refine ⟨5437560215979123597165955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7250080287972164796221273 5437560215979123597165955)
                  ·
                    refine ⟨8156340323968685395748933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5437560215979123597165955 8156340323968685395748933)
                    ·
                      refine ⟨1529313810744128511702925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8156340323968685395748933 1529313810744128511702925)
                      ·
                        rfl

theorem cell23_2978328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_2978328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978328 prefixEnd_2978328 := by exact prefixLift 2978328
  have htrace : WordTrace (prefixWord ++ tailWord_2978328) baseStart_2978328 baseEnd_2978328 := by
    simpa [prefixWord, tailWord_2978328, baseEnd_2978328] using wordTrace_append hprefix tailTrace_2978328
  have hstable : (prefixWord ++ tailWord_2978328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978328).length < 2 ^ (prefixWord ++ tailWord_2978328).sum := by decide
  have hdescent : baseEnd_2978328 < baseStart_2978328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978354 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_2978354 : Nat := 118140960795 + 2978354 * 2 ^ 59
def prefixEnd_2978354 : Nat := 4983230072969 + 3 ^ 40 * 2978354 * 2
def baseEnd_2978354 : Nat := 1529327161241145409977805

theorem tailTrace_2978354 : CollatzResearch.WordTrace tailWord_2978354 prefixEnd_2978354 1529327161241145409977805 := by
  unfold tailWord_2978354
  simp only [CollatzResearch.WordTrace]
  refine ⟨27157373662984898802907529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72419663101293063474420077 27157373662984898802907529)
  ·
    refine ⟨20368030247238674102180647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27157373662984898802907529 20368030247238674102180647)
    ·
      refine ⟨30552045370858011153270971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20368030247238674102180647 30552045370858011153270971)
      ·
        refine ⟨45828068056287016729906457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30552045370858011153270971 45828068056287016729906457)
        ·
          refine ⟨34371051042215262547429843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45828068056287016729906457 34371051042215262547429843)
          ·
            refine ⟨51556576563322893821144765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34371051042215262547429843 51556576563322893821144765)
            ·
              refine ⟨19333716211246085182929287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51556576563322893821144765 19333716211246085182929287)
              ·
                refine ⟨29000574316869127774393931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19333716211246085182929287 29000574316869127774393931)
                ·
                  refine ⟨43500861475303691661590897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29000574316869127774393931 43500861475303691661590897)
                  ·
                    refine ⟨32625646106477768746193173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43500861475303691661590897 32625646106477768746193173)
                    ·
                      refine ⟨1529327161241145409977805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32625646106477768746193173 1529327161241145409977805)
                      ·
                        rfl

theorem cell23_2978354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_2978354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978354 prefixEnd_2978354 := by exact prefixLift 2978354
  have htrace : WordTrace (prefixWord ++ tailWord_2978354) baseStart_2978354 baseEnd_2978354 := by
    simpa [prefixWord, tailWord_2978354, baseEnd_2978354] using wordTrace_append hprefix tailTrace_2978354
  have hstable : (prefixWord ++ tailWord_2978354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978354).length < 2 ^ (prefixWord ++ tailWord_2978354).sum := by decide
  have hdescent : baseEnd_2978354 < baseStart_2978354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978378 : List Nat := [3, 1, 2, 1, 1, 4, 2, 2, 3, 1, 3]
def baseStart_2978378 : Nat := 118140960795 + 2978378 * 2 ^ 59
def prefixEnd_2978378 : Nat := 4983230072969 + 3 ^ 40 * 2978378 * 2
def baseEnd_2978378 : Nat := 1529339484776853316077695

theorem tailTrace_2978378 : CollatzResearch.WordTrace tailWord_2978378 prefixEnd_2978378 1529339484776853316077695 := by
  unfold tailWord_2978378
  simp only [CollatzResearch.WordTrace]
  refine ⟨27157592500963161827625947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72420246669235098207002525 27157592500963161827625947)
  ·
    refine ⟨40736388751444742741438921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27157592500963161827625947 40736388751444742741438921)
    ·
      refine ⟨30552291563583557056079191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40736388751444742741438921 30552291563583557056079191)
      ·
        refine ⟨45828437345375335584118787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30552291563583557056079191 45828437345375335584118787)
        ·
          refine ⟨68742656018063003376178181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45828437345375335584118787 68742656018063003376178181)
          ·
            refine ⟨12889248003386813133033409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68742656018063003376178181 12889248003386813133033409)
            ·
              refine ⟨9666936002540109849775057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12889248003386813133033409 9666936002540109849775057)
              ·
                refine ⟨7250202001905082387331293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9666936002540109849775057 7250202001905082387331293)
                ·
                  refine ⟨2718825750714405895249235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7250202001905082387331293 2718825750714405895249235)
                  ·
                    refine ⟨4078238626071608842873853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2718825750714405895249235 4078238626071608842873853)
                    ·
                      refine ⟨1529339484776853316077695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4078238626071608842873853 1529339484776853316077695)
                      ·
                        rfl

theorem cell23_2978378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_2978378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978378 prefixEnd_2978378 := by exact prefixLift 2978378
  have htrace : WordTrace (prefixWord ++ tailWord_2978378) baseStart_2978378 baseEnd_2978378 := by
    simpa [prefixWord, tailWord_2978378, baseEnd_2978378] using wordTrace_append hprefix tailTrace_2978378
  have hstable : (prefixWord ++ tailWord_2978378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978378).length < 2 ^ (prefixWord ++ tailWord_2978378).sum := by decide
  have hdescent : baseEnd_2978378 < baseStart_2978378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978388 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 1, 5, 2]
def baseStart_2978388 : Nat := 118140960795 + 2978388 * 2 ^ 59
def prefixEnd_2978388 : Nat := 4983230072969 + 3 ^ 40 * 2978388 * 2
def baseEnd_2978388 : Nat := 1529344619583398276952649

theorem tailTrace_2978388 : CollatzResearch.WordTrace tailWord_2978388 prefixEnd_2978388 1529344619583398276952649 := by
  unfold tailWord_2978388
  simp only [CollatzResearch.WordTrace]
  refine ⟨54315367366908209509183909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72420489822544279345578545 54315367366908209509183909)
  ·
    refine ⟨10184131381295289282971983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54315367366908209509183909 10184131381295289282971983)
    ·
      refine ⟨15276197071942933924457975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10184131381295289282971983 15276197071942933924457975)
      ·
        refine ⟨22914295607914400886686963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15276197071942933924457975 22914295607914400886686963)
        ·
          refine ⟨34371443411871601330030445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22914295607914400886686963 34371443411871601330030445)
          ·
            refine ⟨12889291279451850498761417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34371443411871601330030445 12889291279451850498761417)
            ·
              refine ⟨9666968459588887874071063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12889291279451850498761417 9666968459588887874071063)
              ·
                refine ⟨14500452689383331811106595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9666968459588887874071063 14500452689383331811106595)
                ·
                  refine ⟨21750679034074997716659893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14500452689383331811106595 21750679034074997716659893)
                  ·
                    refine ⟨2039126159444531035936865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21750679034074997716659893 2039126159444531035936865)
                    ·
                      refine ⟨1529344619583398276952649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2039126159444531035936865 1529344619583398276952649)
                      ·
                        rfl

theorem cell23_2978388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_2978388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978388 prefixEnd_2978388 := by exact prefixLift 2978388
  have htrace : WordTrace (prefixWord ++ tailWord_2978388) baseStart_2978388 baseEnd_2978388 := by
    simpa [prefixWord, tailWord_2978388, baseEnd_2978388] using wordTrace_append hprefix tailTrace_2978388
  have hstable : (prefixWord ++ tailWord_2978388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978388).length < 2 ^ (prefixWord ++ tailWord_2978388).sum := by decide
  have hdescent : baseEnd_2978388 < baseStart_2978388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978405 : List Nat := [1, 3, 1, 3, 4, 1, 1, 2, 2, 3, 2]
def baseStart_2978405 : Nat := 118140960795 + 2978405 * 2 ^ 59
def prefixEnd_2978405 : Nat := 4983230072969 + 3 ^ 40 * 2978405 * 2
def baseEnd_2978405 : Nat := 1529353348754524710440071

theorem tailTrace_2978405 : CollatzResearch.WordTrace tailWord_2978405 prefixEnd_2978405 1529353348754524710440071 := by
  unfold tailWord_2978405
  simp only [CollatzResearch.WordTrace]
  refine ⟨108631354774754830921736669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72420903183169887281157779 108631354774754830921736669)
  ·
    refine ⟨40736758040533061595651251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108631354774754830921736669 40736758040533061595651251)
    ·
      refine ⟨61105137060799592393476877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40736758040533061595651251 61105137060799592393476877)
      ·
        refine ⟨22914426397799847147553829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61105137060799592393476877 22914426397799847147553829)
        ·
          refine ⟨4296454949587471340166343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22914426397799847147553829 4296454949587471340166343)
          ·
            refine ⟨6444682424381207010249515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4296454949587471340166343 6444682424381207010249515)
            ·
              refine ⟨9667023636571810515374273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6444682424381207010249515 9667023636571810515374273)
              ·
                refine ⟨7250267727428857886530705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9667023636571810515374273 7250267727428857886530705)
                ·
                  refine ⟨5437700795571643414898029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7250267727428857886530705 5437700795571643414898029)
                  ·
                    refine ⟨2039137798339366280586761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5437700795571643414898029 2039137798339366280586761)
                    ·
                      refine ⟨1529353348754524710440071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2039137798339366280586761 1529353348754524710440071)
                      ·
                        rfl

theorem cell23_2978405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_2978405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978405 prefixEnd_2978405 := by exact prefixLift 2978405
  have htrace : WordTrace (prefixWord ++ tailWord_2978405) baseStart_2978405 baseEnd_2978405 := by
    simpa [prefixWord, tailWord_2978405, baseEnd_2978405] using wordTrace_append hprefix tailTrace_2978405
  have hstable : (prefixWord ++ tailWord_2978405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978405).length < 2 ^ (prefixWord ++ tailWord_2978405).sum := by decide
  have hdescent : baseEnd_2978405 < baseStart_2978405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978451 : List Nat := [1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 3]
def baseStart_2978451 : Nat := 118140960795 + 2978451 * 2 ^ 59
def prefixEnd_2978451 : Nat := 4983230072969 + 3 ^ 40 * 2978451 * 2
def baseEnd_2978451 : Nat := 1529376968864631530464859

theorem tailTrace_2978451 : CollatzResearch.WordTrace tailWord_2978451 prefixEnd_2978451 1529376968864631530464859 := by
  unfold tailWord_2978451
  simp only [CollatzResearch.WordTrace]
  refine ⟨108633032532588180777911207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72422021688392120518607471 108633032532588180777911207)
  ·
    refine ⟨162949548798882271166866811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108633032532588180777911207 162949548798882271166866811)
    ·
      refine ⟨244424323198323406750300217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162949548798882271166866811 244424323198323406750300217)
      ·
        refine ⟨183318242398742555062725163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244424323198323406750300217 183318242398742555062725163)
        ·
          refine ⟨274977363598113832594087745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183318242398742555062725163 274977363598113832594087745)
          ·
            refine ⟨206233022698585374445565809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274977363598113832594087745 206233022698585374445565809)
            ·
              refine ⟨154674767023939030834174357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206233022698585374445565809 154674767023939030834174357)
              ·
                refine ⟨7250379704247142070351923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154674767023939030834174357 7250379704247142070351923)
                ·
                  refine ⟨10875569556370713105527885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7250379704247142070351923 10875569556370713105527885)
                  ·
                    refine ⟨4078338583639017414572957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10875569556370713105527885 4078338583639017414572957)
                    ·
                      refine ⟨1529376968864631530464859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4078338583639017414572957 1529376968864631530464859)
                      ·
                        rfl

theorem cell23_2978451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 3].length) (baseStart_2978451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978451 prefixEnd_2978451 := by exact prefixLift 2978451
  have htrace : WordTrace (prefixWord ++ tailWord_2978451) baseStart_2978451 baseEnd_2978451 := by
    simpa [prefixWord, tailWord_2978451, baseEnd_2978451] using wordTrace_append hprefix tailTrace_2978451
  have hstable : (prefixWord ++ tailWord_2978451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978451).length < 2 ^ (prefixWord ++ tailWord_2978451).sum := by decide
  have hdescent : baseEnd_2978451 < baseStart_2978451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978452 : List Nat := [2, 4, 2, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_2978452 : Nat := 118140960795 + 2978452 * 2 ^ 59
def prefixEnd_2978452 : Nat := 4983230072969 + 3 ^ 40 * 2978452 * 2
def baseEnd_2978452 : Nat := 1529377482345286026552355

theorem tailTrace_2978452 : CollatzResearch.WordTrace tailWord_2978452 prefixEnd_2978452 1529377482345286026552355 := by
  unfold tailWord_2978452
  simp only [CollatzResearch.WordTrace]
  refine ⟨54316534502792278974348805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72422046003723038632465073 54316534502792278974348805)
  ·
    refine ⟨10184350219273552307690401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54316534502792278974348805 10184350219273552307690401)
    ·
      refine ⟨7638262664455164230767801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10184350219273552307690401 7638262664455164230767801)
      ·
        refine ⟨5728696998341373173075851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7638262664455164230767801 5728696998341373173075851)
        ·
          refine ⟨8593045497512059759613777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5728696998341373173075851 8593045497512059759613777)
          ·
            refine ⟨6444784123134044819710333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8593045497512059759613777 6444784123134044819710333)
            ·
              refine ⟨2416794046175266807391375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6444784123134044819710333 2416794046175266807391375)
              ·
                refine ⟨3625191069262900211087063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2416794046175266807391375 3625191069262900211087063)
                ·
                  refine ⟨5437786603894350316630595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3625191069262900211087063 5437786603894350316630595)
                  ·
                    refine ⟨8156679905841525474945893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5437786603894350316630595 8156679905841525474945893)
                    ·
                      refine ⟨1529377482345286026552355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8156679905841525474945893 1529377482345286026552355)
                      ·
                        rfl

theorem cell23_2978452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_2978452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978452 prefixEnd_2978452 := by exact prefixLift 2978452
  have htrace : WordTrace (prefixWord ++ tailWord_2978452) baseStart_2978452 baseEnd_2978452 := by
    simpa [prefixWord, tailWord_2978452, baseEnd_2978452] using wordTrace_append hprefix tailTrace_2978452
  have hstable : (prefixWord ++ tailWord_2978452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978452).length < 2 ^ (prefixWord ++ tailWord_2978452).sum := by decide
  have hdescent : baseEnd_2978452 < baseStart_2978452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978455 : List Nat := [1, 1, 3, 3, 2, 1, 5, 1, 1, 2, 3]
def baseStart_2978455 : Nat := 118140960795 + 2978455 * 2 ^ 59
def prefixEnd_2978455 : Nat := 4983230072969 + 3 ^ 40 * 2978455 * 2
def baseEnd_2978455 : Nat := 1529379022787249514814841

theorem tailTrace_2978455 : CollatzResearch.WordTrace tailWord_2978455 prefixEnd_2978455 1529379022787249514814841 := by
  unfold tailWord_2978455
  simp only [CollatzResearch.WordTrace]
  refine ⟨108633178424573689461056819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72422118949715792974037879 108633178424573689461056819)
  ·
    refine ⟨162949767636860534191585229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108633178424573689461056819 162949767636860534191585229)
    ·
      refine ⟨61106162863822700321844461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162949767636860534191585229 61106162863822700321844461)
      ·
        refine ⟨22914811073933512620691673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61106162863822700321844461 22914811073933512620691673)
        ·
          refine ⟨17186108305450134465518755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22914811073933512620691673 17186108305450134465518755)
          ·
            refine ⟨25779162458175201698278133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17186108305450134465518755 25779162458175201698278133)
            ·
              refine ⟨2416796480453925159213575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25779162458175201698278133 2416796480453925159213575)
              ·
                refine ⟨3625194720680887738820363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2416796480453925159213575 3625194720680887738820363)
                ·
                  refine ⟨5437792081021331608230545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3625194720680887738820363 5437792081021331608230545)
                  ·
                    refine ⟨4078344060765998706172909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5437792081021331608230545 4078344060765998706172909)
                    ·
                      refine ⟨1529379022787249514814841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4078344060765998706172909 1529379022787249514814841)
                      ·
                        rfl

theorem cell23_2978455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_2978455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978455 prefixEnd_2978455 := by exact prefixLift 2978455
  have htrace : WordTrace (prefixWord ++ tailWord_2978455) baseStart_2978455 baseEnd_2978455 := by
    simpa [prefixWord, tailWord_2978455, baseEnd_2978455] using wordTrace_append hprefix tailTrace_2978455
  have hstable : (prefixWord ++ tailWord_2978455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978455).length < 2 ^ (prefixWord ++ tailWord_2978455).sum := by decide
  have hdescent : baseEnd_2978455 < baseStart_2978455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978458 : List Nat := [3, 1, 1, 6, 2, 10]
def baseStart_2978458 : Nat := 118140960795 + 2978458 * 2 ^ 59
def prefixEnd_2978458 : Nat := 4983230072969 + 3 ^ 40 * 2978458 * 2
def baseEnd_2978458 : Nat := 6293747173782769559989

theorem tailTrace_2978458 : CollatzResearch.WordTrace tailWord_2978458 prefixEnd_2978458 6293747173782769559989 := by
  unfold tailWord_2978458
  simp only [CollatzResearch.WordTrace]
  refine ⟨27158321960890705243354007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72422191895708547315610685 27158321960890705243354007)
  ·
    refine ⟨40737482941336057865031011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27158321960890705243354007 40737482941336057865031011)
    ·
      refine ⟨61106224412004086797546517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40737482941336057865031011 61106224412004086797546517)
      ·
        refine ⟨2864354269312691568634993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61106224412004086797546517 2864354269312691568634993)
        ·
          refine ⟨2148265701984518676476245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2864354269312691568634993 2148265701984518676476245)
          ·
            refine ⟨6293747173782769559989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2148265701984518676476245 6293747173782769559989)
            ·
              rfl

theorem cell23_2978458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 10].length) (baseStart_2978458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978458 prefixEnd_2978458 := by exact prefixLift 2978458
  have htrace : WordTrace (prefixWord ++ tailWord_2978458) baseStart_2978458 baseEnd_2978458 := by
    simpa [prefixWord, tailWord_2978458, baseEnd_2978458] using wordTrace_append hprefix tailTrace_2978458
  have hstable : (prefixWord ++ tailWord_2978458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978458).length < 2 ^ (prefixWord ++ tailWord_2978458).sum := by decide
  have hdescent : baseEnd_2978458 < baseStart_2978458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978485 : List Nat := [1, 3, 3, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_2978485 : Nat := 118140960795 + 2978485 * 2 ^ 59
def prefixEnd_2978485 : Nat := 4983230072969 + 3 ^ 40 * 2978485 * 2
def baseEnd_2978485 : Nat := 1529394427206884397439703

theorem tailTrace_2978485 : CollatzResearch.WordTrace tailWord_2978485 prefixEnd_2978485 1529394427206884397439703 := by
  unfold tailWord_2978485
  simp only [CollatzResearch.WordTrace]
  refine ⟨108634272614465004584648909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72422848409643336389765939 108634272614465004584648909)
  ·
    refine ⟨40737852230424376719243341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108634272614465004584648909 40737852230424376719243341)
    ·
      refine ⟨15276694586409141269716253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40737852230424376719243341 15276694586409141269716253)
      ·
        refine ⟨5728760469903427976143595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15276694586409141269716253 5728760469903427976143595)
        ·
          refine ⟨8593140704855141964215393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5728760469903427976143595 8593140704855141964215393)
          ·
            refine ⟨6444855528641356473161545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8593140704855141964215393 6444855528641356473161545)
            ·
              refine ⟨4833641646481017354871159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6444855528641356473161545 4833641646481017354871159)
              ·
                refine ⟨7250462469721526032306739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4833641646481017354871159 7250462469721526032306739)
                ·
                  refine ⟨10875693704582289048460109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7250462469721526032306739 10875693704582289048460109)
                  ·
                    refine ⟨4078385139218358393172541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10875693704582289048460109 4078385139218358393172541)
                    ·
                      refine ⟨1529394427206884397439703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4078385139218358393172541 1529394427206884397439703)
                      ·
                        rfl

theorem cell23_2978485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_2978485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978485 prefixEnd_2978485 := by exact prefixLift 2978485
  have htrace : WordTrace (prefixWord ++ tailWord_2978485) baseStart_2978485 baseEnd_2978485 := by
    simpa [prefixWord, tailWord_2978485, baseEnd_2978485] using wordTrace_append hprefix tailTrace_2978485
  have hstable : (prefixWord ++ tailWord_2978485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978485).length < 2 ^ (prefixWord ++ tailWord_2978485).sum := by decide
  have hdescent : baseEnd_2978485 < baseStart_2978485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978521 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 4, 2, 4]
def baseStart_2978521 : Nat := 118140960795 + 2978521 * 2 ^ 59
def prefixEnd_2978521 : Nat := 4983230072969 + 3 ^ 40 * 2978521 * 2
def baseEnd_2978521 : Nat := 1529412912510446256589537

theorem tailTrace_2978521 : CollatzResearch.WordTrace tailWord_2978521 prefixEnd_2978521 1529412912510446256589537 := by
  unfold tailWord_2978521
  simp only [CollatzResearch.WordTrace]
  refine ⟨108635585642334582732959417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72423723761556388488639611 108635585642334582732959417)
  ·
    refine ⟨81476689231750937049719563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108635585642334582732959417 81476689231750937049719563)
    ·
      refine ⟨122215033847626405574579345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81476689231750937049719563 122215033847626405574579345)
      ·
        refine ⟨91661275385719804180934509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122215033847626405574579345 91661275385719804180934509)
        ·
          refine ⟨34372978269644926567850441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91661275385719804180934509 34372978269644926567850441)
          ·
            refine ⟨25779733702233694925887831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34372978269644926567850441 25779733702233694925887831)
            ·
              refine ⟨38669600553350542388831747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25779733702233694925887831 38669600553350542388831747)
              ·
                refine ⟨58004400830025813583247621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38669600553350542388831747 58004400830025813583247621)
                ·
                  refine ⟨10875825155629840046858929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58004400830025813583247621 10875825155629840046858929)
                  ·
                    refine ⟨8156868866722380035144197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10875825155629840046858929 8156868866722380035144197)
                    ·
                      refine ⟨1529412912510446256589537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8156868866722380035144197 1529412912510446256589537)
                      ·
                        rfl

theorem cell23_2978521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_2978521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978521 prefixEnd_2978521 := by exact prefixLift 2978521
  have htrace : WordTrace (prefixWord ++ tailWord_2978521) baseStart_2978521 baseEnd_2978521 := by
    simpa [prefixWord, tailWord_2978521, baseEnd_2978521] using wordTrace_append hprefix tailTrace_2978521
  have hstable : (prefixWord ++ tailWord_2978521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978521).length < 2 ^ (prefixWord ++ tailWord_2978521).sum := by decide
  have hdescent : baseEnd_2978521 < baseStart_2978521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978542 : List Nat := [4, 1, 2, 1, 1, 5, 1, 1, 1, 4, 2]
def baseStart_2978542 : Nat := 118140960795 + 2978542 * 2 ^ 59
def prefixEnd_2978542 : Nat := 4983230072969 + 3 ^ 40 * 2978542 * 2
def baseEnd_2978542 : Nat := 1529423695604190674426941

theorem tailTrace_2978542 : CollatzResearch.WordTrace tailWord_2978542 prefixEnd_2978542 1529423695604190674426941 := by
  unfold tailWord_2978542
  simp only [CollatzResearch.WordTrace]
  refine ⟨13579543946907312914934235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72424234383505668879649253 13579543946907312914934235)
  ·
    refine ⟨20369315920360969372401353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13579543946907312914934235 20369315920360969372401353)
    ·
      refine ⟨15276986940270727029301015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20369315920360969372401353 15276986940270727029301015)
      ·
        refine ⟨22915480410406090543951523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15276986940270727029301015 22915480410406090543951523)
        ·
          refine ⟨34373220615609135815927285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22915480410406090543951523 34373220615609135815927285)
          ·
            refine ⟨3222489432713356482743183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34373220615609135815927285 3222489432713356482743183)
            ·
              refine ⟨4833734149070034724114775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3222489432713356482743183 4833734149070034724114775)
              ·
                refine ⟨7250601223605052086172163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4833734149070034724114775 7250601223605052086172163)
                ·
                  refine ⟨10875901835407578129258245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7250601223605052086172163 10875901835407578129258245)
                  ·
                    refine ⟨2039231594138920899235921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10875901835407578129258245 2039231594138920899235921)
                    ·
                      refine ⟨1529423695604190674426941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2039231594138920899235921 1529423695604190674426941)
                      ·
                        rfl

theorem cell23_2978542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_2978542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978542 prefixEnd_2978542 := by exact prefixLift 2978542
  have htrace : WordTrace (prefixWord ++ tailWord_2978542) baseStart_2978542 baseEnd_2978542 := by
    simpa [prefixWord, tailWord_2978542, baseEnd_2978542] using wordTrace_append hprefix tailTrace_2978542
  have hstable : (prefixWord ++ tailWord_2978542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978542).length < 2 ^ (prefixWord ++ tailWord_2978542).sum := by decide
  have hdescent : baseEnd_2978542 < baseStart_2978542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978571 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 5]
def baseStart_2978571 : Nat := 118140960795 + 2978571 * 2 ^ 59
def prefixEnd_2978571 : Nat := 4983230072969 + 3 ^ 40 * 2978571 * 2
def baseEnd_2978571 : Nat := 1529438586543171060964307

theorem tailTrace_2978571 : CollatzResearch.WordTrace tailWord_2978571 prefixEnd_2978571 1529438586543171060964307 := by
  unfold tailWord_2978571
  simp only [CollatzResearch.WordTrace]
  refine ⟨108637409292153441272279567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72424939528102294181519711 108637409292153441272279567)
  ·
    refine ⟨162956113938230161908419351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108637409292153441272279567 162956113938230161908419351)
    ·
      refine ⟨244434170907345242862629027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162956113938230161908419351 244434170907345242862629027)
      ·
        refine ⟨366651256361017864293943541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244434170907345242862629027 366651256361017864293943541)
        ·
          refine ⟨34373555283845424777557207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 366651256361017864293943541 34373555283845424777557207)
          ·
            refine ⟨51560332925768137166335811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34373555283845424777557207 51560332925768137166335811)
            ·
              refine ⟨77340499388652205749503717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51560332925768137166335811 77340499388652205749503717)
              ·
                refine ⟨14501343635372288578031947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77340499388652205749503717 14501343635372288578031947)
                ·
                  refine ⟨21752015453058432867047921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14501343635372288578031947 21752015453058432867047921)
                  ·
                    refine ⟨16314011589793824650285941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21752015453058432867047921 16314011589793824650285941)
                    ·
                      refine ⟨1529438586543171060964307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16314011589793824650285941 1529438586543171060964307)
                      ·
                        rfl

theorem cell23_2978571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 5].length) (baseStart_2978571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978571 prefixEnd_2978571 := by exact prefixLift 2978571
  have htrace : WordTrace (prefixWord ++ tailWord_2978571) baseStart_2978571 baseEnd_2978571 := by
    simpa [prefixWord, tailWord_2978571, baseEnd_2978571] using wordTrace_append hprefix tailTrace_2978571
  have hstable : (prefixWord ++ tailWord_2978571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978571).length < 2 ^ (prefixWord ++ tailWord_2978571).sum := by decide
  have hdescent : baseEnd_2978571 < baseStart_2978571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978588 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_2978588 : Nat := 118140960795 + 2978588 * 2 ^ 59
def prefixEnd_2978588 : Nat := 4983230072969 + 3 ^ 40 * 2978588 * 2
def baseEnd_2978588 : Nat := 1529447315714297494451729

theorem tailTrace_2978588 : CollatzResearch.WordTrace tailWord_2978588 prefixEnd_2978588 1529447315714297494451729 := by
  unfold tailWord_2978588
  simp only [CollatzResearch.WordTrace]
  refine ⟨54319014666545926587824209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72425352888727902117098945 54319014666545926587824209)
  ·
    refine ⟨40739260999909444940868157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54319014666545926587824209 40739260999909444940868157)
    ·
      refine ⟨15277222874966041852825559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40739260999909444940868157 15277222874966041852825559)
      ·
        refine ⟨22915834312449062779238339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15277222874966041852825559 22915834312449062779238339)
        ·
          refine ⟨34373751468673594168857509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22915834312449062779238339 34373751468673594168857509)
          ·
            refine ⟨6445078400376298906660783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34373751468673594168857509 6445078400376298906660783)
            ·
              refine ⟨9667617600564448359991175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6445078400376298906660783 9667617600564448359991175)
              ·
                refine ⟨14501426400846672539986763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9667617600564448359991175 14501426400846672539986763)
                ·
                  refine ⟨21752139601270008809980145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14501426400846672539986763 21752139601270008809980145)
                  ·
                    refine ⟨16314104700952506607485109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21752139601270008809980145 16314104700952506607485109)
                    ·
                      refine ⟨1529447315714297494451729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16314104700952506607485109 1529447315714297494451729)
                      ·
                        rfl

theorem cell23_2978588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_2978588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978588 prefixEnd_2978588 := by exact prefixLift 2978588
  have htrace : WordTrace (prefixWord ++ tailWord_2978588) baseStart_2978588 baseEnd_2978588 := by
    simpa [prefixWord, tailWord_2978588, baseEnd_2978588] using wordTrace_append hprefix tailTrace_2978588
  have hstable : (prefixWord ++ tailWord_2978588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978588).length < 2 ^ (prefixWord ++ tailWord_2978588).sum := by decide
  have hdescent : baseEnd_2978588 < baseStart_2978588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978608 : List Nat := [2, 1, 1, 1, 2, 2, 1, 6, 3, 4]
def baseStart_2978608 : Nat := 118140960795 + 2978608 * 2 ^ 59
def prefixEnd_2978608 : Nat := 4983230072969 + 3 ^ 40 * 2978608 * 2
def baseEnd_2978608 : Nat := 509819195109129138733879

theorem tailTrace_2978608 : CollatzResearch.WordTrace tailWord_2978608 prefixEnd_2978608 509819195109129138733879 := by
  unfold tailWord_2978608
  simp only [CollatzResearch.WordTrace]
  refine ⟨54319379396509698295688239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72425839195346264394250985 54319379396509698295688239)
  ·
    refine ⟨81479069094764547443532359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54319379396509698295688239 81479069094764547443532359)
    ·
      refine ⟨122218603642146821165298539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81479069094764547443532359 122218603642146821165298539)
      ·
        refine ⟨183327905463220231747947809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122218603642146821165298539 183327905463220231747947809)
        ·
          refine ⟨137495929097415173810960857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183327905463220231747947809 137495929097415173810960857)
          ·
            refine ⟨103121946823061380358220643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137495929097415173810960857 103121946823061380358220643)
            ·
              refine ⟨154682920234592070537330965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103121946823061380358220643 154682920234592070537330965)
              ·
                refine ⟨7250761885996503306437389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154682920234592070537330965 7250761885996503306437389)
                ·
                  refine ⟨2719035707248688739914021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7250761885996503306437389 2719035707248688739914021)
                  ·
                    refine ⟨509819195109129138733879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2719035707248688739914021 509819195109129138733879)
                    ·
                      rfl

theorem cell23_2978608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 3, 4].length) (baseStart_2978608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978608 prefixEnd_2978608 := by exact prefixLift 2978608
  have htrace : WordTrace (prefixWord ++ tailWord_2978608) baseStart_2978608 baseEnd_2978608 := by
    simpa [prefixWord, tailWord_2978608, baseEnd_2978608] using wordTrace_append hprefix tailTrace_2978608
  have hstable : (prefixWord ++ tailWord_2978608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978608).length < 2 ^ (prefixWord ++ tailWord_2978608).sum := by decide
  have hdescent : baseEnd_2978608 < baseStart_2978608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978612 : List Nat := [2, 5, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_2978612 : Nat := 118140960795 + 2978612 * 2 ^ 59
def prefixEnd_2978612 : Nat := 4983230072969 + 3 ^ 40 * 2978612 * 2
def baseEnd_2978612 : Nat := 509819879750001800183873

theorem tailTrace_2978612 : CollatzResearch.WordTrace tailWord_2978612 prefixEnd_2978612 509819879750001800183873 := by
  unfold tailWord_2978612
  simp only [CollatzResearch.WordTrace]
  refine ⟨54319452342502452637261045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72425936456669936849681393 54319452342502452637261045)
  ·
    refine ⟨5092448657109604934743223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54319452342502452637261045 5092448657109604934743223)
    ·
      refine ⟨7638672985664407402114835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5092448657109604934743223 7638672985664407402114835)
      ·
        refine ⟨11458009478496611103172253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7638672985664407402114835 11458009478496611103172253)
        ·
          refine ⟨4296753554436229163689595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11458009478496611103172253 4296753554436229163689595)
          ·
            refine ⟨6445130331654343745534393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4296753554436229163689595 6445130331654343745534393)
            ·
              refine ⟨4833847748740757809150795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6445130331654343745534393 4833847748740757809150795)
              ·
                refine ⟨7250771623111136713726193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4833847748740757809150795 7250771623111136713726193)
                ·
                  refine ⟨5438078717333352535294645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7250771623111136713726193 5438078717333352535294645)
                  ·
                    refine ⟨509819879750001800183873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5438078717333352535294645 509819879750001800183873)
                    ·
                      rfl

theorem cell23_2978612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_2978612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978612 prefixEnd_2978612 := by exact prefixLift 2978612
  have htrace : WordTrace (prefixWord ++ tailWord_2978612) baseStart_2978612 baseEnd_2978612 := by
    simpa [prefixWord, tailWord_2978612, baseEnd_2978612] using wordTrace_append hprefix tailTrace_2978612
  have hstable : (prefixWord ++ tailWord_2978612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978612).length < 2 ^ (prefixWord ++ tailWord_2978612).sum := by decide
  have hdescent : baseEnd_2978612 < baseStart_2978612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978642 : List Nat := [3, 2, 2, 1, 1, 2, 3, 4, 1, 4]
def baseStart_2978642 : Nat := 118140960795 + 2978642 * 2 ^ 59
def prefixEnd_2978642 : Nat := 4983230072969 + 3 ^ 40 * 2978642 * 2
def baseEnd_2978642 : Nat := 509825014556546761058827

theorem tailTrace_2978642 : CollatzResearch.WordTrace tailWord_2978642 prefixEnd_2978642 509825014556546761058827 := by
  unfold tailWord_2978642
  simp only [CollatzResearch.WordTrace]
  refine ⟨27159999718724055099528545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72426665916597480265409453 27159999718724055099528545)
  ·
    refine ⟨20369999789043041324646409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27159999718724055099528545 20369999789043041324646409)
    ·
      refine ⟨15277499841782280993484807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20369999789043041324646409 15277499841782280993484807)
      ·
        refine ⟨22916249762673421490227211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15277499841782280993484807 22916249762673421490227211)
        ·
          refine ⟨34374374644010132235340817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22916249762673421490227211 34374374644010132235340817)
          ·
            refine ⟨25780780983007599176505613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34374374644010132235340817 25780780983007599176505613)
            ·
              refine ⟨9667792868627849691189605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25780780983007599176505613 9667792868627849691189605)
              ·
                refine ⟨1812711162867721817098051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9667792868627849691189605 1812711162867721817098051)
                ·
                  refine ⟨2719066744301582725647077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1812711162867721817098051 2719066744301582725647077)
                  ·
                    refine ⟨509825014556546761058827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2719066744301582725647077 509825014556546761058827)
                    ·
                      rfl

theorem cell23_2978642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_2978642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978642 prefixEnd_2978642 := by exact prefixLift 2978642
  have htrace : WordTrace (prefixWord ++ tailWord_2978642) baseStart_2978642 baseEnd_2978642 := by
    simpa [prefixWord, tailWord_2978642, baseEnd_2978642] using wordTrace_append hprefix tailTrace_2978642
  have hstable : (prefixWord ++ tailWord_2978642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978642).length < 2 ^ (prefixWord ++ tailWord_2978642).sum := by decide
  have hdescent : baseEnd_2978642 < baseStart_2978642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978668 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 3, 5]
def baseStart_2978668 : Nat := 118140960795 + 2978668 * 2 ^ 59
def prefixEnd_2978668 : Nat := 4983230072969 + 3 ^ 40 * 2978668 * 2
def baseEnd_2978668 : Nat := 509829464722219060483787

theorem tailTrace_2978668 : CollatzResearch.WordTrace tailWord_2978668 prefixEnd_2978668 509829464722219060483787 := by
  unfold tailWord_2978668
  simp only [CollatzResearch.WordTrace]
  refine ⟨54320473586401013419280329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72427298115201351225707105 54320473586401013419280329)
  ·
    refine ⟨40740355189800760064460247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54320473586401013419280329 40740355189800760064460247)
    ·
      refine ⟨61110532784701140096690371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40740355189800760064460247 61110532784701140096690371)
      ·
        refine ⟨91665799177051710145035557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61110532784701140096690371 91665799177051710145035557)
        ·
          refine ⟨17187337345697195652194167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91665799177051710145035557 17187337345697195652194167)
          ·
            refine ⟨25781006018545793478291251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17187337345697195652194167 25781006018545793478291251)
            ·
              refine ⟨38671509027818690217436877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25781006018545793478291251 38671509027818690217436877)
              ·
                refine ⟨14501815885432008831538829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38671509027818690217436877 14501815885432008831538829)
                ·
                  refine ⟨5438180957037003311827061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14501815885432008831538829 5438180957037003311827061)
                  ·
                    refine ⟨509829464722219060483787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5438180957037003311827061 509829464722219060483787)
                    ·
                      rfl

theorem cell23_2978668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_2978668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978668 prefixEnd_2978668 := by exact prefixLift 2978668
  have htrace : WordTrace (prefixWord ++ tailWord_2978668) baseStart_2978668 baseEnd_2978668 := by
    simpa [prefixWord, tailWord_2978668, baseEnd_2978668] using wordTrace_append hprefix tailTrace_2978668
  have hstable : (prefixWord ++ tailWord_2978668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978668).length < 2 ^ (prefixWord ++ tailWord_2978668).sum := by decide
  have hdescent : baseEnd_2978668 < baseStart_2978668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978688 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 4]
def baseStart_2978688 : Nat := 118140960795 + 2978688 * 2 ^ 59
def prefixEnd_2978688 : Nat := 4983230072969 + 3 ^ 40 * 2978688 * 2
def baseEnd_2978688 : Nat := 1529498663779747103201269

theorem tailTrace_2978688 : CollatzResearch.WordTrace tailWord_2978688 prefixEnd_2978688 1529498663779747103201269 := by
  unfold tailWord_2978688
  simp only [CollatzResearch.WordTrace]
  refine ⟨54320838316364785127144359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72427784421819713502859145 54320838316364785127144359)
  ·
    refine ⟨81481257474547177690716539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54320838316364785127144359 81481257474547177690716539)
    ·
      refine ⟨122221886211820766536074809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81481257474547177690716539 122221886211820766536074809)
      ·
        refine ⟨91666414658865574902056107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122221886211820766536074809 91666414658865574902056107)
        ·
          refine ⟨137499621988298362353084161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91666414658865574902056107 137499621988298362353084161)
          ·
            refine ⟨103124716491223771764813121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137499621988298362353084161 103124716491223771764813121)
            ·
              refine ⟨77343537368417828823609841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103124716491223771764813121 77343537368417828823609841)
              ·
                refine ⟨58007653026313371617707381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77343537368417828823609841 58007653026313371617707381)
                ·
                  refine ⟨5438217471216878589160067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58007653026313371617707381 5438217471216878589160067)
                  ·
                    refine ⟨8157326206825317883740101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5438217471216878589160067 8157326206825317883740101)
                    ·
                      refine ⟨1529498663779747103201269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8157326206825317883740101 1529498663779747103201269)
                      ·
                        rfl

theorem cell23_2978688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_2978688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978688 prefixEnd_2978688 := by exact prefixLift 2978688
  have htrace : WordTrace (prefixWord ++ tailWord_2978688) baseStart_2978688 baseEnd_2978688 := by
    simpa [prefixWord, tailWord_2978688, baseEnd_2978688] using wordTrace_append hprefix tailTrace_2978688
  have hstable : (prefixWord ++ tailWord_2978688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978688).length < 2 ^ (prefixWord ++ tailWord_2978688).sum := by decide
  have hdescent : baseEnd_2978688 < baseStart_2978688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978722 : List Nat := [3, 3, 1, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_2978722 : Nat := 118140960795 + 2978722 * 2 ^ 59
def prefixEnd_2978722 : Nat := 4983230072969 + 3 ^ 40 * 2978722 * 2
def baseEnd_2978722 : Nat := 1529516122121999970176113

theorem tailTrace_2978722 : CollatzResearch.WordTrace tailWord_2978722 prefixEnd_2978722 1529516122121999970176113 := by
  unfold tailWord_2978722
  simp only [CollatzResearch.WordTrace]
  refine ⟨27160729178651598515256605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72428611143070929374017613 27160729178651598515256605)
  ·
    refine ⟨10185273441994349443221227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27160729178651598515256605 10185273441994349443221227)
    ·
      refine ⟨15277910162991524164831841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10185273441994349443221227 15277910162991524164831841)
      ·
        refine ⟨11458432622243643123623881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15277910162991524164831841 11458432622243643123623881)
        ·
          refine ⟨8593824466682732342717911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11458432622243643123623881 8593824466682732342717911)
          ·
            refine ⟨12890736700024098514076867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8593824466682732342717911 12890736700024098514076867)
            ·
              refine ⟨19336105050036147771115301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12890736700024098514076867 19336105050036147771115301)
              ·
                refine ⟨3625519696881777707084119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19336105050036147771115301 3625519696881777707084119)
                ·
                  refine ⟨5438279545322666560626179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3625519696881777707084119 5438279545322666560626179)
                  ·
                    refine ⟨8157419317983999840939269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5438279545322666560626179 8157419317983999840939269)
                    ·
                      refine ⟨1529516122121999970176113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8157419317983999840939269 1529516122121999970176113)
                      ·
                        rfl

theorem cell23_2978722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_2978722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978722 prefixEnd_2978722 := by exact prefixLift 2978722
  have htrace : WordTrace (prefixWord ++ tailWord_2978722) baseStart_2978722 baseEnd_2978722 := by
    simpa [prefixWord, tailWord_2978722, baseEnd_2978722] using wordTrace_append hprefix tailTrace_2978722
  have hstable : (prefixWord ++ tailWord_2978722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978722).length < 2 ^ (prefixWord ++ tailWord_2978722).sum := by decide
  have hdescent : baseEnd_2978722 < baseStart_2978722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978739 : List Nat := [1, 1, 1, 2, 3, 1, 2, 7, 1, 2, 2]
def baseStart_2978739 : Nat := 118140960795 + 2978739 * 2 ^ 59
def prefixEnd_2978739 : Nat := 4983230072969 + 3 ^ 40 * 2978739 * 2
def baseEnd_2978739 : Nat := 1529524851293126403663535

theorem tailTrace_2978739 : CollatzResearch.WordTrace tailWord_2978739 prefixEnd_2978739 1529524851293126403663535 := by
  unfold tailWord_2978739
  simp only [CollatzResearch.WordTrace]
  refine ⟨108643536755544805964395271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72429024503696537309596847 108643536755544805964395271)
  ·
    refine ⟨162965305133317208946592907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108643536755544805964395271 162965305133317208946592907)
    ·
      refine ⟨244447957699975813419889361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162965305133317208946592907 244447957699975813419889361)
      ·
        refine ⟨183335968274981860064917021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244447957699975813419889361 183335968274981860064917021)
        ·
          refine ⟨68750988103118197524343883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183335968274981860064917021 68750988103118197524343883)
          ·
            refine ⟨103126482154677296286515825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68750988103118197524343883 103126482154677296286515825)
            ·
              refine ⟨77344861616007972214886869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103126482154677296286515825 77344861616007972214886869)
              ·
                refine ⟨1812770194125186848786411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 77344861616007972214886869 1812770194125186848786411)
                ·
                  refine ⟨2719155291187780273179617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1812770194125186848786411 2719155291187780273179617)
                  ·
                    refine ⟨2039366468390835204884713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2719155291187780273179617 2039366468390835204884713)
                    ·
                      refine ⟨1529524851293126403663535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2039366468390835204884713 1529524851293126403663535)
                      ·
                        rfl

theorem cell23_2978739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 1, 2, 2].length) (baseStart_2978739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978739 prefixEnd_2978739 := by exact prefixLift 2978739
  have htrace : WordTrace (prefixWord ++ tailWord_2978739) baseStart_2978739 baseEnd_2978739 := by
    simpa [prefixWord, tailWord_2978739, baseEnd_2978739] using wordTrace_append hprefix tailTrace_2978739
  have hstable : (prefixWord ++ tailWord_2978739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978739).length < 2 ^ (prefixWord ++ tailWord_2978739).sum := by decide
  have hdescent : baseEnd_2978739 < baseStart_2978739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978788 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 3, 8]
def baseStart_2978788 : Nat := 118140960795 + 2978788 * 2 ^ 59
def prefixEnd_2978788 : Nat := 4983230072969 + 3 ^ 40 * 2978788 * 2
def baseEnd_2978788 : Nat := 509850003948398903983603

theorem tailTrace_2978788 : CollatzResearch.WordTrace tailWord_2978788 prefixEnd_2978788 509850003948398903983603 := by
  unfold tailWord_2978788
  simp only [CollatzResearch.WordTrace]
  refine ⟨54322661966183643666464509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72430215954911524888619345 54322661966183643666464509)
  ·
    refine ⟨20370998237318866374924191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54322661966183643666464509 20370998237318866374924191)
    ·
      refine ⟨30556497355978299562386287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20370998237318866374924191 30556497355978299562386287)
      ·
        refine ⟨45834746033967449343579431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30556497355978299562386287 45834746033967449343579431)
        ·
          refine ⟨68752119050951174015369147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45834746033967449343579431 68752119050951174015369147)
          ·
            refine ⟨103128178576426761023053721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68752119050951174015369147 103128178576426761023053721)
            ·
              refine ⟨77346133932320070767290291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103128178576426761023053721 77346133932320070767290291)
              ·
                refine ⟨116019200898480106150935437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77346133932320070767290291 116019200898480106150935437)
                ·
                  refine ⟨43507200336930039806600789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116019200898480106150935437 43507200336930039806600789)
                  ·
                    refine ⟨509850003948398903983603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43507200336930039806600789 509850003948398903983603)
                    ·
                      rfl

theorem cell23_2978788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_2978788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978788 prefixEnd_2978788 := by exact prefixLift 2978788
  have htrace : WordTrace (prefixWord ++ tailWord_2978788) baseStart_2978788 baseEnd_2978788 := by
    simpa [prefixWord, tailWord_2978788, baseEnd_2978788] using wordTrace_append hprefix tailTrace_2978788
  have hstable : (prefixWord ++ tailWord_2978788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978788).length < 2 ^ (prefixWord ++ tailWord_2978788).sum := by decide
  have hdescent : baseEnd_2978788 < baseStart_2978788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978789 : List Nat := [1, 3, 1, 6, 1, 1, 1, 2, 1, 3, 3]
def baseStart_2978789 : Nat := 118140960795 + 2978789 * 2 ^ 59
def prefixEnd_2978789 : Nat := 4983230072969 + 3 ^ 40 * 2978789 * 2
def baseEnd_2978789 : Nat := 1529550525325851208038305

theorem tailTrace_2978789 : CollatzResearch.WordTrace tailWord_2978789 prefixEnd_2978789 1529550525325851208038305 := by
  unfold tailWord_2978789
  simp only [CollatzResearch.WordTrace]
  refine ⟨108645360405363664503715421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72430240270242443002476947 108645360405363664503715421)
  ·
    refine ⟨40742010152011374188893283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108645360405363664503715421 40742010152011374188893283)
    ·
      refine ⟨61113015228017061283339925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40742010152011374188893283 61113015228017061283339925)
      ·
        refine ⟨2864672588813299747656559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61113015228017061283339925 2864672588813299747656559)
        ·
          refine ⟨4297008883219949621484839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2864672588813299747656559 4297008883219949621484839)
          ·
            refine ⟨6445513324829924432227259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4297008883219949621484839 6445513324829924432227259)
            ·
              refine ⟨9668269987244886648340889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6445513324829924432227259 9668269987244886648340889)
              ·
                refine ⟨7251202490433664986255667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9668269987244886648340889 7251202490433664986255667)
                ·
                  refine ⟨10876803735650497479383501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7251202490433664986255667 10876803735650497479383501)
                  ·
                    refine ⟨4078801400868936554768813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10876803735650497479383501 4078801400868936554768813)
                    ·
                      refine ⟨1529550525325851208038305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4078801400868936554768813 1529550525325851208038305)
                      ·
                        rfl

theorem cell23_2978789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_2978789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978789 prefixEnd_2978789 := by exact prefixLift 2978789
  have htrace : WordTrace (prefixWord ++ tailWord_2978789) baseStart_2978789 baseEnd_2978789 := by
    simpa [prefixWord, tailWord_2978789, baseEnd_2978789] using wordTrace_append hprefix tailTrace_2978789
  have hstable : (prefixWord ++ tailWord_2978789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978789).length < 2 ^ (prefixWord ++ tailWord_2978789).sum := by decide
  have hdescent : baseEnd_2978789 < baseStart_2978789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978806 : List Nat := [5, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_2978806 : Nat := 118140960795 + 2978806 * 2 ^ 59
def prefixEnd_2978806 : Nat := 4983230072969 + 3 ^ 40 * 2978806 * 2
def baseEnd_2978806 : Nat := 1529559254496977641525727

theorem tailTrace_2978806 : CollatzResearch.WordTrace tailWord_2978806 prefixEnd_2978806 1529559254496977641525727 := by
  unfold tailWord_2978806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6790373777893879775442767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72430653630868050938056181 6790373777893879775442767)
  ·
    refine ⟨10185560666840819663164151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6790373777893879775442767 10185560666840819663164151)
    ·
      refine ⟨15278341000261229494746227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10185560666840819663164151 15278341000261229494746227)
      ·
        refine ⟨22917511500391844242119341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15278341000261229494746227 22917511500391844242119341)
        ·
          refine ⟨8594066812646941590794753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22917511500391844242119341 8594066812646941590794753)
          ·
            refine ⟨6445550109485206193096065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8594066812646941590794753 6445550109485206193096065)
            ·
              refine ⟨4834162582113904644822049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6445550109485206193096065 4834162582113904644822049)
              ·
                refine ⟨3625621936585428483616537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4834162582113904644822049 3625621936585428483616537)
                ·
                  refine ⟨2719216452439071362712403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3625621936585428483616537 2719216452439071362712403)
                  ·
                    refine ⟨4078824678658607044068605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2719216452439071362712403 4078824678658607044068605)
                    ·
                      refine ⟨1529559254496977641525727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4078824678658607044068605 1529559254496977641525727)
                      ·
                        rfl

theorem cell23_2978806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_2978806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978806 prefixEnd_2978806 := by exact prefixLift 2978806
  have htrace : WordTrace (prefixWord ++ tailWord_2978806) baseStart_2978806 baseEnd_2978806 := by
    simpa [prefixWord, tailWord_2978806, baseEnd_2978806] using wordTrace_append hprefix tailTrace_2978806
  have hstable : (prefixWord ++ tailWord_2978806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978806).length < 2 ^ (prefixWord ++ tailWord_2978806).sum := by decide
  have hdescent : baseEnd_2978806 < baseStart_2978806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978808 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 2, 3, 6]
def baseStart_2978808 : Nat := 118140960795 + 2978808 * 2 ^ 59
def prefixEnd_2978808 : Nat := 4983230072969 + 3 ^ 40 * 2978808 * 2
def baseEnd_2978808 : Nat := 1529560281458286633700717

theorem tailTrace_2978808 : CollatzResearch.WordTrace tailWord_2978808 prefixEnd_2978808 1529560281458286633700717 := by
  unfold tailWord_2978808
  simp only [CollatzResearch.WordTrace]
  refine ⟨54323026696147415374328539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72430702261529887165771385 54323026696147415374328539)
  ·
    refine ⟨81484540044221123061492809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54323026696147415374328539 81484540044221123061492809)
    ·
      refine ⟨61113405033165842296119607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81484540044221123061492809 61113405033165842296119607)
      ·
        refine ⟨91670107549748763444179411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61113405033165842296119607 91670107549748763444179411)
        ·
          refine ⟨137505161324623145166269117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91670107549748763444179411 137505161324623145166269117)
          ·
            refine ⟨51564435496733679437350919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137505161324623145166269117 51564435496733679437350919)
            ·
              refine ⟨77346653245100519156026379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51564435496733679437350919 77346653245100519156026379)
              ·
                refine ⟨116019979867650778734039569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77346653245100519156026379 116019979867650778734039569)
                ·
                  refine ⟨87014984900738084050529677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116019979867650778734039569 87014984900738084050529677)
                  ·
                    refine ⟨32630619337776781518948629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87014984900738084050529677 32630619337776781518948629)
                    ·
                      refine ⟨1529560281458286633700717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32630619337776781518948629 1529560281458286633700717)
                      ·
                        rfl

theorem cell23_2978808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_2978808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978808 prefixEnd_2978808 := by exact prefixLift 2978808
  have htrace : WordTrace (prefixWord ++ tailWord_2978808) baseStart_2978808 baseEnd_2978808 := by
    simpa [prefixWord, tailWord_2978808, baseEnd_2978808] using wordTrace_append hprefix tailTrace_2978808
  have hstable : (prefixWord ++ tailWord_2978808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978808).length < 2 ^ (prefixWord ++ tailWord_2978808).sum := by decide
  have hdescent : baseEnd_2978808 < baseStart_2978808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978862 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_2978862 : Nat := 118140960795 + 2978862 * 2 ^ 59
def prefixEnd_2978862 : Nat := 4983230072969 + 3 ^ 40 * 2978862 * 2
def baseEnd_2978862 : Nat := 1529588009413629422425469

theorem tailTrace_2978862 : CollatzResearch.WordTrace tailWord_2978862 prefixEnd_2978862 1529588009413629422425469 := by
  unfold tailWord_2978862
  simp only [CollatzResearch.WordTrace]
  refine ⟨13581002866762399746390355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72432015289399465314081893 13581002866762399746390355)
  ·
    refine ⟨20371504300143599619585533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13581002866762399746390355 20371504300143599619585533)
    ·
      refine ⟨7639314112553849857344575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20371504300143599619585533 7639314112553849857344575)
      ·
        refine ⟨11458971168830774786016863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7639314112553849857344575 11458971168830774786016863)
        ·
          refine ⟨17188456753246162179025295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11458971168830774786016863 17188456753246162179025295)
          ·
            refine ⟨25782685129869243268537943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17188456753246162179025295 25782685129869243268537943)
            ·
              refine ⟨38674027694803864902806915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25782685129869243268537943 38674027694803864902806915)
              ·
                refine ⟨58011041542205797354210373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38674027694803864902806915 58011041542205797354210373)
                ·
                  refine ⟨10877070289163587003914445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58011041542205797354210373 10877070289163587003914445)
                  ·
                    refine ⟨4078901358436345126467917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10877070289163587003914445 4078901358436345126467917)
                    ·
                      refine ⟨1529588009413629422425469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4078901358436345126467917 1529588009413629422425469)
                      ·
                        rfl

theorem cell23_2978862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_2978862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978862 prefixEnd_2978862 := by exact prefixLift 2978862
  have htrace : WordTrace (prefixWord ++ tailWord_2978862) baseStart_2978862 baseEnd_2978862 := by
    simpa [prefixWord, tailWord_2978862, baseEnd_2978862] using wordTrace_append hprefix tailTrace_2978862
  have hstable : (prefixWord ++ tailWord_2978862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978862).length < 2 ^ (prefixWord ++ tailWord_2978862).sum := by decide
  have hdescent : baseEnd_2978862 < baseStart_2978862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978865 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 4, 5]
def baseStart_2978865 : Nat := 118140960795 + 2978865 * 2 ^ 59
def prefixEnd_2978865 : Nat := 4983230072969 + 3 ^ 40 * 2978865 * 2
def baseEnd_2978865 : Nat := 509863183285197636895985

theorem tailTrace_2978865 : CollatzResearch.WordTrace tailWord_2978865 prefixEnd_2978865 509863183285197636895985 := by
  unfold tailWord_2978865
  simp only [CollatzResearch.WordTrace]
  refine ⟨108648132353088329483482049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72432088235392219655654699 108648132353088329483482049)
  ·
    refine ⟨81486099264816247112611537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108648132353088329483482049 81486099264816247112611537)
    ·
      refine ⟨61114574448612185334458653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81486099264816247112611537 61114574448612185334458653)
      ·
        refine ⟨22917965418229569500421995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61114574448612185334458653 22917965418229569500421995)
        ·
          refine ⟨34376948127344354250632993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22917965418229569500421995 34376948127344354250632993)
          ·
            refine ⟨25782711095508265687974745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34376948127344354250632993 25782711095508265687974745)
            ·
              refine ⟨19337033321631199265981059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25782711095508265687974745 19337033321631199265981059)
              ·
                refine ⟨29005549982446798898971589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19337033321631199265981059 29005549982446798898971589)
                ·
                  refine ⟨5438540621708774793557173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29005549982446798898971589 5438540621708774793557173)
                  ·
                    refine ⟨509863183285197636895985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5438540621708774793557173 509863183285197636895985)
                    ·
                      rfl

theorem cell23_2978865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_2978865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978865 prefixEnd_2978865 := by exact prefixLift 2978865
  have htrace : WordTrace (prefixWord ++ tailWord_2978865) baseStart_2978865 baseEnd_2978865 := by
    simpa [prefixWord, tailWord_2978865, baseEnd_2978865] using wordTrace_append hprefix tailTrace_2978865
  have hstable : (prefixWord ++ tailWord_2978865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978865).length < 2 ^ (prefixWord ++ tailWord_2978865).sum := by decide
  have hdescent : baseEnd_2978865 < baseStart_2978865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978885 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 1, 3, 4]
def baseStart_2978885 : Nat := 118140960795 + 2978885 * 2 ^ 59
def prefixEnd_2978885 : Nat := 4983230072969 + 3 ^ 40 * 2978885 * 2
def baseEnd_2978885 : Nat := 1529599819468682832437863

theorem tailTrace_2978885 : CollatzResearch.WordTrace tailWord_2978885 prefixEnd_2978885 1529599819468682832437863 := by
  unfold tailWord_2978885
  simp only [CollatzResearch.WordTrace]
  refine ⟨108648861813015872899210109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72432574542010581932806739 108648861813015872899210109)
  ·
    refine ⟨40743323179880952337203791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108648861813015872899210109 40743323179880952337203791)
    ·
      refine ⟨61114984769821428505805687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40743323179880952337203791 61114984769821428505805687)
      ·
        refine ⟨91672477154732142758708531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61114984769821428505805687 91672477154732142758708531)
        ·
          refine ⟨137508715732098214138062797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91672477154732142758708531 137508715732098214138062797)
          ·
            refine ⟨51565768399536830301773549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137508715732098214138062797 51565768399536830301773549)
            ·
              refine ⟨19337163149826311363165081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51565768399536830301773549 19337163149826311363165081)
              ·
                refine ⟨14502872362369733522373811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19337163149826311363165081 14502872362369733522373811)
                ·
                  refine ⟨21754308543554600283560717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14502872362369733522373811 21754308543554600283560717)
                  ·
                    refine ⟨8157865703832975106335269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21754308543554600283560717 8157865703832975106335269)
                    ·
                      refine ⟨1529599819468682832437863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8157865703832975106335269 1529599819468682832437863)
                      ·
                        rfl

theorem cell23_2978885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_2978885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978885 prefixEnd_2978885 := by exact prefixLift 2978885
  have htrace : WordTrace (prefixWord ++ tailWord_2978885) baseStart_2978885 baseEnd_2978885 := by
    simpa [prefixWord, tailWord_2978885, baseEnd_2978885] using wordTrace_append hprefix tailTrace_2978885
  have hstable : (prefixWord ++ tailWord_2978885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978885).length < 2 ^ (prefixWord ++ tailWord_2978885).sum := by decide
  have hdescent : baseEnd_2978885 < baseStart_2978885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2978965 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_2978965 : Nat := 118140960795 + 2978965 * 2 ^ 59
def prefixEnd_2978965 : Nat := 4983230072969 + 3 ^ 40 * 2978965 * 2
def baseEnd_2978965 : Nat := 1529640897921042519437495

theorem tailTrace_2978965 : CollatzResearch.WordTrace tailWord_2978965 prefixEnd_2978965 1529640897921042519437495 := by
  unfold tailWord_2978965
  simp only [CollatzResearch.WordTrace]
  refine ⟨108651779652726046562122349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72434519768484031041414899 108651779652726046562122349)
  ·
    refine ⟨40744417369772267460795881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108651779652726046562122349 40744417369772267460795881)
    ·
      refine ⟨30558313027329200595596911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40744417369772267460795881 30558313027329200595596911)
      ·
        refine ⟨45837469540993800893395367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30558313027329200595596911 45837469540993800893395367)
        ·
          refine ⟨68756204311490701340093051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45837469540993800893395367 68756204311490701340093051)
          ·
            refine ⟨103134306467236052010139577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68756204311490701340093051 103134306467236052010139577)
            ·
              refine ⟨77350729850427039007604683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103134306467236052010139577 77350729850427039007604683)
              ·
                refine ⟨116026094775640558511407025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77350729850427039007604683 116026094775640558511407025)
                ·
                  refine ⟨87019571081730418883555269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116026094775640558511407025 87019571081730418883555269)
                  ·
                    refine ⟨16316169577824453540666613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87019571081730418883555269 16316169577824453540666613)
                    ·
                      refine ⟨1529640897921042519437495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16316169577824453540666613 1529640897921042519437495)
                      ·
                        rfl

theorem cell23_2978965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_2978965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2978965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2978965 prefixEnd_2978965 := by exact prefixLift 2978965
  have htrace : WordTrace (prefixWord ++ tailWord_2978965) baseStart_2978965 baseEnd_2978965 := by
    simpa [prefixWord, tailWord_2978965, baseEnd_2978965] using wordTrace_append hprefix tailTrace_2978965
  have hstable : (prefixWord ++ tailWord_2978965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2978965).length < 2 ^ (prefixWord ++ tailWord_2978965).sum := by decide
  have hdescent : baseEnd_2978965 < baseStart_2978965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2978965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979002 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 6, 4]
def baseStart_2979002 : Nat := 118140960795 + 2979002 * 2 ^ 59
def prefixEnd_2979002 : Nat := 4983230072969 + 3 ^ 40 * 2979002 * 2
def baseEnd_2979002 : Nat := 509886632235086291558275

theorem tailTrace_2979002 : CollatzResearch.WordTrace tailWord_2979002 prefixEnd_2979002 509886632235086291558275 := by
  unfold tailWord_2979002
  simp only [CollatzResearch.WordTrace]
  refine ⟨27163282288398000470304815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72435419435728001254146173 27163282288398000470304815)
  ·
    refine ⟨40744923432597000705457223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27163282288398000470304815 40744923432597000705457223)
    ·
      refine ⟨61117385148895501058185835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40744923432597000705457223 61117385148895501058185835)
      ·
        refine ⟨91676077723343251587278753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61117385148895501058185835 91676077723343251587278753)
        ·
          refine ⟨68757058292507438690459065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91676077723343251587278753 68757058292507438690459065)
          ·
            refine ⟨51567793719380579017844299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68757058292507438690459065 51567793719380579017844299)
            ·
              refine ⟨77351690579070868526766449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51567793719380579017844299 77351690579070868526766449)
              ·
                refine ⟨58013767934303151395074837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77351690579070868526766449 58013767934303151395074837)
                ·
                  refine ⟨2719395371920460221644133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58013767934303151395074837 2719395371920460221644133)
                  ·
                    refine ⟨509886632235086291558275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2719395371920460221644133 509886632235086291558275)
                    ·
                      rfl

theorem cell23_2979002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_2979002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979002 prefixEnd_2979002 := by exact prefixLift 2979002
  have htrace : WordTrace (prefixWord ++ tailWord_2979002) baseStart_2979002 baseEnd_2979002 := by
    simpa [prefixWord, tailWord_2979002, baseEnd_2979002] using wordTrace_append hprefix tailTrace_2979002
  have hstable : (prefixWord ++ tailWord_2979002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979002).length < 2 ^ (prefixWord ++ tailWord_2979002).sum := by decide
  have hdescent : baseEnd_2979002 < baseStart_2979002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979015 : List Nat := [1, 1, 4, 1, 1, 1, 1, 13]
def baseStart_2979015 : Nat := 118140960795 + 2979015 * 2 ^ 59
def prefixEnd_2979015 : Nat := 4983230072969 + 3 ^ 40 * 2979015 * 2
def baseEnd_2979015 : Nat := 56654317479769160141195

theorem tailTrace_2979015 : CollatzResearch.WordTrace tailWord_2979015 prefixEnd_2979015 56654317479769160141195 := by
  unfold tailWord_2979015
  simp only [CollatzResearch.WordTrace]
  refine ⟨108653603302544905101442499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72435735535029936734294999 108653603302544905101442499)
  ·
    refine ⟨162980404953817357652163749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108653603302544905101442499 162980404953817357652163749)
    ·
      refine ⟨30558825928840754559780703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162980404953817357652163749 30558825928840754559780703)
      ·
        refine ⟨45838238893261131839671055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30558825928840754559780703 45838238893261131839671055)
        ·
          refine ⟨68757358339891697759506583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45838238893261131839671055 68757358339891697759506583)
          ·
            refine ⟨103136037509837546639259875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68757358339891697759506583 103136037509837546639259875)
            ·
              refine ⟨154704056264756319958889813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103136037509837546639259875 154704056264756319958889813)
              ·
                refine ⟨56654317479769160141195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 154704056264756319958889813 56654317479769160141195)
                ·
                  rfl

theorem cell23_2979015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 13].length) (baseStart_2979015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979015 prefixEnd_2979015 := by exact prefixLift 2979015
  have htrace : WordTrace (prefixWord ++ tailWord_2979015) baseStart_2979015 baseEnd_2979015 := by
    simpa [prefixWord, tailWord_2979015, baseEnd_2979015] using wordTrace_append hprefix tailTrace_2979015
  have hstable : (prefixWord ++ tailWord_2979015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979015).length < 2 ^ (prefixWord ++ tailWord_2979015).sum := by decide
  have hdescent : baseEnd_2979015 < baseStart_2979015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979026 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 5, 2, 2]
def baseStart_2979026 : Nat := 118140960795 + 2979026 * 2 ^ 59
def prefixEnd_2979026 : Nat := 4983230072969 + 3 ^ 40 * 2979026 * 2
def baseEnd_2979026 : Nat := 1529672220240966780774715

theorem tailTrace_2979026 : CollatzResearch.WordTrace tailWord_2979026 prefixEnd_2979026 1529672220240966780774715 := by
  unfold tailWord_2979026
  simp only [CollatzResearch.WordTrace]
  refine ⟨27163501126376263495023233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72436003003670035986728621 27163501126376263495023233)
  ·
    refine ⟨20372625844782197621267425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27163501126376263495023233 20372625844782197621267425)
    ·
      refine ⟨15279469383586648215950569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20372625844782197621267425 15279469383586648215950569)
      ·
        refine ⟨11459602037689986161962927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15279469383586648215950569 11459602037689986161962927)
        ·
          refine ⟨17189403056534979242944391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11459602037689986161962927 17189403056534979242944391)
          ·
            refine ⟨25784104584802468864416587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17189403056534979242944391 25784104584802468864416587)
            ·
              refine ⟨38676156877203703296624881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25784104584802468864416587 38676156877203703296624881)
              ·
                refine ⟨29007117657902777472468661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38676156877203703296624881 29007117657902777472468661)
                ·
                  refine ⟨2719417280428385388043937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29007117657902777472468661 2719417280428385388043937)
                  ·
                    refine ⟨2039562960321289041032953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2719417280428385388043937 2039562960321289041032953)
                    ·
                      refine ⟨1529672220240966780774715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2039562960321289041032953 1529672220240966780774715)
                      ·
                        rfl

theorem cell23_2979026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_2979026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979026 prefixEnd_2979026 := by exact prefixLift 2979026
  have htrace : WordTrace (prefixWord ++ tailWord_2979026) baseStart_2979026 baseEnd_2979026 := by
    simpa [prefixWord, tailWord_2979026, baseEnd_2979026] using wordTrace_append hprefix tailTrace_2979026
  have hstable : (prefixWord ++ tailWord_2979026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979026).length < 2 ^ (prefixWord ++ tailWord_2979026).sum := by decide
  have hdescent : baseEnd_2979026 < baseStart_2979026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979032 : List Nat := [2, 1, 2, 2, 5, 1, 10]
def baseStart_2979032 : Nat := 118140960795 + 2979032 * 2 ^ 59
def prefixEnd_2979032 : Nat := 4983230072969 + 3 ^ 40 * 2979032 * 2
def baseEnd_2979032 : Nat := 18884880260801157497527

theorem tailTrace_2979032 : CollatzResearch.WordTrace tailWord_2979032 prefixEnd_2979032 18884880260801157497527 := by
  unfold tailWord_2979032
  simp only [CollatzResearch.WordTrace]
  refine ⟨54327111671741658502405675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72436148895655544669874233 54327111671741658502405675)
  ·
    refine ⟨81490667507612487753608513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54327111671741658502405675 81490667507612487753608513)
    ·
      refine ⟨61118000630709365815206385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81490667507612487753608513 61118000630709365815206385)
      ·
        refine ⟨45838500473032024361404789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61118000630709365815206385 45838500473032024361404789)
        ·
          refine ⟨4297359419346752283881699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45838500473032024361404789 4297359419346752283881699)
          ·
            refine ⟨6446039129020128425822549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4297359419346752283881699 6446039129020128425822549)
            ·
              refine ⟨18884880260801157497527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6446039129020128425822549 18884880260801157497527)
              ·
                rfl

theorem cell23_2979032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 10].length) (baseStart_2979032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979032 prefixEnd_2979032 := by exact prefixLift 2979032
  have htrace : WordTrace (prefixWord ++ tailWord_2979032) baseStart_2979032 baseEnd_2979032 := by
    simpa [prefixWord, tailWord_2979032, baseEnd_2979032] using wordTrace_append hprefix tailTrace_2979032
  have hstable : (prefixWord ++ tailWord_2979032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979032).length < 2 ^ (prefixWord ++ tailWord_2979032).sum := by decide
  have hdescent : baseEnd_2979032 < baseStart_2979032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979053 : List Nat := [1, 5, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_2979053 : Nat := 118140960795 + 2979053 * 2 ^ 59
def prefixEnd_2979053 : Nat := 4983230072969 + 3 ^ 40 * 2979053 * 2
def baseEnd_2979053 : Nat := 509895361406212725045697

theorem tailTrace_2979053 : CollatzResearch.WordTrace tailWord_2979053 prefixEnd_2979053 509895361406212725045697 := by
  unfold tailWord_2979053
  simp only [CollatzResearch.WordTrace]
  refine ⟨108654989276407237591325813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72436659517604825060883875 108654989276407237591325813)
  ·
    refine ⟨10186405244663178524186795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108654989276407237591325813 10186405244663178524186795)
    ·
      refine ⟨15279607866994767786280193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10186405244663178524186795 15279607866994767786280193)
      ·
        refine ⟨11459705900246075839710145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15279607866994767786280193 11459705900246075839710145)
        ·
          refine ⟨8594779425184556879782609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11459705900246075839710145 8594779425184556879782609)
          ·
            refine ⟨6446084568888417659836957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8594779425184556879782609 6446084568888417659836957)
            ·
              refine ⟨2417281713333156622438859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6446084568888417659836957 2417281713333156622438859)
              ·
                refine ⟨3625922569999734933658289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2417281713333156622438859 3625922569999734933658289)
                ·
                  refine ⟨2719441927499801200243717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3625922569999734933658289 2719441927499801200243717)
                  ·
                    refine ⟨509895361406212725045697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2719441927499801200243717 509895361406212725045697)
                    ·
                      rfl

theorem cell23_2979053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_2979053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979053 prefixEnd_2979053 := by exact prefixLift 2979053
  have htrace : WordTrace (prefixWord ++ tailWord_2979053) baseStart_2979053 baseEnd_2979053 := by
    simpa [prefixWord, tailWord_2979053, baseEnd_2979053] using wordTrace_append hprefix tailTrace_2979053
  have hstable : (prefixWord ++ tailWord_2979053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979053).length < 2 ^ (prefixWord ++ tailWord_2979053).sum := by decide
  have hdescent : baseEnd_2979053 < baseStart_2979053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979059 : List Nat := [1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 3]
def baseStart_2979059 : Nat := 118140960795 + 2979059 * 2 ^ 59
def prefixEnd_2979059 : Nat := 4983230072969 + 3 ^ 40 * 2979059 * 2
def baseEnd_2979059 : Nat := 1529689165102565151662063

theorem tailTrace_2979059 : CollatzResearch.WordTrace tailWord_2979059 prefixEnd_2979059 1529689165102565151662063 := by
  unfold tailWord_2979059
  simp only [CollatzResearch.WordTrace]
  refine ⟨108655208114385500616044231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72436805409590333744029487 108655208114385500616044231)
  ·
    refine ⟨162982812171578250924066347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108655208114385500616044231 162982812171578250924066347)
    ·
      refine ⟨244474218257367376386099521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162982812171578250924066347 244474218257367376386099521)
      ·
        refine ⟨183355663693025532289574641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244474218257367376386099521 183355663693025532289574641)
        ·
          refine ⟨137516747769769149217180981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183355663693025532289574641 137516747769769149217180981)
          ·
            refine ⟨12892195103415857739110717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137516747769769149217180981 12892195103415857739110717)
            ·
              refine ⟨4834573163780946652166519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12892195103415857739110717 4834573163780946652166519)
              ·
                refine ⟨7251859745671419978249779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4834573163780946652166519 7251859745671419978249779)
                ·
                  refine ⟨10877789618507129967374669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7251859745671419978249779 10877789618507129967374669)
                  ·
                    refine ⟨4079171106940173737765501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10877789618507129967374669 4079171106940173737765501)
                    ·
                      refine ⟨1529689165102565151662063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4079171106940173737765501 1529689165102565151662063)
                      ·
                        rfl

theorem cell23_2979059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 3].length) (baseStart_2979059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979059 prefixEnd_2979059 := by exact prefixLift 2979059
  have htrace : WordTrace (prefixWord ++ tailWord_2979059) baseStart_2979059 baseEnd_2979059 := by
    simpa [prefixWord, tailWord_2979059, baseEnd_2979059] using wordTrace_append hprefix tailTrace_2979059
  have hstable : (prefixWord ++ tailWord_2979059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979059).length < 2 ^ (prefixWord ++ tailWord_2979059).sum := by decide
  have hdescent : baseEnd_2979059 < baseStart_2979059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979076 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_2979076 : Nat := 118140960795 + 2979076 * 2 ^ 59
def prefixEnd_2979076 : Nat := 4983230072969 + 3 ^ 40 * 2979076 * 2
def baseEnd_2979076 : Nat := 1529697894273691585149485

theorem tailTrace_2979076 : CollatzResearch.WordTrace tailWord_2979076 prefixEnd_2979076 1529697894273691585149485 := by
  unfold tailWord_2979076
  simp only [CollatzResearch.WordTrace]
  refine ⟨54327914077661956259706541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72437218770215941679608721 54327914077661956259706541)
  ·
    refine ⟨20372967779123233597389953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54327914077661956259706541 20372967779123233597389953)
    ·
      refine ⟨15279725834342425198042465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20372967779123233597389953 15279725834342425198042465)
      ·
        refine ⟨11459794375756818898531849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15279725834342425198042465 11459794375756818898531849)
        ·
          refine ⟨8594845781817614173898887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11459794375756818898531849 8594845781817614173898887)
          ·
            refine ⟨12892268672726421260848331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8594845781817614173898887 12892268672726421260848331)
            ·
              refine ⟨19338403009089631891272497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12892268672726421260848331 19338403009089631891272497)
              ·
                refine ⟨14503802256817223918454373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19338403009089631891272497 14503802256817223918454373)
                ·
                  refine ⟨2719462923153229484710195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14503802256817223918454373 2719462923153229484710195)
                  ·
                    refine ⟨4079194384729844227065293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2719462923153229484710195 4079194384729844227065293)
                    ·
                      refine ⟨1529697894273691585149485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4079194384729844227065293 1529697894273691585149485)
                      ·
                        rfl

theorem cell23_2979076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_2979076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979076 prefixEnd_2979076 := by exact prefixLift 2979076
  have htrace : WordTrace (prefixWord ++ tailWord_2979076) baseStart_2979076 baseEnd_2979076 := by
    simpa [prefixWord, tailWord_2979076, baseEnd_2979076] using wordTrace_append hprefix tailTrace_2979076
  have hstable : (prefixWord ++ tailWord_2979076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979076).length < 2 ^ (prefixWord ++ tailWord_2979076).sum := by decide
  have hdescent : baseEnd_2979076 < baseStart_2979076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979082 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_2979082 : Nat := 118140960795 + 2979082 * 2 ^ 59
def prefixEnd_2979082 : Nat := 4983230072969 + 3 ^ 40 * 2979082 * 2
def baseEnd_2979082 : Nat := 1529700975157618561674457

theorem tailTrace_2979082 : CollatzResearch.WordTrace tailWord_2979082 prefixEnd_2979082 1529700975157618561674457 := by
  unfold tailWord_2979082
  simp only [CollatzResearch.WordTrace]
  refine ⟨27164011748325543886032875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72437364662201450362754333 27164011748325543886032875)
  ·
    refine ⟨40746017622488315829049313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27164011748325543886032875 40746017622488315829049313)
    ·
      refine ⟨30559513216866236871786985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40746017622488315829049313 30559513216866236871786985)
      ·
        refine ⟨22919634912649677653840239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30559513216866236871786985 22919634912649677653840239)
        ·
          refine ⟨34379452368974516480760359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22919634912649677653840239 34379452368974516480760359)
          ·
            refine ⟨51569178553461774721140539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34379452368974516480760359 51569178553461774721140539)
            ·
              refine ⟨77353767830192662081710809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51569178553461774721140539 77353767830192662081710809)
              ·
                refine ⟨58015325872644496561283107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77353767830192662081710809 58015325872644496561283107)
                ·
                  refine ⟨87022988808966744841924661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58015325872644496561283107 87022988808966744841924661)
                  ·
                    refine ⟨8158405200840632328930437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87022988808966744841924661 8158405200840632328930437)
                    ·
                      refine ⟨1529700975157618561674457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8158405200840632328930437 1529700975157618561674457)
                      ·
                        rfl

theorem cell23_2979082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_2979082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979082 prefixEnd_2979082 := by exact prefixLift 2979082
  have htrace : WordTrace (prefixWord ++ tailWord_2979082) baseStart_2979082 baseEnd_2979082 := by
    simpa [prefixWord, tailWord_2979082, baseEnd_2979082] using wordTrace_append hprefix tailTrace_2979082
  have hstable : (prefixWord ++ tailWord_2979082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979082).length < 2 ^ (prefixWord ++ tailWord_2979082).sum := by decide
  have hdescent : baseEnd_2979082 < baseStart_2979082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979139 : List Nat := [1, 1, 1, 3, 1, 3, 1, 7, 5]
def baseStart_2979139 : Nat := 118140960795 + 2979139 * 2 ^ 59
def prefixEnd_2979139 : Nat := 4983230072969 + 3 ^ 40 * 2979139 * 2
def baseEnd_2979139 : Nat := 169970027061658315406855

theorem tailTrace_2979139 : CollatzResearch.WordTrace tailWord_2979139 prefixEnd_2979139 169970027061658315406855 := by
  unfold tailWord_2979139
  simp only [CollatzResearch.WordTrace]
  refine ⟨108658125954095674278956471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72438750636063782852637647 108658125954095674278956471)
  ·
    refine ⟨162987188931143511418434707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108658125954095674278956471 162987188931143511418434707)
    ·
      refine ⟨244480783396715267127652061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162987188931143511418434707 244480783396715267127652061)
      ·
        refine ⟨91680293773768225172869523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244480783396715267127652061 91680293773768225172869523)
        ·
          refine ⟨137520440660652337759304285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91680293773768225172869523 137520440660652337759304285)
          ·
            refine ⟨51570165247744626659739107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137520440660652337759304285 51570165247744626659739107)
            ·
              refine ⟨77355247871616939989608661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51570165247744626659739107 77355247871616939989608661)
              ·
                refine ⟨1813013621991022031006453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 77355247871616939989608661 1813013621991022031006453)
                ·
                  refine ⟨169970027061658315406855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1813013621991022031006453 169970027061658315406855)
                  ·
                    rfl

theorem cell23_2979139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 5].length) (baseStart_2979139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979139 prefixEnd_2979139 := by exact prefixLift 2979139
  have htrace : WordTrace (prefixWord ++ tailWord_2979139) baseStart_2979139 baseEnd_2979139 := by
    simpa [prefixWord, tailWord_2979139, baseEnd_2979139] using wordTrace_append hprefix tailTrace_2979139
  have hstable : (prefixWord ++ tailWord_2979139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979139).length < 2 ^ (prefixWord ++ tailWord_2979139).sum := by decide
  have hdescent : baseEnd_2979139 < baseStart_2979139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979156 : List Nat := [2, 4, 1, 1, 2, 1, 3, 4, 5]
def baseStart_2979156 : Nat := 118140960795 + 2979156 * 2 ^ 59
def prefixEnd_2979156 : Nat := 4983230072969 + 3 ^ 40 * 2979156 * 2
def baseEnd_2979156 : Nat := 169970996969561252461013

theorem tailTrace_2979156 : CollatzResearch.WordTrace tailWord_2979156 prefixEnd_2979156 169970996969561252461013 := by
  unfold tailWord_2979156
  simp only [CollatzResearch.WordTrace]
  refine ⟨54329372997517043091162661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72439163996689390788216881 54329372997517043091162661)
  ·
    refine ⟨10186757437034445579592999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54329372997517043091162661 10186757437034445579592999)
    ·
      refine ⟨15280136155551668369389499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10186757437034445579592999 15280136155551668369389499)
      ·
        refine ⟨22920204233327502554084249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15280136155551668369389499 22920204233327502554084249)
        ·
          refine ⟨17190153174995626915563187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22920204233327502554084249 17190153174995626915563187)
          ·
            refine ⟨25785229762493440373344781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17190153174995626915563187 25785229762493440373344781)
            ·
              refine ⟨9669461160935040140004293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25785229762493440373344781 9669461160935040140004293)
              ·
                refine ⟨1813023967675320026250805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9669461160935040140004293 1813023967675320026250805)
                ·
                  refine ⟨169970996969561252461013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1813023967675320026250805 169970996969561252461013)
                  ·
                    rfl

theorem cell23_2979156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_2979156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979156 prefixEnd_2979156 := by exact prefixLift 2979156
  have htrace : WordTrace (prefixWord ++ tailWord_2979156) baseStart_2979156 baseEnd_2979156 := by
    simpa [prefixWord, tailWord_2979156, baseEnd_2979156] using wordTrace_append hprefix tailTrace_2979156
  have hstable : (prefixWord ++ tailWord_2979156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979156).length < 2 ^ (prefixWord ++ tailWord_2979156).sum := by decide
  have hdescent : baseEnd_2979156 < baseStart_2979156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979256 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 5, 1, 3]
def baseStart_2979256 : Nat := 118140960795 + 2979256 * 2 ^ 59
def prefixEnd_2979256 : Nat := 4983230072969 + 3 ^ 40 * 2979256 * 2
def baseEnd_2979256 : Nat := 1529790320791500880898657

theorem tailTrace_2979256 : CollatzResearch.WordTrace tailWord_2979256 prefixEnd_2979256 1529790320791500880898657 := by
  unfold tailWord_2979256
  simp only [CollatzResearch.WordTrace]
  refine ⟨54331196647335901630482811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72441595529781202173977081 54331196647335901630482811)
  ·
    refine ⟨81496794971003852445724217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54331196647335901630482811 81496794971003852445724217)
    ·
      refine ⟨61122596228252889334293163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81496794971003852445724217 61122596228252889334293163)
      ·
        refine ⟨91683894342379334001439745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61122596228252889334293163 91683894342379334001439745)
        ·
          refine ⟨68762920756784500501079809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91683894342379334001439745 68762920756784500501079809)
          ·
            refine ⟨51572190567588375375809857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68762920756784500501079809 51572190567588375375809857)
            ·
              refine ⟨38679142925691281531857393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51572190567588375375809857 38679142925691281531857393)
              ·
                refine ⟨29009357194268461148893045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38679142925691281531857393 29009357194268461148893045)
                ·
                  refine ⟨2719627236962668232708723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29009357194268461148893045 2719627236962668232708723)
                  ·
                    refine ⟨4079440855444002349063085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2719627236962668232708723 4079440855444002349063085)
                    ·
                      refine ⟨1529790320791500880898657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4079440855444002349063085 1529790320791500880898657)
                      ·
                        rfl

theorem cell23_2979256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 5, 1, 3].length) (baseStart_2979256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979256 prefixEnd_2979256 := by exact prefixLift 2979256
  have htrace : WordTrace (prefixWord ++ tailWord_2979256) baseStart_2979256 baseEnd_2979256 := by
    simpa [prefixWord, tailWord_2979256, baseEnd_2979256] using wordTrace_append hprefix tailTrace_2979256
  have hstable : (prefixWord ++ tailWord_2979256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979256).length < 2 ^ (prefixWord ++ tailWord_2979256).sum := by decide
  have hdescent : baseEnd_2979256 < baseStart_2979256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979293 : List Nat := [1, 4, 3, 1, 1, 2, 3, 2, 1, 5]
def baseStart_2979293 : Nat := 118140960795 + 2979293 * 2 ^ 59
def prefixEnd_2979293 : Nat := 4983230072969 + 3 ^ 40 * 2979293 * 2
def baseEnd_2979293 : Nat := 509936439858572412045329

theorem tailTrace_2979293 : CollatzResearch.WordTrace tailWord_2979293 prefixEnd_2979293 509936439858572412045329 := by
  unfold tailWord_2979293
  simp only [CollatzResearch.WordTrace]
  refine ⟨108663742795537758580062533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72442495197025172386708355 108663742795537758580062533)
  ·
    refine ⟨20374451774163329733761725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108663742795537758580062533 20374451774163329733761725)
    ·
      refine ⟨7640419415311248650160647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20374451774163329733761725 7640419415311248650160647)
      ·
        refine ⟨11460629122966872975240971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7640419415311248650160647 11460629122966872975240971)
        ·
          refine ⟨17190943684450309462861457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11460629122966872975240971 17190943684450309462861457)
          ·
            refine ⟨12893207763337732097146093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17190943684450309462861457 12893207763337732097146093)
            ·
              refine ⟨4834952911251649536429785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12893207763337732097146093 4834952911251649536429785)
              ·
                refine ⟨3626214683438737152322339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4834952911251649536429785 3626214683438737152322339)
                ·
                  refine ⟨5439322025158105728483509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3626214683438737152322339 5439322025158105728483509)
                  ·
                    refine ⟨509936439858572412045329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5439322025158105728483509 509936439858572412045329)
                    ·
                      rfl

theorem cell23_2979293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_2979293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979293 prefixEnd_2979293 := by exact prefixLift 2979293
  have htrace : WordTrace (prefixWord ++ tailWord_2979293) baseStart_2979293 baseEnd_2979293 := by
    simpa [prefixWord, tailWord_2979293, baseEnd_2979293] using wordTrace_append hprefix tailTrace_2979293
  have hstable : (prefixWord ++ tailWord_2979293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979293).length < 2 ^ (prefixWord ++ tailWord_2979293).sum := by decide
  have hdescent : baseEnd_2979293 < baseStart_2979293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979296 : List Nat := [2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 4]
def baseStart_2979296 : Nat := 118140960795 + 2979296 * 2 ^ 59
def prefixEnd_2979296 : Nat := 4983230072969 + 3 ^ 40 * 2979296 * 2
def baseEnd_2979296 : Nat := 1529810860017680724398473

theorem tailTrace_2979296 : CollatzResearch.WordTrace tailWord_2979296 prefixEnd_2979296 1529810860017680724398473 := by
  unfold tailWord_2979296
  simp only [CollatzResearch.WordTrace]
  refine ⟨54331926107263445046210871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72442568143017926728281161 54331926107263445046210871)
  ·
    refine ⟨81497889160895167569316307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54331926107263445046210871 81497889160895167569316307)
    ·
      refine ⟨122246833741342751353974461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81497889160895167569316307 122246833741342751353974461)
      ·
        refine ⟨45842562653003531757740423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122246833741342751353974461 45842562653003531757740423)
        ·
          refine ⟨68763843979505297636610635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45842562653003531757740423 68763843979505297636610635)
          ·
            refine ⟨103145765969257946454915953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68763843979505297636610635 103145765969257946454915953)
            ·
              refine ⟨77359324476943459841186965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103145765969257946454915953 77359324476943459841186965)
              ·
                refine ⟨3626218334856724680055639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77359324476943459841186965 3626218334856724680055639)
                ·
                  refine ⟨5439327502285087020083459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3626218334856724680055639 5439327502285087020083459)
                  ·
                    refine ⟨8158991253427630530125189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5439327502285087020083459 8158991253427630530125189)
                    ·
                      refine ⟨1529810860017680724398473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8158991253427630530125189 1529810860017680724398473)
                      ·
                        rfl

theorem cell23_2979296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_2979296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979296 prefixEnd_2979296 := by exact prefixLift 2979296
  have htrace : WordTrace (prefixWord ++ tailWord_2979296) baseStart_2979296 baseEnd_2979296 := by
    simpa [prefixWord, tailWord_2979296, baseEnd_2979296] using wordTrace_append hprefix tailTrace_2979296
  have hstable : (prefixWord ++ tailWord_2979296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979296).length < 2 ^ (prefixWord ++ tailWord_2979296).sum := by decide
  have hdescent : baseEnd_2979296 < baseStart_2979296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979358 : List Nat := [4, 3, 3, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_2979358 : Nat := 118140960795 + 2979358 * 2 ^ 59
def prefixEnd_2979358 : Nat := 4983230072969 + 3 ^ 40 * 2979358 * 2
def baseEnd_2979358 : Nat := 1529842695818259481823189

theorem tailTrace_2979358 : CollatzResearch.WordTrace tailWord_2979358 prefixEnd_2979358 1529842695818259481823189 := by
  unfold tailWord_2979358
  simp only [CollatzResearch.WordTrace]
  refine ⟨13583264192537784335147341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72444075693534849787452485 13583264192537784335147341)
  ·
    refine ⟨5093724072201669125680253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13583264192537784335147341 5093724072201669125680253)
    ·
      refine ⟨1910146527075625922130095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5093724072201669125680253 1910146527075625922130095)
      ·
        refine ⟨2865219790613438883195143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1910146527075625922130095 2865219790613438883195143)
        ·
          refine ⟨4297829685920158324792715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2865219790613438883195143 4297829685920158324792715)
          ·
            refine ⟨6446744528880237487189073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4297829685920158324792715 6446744528880237487189073)
            ·
              refine ⟨4835058396660178115391805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6446744528880237487189073 4835058396660178115391805)
              ·
                refine ⟨1813146898747566793271927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4835058396660178115391805 1813146898747566793271927)
                ·
                  refine ⟨2719720348121350189907891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1813146898747566793271927 2719720348121350189907891)
                  ·
                    refine ⟨4079580522182025284861837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2719720348121350189907891 4079580522182025284861837)
                    ·
                      refine ⟨1529842695818259481823189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4079580522182025284861837 1529842695818259481823189)
                      ·
                        rfl

theorem cell23_2979358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_2979358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979358 prefixEnd_2979358 := by exact prefixLift 2979358
  have htrace : WordTrace (prefixWord ++ tailWord_2979358) baseStart_2979358 baseEnd_2979358 := by
    simpa [prefixWord, tailWord_2979358, baseEnd_2979358] using wordTrace_append hprefix tailTrace_2979358
  have hstable : (prefixWord ++ tailWord_2979358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979358).length < 2 ^ (prefixWord ++ tailWord_2979358).sum := by decide
  have hdescent : baseEnd_2979358 < baseStart_2979358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979406 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_2979406 : Nat := 118140960795 + 2979406 * 2 ^ 59
def prefixEnd_2979406 : Nat := 4983230072969 + 3 ^ 40 * 2979406 * 2
def baseEnd_2979406 : Nat := 1529867342889675294022967

theorem tailTrace_2979406 : CollatzResearch.WordTrace tailWord_2979406 prefixEnd_2979406 1529867342889675294022967 := by
  unfold tailWord_2979406
  simp only [CollatzResearch.WordTrace]
  refine ⟨13583483030516047359865759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72445242829418919252617381 13583483030516047359865759)
  ·
    refine ⟨20375224545774071039798639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13583483030516047359865759 20375224545774071039798639)
    ·
      refine ⟨30562836818661106559697959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20375224545774071039798639 30562836818661106559697959)
      ·
        refine ⟨45844255227991659839546939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30562836818661106559697959 45844255227991659839546939)
        ·
          refine ⟨68766382841987489759320409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45844255227991659839546939 68766382841987489759320409)
          ·
            refine ⟨51574787131490617319490307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68766382841987489759320409 51574787131490617319490307)
            ·
              refine ⟨77362180697235925979235461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51574787131490617319490307 77362180697235925979235461)
              ·
                refine ⟨14505408880731736121106649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77362180697235925979235461 14505408880731736121106649)
                ·
                  refine ⟨10879056660548802090829987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14505408880731736121106649 10879056660548802090829987)
                  ·
                    refine ⟨16318584990823203136244981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10879056660548802090829987 16318584990823203136244981)
                    ·
                      refine ⟨1529867342889675294022967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16318584990823203136244981 1529867342889675294022967)
                      ·
                        rfl

theorem cell23_2979406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_2979406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979406 prefixEnd_2979406 := by exact prefixLift 2979406
  have htrace : WordTrace (prefixWord ++ tailWord_2979406) baseStart_2979406 baseEnd_2979406 := by
    simpa [prefixWord, tailWord_2979406, baseEnd_2979406] using wordTrace_append hprefix tailTrace_2979406
  have hstable : (prefixWord ++ tailWord_2979406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979406).length < 2 ^ (prefixWord ++ tailWord_2979406).sum := by decide
  have hdescent : baseEnd_2979406 < baseStart_2979406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979456 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 4, 5]
def baseStart_2979456 : Nat := 118140960795 + 2979456 * 2 ^ 59
def prefixEnd_2979456 : Nat := 4983230072969 + 3 ^ 40 * 2979456 * 2
def baseEnd_2979456 : Nat := 509964338974133366132579

theorem tailTrace_2979456 : CollatzResearch.WordTrace tailWord_2979456 prefixEnd_2979456 509964338974133366132579 := by
  unfold tailWord_2979456
  simp only [CollatzResearch.WordTrace]
  refine ⟨54334843946973618709123111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72446458595964824945497481 54334843946973618709123111)
  ·
    refine ⟨81502265920460428063684667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54334843946973618709123111 81502265920460428063684667)
    ·
      refine ⟨122253398880690642095527001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81502265920460428063684667 122253398880690642095527001)
      ·
        refine ⟨91690049160517981571645251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122253398880690642095527001 91690049160517981571645251)
        ·
          refine ⟨137535073740776972357467877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91690049160517981571645251 137535073740776972357467877)
          ·
            refine ⟨25787826326395682317025227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137535073740776972357467877 25787826326395682317025227)
            ·
              refine ⟨38681739489593523475537841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25787826326395682317025227 38681739489593523475537841)
              ·
                refine ⟨29011304617195142606653381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38681739489593523475537841 29011304617195142606653381)
                ·
                  refine ⟨5439619615724089238747509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29011304617195142606653381 5439619615724089238747509)
                  ·
                    refine ⟨509964338974133366132579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5439619615724089238747509 509964338974133366132579)
                    ·
                      rfl

theorem cell23_2979456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 4, 5].length) (baseStart_2979456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979456 prefixEnd_2979456 := by exact prefixLift 2979456
  have htrace : WordTrace (prefixWord ++ tailWord_2979456) baseStart_2979456 baseEnd_2979456 := by
    simpa [prefixWord, tailWord_2979456, baseEnd_2979456] using wordTrace_append hprefix tailTrace_2979456
  have hstable : (prefixWord ++ tailWord_2979456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979456).length < 2 ^ (prefixWord ++ tailWord_2979456).sum := by decide
  have hdescent : baseEnd_2979456 < baseStart_2979456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979493 : List Nat := [1, 3, 1, 2, 1, 2, 4, 2, 2, 1, 4]
def baseStart_2979493 : Nat := 118140960795 + 2979493 * 2 ^ 59
def prefixEnd_2979493 : Nat := 4983230072969 + 3 ^ 40 * 2979493 * 2
def baseEnd_2979493 : Nat := 1529912015706616453635067

theorem tailTrace_2979493 : CollatzResearch.WordTrace tailWord_2979493 prefixEnd_2979493 1529912015706616453635067 := by
  unfold tailWord_2979493
  simp only [CollatzResearch.WordTrace]
  refine ⟨108671037394813192737343133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72447358263208795158228755 108671037394813192737343133)
  ·
    refine ⟨40751639023054947276503675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108671037394813192737343133 40751639023054947276503675)
    ·
      refine ⟨61127458534582420914755513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40751639023054947276503675 61127458534582420914755513)
      ·
        refine ⟨45845593900936815686066635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61127458534582420914755513 45845593900936815686066635)
        ·
          refine ⟨68768390851405223529099953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45845593900936815686066635 68768390851405223529099953)
          ·
            refine ⟨51576293138553917646824965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68768390851405223529099953 51576293138553917646824965)
            ·
              refine ⟨9670554963478859558779681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51576293138553917646824965 9670554963478859558779681)
              ·
                refine ⟨7252916222609144669084761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9670554963478859558779681 7252916222609144669084761)
                ·
                  refine ⟨5439687166956858501813571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7252916222609144669084761 5439687166956858501813571)
                  ·
                    refine ⟨8159530750435287752720357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5439687166956858501813571 8159530750435287752720357)
                    ·
                      refine ⟨1529912015706616453635067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8159530750435287752720357 1529912015706616453635067)
                      ·
                        rfl

theorem cell23_2979493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_2979493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979493 prefixEnd_2979493 := by exact prefixLift 2979493
  have htrace : WordTrace (prefixWord ++ tailWord_2979493) baseStart_2979493 baseEnd_2979493 := by
    simpa [prefixWord, tailWord_2979493, baseEnd_2979493] using wordTrace_append hprefix tailTrace_2979493
  have hstable : (prefixWord ++ tailWord_2979493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979493).length < 2 ^ (prefixWord ++ tailWord_2979493).sum := by decide
  have hdescent : baseEnd_2979493 < baseStart_2979493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979503 : List Nat := [1, 1, 2, 1, 2, 4, 2, 3, 3, 4]
def baseStart_2979503 : Nat := 118140960795 + 2979503 * 2 ^ 59
def prefixEnd_2979503 : Nat := 4983230072969 + 3 ^ 40 * 2979503 * 2
def baseEnd_2979503 : Nat := 509972383504387138170007

theorem tailTrace_2979503 : CollatzResearch.WordTrace tailWord_2979503 prefixEnd_2979503 509972383504387138170007 := by
  unfold tailWord_2979503
  simp only [CollatzResearch.WordTrace]
  refine ⟨108671402124776964445207163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72447601416517976296804775 108671402124776964445207163)
  ·
    refine ⟨163007103187165446667810745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108671402124776964445207163 163007103187165446667810745)
    ·
      refine ⟨122255327390374085000858059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163007103187165446667810745 122255327390374085000858059)
      ·
        refine ⟨183382991085561127501287089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122255327390374085000858059 183382991085561127501287089)
        ·
          refine ⟨137537243314170845625965317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183382991085561127501287089 137537243314170845625965317)
          ·
            refine ⟨25788233121407033554868497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137537243314170845625965317 25788233121407033554868497)
            ·
              refine ⟨19341174841055275166151373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25788233121407033554868497 19341174841055275166151373)
              ·
                refine ⟨7252940565395728187306765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19341174841055275166151373 7252940565395728187306765)
                ·
                  refine ⟨2719852712023398070240037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7252940565395728187306765 2719852712023398070240037)
                  ·
                    refine ⟨509972383504387138170007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2719852712023398070240037 509972383504387138170007)
                    ·
                      rfl

theorem cell23_2979503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 4].length) (baseStart_2979503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979503 prefixEnd_2979503 := by exact prefixLift 2979503
  have htrace : WordTrace (prefixWord ++ tailWord_2979503) baseStart_2979503 baseEnd_2979503 := by
    simpa [prefixWord, tailWord_2979503, baseEnd_2979503] using wordTrace_append hprefix tailTrace_2979503
  have hstable : (prefixWord ++ tailWord_2979503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979503).length < 2 ^ (prefixWord ++ tailWord_2979503).sum := by decide
  have hdescent : baseEnd_2979503 < baseStart_2979503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979513 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 4, 2, 3]
def baseStart_2979513 : Nat := 118140960795 + 2979513 * 2 ^ 59
def prefixEnd_2979513 : Nat := 4983230072969 + 3 ^ 40 * 2979513 * 2
def baseEnd_2979513 : Nat := 1529922285319706375384975

theorem tailTrace_2979513 : CollatzResearch.WordTrace tailWord_2979513 prefixEnd_2979513 1529922285319706375384975 := by
  unfold tailWord_2979513
  simp only [CollatzResearch.WordTrace]
  refine ⟨108671766854740736153071193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72447844569827157435380795 108671766854740736153071193)
  ·
    refine ⟨81503825141055552114803395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108671766854740736153071193 81503825141055552114803395)
    ·
      refine ⟨122255737711583328172205093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81503825141055552114803395 122255737711583328172205093)
      ·
        refine ⟨22922950820921874032288455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122255737711583328172205093 22922950820921874032288455)
        ·
          refine ⟨34384426231382811048432683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22922950820921874032288455 34384426231382811048432683)
          ·
            refine ⟨51576639347074216572649025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34384426231382811048432683 51576639347074216572649025)
            ·
              refine ⟨38682479510305662429486769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51576639347074216572649025 38682479510305662429486769)
              ·
                refine ⟨29011859632729246822115077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38682479510305662429486769 29011859632729246822115077)
                ·
                  refine ⟨5439723681136733779146577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29011859632729246822115077 5439723681136733779146577)
                  ·
                    refine ⟨4079792760852550334359933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5439723681136733779146577 4079792760852550334359933)
                    ·
                      refine ⟨1529922285319706375384975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4079792760852550334359933 1529922285319706375384975)
                      ·
                        rfl

theorem cell23_2979513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_2979513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979513 prefixEnd_2979513 := by exact prefixLift 2979513
  have htrace : WordTrace (prefixWord ++ tailWord_2979513) baseStart_2979513 baseEnd_2979513 := by
    simpa [prefixWord, tailWord_2979513, baseEnd_2979513] using wordTrace_append hprefix tailTrace_2979513
  have hstable : (prefixWord ++ tailWord_2979513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979513).length < 2 ^ (prefixWord ++ tailWord_2979513).sum := by decide
  have hdescent : baseEnd_2979513 < baseStart_2979513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979530 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 1, 4, 3]
def baseStart_2979530 : Nat := 118140960795 + 2979530 * 2 ^ 59
def prefixEnd_2979530 : Nat := 4983230072969 + 3 ^ 40 * 2979530 * 2
def baseEnd_2979530 : Nat := 1529931014490832808872397

theorem tailTrace_2979530 : CollatzResearch.WordTrace tailWord_2979530 prefixEnd_2979530 1529931014490832808872397 := by
  unfold tailWord_2979530
  simp only [CollatzResearch.WordTrace]
  refine ⟨27168096723919787014110011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72448257930452765370960029 27168096723919787014110011)
  ·
    refine ⟨40752145085879680521165017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27168096723919787014110011 40752145085879680521165017)
    ·
      refine ⟨30564108814409760390873763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40752145085879680521165017 30564108814409760390873763)
      ·
        refine ⟨45846163221614640586310645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30564108814409760390873763 45846163221614640586310645)
        ·
          refine ⟨4298077802026372554966623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45846163221614640586310645 4298077802026372554966623)
          ·
            refine ⟨6447116703039558832449935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298077802026372554966623 6447116703039558832449935)
            ·
              refine ⟨9670675054559338248674903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6447116703039558832449935 9670675054559338248674903)
              ·
                refine ⟨14506012581839007373012355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9670675054559338248674903 14506012581839007373012355)
                ·
                  refine ⟨21759018872758511059518533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14506012581839007373012355 21759018872758511059518533)
                  ·
                    refine ⟨4079816038642220823659725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21759018872758511059518533 4079816038642220823659725)
                    ·
                      refine ⟨1529931014490832808872397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4079816038642220823659725 1529931014490832808872397)
                      ·
                        rfl

theorem cell23_2979530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_2979530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979530 prefixEnd_2979530 := by exact prefixLift 2979530
  have htrace : WordTrace (prefixWord ++ tailWord_2979530) baseStart_2979530 baseEnd_2979530 := by
    simpa [prefixWord, tailWord_2979530, baseEnd_2979530] using wordTrace_append hprefix tailTrace_2979530
  have hstable : (prefixWord ++ tailWord_2979530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979530).length < 2 ^ (prefixWord ++ tailWord_2979530).sum := by decide
  have hdescent : baseEnd_2979530 < baseStart_2979530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979537 : List Nat := [1, 2, 2, 1, 2, 5, 2, 3, 1, 4]
def baseStart_2979537 : Nat := 118140960795 + 2979537 * 2 ^ 59
def prefixEnd_2979537 : Nat := 4983230072969 + 3 ^ 40 * 2979537 * 2
def baseEnd_2979537 : Nat := 509978202951804760494955

theorem tailTrace_2979537 : CollatzResearch.WordTrace tailWord_2979537 prefixEnd_2979537 509978202951804760494955 := by
  unfold tailWord_2979537
  simp only [CollatzResearch.WordTrace]
  refine ⟨108672642206653788251944865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72448428137769192167963243 108672642206653788251944865)
  ·
    refine ⟨81504481654990341188958649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108672642206653788251944865 81504481654990341188958649)
    ·
      refine ⟨61128361241242755891718987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81504481654990341188958649 61128361241242755891718987)
      ·
        refine ⟨91692541861864133837578481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61128361241242755891718987 91692541861864133837578481)
        ·
          refine ⟨68769406396398100378183861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91692541861864133837578481 68769406396398100378183861)
          ·
            refine ⟨6447131849662321910454737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68769406396398100378183861 6447131849662321910454737)
            ·
              refine ⟨4835348887246741432841053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6447131849662321910454737 4835348887246741432841053)
              ·
                refine ⟨1813255832717528037315395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4835348887246741432841053 1813255832717528037315395)
                ·
                  refine ⟨2719883749076292055973093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1813255832717528037315395 2719883749076292055973093)
                  ·
                    refine ⟨509978202951804760494955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2719883749076292055973093 509978202951804760494955)
                    ·
                      rfl

theorem cell23_2979537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 1, 4].length) (baseStart_2979537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979537 prefixEnd_2979537 := by exact prefixLift 2979537
  have htrace : WordTrace (prefixWord ++ tailWord_2979537) baseStart_2979537 baseEnd_2979537 := by
    simpa [prefixWord, tailWord_2979537, baseEnd_2979537] using wordTrace_append hprefix tailTrace_2979537
  have hstable : (prefixWord ++ tailWord_2979537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979537).length < 2 ^ (prefixWord ++ tailWord_2979537).sum := by decide
  have hdescent : baseEnd_2979537 < baseStart_2979537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979570 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 3, 5, 2]
def baseStart_2979570 : Nat := 118140960795 + 2979570 * 2 ^ 59
def prefixEnd_2979570 : Nat := 4983230072969 + 3 ^ 40 * 2979570 * 2
def baseEnd_2979570 : Nat := 1529951553717012652372213

theorem tailTrace_2979570 : CollatzResearch.WordTrace tailWord_2979570 prefixEnd_2979570 1529951553717012652372213 := by
  unfold tailWord_2979570
  simp only [CollatzResearch.WordTrace]
  refine ⟨27168461453883558721974041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72449230543689489925264109 27168461453883558721974041)
  ·
    refine ⟨20376346090412669041480531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27168461453883558721974041 20376346090412669041480531)
    ·
      refine ⟨30564519135619003562220797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20376346090412669041480531 30564519135619003562220797)
      ·
        refine ⟨11461694675857126335832799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30564519135619003562220797 11461694675857126335832799)
        ·
          refine ⟨17192542013785689503749199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11461694675857126335832799 17192542013785689503749199)
          ·
            refine ⟨25788813020678534255623799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17192542013785689503749199 25788813020678534255623799)
            ·
              refine ⟨38683219531017801383435699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25788813020678534255623799 38683219531017801383435699)
              ·
                refine ⟨58024829296526702075153549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38683219531017801383435699 58024829296526702075153549)
                ·
                  refine ⟨21759310986197513278182581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58024829296526702075153549 21759310986197513278182581)
                  ·
                    refine ⟨2039935404956016869829617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21759310986197513278182581 2039935404956016869829617)
                    ·
                      refine ⟨1529951553717012652372213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2039935404956016869829617 1529951553717012652372213)
                      ·
                        rfl

theorem cell23_2979570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_2979570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979570 prefixEnd_2979570 := by exact prefixLift 2979570
  have htrace : WordTrace (prefixWord ++ tailWord_2979570) baseStart_2979570 baseEnd_2979570 := by
    simpa [prefixWord, tailWord_2979570, baseEnd_2979570] using wordTrace_append hprefix tailTrace_2979570
  have hstable : (prefixWord ++ tailWord_2979570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979570).length < 2 ^ (prefixWord ++ tailWord_2979570).sum := by decide
  have hdescent : baseEnd_2979570 < baseStart_2979570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979580 : List Nat := [2, 2, 2, 1, 3, 1, 4, 2, 1, 5]
def baseStart_2979580 : Nat := 118140960795 + 2979580 * 2 ^ 59
def prefixEnd_2979580 : Nat := 4983230072969 + 3 ^ 40 * 2979580 * 2
def baseEnd_2979580 : Nat := 509985562841185871082389

theorem tailTrace_2979580 : CollatzResearch.WordTrace tailWord_2979580 prefixEnd_2979580 509985562841185871082389 := by
  unfold tailWord_2979580
  simp only [CollatzResearch.WordTrace]
  refine ⟨54337105272749003297880097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72449473696998671063840129 54337105272749003297880097)
  ·
    refine ⟨40752828954561752473410073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54337105272749003297880097 40752828954561752473410073)
    ·
      refine ⟨30564621715921314355057555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40752828954561752473410073 30564621715921314355057555)
      ·
        refine ⟨45846932573881971532586333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30564621715921314355057555 45846932573881971532586333)
        ·
          refine ⟨17192599715205739324719875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45846932573881971532586333 17192599715205739324719875)
          ·
            refine ⟨25788899572808608987079813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17192599715205739324719875 25788899572808608987079813)
            ·
              refine ⟨4835418669901614185077465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25788899572808608987079813 4835418669901614185077465)
              ·
                refine ⟨3626564002426210638808099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4835418669901614185077465 3626564002426210638808099)
                ·
                  refine ⟨5439846003639315958212149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3626564002426210638808099 5439846003639315958212149)
                  ·
                    refine ⟨509985562841185871082389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5439846003639315958212149 509985562841185871082389)
                    ·
                      rfl

theorem cell23_2979580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_2979580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979580 prefixEnd_2979580 := by exact prefixLift 2979580
  have htrace : WordTrace (prefixWord ++ tailWord_2979580) baseStart_2979580 baseEnd_2979580 := by
    simpa [prefixWord, tailWord_2979580, baseEnd_2979580] using wordTrace_append hprefix tailTrace_2979580
  have hstable : (prefixWord ++ tailWord_2979580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979580).length < 2 ^ (prefixWord ++ tailWord_2979580).sum := by decide
  have hdescent : baseEnd_2979580 < baseStart_2979580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979583 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 4]
def baseStart_2979583 : Nat := 118140960795 + 2979583 * 2 ^ 59
def prefixEnd_2979583 : Nat := 4983230072969 + 3 ^ 40 * 2979583 * 2
def baseEnd_2979583 : Nat := 1529958228965521101509653

theorem tailTrace_2979583 : CollatzResearch.WordTrace tailWord_2979583 prefixEnd_2979583 1529958228965521101509653 := by
  unfold tailWord_2979583
  simp only [CollatzResearch.WordTrace]
  refine ⟨108674319964487138108119403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72449546642991425405412935 108674319964487138108119403)
  ·
    refine ⟨163011479946730707162179105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108674319964487138108119403 163011479946730707162179105)
    ·
      refine ⟨122258609960048030371634329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163011479946730707162179105 122258609960048030371634329)
      ·
        refine ⟨91693957470036022778725747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122258609960048030371634329 91693957470036022778725747)
        ·
          refine ⟨137540936205054034168088621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91693957470036022778725747 137540936205054034168088621)
          ·
            refine ⟨51577851076895262813033233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137540936205054034168088621 51577851076895262813033233)
            ·
              refine ⟨38683388307671447109774925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51577851076895262813033233 38683388307671447109774925)
              ·
                refine ⟨14506270615376792666165597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38683388307671447109774925 14506270615376792666165597)
                ·
                  refine ⟨5439851480766297249812099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14506270615376792666165597 5439851480766297249812099)
                  ·
                    refine ⟨8159777221149445874718149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5439851480766297249812099 8159777221149445874718149)
                    ·
                      refine ⟨1529958228965521101509653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8159777221149445874718149 1529958228965521101509653)
                      ·
                        rfl

theorem cell23_2979583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_2979583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979583 prefixEnd_2979583 := by exact prefixLift 2979583
  have htrace : WordTrace (prefixWord ++ tailWord_2979583) baseStart_2979583 baseEnd_2979583 := by
    simpa [prefixWord, tailWord_2979583, baseEnd_2979583] using wordTrace_append hprefix tailTrace_2979583
  have hstable : (prefixWord ++ tailWord_2979583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979583).length < 2 ^ (prefixWord ++ tailWord_2979583).sum := by decide
  have hdescent : baseEnd_2979583 < baseStart_2979583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979594 : List Nat := [3, 1, 2, 2, 1, 3, 3, 3, 1, 1, 3]
def baseStart_2979594 : Nat := 118140960795 + 2979594 * 2 ^ 59
def prefixEnd_2979594 : Nat := 4983230072969 + 3 ^ 40 * 2979594 * 2
def baseEnd_2979594 : Nat := 1529963877252720558472103

theorem tailTrace_2979594 : CollatzResearch.WordTrace tailWord_2979594 prefixEnd_2979594 1529963877252720558472103 := by
  unfold tailWord_2979594
  simp only [CollatzResearch.WordTrace]
  refine ⟨27168680291861821746692459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72449814111631524657846557 27168680291861821746692459)
  ·
    refine ⟨40753020437792732620038689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27168680291861821746692459 40753020437792732620038689)
    ·
      refine ⟨30564765328344549465029017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40753020437792732620038689 30564765328344549465029017)
      ·
        refine ⟨22923573996258412098771763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30564765328344549465029017 22923573996258412098771763)
        ·
          refine ⟨34385360994387618148157645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22923573996258412098771763 34385360994387618148157645)
          ·
            refine ⟨12894510372895356805559117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34385360994387618148157645 12894510372895356805559117)
            ·
              refine ⟨4835441389835758802084669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12894510372895356805559117 4835441389835758802084669)
              ·
                refine ⟨1813290521188409550781751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4835441389835758802084669 1813290521188409550781751)
                ·
                  refine ⟨2719935781782614326172627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1813290521188409550781751 2719935781782614326172627)
                  ·
                    refine ⟨4079903672673921489258941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2719935781782614326172627 4079903672673921489258941)
                    ·
                      refine ⟨1529963877252720558472103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4079903672673921489258941 1529963877252720558472103)
                      ·
                        rfl

theorem cell23_2979594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_2979594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979594 prefixEnd_2979594 := by exact prefixLift 2979594
  have htrace : WordTrace (prefixWord ++ tailWord_2979594) baseStart_2979594 baseEnd_2979594 := by
    simpa [prefixWord, tailWord_2979594, baseEnd_2979594] using wordTrace_append hprefix tailTrace_2979594
  have hstable : (prefixWord ++ tailWord_2979594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979594).length < 2 ^ (prefixWord ++ tailWord_2979594).sum := by decide
  have hdescent : baseEnd_2979594 < baseStart_2979594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979610 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 4, 4]
def baseStart_2979610 : Nat := 118140960795 + 2979610 * 2 ^ 59
def prefixEnd_2979610 : Nat := 4983230072969 + 3 ^ 40 * 2979610 * 2
def baseEnd_2979610 : Nat := 509990697647730831957343

theorem tailTrace_2979610 : CollatzResearch.WordTrace tailWord_2979610 prefixEnd_2979610 509990697647730831957343 := by
  unfold tailWord_2979610
  simp only [CollatzResearch.WordTrace]
  refine ⟨27168826183847330429838071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72450203156926214479568189 27168826183847330429838071)
  ·
    refine ⟨40753239275770995644757107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27168826183847330429838071 40753239275770995644757107)
    ·
      refine ⟨61129858913656493467135661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40753239275770995644757107 61129858913656493467135661)
      ·
        refine ⟨22923697092621185050175873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61129858913656493467135661 22923697092621185050175873)
        ·
          refine ⟨17192772819465888787631905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22923697092621185050175873 17192772819465888787631905)
          ·
            refine ⟨12894579614599416590723929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17192772819465888787631905 12894579614599416590723929)
            ·
              refine ⟨9670934710949562443042947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12894579614599416590723929 9670934710949562443042947)
              ·
                refine ⟨14506402066424343664564421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9670934710949562443042947 14506402066424343664564421)
                ·
                  refine ⟨2719950387454564437105829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14506402066424343664564421 2719950387454564437105829)
                  ·
                    refine ⟨509990697647730831957343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2719950387454564437105829 509990697647730831957343)
                    ·
                      rfl

theorem cell23_2979610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_2979610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979610 prefixEnd_2979610 := by exact prefixLift 2979610
  have htrace : WordTrace (prefixWord ++ tailWord_2979610) baseStart_2979610 baseEnd_2979610 := by
    simpa [prefixWord, tailWord_2979610, baseEnd_2979610] using wordTrace_append hprefix tailTrace_2979610
  have hstable : (prefixWord ++ tailWord_2979610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979610).length < 2 ^ (prefixWord ++ tailWord_2979610).sum := by decide
  have hdescent : baseEnd_2979610 < baseStart_2979610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979620 : List Nat := [2, 3, 1, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_2979620 : Nat := 118140960795 + 2979620 * 2 ^ 59
def prefixEnd_2979620 : Nat := 4983230072969 + 3 ^ 40 * 2979620 * 2
def baseEnd_2979620 : Nat := 1529977227749737456746983

theorem tailTrace_2979620 : CollatzResearch.WordTrace tailWord_2979620 prefixEnd_2979620 1529977227749737456746983 := by
  unfold tailWord_2979620
  simp only [CollatzResearch.WordTrace]
  refine ⟨54337834732676546713608157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72450446310235395618144209 54337834732676546713608157)
  ·
    refine ⟨20376688024753705017603059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54337834732676546713608157 20376688024753705017603059)
    ·
      refine ⟨30565032037130557526404589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20376688024753705017603059 30565032037130557526404589)
      ·
        refine ⟨11461887013923959072401721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30565032037130557526404589 11461887013923959072401721)
        ·
          refine ⟨8596415260442969304301291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11461887013923959072401721 8596415260442969304301291)
          ·
            refine ⟨12894622890664453956451937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8596415260442969304301291 12894622890664453956451937)
            ·
              refine ⟨9670967167998340467338953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12894622890664453956451937 9670967167998340467338953)
              ·
                refine ⟨7253225375998755350504215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9670967167998340467338953 7253225375998755350504215)
                ·
                  refine ⟨10879838063998133025756323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7253225375998755350504215 10879838063998133025756323)
                  ·
                    refine ⟨16319757095997199538634485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10879838063998133025756323 16319757095997199538634485)
                    ·
                      refine ⟨1529977227749737456746983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16319757095997199538634485 1529977227749737456746983)
                      ·
                        rfl

theorem cell23_2979620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_2979620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979620 prefixEnd_2979620 := by exact prefixLift 2979620
  have htrace : WordTrace (prefixWord ++ tailWord_2979620) baseStart_2979620 baseEnd_2979620 := by
    simpa [prefixWord, tailWord_2979620, baseEnd_2979620] using wordTrace_append hprefix tailTrace_2979620
  have hstable : (prefixWord ++ tailWord_2979620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979620).length < 2 ^ (prefixWord ++ tailWord_2979620).sum := by decide
  have hdescent : baseEnd_2979620 < baseStart_2979620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979637 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_2979637 : Nat := 118140960795 + 2979637 * 2 ^ 59
def prefixEnd_2979637 : Nat := 4983230072969 + 3 ^ 40 * 2979637 * 2
def baseEnd_2979637 : Nat := 1529985956920863890234405

theorem tailTrace_2979637 : CollatzResearch.WordTrace tailWord_2979637 prefixEnd_2979637 1529985956920863890234405 := by
  unfold tailWord_2979637
  simp only [CollatzResearch.WordTrace]
  refine ⟨108676289506291505330585165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72450859670861003553723443 108676289506291505330585165)
  ·
    refine ⟨40753608564859314498969437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108676289506291505330585165 40753608564859314498969437)
    ·
      refine ⟨15282603211822242937113539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40753608564859314498969437 15282603211822242937113539)
      ·
        refine ⟨22923904817733364405670309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15282603211822242937113539 22923904817733364405670309)
        ·
          refine ⟨4298232153325005826063183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22923904817733364405670309 4298232153325005826063183)
          ·
            refine ⟨6447348229987508739094775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298232153325005826063183 6447348229987508739094775)
            ·
              refine ⟨9671022344981263108642163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6447348229987508739094775 9671022344981263108642163)
              ·
                refine ⟨14506533517471894662963245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9671022344981263108642163 14506533517471894662963245)
                ·
                  refine ⟨5439950069051960498611217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14506533517471894662963245 5439950069051960498611217)
                  ·
                    refine ⟨4079962551788970373958413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5439950069051960498611217 4079962551788970373958413)
                    ·
                      refine ⟨1529985956920863890234405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4079962551788970373958413 1529985956920863890234405)
                      ·
                        rfl

theorem cell23_2979637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_2979637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979637 prefixEnd_2979637 := by exact prefixLift 2979637
  have htrace : WordTrace (prefixWord ++ tailWord_2979637) baseStart_2979637 baseEnd_2979637 := by
    simpa [prefixWord, tailWord_2979637, baseEnd_2979637] using wordTrace_append hprefix tailTrace_2979637
  have hstable : (prefixWord ++ tailWord_2979637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979637).length < 2 ^ (prefixWord ++ tailWord_2979637).sum := by decide
  have hdescent : baseEnd_2979637 < baseStart_2979637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979654 : List Nat := [6, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_2979654 : Nat := 118140960795 + 2979654 * 2 ^ 59
def prefixEnd_2979654 : Nat := 4983230072969 + 3 ^ 40 * 2979654 * 2
def baseEnd_2979654 : Nat := 1529994686091990323721827

theorem tailTrace_2979654 : CollatzResearch.WordTrace tailWord_2979654 prefixEnd_2979654 1529994686091990323721827 := by
  unfold tailWord_2979654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3396153423350934913561063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72451273031486611489302677 3396153423350934913561063)
  ·
    refine ⟨5094230135026402370341595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3396153423350934913561063 5094230135026402370341595)
    ·
      refine ⟨7641345202539603555512393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5094230135026402370341595 7641345202539603555512393)
      ·
        refine ⟨5731008901904702666634295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7641345202539603555512393 5731008901904702666634295)
        ·
          refine ⟨8596513352857053999951443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5731008901904702666634295 8596513352857053999951443)
          ·
            refine ⟨12894770029285580999927165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8596513352857053999951443 12894770029285580999927165)
            ·
              refine ⟨4835538760982092874972687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12894770029285580999927165 4835538760982092874972687)
              ·
                refine ⟨7253308141473139312459031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4835538760982092874972687 7253308141473139312459031)
                ·
                  refine ⟨10879962212209708968688547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7253308141473139312459031 10879962212209708968688547)
                  ·
                    refine ⟨16319943318314563453032821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10879962212209708968688547 16319943318314563453032821)
                    ·
                      refine ⟨1529994686091990323721827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16319943318314563453032821 1529994686091990323721827)
                      ·
                        rfl

theorem cell23_2979654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_2979654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979654 prefixEnd_2979654 := by exact prefixLift 2979654
  have htrace : WordTrace (prefixWord ++ tailWord_2979654) baseStart_2979654 baseEnd_2979654 := by
    simpa [prefixWord, tailWord_2979654, baseEnd_2979654] using wordTrace_append hprefix tailTrace_2979654
  have hstable : (prefixWord ++ tailWord_2979654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979654).length < 2 ^ (prefixWord ++ tailWord_2979654).sum := by decide
  have hdescent : baseEnd_2979654 < baseStart_2979654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979668 : List Nat := [2, 4, 1, 1, 3, 1, 4, 2, 1, 2, 2]
def baseStart_2979668 : Nat := 118140960795 + 2979668 * 2 ^ 59
def prefixEnd_2979668 : Nat := 4983230072969 + 3 ^ 40 * 2979668 * 2
def baseEnd_2979668 : Nat := 1530001874821153268946763

theorem tailTrace_2979668 : CollatzResearch.WordTrace tailWord_2979668 prefixEnd_2979668 1530001874821153268946763 := by
  unfold tailWord_2979668
  simp only [CollatzResearch.WordTrace]
  refine ⟨54338710084589598812481829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72451613446119465083309105 54338710084589598812481829)
  ·
    refine ⟨10188508140860549777340343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54338710084589598812481829 10188508140860549777340343)
    ·
      refine ⟨15282762211290824666010515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10188508140860549777340343 15282762211290824666010515)
      ·
        refine ⟨22924143316936236999015773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15282762211290824666010515 22924143316936236999015773)
        ·
          refine ⟨8596553743851088874630915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22924143316936236999015773 8596553743851088874630915)
          ·
            refine ⟨12894830615776633311946373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8596553743851088874630915 12894830615776633311946373)
            ·
              refine ⟨2417780740458118745989945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12894830615776633311946373 2417780740458118745989945)
              ·
                refine ⟨1813335555343589059492459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2417780740458118745989945 1813335555343589059492459)
                ·
                  refine ⟨2720003333015383589238689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1813335555343589059492459 2720003333015383589238689)
                  ·
                    refine ⟨2040002499761537691929017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2720003333015383589238689 2040002499761537691929017)
                    ·
                      refine ⟨1530001874821153268946763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2040002499761537691929017 1530001874821153268946763)
                      ·
                        rfl

theorem cell23_2979668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_2979668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979668 prefixEnd_2979668 := by exact prefixLift 2979668
  have htrace : WordTrace (prefixWord ++ tailWord_2979668) baseStart_2979668 baseEnd_2979668 := by
    simpa [prefixWord, tailWord_2979668, baseEnd_2979668] using wordTrace_append hprefix tailTrace_2979668
  have hstable : (prefixWord ++ tailWord_2979668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979668).length < 2 ^ (prefixWord ++ tailWord_2979668).sum := by decide
  have hdescent : baseEnd_2979668 < baseStart_2979668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979673 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 1, 5, 4]
def baseStart_2979673 : Nat := 118140960795 + 2979673 * 2 ^ 59
def prefixEnd_2979673 : Nat := 4983230072969 + 3 ^ 40 * 2979673 * 2
def baseEnd_2979673 : Nat := 1530004442224425749384239

theorem tailTrace_2979673 : CollatzResearch.WordTrace tailWord_2979673 prefixEnd_2979673 1530004442224425749384239 := by
  unfold tailWord_2979673
  simp only [CollatzResearch.WordTrace]
  refine ⟨108677602534161083478895673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72451735022774055652597115 108677602534161083478895673)
  ·
    refine ⟨81508201900620812609171755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108677602534161083478895673 81508201900620812609171755)
    ·
      refine ⟨122262302850931218913757633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81508201900620812609171755 122262302850931218913757633)
      ·
        refine ⟨91696727138198414185318225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122262302850931218913757633 91696727138198414185318225)
        ·
          refine ⟨68772545353648810638988669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91696727138198414185318225 68772545353648810638988669)
          ·
            refine ⟨25789704507618303989620751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68772545353648810638988669 25789704507618303989620751)
            ·
              refine ⟨38684556761427455984431127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25789704507618303989620751 38684556761427455984431127)
              ·
                refine ⟨58026835142141183976646691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38684556761427455984431127 58026835142141183976646691)
                ·
                  refine ⟨87040252713211775964970037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58026835142141183976646691 87040252713211775964970037)
                  ·
                    refine ⟨8160023691863603996715941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87040252713211775964970037 8160023691863603996715941)
                    ·
                      refine ⟨1530004442224425749384239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8160023691863603996715941 1530004442224425749384239)
                      ·
                        rfl

theorem cell23_2979673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_2979673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979673 prefixEnd_2979673 := by exact prefixLift 2979673
  have htrace : WordTrace (prefixWord ++ tailWord_2979673) baseStart_2979673 baseEnd_2979673 := by
    simpa [prefixWord, tailWord_2979673, baseEnd_2979673] using wordTrace_append hprefix tailTrace_2979673
  have hstable : (prefixWord ++ tailWord_2979673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979673).length < 2 ^ (prefixWord ++ tailWord_2979673).sum := by decide
  have hdescent : baseEnd_2979673 < baseStart_2979673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979694 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 3, 3, 2]
def baseStart_2979694 : Nat := 118140960795 + 2979694 * 2 ^ 59
def prefixEnd_2979694 : Nat := 4983230072969 + 3 ^ 40 * 2979694 * 2
def baseEnd_2979694 : Nat := 1530015225318170167221643

theorem tailTrace_2979694 : CollatzResearch.WordTrace tailWord_2979694 prefixEnd_2979694 1530015225318170167221643 := by
  unfold tailWord_2979694
  simp only [CollatzResearch.WordTrace]
  refine ⟨13584796058385625508176267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72452245644723336043606757 13584796058385625508176267)
  ·
    refine ⟨20377194087578438262264401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13584796058385625508176267 20377194087578438262264401)
    ·
      refine ⟨15282895565683828696698301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20377194087578438262264401 15282895565683828696698301)
      ·
        refine ⟨5731085837131435761261863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15282895565683828696698301 5731085837131435761261863)
        ·
          refine ⟨8596628755697153641892795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5731085837131435761261863 8596628755697153641892795)
          ·
            refine ⟨12894943133545730462839193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8596628755697153641892795 12894943133545730462839193)
            ·
              refine ⟨9671207350159297847129395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12894943133545730462839193 9671207350159297847129395)
              ·
                refine ⟨14506811025238946770694093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9671207350159297847129395 14506811025238946770694093)
                ·
                  refine ⟨5440054134464605039010285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14506811025238946770694093 5440054134464605039010285)
                  ·
                    refine ⟨2040020300424226889628857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5440054134464605039010285 2040020300424226889628857)
                    ·
                      refine ⟨1530015225318170167221643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2040020300424226889628857 1530015225318170167221643)
                      ·
                        rfl

theorem cell23_2979694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_2979694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979694 prefixEnd_2979694 := by exact prefixLift 2979694
  have htrace : WordTrace (prefixWord ++ tailWord_2979694) baseStart_2979694 baseEnd_2979694 := by
    simpa [prefixWord, tailWord_2979694, baseEnd_2979694] using wordTrace_append hprefix tailTrace_2979694
  have hstable : (prefixWord ++ tailWord_2979694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979694).length < 2 ^ (prefixWord ++ tailWord_2979694).sum := by decide
  have hdescent : baseEnd_2979694 < baseStart_2979694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979707 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 4, 2, 2]
def baseStart_2979707 : Nat := 118140960795 + 2979707 * 2 ^ 59
def prefixEnd_2979707 : Nat := 4983230072969 + 3 ^ 40 * 2979707 * 2
def baseEnd_2979707 : Nat := 1530021900566678616359083

theorem tailTrace_2979707 : CollatzResearch.WordTrace tailWord_2979707 prefixEnd_2979707 1530021900566678616359083 := by
  unfold tailWord_2979707
  simp only [CollatzResearch.WordTrace]
  refine ⟨108678842616037907285633375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72452561744025271523755583 108678842616037907285633375)
  ·
    refine ⟨163018263924056860928450063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108678842616037907285633375 163018263924056860928450063)
    ·
      refine ⟨244527395886085291392675095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163018263924056860928450063 244527395886085291392675095)
      ·
        refine ⟨366791093829127937089012643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244527395886085291392675095 366791093829127937089012643)
        ·
          refine ⟨550186640743691905633518965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366791093829127937089012643 550186640743691905633518965)
          ·
            refine ⟨51579997569721116153142403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 550186640743691905633518965 51579997569721116153142403)
            ·
              refine ⟨77369996354581674229713605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51579997569721116153142403 77369996354581674229713605)
              ·
                refine ⟨14506874316484063918071301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77369996354581674229713605 14506874316484063918071301)
                ·
                  refine ⟨2720038934340761984638369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14506874316484063918071301 2720038934340761984638369)
                  ·
                    refine ⟨2040029200755571488478777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2720038934340761984638369 2040029200755571488478777)
                    ·
                      refine ⟨1530021900566678616359083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2040029200755571488478777 1530021900566678616359083)
                      ·
                        rfl

theorem cell23_2979707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 2, 2].length) (baseStart_2979707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979707 prefixEnd_2979707 := by exact prefixLift 2979707
  have htrace : WordTrace (prefixWord ++ tailWord_2979707) baseStart_2979707 baseEnd_2979707 := by
    simpa [prefixWord, tailWord_2979707, baseEnd_2979707] using wordTrace_append hprefix tailTrace_2979707
  have hstable : (prefixWord ++ tailWord_2979707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979707).length < 2 ^ (prefixWord ++ tailWord_2979707).sum := by decide
  have hdescent : baseEnd_2979707 < baseStart_2979707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979753 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 3, 1, 7]
def baseStart_2979753 : Nat := 118140960795 + 2979753 * 2 ^ 59
def prefixEnd_2979753 : Nat := 4983230072969 + 3 ^ 40 * 2979753 * 2
def baseEnd_2979753 : Nat := 1530045520676785436383871

theorem tailTrace_2979753 : CollatzResearch.WordTrace tailWord_2979753 prefixEnd_2979753 1530045520676785436383871 := by
  unfold tailWord_2979753
  simp only [CollatzResearch.WordTrace]
  refine ⟨108680520373871257141807913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72453680249247504761205275 108680520373871257141807913)
  ·
    refine ⟨81510390280403442856355935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108680520373871257141807913 81510390280403442856355935)
    ·
      refine ⟨122265585420605164284533903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81510390280403442856355935 122265585420605164284533903)
      ·
        refine ⟨183398378130907746426800855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122265585420605164284533903 183398378130907746426800855)
        ·
          refine ⟨275097567196361619640201283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183398378130907746426800855 275097567196361619640201283)
          ·
            refine ⟨412646350794542429460301925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275097567196361619640201283 412646350794542429460301925)
            ·
              refine ⟨77371190773976705523806611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 412646350794542429460301925 77371190773976705523806611)
              ·
                refine ⟨116056786160965058285709917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77371190773976705523806611 116056786160965058285709917)
                ·
                  refine ⟨43521294810361896857141219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116056786160965058285709917 43521294810361896857141219)
                  ·
                    refine ⟨65281942215542845285711829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43521294810361896857141219 65281942215542845285711829)
                    ·
                      refine ⟨1530045520676785436383871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65281942215542845285711829 1530045520676785436383871)
                      ·
                        rfl

theorem cell23_2979753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_2979753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979753 prefixEnd_2979753 := by exact prefixLift 2979753
  have htrace : WordTrace (prefixWord ++ tailWord_2979753) baseStart_2979753 baseEnd_2979753 := by
    simpa [prefixWord, tailWord_2979753, baseEnd_2979753] using wordTrace_append hprefix tailTrace_2979753
  have hstable : (prefixWord ++ tailWord_2979753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979753).length < 2 ^ (prefixWord ++ tailWord_2979753).sum := by decide
  have hdescent : baseEnd_2979753 < baseStart_2979753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979864 : List Nat := [2, 1, 2, 3, 2, 1, 3, 2, 3, 1, 3]
def baseStart_2979864 : Nat := 118140960795 + 2979864 * 2 ^ 59
def prefixEnd_2979864 : Nat := 4983230072969 + 3 ^ 40 * 2979864 * 2
def baseEnd_2979864 : Nat := 1530102517029434502095861

theorem tailTrace_2979864 : CollatzResearch.WordTrace tailWord_2979864 prefixEnd_2979864 1530102517029434502095861 := by
  unfold tailWord_2979864
  simp only [CollatzResearch.WordTrace]
  refine ⟨54342284438234561549549323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72456379250979415399399097 54342284438234561549549323)
  ·
    refine ⟨81513426657351842324323985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54342284438234561549549323 81513426657351842324323985)
    ·
      refine ⟨61135069993013881743242989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81513426657351842324323985 61135069993013881743242989)
      ·
        refine ⟨22925651247380205653716121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61135069993013881743242989 22925651247380205653716121)
        ·
          refine ⟨17194238435535154240287091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22925651247380205653716121 17194238435535154240287091)
          ·
            refine ⟨25791357653302731360430637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17194238435535154240287091 25791357653302731360430637)
            ·
              refine ⟨9671759119988524260161489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25791357653302731360430637 9671759119988524260161489)
              ·
                refine ⟨7253819339991393195121117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9671759119988524260161489 7253819339991393195121117)
                ·
                  refine ⟨2720182252496772448170419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7253819339991393195121117 2720182252496772448170419)
                  ·
                    refine ⟨4080273378745158672255629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2720182252496772448170419 4080273378745158672255629)
                    ·
                      refine ⟨1530102517029434502095861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4080273378745158672255629 1530102517029434502095861)
                      ·
                        rfl

theorem cell23_2979864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_2979864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979864 prefixEnd_2979864 := by exact prefixLift 2979864
  have htrace : WordTrace (prefixWord ++ tailWord_2979864) baseStart_2979864 baseEnd_2979864 := by
    simpa [prefixWord, tailWord_2979864, baseEnd_2979864] using wordTrace_append hprefix tailTrace_2979864
  have hstable : (prefixWord ++ tailWord_2979864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979864).length < 2 ^ (prefixWord ++ tailWord_2979864).sum := by decide
  have hdescent : baseEnd_2979864 < baseStart_2979864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979874 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 1, 5, 2]
def baseStart_2979874 : Nat := 118140960795 + 2979874 * 2 ^ 59
def prefixEnd_2979874 : Nat := 4983230072969 + 3 ^ 40 * 2979874 * 2
def baseEnd_2979874 : Nat := 1530107651835979462970815

theorem tailTrace_2979874 : CollatzResearch.WordTrace tailWord_2979874 prefixEnd_2979874 1530107651835979462970815 := by
  unfold tailWord_2979874
  simp only [CollatzResearch.WordTrace]
  refine ⟨27171233401608223701740669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72456622404288596537975117 27171233401608223701740669)
  ·
    refine ⟨10189212525603083888152751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27171233401608223701740669 10189212525603083888152751)
    ·
      refine ⟨15283818788404625832229127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10189212525603083888152751 15283818788404625832229127)
      ·
        refine ⟨22925728182606938748343691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15283818788404625832229127 22925728182606938748343691)
        ·
          refine ⟨34388592273910408122515537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22925728182606938748343691 34388592273910408122515537)
          ·
            refine ⟨25791444205432806091886653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34388592273910408122515537 25791444205432806091886653)
            ·
              refine ⟨9671791577037302284457495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25791444205432806091886653 9671791577037302284457495)
              ·
                refine ⟨14507687365555953426686243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9671791577037302284457495 14507687365555953426686243)
                ·
                  refine ⟨21761531048333930140029365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14507687365555953426686243 21761531048333930140029365)
                  ·
                    refine ⟨2040143535781305950627753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21761531048333930140029365 2040143535781305950627753)
                    ·
                      refine ⟨1530107651835979462970815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2040143535781305950627753 1530107651835979462970815)
                      ·
                        rfl

theorem cell23_2979874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_2979874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979874 prefixEnd_2979874 := by exact prefixLift 2979874
  have htrace : WordTrace (prefixWord ++ tailWord_2979874) baseStart_2979874 baseEnd_2979874 := by
    simpa [prefixWord, tailWord_2979874, baseEnd_2979874] using wordTrace_append hprefix tailTrace_2979874
  have hstable : (prefixWord ++ tailWord_2979874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979874).length < 2 ^ (prefixWord ++ tailWord_2979874).sum := by decide
  have hdescent : baseEnd_2979874 < baseStart_2979874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979907 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 3]
def baseStart_2979907 : Nat := 118140960795 + 2979907 * 2 ^ 59
def prefixEnd_2979907 : Nat := 4983230072969 + 3 ^ 40 * 2979907 * 2
def baseEnd_2979907 : Nat := 1530124596697577833858163

theorem tailTrace_2979907 : CollatzResearch.WordTrace tailWord_2979907 prefixEnd_2979907 1530124596697577833858163 := by
  unfold tailWord_2979907
  simp only [CollatzResearch.WordTrace]
  refine ⟨108686137215313341442913975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72457424810208894295275983 108686137215313341442913975)
  ·
    refine ⟨163029205822970012164370963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108686137215313341442913975 163029205822970012164370963)
    ·
      refine ⟨244543808734455018246556445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163029205822970012164370963 244543808734455018246556445)
      ·
        refine ⟨91703928275420631842458667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244543808734455018246556445 91703928275420631842458667)
        ·
          refine ⟨137555892413130947763688001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91703928275420631842458667 137555892413130947763688001)
          ·
            refine ⟨103166919309848210822766001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137555892413130947763688001 103166919309848210822766001)
            ·
              refine ⟨77375189482386158117074501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103166919309848210822766001 77375189482386158117074501)
              ·
                refine ⟨14507848027947404646951469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77375189482386158117074501 14507848027947404646951469)
                ·
                  refine ⟨5440443010480276742606801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14507848027947404646951469 5440443010480276742606801)
                  ·
                    refine ⟨4080332257860207556955101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5440443010480276742606801 4080332257860207556955101)
                    ·
                      refine ⟨1530124596697577833858163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4080332257860207556955101 1530124596697577833858163)
                      ·
                        rfl

theorem cell23_2979907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_2979907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979907 prefixEnd_2979907 := by exact prefixLift 2979907
  have htrace : WordTrace (prefixWord ++ tailWord_2979907) baseStart_2979907 baseEnd_2979907 := by
    simpa [prefixWord, tailWord_2979907, baseEnd_2979907] using wordTrace_append hprefix tailTrace_2979907
  have hstable : (prefixWord ++ tailWord_2979907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979907).length < 2 ^ (prefixWord ++ tailWord_2979907).sum := by decide
  have hdescent : baseEnd_2979907 < baseStart_2979907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979927 : List Nat := [1, 1, 3, 2, 2, 1, 6, 7]
def baseStart_2979927 : Nat := 118140960795 + 2979927 * 2 ^ 59
def prefixEnd_2979927 : Nat := 4983230072969 + 3 ^ 40 * 2979927 * 2
def baseEnd_2979927 : Nat := 56671661715209916874373

theorem tailTrace_2979927 : CollatzResearch.WordTrace tailWord_2979927 prefixEnd_2979927 56671661715209916874373 := by
  unfold tailWord_2979927
  simp only [CollatzResearch.WordTrace]
  refine ⟨108686866675240884858642035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72457911116827256572428023 108686866675240884858642035)
  ·
    refine ⟨163030300012861327287963053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108686866675240884858642035 163030300012861327287963053)
    ·
      refine ⟨61136362504822997732986145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163030300012861327287963053 61136362504822997732986145)
      ·
        refine ⟨45852271878617248299739609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61136362504822997732986145 45852271878617248299739609)
        ·
          refine ⟨34389203908962936224804707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45852271878617248299739609 34389203908962936224804707)
          ·
            refine ⟨51583805863444404337207061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34389203908962936224804707 51583805863444404337207061)
            ·
              refine ⟨2417990899848956453306581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51583805863444404337207061 2417990899848956453306581)
              ·
                refine ⟨56671661715209916874373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2417990899848956453306581 56671661715209916874373)
                ·
                  rfl

theorem cell23_2979927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 7].length) (baseStart_2979927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979927 prefixEnd_2979927 := by exact prefixLift 2979927
  have htrace : WordTrace (prefixWord ++ tailWord_2979927) baseStart_2979927 baseEnd_2979927 := by
    simpa [prefixWord, tailWord_2979927, baseEnd_2979927] using wordTrace_append hprefix tailTrace_2979927
  have hstable : (prefixWord ++ tailWord_2979927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979927).length < 2 ^ (prefixWord ++ tailWord_2979927).sum := by decide
  have hdescent : baseEnd_2979927 < baseStart_2979927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979937 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 3, 3, 3]
def baseStart_2979937 : Nat := 118140960795 + 2979937 * 2 ^ 59
def prefixEnd_2979937 : Nat := 4983230072969 + 3 ^ 40 * 2979937 * 2
def baseEnd_2979937 : Nat := 1530140001117212716483025

theorem tailTrace_2979937 : CollatzResearch.WordTrace tailWord_2979937 prefixEnd_2979937 1530140001117212716483025 := by
  unfold tailWord_2979937
  simp only [CollatzResearch.WordTrace]
  refine ⟨108687231405204656566506065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72458154270136437711004043 108687231405204656566506065)
  ·
    refine ⟨81515423553903492424879549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108687231405204656566506065 81515423553903492424879549)
    ·
      refine ⟨30568283832713809659329831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81515423553903492424879549 30568283832713809659329831)
      ·
        refine ⟨45852425749070714488994747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30568283832713809659329831 45852425749070714488994747)
        ·
          refine ⟨68778638623606071733492121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45852425749070714488994747 68778638623606071733492121)
          ·
            refine ⟨51583978967704553800119091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68778638623606071733492121 51583978967704553800119091)
            ·
              refine ⟨77375968451556830700178637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51583978967704553800119091 77375968451556830700178637)
              ·
                refine ⟨29015988169333811512566989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77375968451556830700178637 29015988169333811512566989)
                ·
                  refine ⟨10880995563500179317212621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29015988169333811512566989 10880995563500179317212621)
                  ·
                    refine ⟨4080373336312567243954733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10880995563500179317212621 4080373336312567243954733)
                    ·
                      refine ⟨1530140001117212716483025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4080373336312567243954733 1530140001117212716483025)
                      ·
                        rfl

theorem cell23_2979937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_2979937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979937 prefixEnd_2979937 := by exact prefixLift 2979937
  have htrace : WordTrace (prefixWord ++ tailWord_2979937) baseStart_2979937 baseEnd_2979937 := by
    simpa [prefixWord, tailWord_2979937, baseEnd_2979937] using wordTrace_append hprefix tailTrace_2979937
  have hstable : (prefixWord ++ tailWord_2979937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979937).length < 2 ^ (prefixWord ++ tailWord_2979937).sum := by decide
  have hdescent : baseEnd_2979937 < baseStart_2979937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979971 : List Nat := [1, 1, 1, 3, 3, 4, 1, 3, 2, 1, 3]
def baseStart_2979971 : Nat := 118140960795 + 2979971 * 2 ^ 59
def prefixEnd_2979971 : Nat := 4983230072969 + 3 ^ 40 * 2979971 * 2
def baseEnd_2979971 : Nat := 1530157459459465583457869

theorem tailTrace_2979971 : CollatzResearch.WordTrace tailWord_2979971 prefixEnd_2979971 1530157459459465583457869 := by
  unfold tailWord_2979971
  simp only [CollatzResearch.WordTrace]
  refine ⟨108688471487081480373243767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72458980991387653582162511 108688471487081480373243767)
  ·
    refine ⟨163032707230622220559865651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108688471487081480373243767 163032707230622220559865651)
    ·
      refine ⟨244549060845933330839798477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163032707230622220559865651 244549060845933330839798477)
      ·
        refine ⟨91705897817224999064924429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244549060845933330839798477 91705897817224999064924429)
        ·
          refine ⟨34389711681459374649346661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91705897817224999064924429 34389711681459374649346661)
          ·
            refine ⟨6448070940273632746752499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34389711681459374649346661 6448070940273632746752499)
            ·
              refine ⟨9672106410410449120128749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6448070940273632746752499 9672106410410449120128749)
              ·
                refine ⟨3627039903903918420048281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9672106410410449120128749 3627039903903918420048281)
                ·
                  refine ⟨2720279927927938815036211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3627039903903918420048281 2720279927927938815036211)
                  ·
                    refine ⟨4080419891891908222554317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2720279927927938815036211 4080419891891908222554317)
                    ·
                      refine ⟨1530157459459465583457869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4080419891891908222554317 1530157459459465583457869)
                      ·
                        rfl

theorem cell23_2979971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 1, 3].length) (baseStart_2979971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979971 prefixEnd_2979971 := by exact prefixLift 2979971
  have htrace : WordTrace (prefixWord ++ tailWord_2979971) baseStart_2979971 baseEnd_2979971 := by
    simpa [prefixWord, tailWord_2979971, baseEnd_2979971] using wordTrace_append hprefix tailTrace_2979971
  have hstable : (prefixWord ++ tailWord_2979971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979971).length < 2 ^ (prefixWord ++ tailWord_2979971).sum := by decide
  have hdescent : baseEnd_2979971 < baseStart_2979971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2979988 : List Nat := [2, 4, 2, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_2979988 : Nat := 118140960795 + 2979988 * 2 ^ 59
def prefixEnd_2979988 : Nat := 4983230072969 + 3 ^ 40 * 2979988 * 2
def baseEnd_2979988 : Nat := 1530166188630592016945291

theorem tailTrace_2979988 : CollatzResearch.WordTrace tailWord_2979988 prefixEnd_2979988 1530166188630592016945291 := by
  unfold tailWord_2979988
  simp only [CollatzResearch.WordTrace]
  refine ⟨54344545764009946138306309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72459394352013261517741745 54344545764009946138306309)
  ·
    refine ⟨10189602330751864900932433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54344545764009946138306309 10189602330751864900932433)
    ·
      refine ⟨7642201748063898675699325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10189602330751864900932433 7642201748063898675699325)
      ·
        refine ⟨2865825655523962003387247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7642201748063898675699325 2865825655523962003387247)
        ·
          refine ⟨4298738483285943005080871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2865825655523962003387247 4298738483285943005080871)
          ·
            refine ⟨6448107724928914507621307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298738483285943005080871 6448107724928914507621307)
            ·
              refine ⟨9672161587393371761431961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6448107724928914507621307 9672161587393371761431961)
              ·
                refine ⟨7254121190545028821073971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9672161587393371761431961 7254121190545028821073971)
                ·
                  refine ⟨10881181785817543231610957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7254121190545028821073971 10881181785817543231610957)
                  ·
                    refine ⟨4080443169681578711854109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10881181785817543231610957 4080443169681578711854109)
                    ·
                      refine ⟨1530166188630592016945291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4080443169681578711854109 1530166188630592016945291)
                      ·
                        rfl

theorem cell23_2979988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_2979988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2979988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2979988 prefixEnd_2979988 := by exact prefixLift 2979988
  have htrace : WordTrace (prefixWord ++ tailWord_2979988) baseStart_2979988 baseEnd_2979988 := by
    simpa [prefixWord, tailWord_2979988, baseEnd_2979988] using wordTrace_append hprefix tailTrace_2979988
  have hstable : (prefixWord ++ tailWord_2979988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2979988).length < 2 ^ (prefixWord ++ tailWord_2979988).sum := by decide
  have hdescent : baseEnd_2979988 < baseStart_2979988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2979988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980021 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 2, 6]
def baseStart_2980021 : Nat := 118140960795 + 2980021 * 2 ^ 59
def prefixEnd_2980021 : Nat := 4983230072969 + 3 ^ 40 * 2980021 * 2
def baseEnd_2980021 : Nat := 510061044497396795944213

theorem tailTrace_2980021 : CollatzResearch.WordTrace tailWord_2980021 prefixEnd_2980021 510061044497396795944213 := by
  unfold tailWord_2980021
  simp only [CollatzResearch.WordTrace]
  refine ⟨108690295136900338912563917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72460196757933559275042611 108690295136900338912563917)
  ·
    refine ⟨40758860676337627092211469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108690295136900338912563917 40758860676337627092211469)
    ·
      refine ⟨15284572753626610159579301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40758860676337627092211469 15284572753626610159579301)
      ·
        refine ⟨2865857391304989404921119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15284572753626610159579301 2865857391304989404921119)
        ·
          refine ⟨4298786086957484107381679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2865857391304989404921119 4298786086957484107381679)
          ·
            refine ⟨6448179130436226161072519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298786086957484107381679 6448179130436226161072519)
            ·
              refine ⟨9672268695654339241608779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6448179130436226161072519 9672268695654339241608779)
              ·
                refine ⟨14508403043481508862413169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9672268695654339241608779 14508403043481508862413169)
                ·
                  refine ⟨10881302282611131646809877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14508403043481508862413169 10881302282611131646809877)
                  ·
                    refine ⟨510061044497396795944213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10881302282611131646809877 510061044497396795944213)
                    ·
                      rfl

theorem cell23_2980021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_2980021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980021 prefixEnd_2980021 := by exact prefixLift 2980021
  have htrace : WordTrace (prefixWord ++ tailWord_2980021) baseStart_2980021 baseEnd_2980021 := by
    simpa [prefixWord, tailWord_2980021, baseEnd_2980021] using wordTrace_append hprefix tailTrace_2980021
  have hstable : (prefixWord ++ tailWord_2980021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980021).length < 2 ^ (prefixWord ++ tailWord_2980021).sum := by decide
  have hdescent : baseEnd_2980021 < baseStart_2980021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980028 : List Nat := [2, 2, 2, 3, 3, 1, 2, 1, 1, 4, 2]
def baseStart_2980028 : Nat := 118140960795 + 2980028 * 2 ^ 59
def prefixEnd_2980028 : Nat := 4983230072969 + 3 ^ 40 * 2980028 * 2
def baseEnd_2980028 : Nat := 1530186727856771860445107

theorem tailTrace_2980028 : CollatzResearch.WordTrace tailWord_2980028 prefixEnd_2980028 1530186727856771860445107 := by
  unfold tailWord_2980028
  simp only [CollatzResearch.WordTrace]
  refine ⟨54345275223937489554034369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72460366965249986072045825 54345275223937489554034369)
  ·
    refine ⟨40758956417953117165525777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54345275223937489554034369 40758956417953117165525777)
    ·
      refine ⟨30569217313464837874144333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40758956417953117165525777 30569217313464837874144333)
      ·
        refine ⟨11463456492549314202804125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30569217313464837874144333 11463456492549314202804125)
        ·
          refine ⟨4298796184705992826051547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11463456492549314202804125 4298796184705992826051547)
          ·
            refine ⟨6448194277058989239077321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298796184705992826051547 6448194277058989239077321)
            ·
              refine ⟨4836145707794241929307991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6448194277058989239077321 4836145707794241929307991)
              ·
                refine ⟨7254218561691362893961987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4836145707794241929307991 7254218561691362893961987)
                ·
                  refine ⟨10881327842537044340942981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7254218561691362893961987 10881327842537044340942981)
                  ·
                    refine ⟨2040248970475695813926809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10881327842537044340942981 2040248970475695813926809)
                    ·
                      refine ⟨1530186727856771860445107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2040248970475695813926809 1530186727856771860445107)
                      ·
                        rfl

theorem cell23_2980028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_2980028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980028 prefixEnd_2980028 := by exact prefixLift 2980028
  have htrace : WordTrace (prefixWord ++ tailWord_2980028) baseStart_2980028 baseEnd_2980028 := by
    simpa [prefixWord, tailWord_2980028, baseEnd_2980028] using wordTrace_append hprefix tailTrace_2980028
  have hstable : (prefixWord ++ tailWord_2980028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980028).length < 2 ^ (prefixWord ++ tailWord_2980028).sum := by decide
  have hdescent : baseEnd_2980028 < baseStart_2980028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980047 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 1, 7]
def baseStart_2980047 : Nat := 118140960795 + 2980047 * 2 ^ 59
def prefixEnd_2980047 : Nat := 4983230072969 + 3 ^ 40 * 2980047 * 2
def baseEnd_2980047 : Nat := 510065494663069095369173

theorem tailTrace_2980047 : CollatzResearch.WordTrace tailWord_2980047 prefixEnd_2980047 510065494663069095369173 := by
  unfold tailWord_2980047
  simp only [CollatzResearch.WordTrace]
  refine ⟨108691243434806145353010395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72460828956537430235340263 108691243434806145353010395)
  ·
    refine ⟨163036865152209218029515593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108691243434806145353010395 163036865152209218029515593)
    ·
      refine ⟨122277648864156913522136695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163036865152209218029515593 122277648864156913522136695)
      ·
        refine ⟨183416473296235370283205043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122277648864156913522136695 183416473296235370283205043)
        ·
          refine ⟨275124709944353055424807565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183416473296235370283205043 275124709944353055424807565)
          ·
            refine ⟨103171766229132395784302837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275124709944353055424807565 103171766229132395784302837)
            ·
              refine ⟨9672353083981162104778391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103171766229132395784302837 9672353083981162104778391)
              ·
                refine ⟨14508529625971743157167587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9672353083981162104778391 14508529625971743157167587)
                ·
                  refine ⟨21762794438957614735751381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14508529625971743157167587 21762794438957614735751381)
                  ·
                    refine ⟨510065494663069095369173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21762794438957614735751381 510065494663069095369173)
                    ·
                      rfl

theorem cell23_2980047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 7].length) (baseStart_2980047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980047 prefixEnd_2980047 := by exact prefixLift 2980047
  have htrace : WordTrace (prefixWord ++ tailWord_2980047) baseStart_2980047 baseEnd_2980047 := by
    simpa [prefixWord, tailWord_2980047, baseEnd_2980047] using wordTrace_append hprefix tailTrace_2980047
  have hstable : (prefixWord ++ tailWord_2980047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980047).length < 2 ^ (prefixWord ++ tailWord_2980047).sum := by decide
  have hdescent : baseEnd_2980047 < baseStart_2980047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980057 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 3, 2, 5]
def baseStart_2980057 : Nat := 118140960795 + 2980057 * 2 ^ 59
def prefixEnd_2980057 : Nat := 4983230072969 + 3 ^ 40 * 2980057 * 2
def baseEnd_2980057 : Nat := 1530201618795752246982473

theorem tailTrace_2980057 : CollatzResearch.WordTrace tailWord_2980057 prefixEnd_2980057 1530201618795752246982473 := by
  unfold tailWord_2980057
  simp only [CollatzResearch.WordTrace]
  refine ⟨108691608164769917060874425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72461072109846611373916283 108691608164769917060874425)
  ·
    refine ⟨81518706123577437795655819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108691608164769917060874425 81518706123577437795655819)
    ·
      refine ⟨122278059185366156693483729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81518706123577437795655819 122278059185366156693483729)
      ·
        refine ⟨91708544389024617520112797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122278059185366156693483729 91708544389024617520112797)
        ·
          refine ⟨34390704145884231570042299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91708544389024617520112797 34390704145884231570042299)
          ·
            refine ⟨51586056218826347355063449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34390704145884231570042299 51586056218826347355063449)
            ·
              refine ⟨38689542164119760516297587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51586056218826347355063449 38689542164119760516297587)
              ·
                refine ⟨58034313246179640774446381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38689542164119760516297587 58034313246179640774446381)
                ·
                  refine ⟨21762867467317365290417393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58034313246179640774446381 21762867467317365290417393)
                  ·
                    refine ⟨16322150600488023967813045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21762867467317365290417393 16322150600488023967813045)
                    ·
                      refine ⟨1530201618795752246982473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16322150600488023967813045 1530201618795752246982473)
                      ·
                        rfl

theorem cell23_2980057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_2980057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980057 prefixEnd_2980057 := by exact prefixLift 2980057
  have htrace : WordTrace (prefixWord ++ tailWord_2980057) baseStart_2980057 baseEnd_2980057 := by
    simpa [prefixWord, tailWord_2980057, baseEnd_2980057] using wordTrace_append hprefix tailTrace_2980057
  have hstable : (prefixWord ++ tailWord_2980057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980057).length < 2 ^ (prefixWord ++ tailWord_2980057).sum := by decide
  have hdescent : baseEnd_2980057 < baseStart_2980057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980061 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2980061 : Nat := 118140960795 + 2980061 * 2 ^ 59
def prefixEnd_2980061 : Nat := 4983230072969 + 3 ^ 40 * 2980061 * 2
def baseEnd_2980061 : Nat := 1530203672718370231332455

theorem tailTrace_2980061 : CollatzResearch.WordTrace tailWord_2980061 prefixEnd_2980061 1530203672718370231332455 := by
  unfold tailWord_2980061
  simp only [CollatzResearch.WordTrace]
  refine ⟨108691754056755425744020037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72461169371170283829346691 108691754056755425744020037)
  ·
    refine ⟨20379703885641642327003757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108691754056755425744020037 20379703885641642327003757)
    ·
      refine ⟨7642388957115615872626409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20379703885641642327003757 7642388957115615872626409)
      ·
        refine ⟨5731791717836711904469807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7642388957115615872626409 5731791717836711904469807)
        ·
          refine ⟨8597687576755067856704711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5731791717836711904469807 8597687576755067856704711)
          ·
            refine ⟨12896531365132601785057067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8597687576755067856704711 12896531365132601785057067)
            ·
              refine ⟨19344797047698902677585601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12896531365132601785057067 19344797047698902677585601)
              ·
                refine ⟨14508597785774177008189201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19344797047698902677585601 14508597785774177008189201)
                ·
                  refine ⟨10881448339330632756141901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14508597785774177008189201 10881448339330632756141901)
                  ·
                    refine ⟨4080543127248987283553213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10881448339330632756141901 4080543127248987283553213)
                    ·
                      refine ⟨1530203672718370231332455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4080543127248987283553213 1530203672718370231332455)
                      ·
                        rfl

theorem cell23_2980061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2980061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980061 prefixEnd_2980061 := by exact prefixLift 2980061
  have htrace : WordTrace (prefixWord ++ tailWord_2980061) baseStart_2980061 baseEnd_2980061 := by
    simpa [prefixWord, tailWord_2980061, baseEnd_2980061] using wordTrace_append hprefix tailTrace_2980061
  have hstable : (prefixWord ++ tailWord_2980061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980061).length < 2 ^ (prefixWord ++ tailWord_2980061).sum := by decide
  have hdescent : baseEnd_2980061 < baseStart_2980061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980094 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_2980094 : Nat := 118140960795 + 2980094 * 2 ^ 59
def prefixEnd_2980094 : Nat := 4983230072969 + 3 ^ 40 * 2980094 * 2
def baseEnd_2980094 : Nat := 510073539193322867406601

theorem tailTrace_2980094 : CollatzResearch.WordTrace tailWord_2980094 prefixEnd_2980094 510073539193322867406601 := by
  unfold tailWord_2980094
  simp only [CollatzResearch.WordTrace]
  refine ⟨13586619708204484047496417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72461971777090581586647557 13586619708204484047496417)
  ·
    refine ⟨10189964781153363035622313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13586619708204484047496417 10189964781153363035622313)
    ·
      refine ⟨7642473585865022276716735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10189964781153363035622313 7642473585865022276716735)
      ·
        refine ⟨11463710378797533415075103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7642473585865022276716735 11463710378797533415075103)
        ·
          refine ⟨17195565568196300122612655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11463710378797533415075103 17195565568196300122612655)
          ·
            refine ⟨25793348352294450183918983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17195565568196300122612655 25793348352294450183918983)
            ·
              refine ⟨38690022528441675275878475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25793348352294450183918983 38690022528441675275878475)
              ·
                refine ⟨58035033792662512913817713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38690022528441675275878475 58035033792662512913817713)
                ·
                  refine ⟨43526275344496884685363285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58035033792662512913817713 43526275344496884685363285)
                  ·
                    refine ⟨510073539193322867406601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43526275344496884685363285 510073539193322867406601)
                    ·
                      rfl

theorem cell23_2980094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_2980094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980094 prefixEnd_2980094 := by exact prefixLift 2980094
  have htrace : WordTrace (prefixWord ++ tailWord_2980094) baseStart_2980094 baseEnd_2980094 := by
    simpa [prefixWord, tailWord_2980094, baseEnd_2980094] using wordTrace_append hprefix tailTrace_2980094
  have hstable : (prefixWord ++ tailWord_2980094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980094).length < 2 ^ (prefixWord ++ tailWord_2980094).sum := by decide
  have hdescent : baseEnd_2980094 < baseStart_2980094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980107 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 10]
def baseStart_2980107 : Nat := 118140960795 + 2980107 * 2 ^ 59
def prefixEnd_2980107 : Nat := 4983230072969 + 3 ^ 40 * 2980107 * 2
def baseEnd_2980107 : Nat := 170025254758719672373027

theorem tailTrace_2980107 : CollatzResearch.WordTrace tailWord_2980107 prefixEnd_2980107 170025254758719672373027 := by
  unfold tailWord_2980107
  simp only [CollatzResearch.WordTrace]
  refine ⟨108693431814588775600194575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72462287876392517066796383 108693431814588775600194575)
  ·
    refine ⟨163040147721883163400291863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108693431814588775600194575 163040147721883163400291863)
    ·
      refine ⟨244560221582824745100437795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163040147721883163400291863 244560221582824745100437795)
      ·
        refine ⟨366840332374237117650656693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244560221582824745100437795 366840332374237117650656693)
        ·
          refine ⟨34391281160084729779749065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 366840332374237117650656693 34391281160084729779749065)
          ·
            refine ⟨25793460870063547334811799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34391281160084729779749065 25793460870063547334811799)
            ·
              refine ⟨38690191305095321002217699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25793460870063547334811799 38690191305095321002217699)
              ·
                refine ⟨58035286957642981503326549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38690191305095321002217699 58035286957642981503326549)
                ·
                  refine ⟨170025254758719672373027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 58035286957642981503326549 170025254758719672373027)
                  ·
                    rfl

theorem cell23_2980107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 10].length) (baseStart_2980107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980107 prefixEnd_2980107 := by exact prefixLift 2980107
  have htrace : WordTrace (prefixWord ++ tailWord_2980107) baseStart_2980107 baseEnd_2980107 := by
    simpa [prefixWord, tailWord_2980107, baseEnd_2980107] using wordTrace_append hprefix tailTrace_2980107
  have hstable : (prefixWord ++ tailWord_2980107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980107).length < 2 ^ (prefixWord ++ tailWord_2980107).sum := by decide
  have hdescent : baseEnd_2980107 < baseStart_2980107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980124 : List Nat := [2, 2, 3, 1, 1, 1, 1, 6, 6]
def baseStart_2980124 : Nat := 118140960795 + 2980124 * 2 ^ 59
def prefixEnd_2980124 : Nat := 4983230072969 + 3 ^ 40 * 2980124 * 2
def baseEnd_2980124 : Nat := 170026224666622609427185

theorem tailTrace_2980124 : CollatzResearch.WordTrace tailWord_2980124 prefixEnd_2980124 170026224666622609427185 := by
  unfold tailWord_2980124
  simp only [CollatzResearch.WordTrace]
  refine ⟨54347025927763593751781713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72462701237018125002375617 54347025927763593751781713)
  ·
    refine ⟨40760269445822695313836285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54347025927763593751781713 40760269445822695313836285)
    ·
      refine ⟨15285101042183510742688607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40760269445822695313836285 15285101042183510742688607)
      ·
        refine ⟨22927651563275266114032911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15285101042183510742688607 22927651563275266114032911)
        ·
          refine ⟨34391477344912899171049367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22927651563275266114032911 34391477344912899171049367)
          ·
            refine ⟨51587216017369348756574051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34391477344912899171049367 51587216017369348756574051)
            ·
              refine ⟨77380824026054023134861077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51587216017369348756574051 77380824026054023134861077)
              ·
                refine ⟨3627226126221282334446613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77380824026054023134861077 3627226126221282334446613)
                ·
                  refine ⟨170026224666622609427185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3627226126221282334446613 170026224666622609427185)
                  ·
                    rfl

theorem cell23_2980124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 6].length) (baseStart_2980124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980124 prefixEnd_2980124 := by exact prefixLift 2980124
  have htrace : WordTrace (prefixWord ++ tailWord_2980124) baseStart_2980124 baseEnd_2980124 := by
    simpa [prefixWord, tailWord_2980124, baseEnd_2980124] using wordTrace_append hprefix tailTrace_2980124
  have hstable : (prefixWord ++ tailWord_2980124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980124).length < 2 ^ (prefixWord ++ tailWord_2980124).sum := by decide
  have hdescent : baseEnd_2980124 < baseStart_2980124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980128 : List Nat := [2, 1, 1, 5, 2, 3, 1, 1, 3, 4]
def baseStart_2980128 : Nat := 118140960795 + 2980128 * 2 ^ 59
def prefixEnd_2980128 : Nat := 4983230072969 + 3 ^ 40 * 2980128 * 2
def baseEnd_2980128 : Nat := 510079358640740489731549

theorem tailTrace_2980128 : CollatzResearch.WordTrace tailWord_2980128 prefixEnd_2980128 510079358640740489731549 := by
  unfold tailWord_2980128
  simp only [CollatzResearch.WordTrace]
  refine ⟨54347098873756348093354519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72462798498341797457806025 54347098873756348093354519)
  ·
    refine ⟨81520648310634522140031779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54347098873756348093354519 81520648310634522140031779)
    ·
      refine ⟨122280972465951783210047669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81520648310634522140031779 122280972465951783210047669)
      ·
        refine ⟨11463841168682979675941969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122280972465951783210047669 11463841168682979675941969)
        ·
          refine ⟨8597880876512234756956477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11463841168682979675941969 8597880876512234756956477)
          ·
            refine ⟨3224205328692088033858679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8597880876512234756956477 3224205328692088033858679)
            ·
              refine ⟨4836307993038132050788019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3224205328692088033858679 4836307993038132050788019)
              ·
                refine ⟨7254461989557198076182029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4836307993038132050788019 7254461989557198076182029)
                ·
                  refine ⟨2720423246083949278568261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7254461989557198076182029 2720423246083949278568261)
                  ·
                    refine ⟨510079358640740489731549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2720423246083949278568261 510079358640740489731549)
                    ·
                      rfl

theorem cell23_2980128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 3, 4].length) (baseStart_2980128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980128 prefixEnd_2980128 := by exact prefixLift 2980128
  have htrace : WordTrace (prefixWord ++ tailWord_2980128) baseStart_2980128 baseEnd_2980128 := by
    simpa [prefixWord, tailWord_2980128, baseEnd_2980128] using wordTrace_append hprefix tailTrace_2980128
  have hstable : (prefixWord ++ tailWord_2980128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980128).length < 2 ^ (prefixWord ++ tailWord_2980128).sum := by decide
  have hdescent : baseEnd_2980128 < baseStart_2980128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980151 : List Nat := [1, 1, 3, 1, 2, 1, 1, 6, 3, 1, 3]
def baseStart_2980151 : Nat := 118140960795 + 2980151 * 2 ^ 59
def prefixEnd_2980151 : Nat := 4983230072969 + 3 ^ 40 * 2980151 * 2
def baseEnd_2980151 : Nat := 1530249885977274879207041

theorem tailTrace_2980151 : CollatzResearch.WordTrace tailWord_2980151 prefixEnd_2980151 1530249885977274879207041 := by
  unfold tailWord_2980151
  simp only [CollatzResearch.WordTrace]
  refine ⟨108695036626429371114796307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72463357750952914076530871 108695036626429371114796307)
  ·
    refine ⟨163042554939644056672194461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108695036626429371114796307 163042554939644056672194461)
    ·
      refine ⟨61140958102366521252072923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163042554939644056672194461 61140958102366521252072923)
      ·
        refine ⟨91711437153549781878109385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61140958102366521252072923 91711437153549781878109385)
        ·
          refine ⟨68783577865162336408582039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91711437153549781878109385 68783577865162336408582039)
          ·
            refine ⟨103175366797743504612873059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68783577865162336408582039 103175366797743504612873059)
            ·
              refine ⟨154763050196615256919309589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103175366797743504612873059 154763050196615256919309589)
              ·
                refine ⟨7254517977966340168092637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154763050196615256919309589 7254517977966340168092637)
                ·
                  refine ⟨2720444241737377563034739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7254517977966340168092637 2720444241737377563034739)
                  ·
                    refine ⟨4080666362606066344552109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2720444241737377563034739 4080666362606066344552109)
                    ·
                      refine ⟨1530249885977274879207041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4080666362606066344552109 1530249885977274879207041)
                      ·
                        rfl

theorem cell23_2980151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 1, 3].length) (baseStart_2980151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980151 prefixEnd_2980151 := by exact prefixLift 2980151
  have htrace : WordTrace (prefixWord ++ tailWord_2980151) baseStart_2980151 baseEnd_2980151 := by
    simpa [prefixWord, tailWord_2980151, baseEnd_2980151] using wordTrace_append hprefix tailTrace_2980151
  have hstable : (prefixWord ++ tailWord_2980151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980151).length < 2 ^ (prefixWord ++ tailWord_2980151).sum := by decide
  have hdescent : baseEnd_2980151 < baseStart_2980151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980178 : List Nat := [3, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2]
def baseStart_2980178 : Nat := 118140960795 + 2980178 * 2 ^ 59
def prefixEnd_2980178 : Nat := 4983230072969 + 3 ^ 40 * 2980178 * 2
def baseEnd_2980178 : Nat := 1530263749954946273569417

theorem tailTrace_2980178 : CollatzResearch.WordTrace tailWord_2980178 prefixEnd_2980178 1530263749954946273569417 := by
  unfold tailWord_2980178
  simp only [CollatzResearch.WordTrace]
  refine ⟨27174005349332888681507297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72464014264887703150686125 27174005349332888681507297)
  ·
    refine ⟨20380504011999666511130473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27174005349332888681507297 20380504011999666511130473)
    ·
      refine ⟨15285378008999749883347855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20380504011999666511130473 15285378008999749883347855)
      ·
        refine ⟨22928067013499624825021783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15285378008999749883347855 22928067013499624825021783)
        ·
          refine ⟨34392100520249437237532675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22928067013499624825021783 34392100520249437237532675)
          ·
            refine ⟨51588150780374155856299013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34392100520249437237532675 51588150780374155856299013)
            ·
              refine ⟨9672778271320154223056065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51588150780374155856299013 9672778271320154223056065)
              ·
                refine ⟨7254583703490115667292049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9672778271320154223056065 7254583703490115667292049)
                ·
                  refine ⟨5440937777617586750469037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7254583703490115667292049 5440937777617586750469037)
                  ·
                    refine ⟨2040351666606595031425889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5440937777617586750469037 2040351666606595031425889)
                    ·
                      refine ⟨1530263749954946273569417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2040351666606595031425889 1530263749954946273569417)
                      ·
                        rfl

theorem cell23_2980178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_2980178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980178 prefixEnd_2980178 := by exact prefixLift 2980178
  have htrace : WordTrace (prefixWord ++ tailWord_2980178) baseStart_2980178 baseEnd_2980178 := by
    simpa [prefixWord, tailWord_2980178, baseEnd_2980178] using wordTrace_append hprefix tailTrace_2980178
  have hstable : (prefixWord ++ tailWord_2980178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980178).length < 2 ^ (prefixWord ++ tailWord_2980178).sum := by decide
  have hdescent : baseEnd_2980178 < baseStart_2980178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980201 : List Nat := [1, 2, 1, 1, 1, 3, 3, 5, 2, 4]
def baseStart_2980201 : Nat := 118140960795 + 2980201 * 2 ^ 59
def prefixEnd_2980201 : Nat := 4983230072969 + 3 ^ 40 * 2980201 * 2
def baseEnd_2980201 : Nat := 510091853336666561193937

theorem tailTrace_2980201 : CollatzResearch.WordTrace tailWord_2980201 prefixEnd_2980201 510091853336666561193937 := by
  unfold tailWord_2980201
  simp only [CollatzResearch.WordTrace]
  refine ⟨108696860276248229654116457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72464573517498819769410971 108696860276248229654116457)
  ·
    refine ⟨81522645207186172240587343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108696860276248229654116457 81522645207186172240587343)
    ·
      refine ⟨122283967810779258360881015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81522645207186172240587343 122283967810779258360881015)
      ·
        refine ⟨183425951716168887541321523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122283967810779258360881015 183425951716168887541321523)
        ·
          refine ⟨275138927574253331311982285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183425951716168887541321523 275138927574253331311982285)
          ·
            refine ⟨103177097840344999241993357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275138927574253331311982285 103177097840344999241993357)
            ·
              refine ⟨38691411690129374715747509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103177097840344999241993357 38691411690129374715747509)
              ·
                refine ⟨3627319845949628879601329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38691411690129374715747509 3627319845949628879601329)
                ·
                  refine ⟨2720489884462221659700997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3627319845949628879601329 2720489884462221659700997)
                  ·
                    refine ⟨510091853336666561193937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2720489884462221659700997 510091853336666561193937)
                    ·
                      rfl

theorem cell23_2980201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 4].length) (baseStart_2980201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980201 prefixEnd_2980201 := by exact prefixLift 2980201
  have htrace : WordTrace (prefixWord ++ tailWord_2980201) baseStart_2980201 baseEnd_2980201 := by
    simpa [prefixWord, tailWord_2980201, baseEnd_2980201] using wordTrace_append hprefix tailTrace_2980201
  have hstable : (prefixWord ++ tailWord_2980201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980201).length < 2 ^ (prefixWord ++ tailWord_2980201).sum := by decide
  have hdescent : baseEnd_2980201 < baseStart_2980201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980208 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 5, 2, 2]
def baseStart_2980208 : Nat := 118140960795 + 2980208 * 2 ^ 59
def prefixEnd_2980208 : Nat := 4983230072969 + 3 ^ 40 * 2980208 * 2
def baseEnd_2980208 : Nat := 1530279154374581156194279

theorem tailTrace_2980208 : CollatzResearch.WordTrace tailWord_2980208 prefixEnd_2980208 1530279154374581156194279 := by
  unfold tailWord_2980208
  simp only [CollatzResearch.WordTrace]
  refine ⟨54348557793611434924810639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72464743724815246566414185 54348557793611434924810639)
  ·
    refine ⟨81522836690417152387215959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54348557793611434924810639 81522836690417152387215959)
    ·
      refine ⟨122284255035625728580823939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81522836690417152387215959 122284255035625728580823939)
      ·
        refine ⟨183426382553438592871235909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122284255035625728580823939 183426382553438592871235909)
        ·
          refine ⟨34392446728769736163356733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183426382553438592871235909 34392446728769736163356733)
          ·
            refine ⟨12897167523288651061258775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34392446728769736163356733 12897167523288651061258775)
            ·
              refine ⟨19345751284932976591888163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12897167523288651061258775 19345751284932976591888163)
              ·
                refine ⟨29018626927399464887832245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19345751284932976591888163 29018626927399464887832245)
                ·
                  refine ⟨2720496274443699833234273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29018626927399464887832245 2720496274443699833234273)
                  ·
                    refine ⟨2040372205832774874925705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2720496274443699833234273 2040372205832774874925705)
                    ·
                      refine ⟨1530279154374581156194279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2040372205832774874925705 1530279154374581156194279)
                      ·
                        rfl

theorem cell23_2980208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 5, 2, 2].length) (baseStart_2980208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980208 prefixEnd_2980208 := by exact prefixLift 2980208
  have htrace : WordTrace (prefixWord ++ tailWord_2980208) baseStart_2980208 baseEnd_2980208 := by
    simpa [prefixWord, tailWord_2980208, baseEnd_2980208] using wordTrace_append hprefix tailTrace_2980208
  have hstable : (prefixWord ++ tailWord_2980208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980208).length < 2 ^ (prefixWord ++ tailWord_2980208).sum := by decide
  have hdescent : baseEnd_2980208 < baseStart_2980208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980221 : List Nat := [1, 4, 1, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_2980221 : Nat := 118140960795 + 2980221 * 2 ^ 59
def prefixEnd_2980221 : Nat := 4983230072969 + 3 ^ 40 * 2980221 * 2
def baseEnd_2980221 : Nat := 1530285829623089605331719

theorem tailTrace_2980221 : CollatzResearch.WordTrace tailWord_2980221 prefixEnd_2980221 1530285829623089605331719 := by
  unfold tailWord_2980221
  simp only [CollatzResearch.WordTrace]
  refine ⟨108697589736175773069844517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72465059824117182046563011 108697589736175773069844517)
  ·
    refine ⟨20380798075532957450595847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108697589736175773069844517 20380798075532957450595847)
    ·
      refine ⟨30571197113299436175893771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20380798075532957450595847 30571197113299436175893771)
      ·
        refine ⟨45856795669949154263840657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30571197113299436175893771 45856795669949154263840657)
        ·
          refine ⟨34392596752461865697880493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45856795669949154263840657 34392596752461865697880493)
          ·
            refine ⟨12897223782173199636705185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34392596752461865697880493 12897223782173199636705185)
            ·
              refine ⟨9672917836629899727528889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12897223782173199636705185 9672917836629899727528889)
              ·
                refine ⟨7254688377472424795646667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9672917836629899727528889 7254688377472424795646667)
                ·
                  refine ⟨10882032566208637193470001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7254688377472424795646667 10882032566208637193470001)
                  ·
                    refine ⟨8161524424656477895102501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10882032566208637193470001 8161524424656477895102501)
                    ·
                      refine ⟨1530285829623089605331719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8161524424656477895102501 1530285829623089605331719)
                      ·
                        rfl

theorem cell23_2980221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_2980221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980221 prefixEnd_2980221 := by exact prefixLift 2980221
  have htrace : WordTrace (prefixWord ++ tailWord_2980221) baseStart_2980221 baseEnd_2980221 := by
    simpa [prefixWord, tailWord_2980221, baseEnd_2980221] using wordTrace_append hprefix tailTrace_2980221
  have hstable : (prefixWord ++ tailWord_2980221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980221).length < 2 ^ (prefixWord ++ tailWord_2980221).sum := by decide
  have hdescent : baseEnd_2980221 < baseStart_2980221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980225 : List Nat := [1, 2, 4, 3, 1, 1, 4, 1, 1, 1, 4]
def baseStart_2980225 : Nat := 118140960795 + 2980225 * 2 ^ 59
def prefixEnd_2980225 : Nat := 4983230072969 + 3 ^ 40 * 2980225 * 2
def baseEnd_2980225 : Nat := 1530287883545707589681701

theorem tailTrace_2980225 : CollatzResearch.WordTrace tailWord_2980225 prefixEnd_2980225 1530287883545707589681701 := by
  unfold tailWord_2980225
  simp only [CollatzResearch.WordTrace]
  refine ⟨108697735628161281752990129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72465157085440854501993419 108697735628161281752990129)
  ·
    refine ⟨81523301721120961314742597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108697735628161281752990129 81523301721120961314742597)
    ·
      refine ⟨15285619072710180246514237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81523301721120961314742597 15285619072710180246514237)
      ·
        refine ⟨5732107152266317592442839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15285619072710180246514237 5732107152266317592442839)
        ·
          refine ⟨8598160728399476388664259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5732107152266317592442839 8598160728399476388664259)
          ·
            refine ⟨12897241092599214582996389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8598160728399476388664259 12897241092599214582996389)
            ·
              refine ⟨2418232704862352734311823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12897241092599214582996389 2418232704862352734311823)
              ·
                refine ⟨3627349057293529101467735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2418232704862352734311823 3627349057293529101467735)
                ·
                  refine ⟨5441023585940293652201603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3627349057293529101467735 5441023585940293652201603)
                  ·
                    refine ⟨8161535378910440478302405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5441023585940293652201603 8161535378910440478302405)
                    ·
                      refine ⟨1530287883545707589681701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8161535378910440478302405 1530287883545707589681701)
                      ·
                        rfl

theorem cell23_2980225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_2980225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980225 prefixEnd_2980225 := by exact prefixLift 2980225
  have htrace : WordTrace (prefixWord ++ tailWord_2980225) baseStart_2980225 baseEnd_2980225 := by
    simpa [prefixWord, tailWord_2980225, baseEnd_2980225] using wordTrace_append hprefix tailTrace_2980225
  have hstable : (prefixWord ++ tailWord_2980225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980225).length < 2 ^ (prefixWord ++ tailWord_2980225).sum := by decide
  have hdescent : baseEnd_2980225 < baseStart_2980225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980228 : List Nat := [2, 3, 2, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_2980228 : Nat := 118140960795 + 2980228 * 2 ^ 59
def prefixEnd_2980228 : Nat := 4983230072969 + 3 ^ 40 * 2980228 * 2
def baseEnd_2980228 : Nat := 1530289423987671077944187

theorem tailTrace_2980228 : CollatzResearch.WordTrace tailWord_2980228 prefixEnd_2980228 1530289423987671077944187 := by
  unfold tailWord_2980228
  simp only [CollatzResearch.WordTrace]
  refine ⟨54348922523575206632674669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72465230031433608843566225 54348922523575206632674669)
  ·
    refine ⟨20380845946340702487253001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54348922523575206632674669 20380845946340702487253001)
    ·
      refine ⟨15285634459755526865439751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20380845946340702487253001 15285634459755526865439751)
      ·
        refine ⟨22928451689633290298159627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15285634459755526865439751 22928451689633290298159627)
        ·
          refine ⟨34392677534449935447239441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22928451689633290298159627 34392677534449935447239441)
          ·
            refine ⟨25794508150837451585429581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34392677534449935447239441 25794508150837451585429581)
            ·
              refine ⟨9672940556564044344536093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25794508150837451585429581 9672940556564044344536093)
              ·
                refine ⟨3627352708711516629201035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9672940556564044344536093 3627352708711516629201035)
                ·
                  refine ⟨5441029063067274943801553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3627352708711516629201035 5441029063067274943801553)
                  ·
                    refine ⟨4080771797300456207851165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5441029063067274943801553 4080771797300456207851165)
                    ·
                      refine ⟨1530289423987671077944187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4080771797300456207851165 1530289423987671077944187)
                      ·
                        rfl

theorem cell23_2980228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_2980228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980228 prefixEnd_2980228 := by exact prefixLift 2980228
  have htrace : WordTrace (prefixWord ++ tailWord_2980228) baseStart_2980228 baseEnd_2980228 := by
    simpa [prefixWord, tailWord_2980228, baseEnd_2980228] using wordTrace_append hprefix tailTrace_2980228
  have hstable : (prefixWord ++ tailWord_2980228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980228).length < 2 ^ (prefixWord ++ tailWord_2980228).sum := by decide
  have hdescent : baseEnd_2980228 < baseStart_2980228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980285 : List Nat := [1, 4, 1, 2, 2, 2, 2, 3, 1, 3, 2]
def baseStart_2980285 : Nat := 118140960795 + 2980285 * 2 ^ 59
def prefixEnd_2980285 : Nat := 4983230072969 + 3 ^ 40 * 2980285 * 2
def baseEnd_2980285 : Nat := 1530318692384977354931425

theorem tailTrace_2980285 : CollatzResearch.WordTrace tailWord_2980285 prefixEnd_2980285 1530318692384977354931425 := by
  unfold tailWord_2980285
  simp only [CollatzResearch.WordTrace]
  refine ⟨108699924007943912000174309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72466616005295941333449539 108699924007943912000174309)
  ·
    refine ⟨20381235751489483500032683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108699924007943912000174309 20381235751489483500032683)
    ·
      refine ⟨30571853627234225250049025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20381235751489483500032683 30571853627234225250049025)
      ·
        refine ⟨22928890220425668937536769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30571853627234225250049025 22928890220425668937536769)
        ·
          refine ⟨17196667665319251703152577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22928890220425668937536769 17196667665319251703152577)
          ·
            refine ⟨12897500748989438777364433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17196667665319251703152577 12897500748989438777364433)
            ·
              refine ⟨9673125561742079083023325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12897500748989438777364433 9673125561742079083023325)
              ·
                refine ⟨3627422085653279656133747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9673125561742079083023325 3627422085653279656133747)
                ·
                  refine ⟨5441133128479919484200621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3627422085653279656133747 5441133128479919484200621)
                  ·
                    refine ⟨2040424923179969806575233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5441133128479919484200621 2040424923179969806575233)
                    ·
                      refine ⟨1530318692384977354931425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2040424923179969806575233 1530318692384977354931425)
                      ·
                        rfl

theorem cell23_2980285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_2980285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980285 prefixEnd_2980285 := by exact prefixLift 2980285
  have htrace : WordTrace (prefixWord ++ tailWord_2980285) baseStart_2980285 baseEnd_2980285 := by
    simpa [prefixWord, tailWord_2980285, baseEnd_2980285] using wordTrace_append hprefix tailTrace_2980285
  have hstable : (prefixWord ++ tailWord_2980285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980285).length < 2 ^ (prefixWord ++ tailWord_2980285).sum := by decide
  have hdescent : baseEnd_2980285 < baseStart_2980285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980351 : List Nat := [1, 1, 2, 2, 1, 2, 3, 4, 2, 5]
def baseStart_2980351 : Nat := 118140960795 + 2980351 * 2 ^ 59
def prefixEnd_2980351 : Nat := 4983230072969 + 3 ^ 40 * 2980351 * 2
def baseEnd_2980351 : Nat := 510117527369391365568707

theorem tailTrace_2980351 : CollatzResearch.WordTrace tailWord_2980351 prefixEnd_2980351 510117527369391365568707 := by
  unfold tailWord_2980351
  simp only [CollatzResearch.WordTrace]
  refine ⟨108702331225704805272076907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72468220817136536848051271 108702331225704805272076907)
  ·
    refine ⟨163053496838557207908115361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108702331225704805272076907 163053496838557207908115361)
    ·
      refine ⟨122290122628917905931086521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163053496838557207908115361 122290122628917905931086521)
      ·
        refine ⟨91717591971688429448314891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122290122628917905931086521 91717591971688429448314891)
        ·
          refine ⟨137576387957532644172472337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91717591971688429448314891 137576387957532644172472337)
          ·
            refine ⟨103182290968149483129354253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137576387957532644172472337 103182290968149483129354253)
            ·
              refine ⟨38693359113056056173507845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103182290968149483129354253 38693359113056056173507845)
              ·
                refine ⟨7255004833698010532532721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38693359113056056173507845 7255004833698010532532721)
                ·
                  refine ⟨5441253625273507899399541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7255004833698010532532721 5441253625273507899399541)
                  ·
                    refine ⟨510117527369391365568707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5441253625273507899399541 510117527369391365568707)
                    ·
                      rfl

theorem cell23_2980351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 5].length) (baseStart_2980351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980351 prefixEnd_2980351 := by exact prefixLift 2980351
  have htrace : WordTrace (prefixWord ++ tailWord_2980351) baseStart_2980351 baseEnd_2980351 := by
    simpa [prefixWord, tailWord_2980351, baseEnd_2980351] using wordTrace_append hprefix tailTrace_2980351
  have hstable : (prefixWord ++ tailWord_2980351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980351).length < 2 ^ (prefixWord ++ tailWord_2980351).sum := by decide
  have hdescent : baseEnd_2980351 < baseStart_2980351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980371 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 4]
def baseStart_2980371 : Nat := 118140960795 + 2980371 * 2 ^ 59
def prefixEnd_2980371 : Nat := 4983230072969 + 3 ^ 40 * 2980371 * 2
def baseEnd_2980371 : Nat := 1530362851721264018456029

theorem tailTrace_2980371 : CollatzResearch.WordTrace tailWord_2980371 prefixEnd_2980371 1530362851721264018456029 := by
  unfold tailWord_2980371
  simp only [CollatzResearch.WordTrace]
  refine ⟨108703060685632348687804967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72468707123754899125203311 108703060685632348687804967)
  ·
    refine ⟨163054591028448523031707451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108703060685632348687804967 163054591028448523031707451)
    ·
      refine ⟨244581886542672784547561177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163054591028448523031707451 244581886542672784547561177)
      ·
        refine ⟨183436414907004588410670883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244581886542672784547561177 183436414907004588410670883)
        ·
          refine ⟨275154622360506882616006325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183436414907004588410670883 275154622360506882616006325)
          ·
            refine ⟨25795745846297520245250593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 275154622360506882616006325 25795745846297520245250593)
            ·
              refine ⟨19346809384723140183937945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25795745846297520245250593 19346809384723140183937945)
              ·
                refine ⟨14510107038542355137953459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19346809384723140183937945 14510107038542355137953459)
                ·
                  refine ⟨21765160557813532706930189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14510107038542355137953459 21765160557813532706930189)
                  ·
                    refine ⟨8161935209180074765098821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21765160557813532706930189 8161935209180074765098821)
                    ·
                      refine ⟨1530362851721264018456029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8161935209180074765098821 1530362851721264018456029)
                      ·
                        rfl

theorem cell23_2980371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_2980371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980371 prefixEnd_2980371 := by exact prefixLift 2980371
  have htrace : WordTrace (prefixWord ++ tailWord_2980371) baseStart_2980371 baseEnd_2980371 := by
    simpa [prefixWord, tailWord_2980371, baseEnd_2980371] using wordTrace_append hprefix tailTrace_2980371
  have hstable : (prefixWord ++ tailWord_2980371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980371).length < 2 ^ (prefixWord ++ tailWord_2980371).sum := by decide
  have hdescent : baseEnd_2980371 < baseStart_2980371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980401 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 2, 1, 6]
def baseStart_2980401 : Nat := 118140960795 + 2980401 * 2 ^ 59
def prefixEnd_2980401 : Nat := 4983230072969 + 3 ^ 40 * 2980401 * 2
def baseEnd_2980401 : Nat := 1530378256140898901080891

theorem tailTrace_2980401 : CollatzResearch.WordTrace tailWord_2980401 prefixEnd_2980401 1530378256140898901080891 := by
  unfold tailWord_2980401
  simp only [CollatzResearch.WordTrace]
  refine ⟨108704154875523663811397057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72469436583682442540931371 108704154875523663811397057)
  ·
    refine ⟨81528116156642747858547793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108704154875523663811397057 81528116156642747858547793)
    ·
      refine ⟨61146087117482060893910845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81528116156642747858547793 61146087117482060893910845)
      ·
        refine ⟨22929782669055772835216567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61146087117482060893910845 22929782669055772835216567)
        ·
          refine ⟨34394674003583659252824851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22929782669055772835216567 34394674003583659252824851)
          ·
            refine ⟨51592011005375488879237277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34394674003583659252824851 51592011005375488879237277)
            ·
              refine ⟨19347004127015808329713979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51592011005375488879237277 19347004127015808329713979)
              ·
                refine ⟨29020506190523712494570969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19347004127015808329713979 29020506190523712494570969)
                ·
                  refine ⟨21765379642892784370928227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29020506190523712494570969 21765379642892784370928227)
                  ·
                    refine ⟨32648069464339176556392341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21765379642892784370928227 32648069464339176556392341)
                    ·
                      refine ⟨1530378256140898901080891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32648069464339176556392341 1530378256140898901080891)
                      ·
                        rfl

theorem cell23_2980401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_2980401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980401 prefixEnd_2980401 := by exact prefixLift 2980401
  have htrace : WordTrace (prefixWord ++ tailWord_2980401) baseStart_2980401 baseEnd_2980401 := by
    simpa [prefixWord, tailWord_2980401, baseEnd_2980401] using wordTrace_append hprefix tailTrace_2980401
  have hstable : (prefixWord ++ tailWord_2980401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980401).length < 2 ^ (prefixWord ++ tailWord_2980401).sum := by decide
  have hdescent : baseEnd_2980401 < baseStart_2980401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980408 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 4, 2, 3]
def baseStart_2980408 : Nat := 118140960795 + 2980408 * 2 ^ 59
def prefixEnd_2980408 : Nat := 4983230072969 + 3 ^ 40 * 2980408 * 2
def baseEnd_2980408 : Nat := 1530381850505480373693359

theorem tailTrace_2980408 : CollatzResearch.WordTrace tailWord_2980408 prefixEnd_2980408 1530381850505480373693359 := by
  unfold tailWord_2980408
  simp only [CollatzResearch.WordTrace]
  refine ⟨54352205093249152003450939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72469606790998869337934585 54352205093249152003450939)
  ·
    refine ⟨81528307639873728005176409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54352205093249152003450939 81528307639873728005176409)
    ·
      refine ⟨61146230729905296003882307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81528307639873728005176409 61146230729905296003882307)
      ·
        refine ⟨91719346094857944005823461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61146230729905296003882307 91719346094857944005823461)
        ·
          refine ⟨17197377392785864501091899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91719346094857944005823461 17197377392785864501091899)
          ·
            refine ⟨25796066089178796751637849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17197377392785864501091899 25796066089178796751637849)
            ·
              refine ⟨19347049566884097563728387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25796066089178796751637849 19347049566884097563728387)
              ·
                refine ⟨29020574350326146345592581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19347049566884097563728387 29020574350326146345592581)
                ·
                  refine ⟨5441357690686152439798609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29020574350326146345592581 5441357690686152439798609)
                  ·
                    refine ⟨4081018268014614329848957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5441357690686152439798609 4081018268014614329848957)
                    ·
                      refine ⟨1530381850505480373693359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4081018268014614329848957 1530381850505480373693359)
                      ·
                        rfl

theorem cell23_2980408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_2980408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980408 prefixEnd_2980408 := by exact prefixLift 2980408
  have htrace : WordTrace (prefixWord ++ tailWord_2980408) baseStart_2980408 baseEnd_2980408 := by
    simpa [prefixWord, tailWord_2980408, baseEnd_2980408] using wordTrace_append hprefix tailTrace_2980408
  have hstable : (prefixWord ++ tailWord_2980408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980408).length < 2 ^ (prefixWord ++ tailWord_2980408).sum := by decide
  have hdescent : baseEnd_2980408 < baseStart_2980408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980415 : List Nat := [1, 1, 2, 2, 3, 2, 1, 6, 1, 4]
def baseStart_2980415 : Nat := 118140960795 + 2980415 * 2 ^ 59
def prefixEnd_2980415 : Nat := 4983230072969 + 3 ^ 40 * 2980415 * 2
def baseEnd_2980415 : Nat := 510128481623353948768609

theorem tailTrace_2980415 : CollatzResearch.WordTrace tailWord_2980415 prefixEnd_2980415 510128481623353948768609 := by
  unfold tailWord_2980415
  simp only [CollatzResearch.WordTrace]
  refine ⟨108704665497472944202406699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72469776998315296134937799 108704665497472944202406699)
  ·
    refine ⟨163056998246209416303610049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108704665497472944202406699 163056998246209416303610049)
    ·
      refine ⟨122292748684657062227707537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163056998246209416303610049 122292748684657062227707537)
      ·
        refine ⟨91719561513492796670780653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122292748684657062227707537 91719561513492796670780653)
        ·
          refine ⟨34394835567559798751542745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91719561513492796670780653 34394835567559798751542745)
          ·
            refine ⟨25796126675669849063657059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34394835567559798751542745 25796126675669849063657059)
            ·
              refine ⟨38694190013504773595485589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25796126675669849063657059 38694190013504773595485589)
              ·
                refine ⟨1813790156883036262288387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38694190013504773595485589 1813790156883036262288387)
                ·
                  refine ⟨2720685235324554393432581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1813790156883036262288387 2720685235324554393432581)
                  ·
                    refine ⟨510128481623353948768609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2720685235324554393432581 510128481623353948768609)
                    ·
                      rfl

theorem cell23_2980415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 1, 4].length) (baseStart_2980415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980415 prefixEnd_2980415 := by exact prefixLift 2980415
  have htrace : WordTrace (prefixWord ++ tailWord_2980415) baseStart_2980415 baseEnd_2980415 := by
    simpa [prefixWord, tailWord_2980415, baseEnd_2980415] using wordTrace_append hprefix tailTrace_2980415
  have hstable : (prefixWord ++ tailWord_2980415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980415).length < 2 ^ (prefixWord ++ tailWord_2980415).sum := by decide
  have hdescent : baseEnd_2980415 < baseStart_2980415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980528 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 3]
def baseStart_2980528 : Nat := 118140960795 + 2980528 * 2 ^ 59
def prefixEnd_2980528 : Nat := 4983230072969 + 3 ^ 40 * 2980528 * 2
def baseEnd_2980528 : Nat := 1530443468184019904192807

theorem tailTrace_2980528 : CollatzResearch.WordTrace tailWord_2980528 prefixEnd_2980528 1530443468184019904192807 := by
  unfold tailWord_2980528
  simp only [CollatzResearch.WordTrace]
  refine ⟨54354393473031782250635119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72472524630709043000846825 54354393473031782250635119)
  ·
    refine ⟨81531590209547673375952679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54354393473031782250635119 81531590209547673375952679)
    ·
      refine ⟨122297385314321510063929019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81531590209547673375952679 122297385314321510063929019)
      ·
        refine ⟨183446077971482265095893529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122297385314321510063929019 183446077971482265095893529)
        ·
          refine ⟨137584558478611698821920147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183446077971482265095893529 137584558478611698821920147)
          ·
            refine ⟨206376837717917548232880221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137584558478611698821920147 206376837717917548232880221)
            ·
              refine ⟨77391314144219080587330083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206376837717917548232880221 77391314144219080587330083)
              ·
                refine ⟨116086971216328620880995125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77391314144219080587330083 116086971216328620880995125)
                ·
                  refine ⟨10883153551530808207593293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116086971216328620880995125 10883153551530808207593293)
                  ·
                    refine ⟨4081182581824053077847485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10883153551530808207593293 4081182581824053077847485)
                    ·
                      refine ⟨1530443468184019904192807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4081182581824053077847485 1530443468184019904192807)
                      ·
                        rfl

theorem cell23_2980528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 3].length) (baseStart_2980528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980528 prefixEnd_2980528 := by exact prefixLift 2980528
  have htrace : WordTrace (prefixWord ++ tailWord_2980528) baseStart_2980528 baseEnd_2980528 := by
    simpa [prefixWord, tailWord_2980528, baseEnd_2980528] using wordTrace_append hprefix tailTrace_2980528
  have hstable : (prefixWord ++ tailWord_2980528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980528).length < 2 ^ (prefixWord ++ tailWord_2980528).sum := by decide
  have hdescent : baseEnd_2980528 < baseStart_2980528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980535 : List Nat := [1, 1, 3, 1, 6, 2, 1, 8]
def baseStart_2980535 : Nat := 118140960795 + 2980535 * 2 ^ 59
def prefixEnd_2980535 : Nat := 4983230072969 + 3 ^ 40 * 2980535 * 2
def baseEnd_2980535 : Nat := 56683224538837088029825

theorem tailTrace_2980535 : CollatzResearch.WordTrace tailWord_2980535 prefixEnd_2980535 56683224538837088029825 := by
  unfold tailWord_2980535
  simp only [CollatzResearch.WordTrace]
  refine ⟨108709042257038204696775059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72472694838025469797850039 108709042257038204696775059)
  ·
    refine ⟨163063563385557307045162589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108709042257038204696775059 163063563385557307045162589)
    ·
      refine ⟨61148836269583990141935971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163063563385557307045162589 61148836269583990141935971)
      ·
        refine ⟨91723254404375985212903957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61148836269583990141935971 91723254404375985212903957)
        ·
          refine ⟨4299527550205124306854873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91723254404375985212903957 4299527550205124306854873)
          ·
            refine ⟨3224645662653843230141155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4299527550205124306854873 3224645662653843230141155)
            ·
              refine ⟨4836968493980764845211733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3224645662653843230141155 4836968493980764845211733)
              ·
                refine ⟨56683224538837088029825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4836968493980764845211733 56683224538837088029825)
                ·
                  rfl

theorem cell23_2980535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 8].length) (baseStart_2980535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980535 prefixEnd_2980535 := by exact prefixLift 2980535
  have htrace : WordTrace (prefixWord ++ tailWord_2980535) baseStart_2980535 baseEnd_2980535 := by
    simpa [prefixWord, tailWord_2980535, baseEnd_2980535] using wordTrace_append hprefix tailTrace_2980535
  have hstable : (prefixWord ++ tailWord_2980535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980535).length < 2 ^ (prefixWord ++ tailWord_2980535).sum := by decide
  have hdescent : baseEnd_2980535 < baseStart_2980535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980550 : List Nat := [6, 1, 2, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_2980550 : Nat := 118140960795 + 2980550 * 2 ^ 59
def prefixEnd_2980550 : Nat := 4983230072969 + 3 ^ 40 * 2980550 * 2
def baseEnd_2980550 : Nat := 1530454764758418818117707

theorem tailTrace_2980550 : CollatzResearch.WordTrace tailWord_2980550 prefixEnd_2980550 1530454764758418818117707 := by
  unfold tailWord_2980550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3397174667249495695580347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72473059567989241505714069 3397174667249495695580347)
  ·
    refine ⟨5095762000874243543370521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3397174667249495695580347 5095762000874243543370521)
    ·
      refine ⟨3821821500655682657527891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5095762000874243543370521 3821821500655682657527891)
      ·
        refine ⟨5732732250983523986291837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3821821500655682657527891 5732732250983523986291837)
        ·
          refine ⟨2149774594118821494859439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5732732250983523986291837 2149774594118821494859439)
          ·
            refine ⟨3224661891178232242289159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2149774594118821494859439 3224661891178232242289159)
            ·
              refine ⟨4836992836767348363433739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3224661891178232242289159 4836992836767348363433739)
              ·
                refine ⟨7255489255151022545150609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4836992836767348363433739 7255489255151022545150609)
                ·
                  refine ⟨5441616941363266908862957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7255489255151022545150609 5441616941363266908862957)
                  ·
                    refine ⟨2040606353011225090823609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5441616941363266908862957 2040606353011225090823609)
                    ·
                      refine ⟨1530454764758418818117707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2040606353011225090823609 1530454764758418818117707)
                      ·
                        rfl

theorem cell23_2980550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_2980550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980550 prefixEnd_2980550 := by exact prefixLift 2980550
  have htrace : WordTrace (prefixWord ++ tailWord_2980550) baseStart_2980550 baseEnd_2980550 := by
    simpa [prefixWord, tailWord_2980550, baseEnd_2980550] using wordTrace_append hprefix tailTrace_2980550
  have hstable : (prefixWord ++ tailWord_2980550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980550).length < 2 ^ (prefixWord ++ tailWord_2980550).sum := by decide
  have hdescent : baseEnd_2980550 < baseStart_2980550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980579 : List Nat := [1, 1, 1, 7, 1, 1, 3, 2, 2, 1, 3]
def baseStart_2980579 : Nat := 118140960795 + 2980579 * 2 ^ 59
def prefixEnd_2980579 : Nat := 4983230072969 + 3 ^ 40 * 2980579 * 2
def baseEnd_2980579 : Nat := 1530469655697399204655073

theorem tailTrace_2980579 : CollatzResearch.WordTrace tailWord_2980579 prefixEnd_2980579 1530469655697399204655073 := by
  unfold tailWord_2980579
  simp only [CollatzResearch.WordTrace]
  refine ⟨108710647068878800211376791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72473764712585866807584527 108710647068878800211376791)
  ·
    refine ⟨163065970603318200317065187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108710647068878800211376791 163065970603318200317065187)
    ·
      refine ⟨244598955904977300475597781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163065970603318200317065187 244598955904977300475597781)
      ·
        refine ⟨5732788029022905479896823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 244598955904977300475597781 5732788029022905479896823)
        ·
          refine ⟨8599182043534358219845235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5732788029022905479896823 8599182043534358219845235)
          ·
            refine ⟨12898773065301537329767853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8599182043534358219845235 12898773065301537329767853)
            ·
              refine ⟨4837039899488076498662945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12898773065301537329767853 4837039899488076498662945)
              ·
                refine ⟨3627779924616057373997209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4837039899488076498662945 3627779924616057373997209)
                ·
                  refine ⟨2720834943462043030497907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3627779924616057373997209 2720834943462043030497907)
                  ·
                    refine ⟨4081252415193064545746861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2720834943462043030497907 4081252415193064545746861)
                    ·
                      refine ⟨1530469655697399204655073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4081252415193064545746861 1530469655697399204655073)
                      ·
                        rfl

theorem cell23_2980579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_2980579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980579 prefixEnd_2980579 := by exact prefixLift 2980579
  have htrace : WordTrace (prefixWord ++ tailWord_2980579) baseStart_2980579 baseEnd_2980579 := by
    simpa [prefixWord, tailWord_2980579, baseEnd_2980579] using wordTrace_append hprefix tailTrace_2980579
  have hstable : (prefixWord ++ tailWord_2980579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980579).length < 2 ^ (prefixWord ++ tailWord_2980579).sum := by decide
  have hdescent : baseEnd_2980579 < baseStart_2980579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980585 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 3, 4, 2]
def baseStart_2980585 : Nat := 118140960795 + 2980585 * 2 ^ 59
def prefixEnd_2980585 : Nat := 4983230072969 + 3 ^ 40 * 2980585 * 2
def baseEnd_2980585 : Nat := 1530472736581326181180045

theorem tailTrace_2980585 : CollatzResearch.WordTrace tailWord_2980585 prefixEnd_2980585 1530472736581326181180045 := by
  unfold tailWord_2980585
  simp only [CollatzResearch.WordTrace]
  refine ⟨108710865906857063236095209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72473910604571375490730139 108710865906857063236095209)
  ·
    refine ⟨81533149430142797427071407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108710865906857063236095209 81533149430142797427071407)
    ·
      refine ⟨122299724145214196140607111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81533149430142797427071407 122299724145214196140607111)
      ·
        refine ⟨183449586217821294210910667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122299724145214196140607111 183449586217821294210910667)
        ·
          refine ⟨275174379326731941316366001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183449586217821294210910667 275174379326731941316366001)
          ·
            refine ⟨206380784495048955987274501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275174379326731941316366001 206380784495048955987274501)
            ·
              refine ⟨38696397092821679247613969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206380784495048955987274501 38696397092821679247613969)
              ·
                refine ⟨29022297819616259435710477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38696397092821679247613969 29022297819616259435710477)
                ·
                  refine ⟨10883361682356097288391429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29022297819616259435710477 10883361682356097288391429)
                  ·
                    refine ⟨2040630315441768241573393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10883361682356097288391429 2040630315441768241573393)
                    ·
                      refine ⟨1530472736581326181180045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2040630315441768241573393 1530472736581326181180045)
                      ·
                        rfl

theorem cell23_2980585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 4, 2].length) (baseStart_2980585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980585 prefixEnd_2980585 := by exact prefixLift 2980585
  have htrace : WordTrace (prefixWord ++ tailWord_2980585) baseStart_2980585 baseEnd_2980585 := by
    simpa [prefixWord, tailWord_2980585, baseEnd_2980585] using wordTrace_append hprefix tailTrace_2980585
  have hstable : (prefixWord ++ tailWord_2980585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980585).length < 2 ^ (prefixWord ++ tailWord_2980585).sum := by decide
  have hdescent : baseEnd_2980585 < baseStart_2980585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980588 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 5]
def baseStart_2980588 : Nat := 118140960795 + 2980588 * 2 ^ 59
def prefixEnd_2980588 : Nat := 4983230072969 + 3 ^ 40 * 2980588 * 2
def baseEnd_2980588 : Nat := 1530474277023289669442531

theorem tailTrace_2980588 : CollatzResearch.WordTrace tailWord_2980588 prefixEnd_2980588 1530474277023289669442531 := by
  unfold tailWord_2980588
  simp only [CollatzResearch.WordTrace]
  refine ⟨54355487662923097374227209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72473983550564129832302945 54355487662923097374227209)
  ·
    refine ⟨40766615747192323030670407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54355487662923097374227209 40766615747192323030670407)
    ·
      refine ⟨61149923620788484546005611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40766615747192323030670407 61149923620788484546005611)
      ·
        refine ⟨91724885431182726819008417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61149923620788484546005611 91724885431182726819008417)
        ·
          refine ⟨68793664073387045114256313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91724885431182726819008417 68793664073387045114256313)
          ·
            refine ⟨51595248055040283835692235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68793664073387045114256313 51595248055040283835692235)
            ·
              refine ⟨77392872082560425753538353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51595248055040283835692235 77392872082560425753538353)
              ·
                refine ⟨58044654061920319315153765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77392872082560425753538353 58044654061920319315153765)
                ·
                  refine ⟨10883372636610059871591331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58044654061920319315153765 10883372636610059871591331)
                  ·
                    refine ⟨16325058954915089807386997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10883372636610059871591331 16325058954915089807386997)
                    ·
                      refine ⟨1530474277023289669442531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16325058954915089807386997 1530474277023289669442531)
                      ·
                        rfl

theorem cell23_2980588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_2980588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980588 prefixEnd_2980588 := by exact prefixLift 2980588
  have htrace : WordTrace (prefixWord ++ tailWord_2980588) baseStart_2980588 baseEnd_2980588 := by
    simpa [prefixWord, tailWord_2980588, baseEnd_2980588] using wordTrace_append hprefix tailTrace_2980588
  have hstable : (prefixWord ++ tailWord_2980588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980588).length < 2 ^ (prefixWord ++ tailWord_2980588).sum := by decide
  have hdescent : baseEnd_2980588 < baseStart_2980588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980602 : List Nat := [3, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2]
def baseStart_2980602 : Nat := 118140960795 + 2980602 * 2 ^ 59
def prefixEnd_2980602 : Nat := 4983230072969 + 3 ^ 40 * 2980602 * 2
def baseEnd_2980602 : Nat := 1530481465752452614667467

theorem tailTrace_2980602 : CollatzResearch.WordTrace tailWord_2980602 prefixEnd_2980602 1530481465752452614667467 := by
  unfold tailWord_2980602
  simp only [CollatzResearch.WordTrace]
  refine ⟨27177871486948868784866015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72474323965196983426309373 27177871486948868784866015)
  ·
    refine ⟨40766807230423303177299023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27177871486948868784866015 40766807230423303177299023)
    ·
      refine ⟨61150210845634954765948535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40766807230423303177299023 61150210845634954765948535)
      ·
        refine ⟨91725316268452432148922803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61150210845634954765948535 91725316268452432148922803)
        ·
          refine ⟨137587974402678648223384205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91725316268452432148922803 137587974402678648223384205)
          ·
            refine ⟨51595490401004493083769077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137587974402678648223384205 51595490401004493083769077)
            ·
              refine ⟨4837077225094171226603351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51595490401004493083769077 4837077225094171226603351)
              ·
                refine ⟨7255615837641256839905027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4837077225094171226603351 7255615837641256839905027)
                ·
                  refine ⟨10883423756461885259857541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7255615837641256839905027 10883423756461885259857541)
                  ·
                    refine ⟨2040641954336603486223289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10883423756461885259857541 2040641954336603486223289)
                    ·
                      refine ⟨1530481465752452614667467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2040641954336603486223289 1530481465752452614667467)
                      ·
                        rfl

theorem cell23_2980602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2].length) (baseStart_2980602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980602 prefixEnd_2980602 := by exact prefixLift 2980602
  have htrace : WordTrace (prefixWord ++ tailWord_2980602) baseStart_2980602 baseEnd_2980602 := by
    simpa [prefixWord, tailWord_2980602, baseEnd_2980602] using wordTrace_append hprefix tailTrace_2980602
  have hstable : (prefixWord ++ tailWord_2980602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980602).length < 2 ^ (prefixWord ++ tailWord_2980602).sum := by decide
  have hdescent : baseEnd_2980602 < baseStart_2980602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980606 : List Nat := [4, 2, 2, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_2980606 : Nat := 118140960795 + 2980606 * 2 ^ 59
def prefixEnd_2980606 : Nat := 4983230072969 + 3 ^ 40 * 2980606 * 2
def baseEnd_2980606 : Nat := 1530483519675070599017449

theorem tailTrace_2980606 : CollatzResearch.WordTrace tailWord_2980606 prefixEnd_2980606 1530483519675070599017449 := by
  unfold tailWord_2980606
  simp only [CollatzResearch.WordTrace]
  refine ⟨13588953979972622977826209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72474421226520655881739781 13588953979972622977826209)
  ·
    refine ⟨10191715484979467233369657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13588953979972622977826209 10191715484979467233369657)
    ·
      refine ⟨7643786613734600425027243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10191715484979467233369657 7643786613734600425027243)
      ·
        refine ⟨11465679920601900637540865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7643786613734600425027243 11465679920601900637540865)
        ·
          refine ⟨8599259940451425478155649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11465679920601900637540865 8599259940451425478155649)
          ·
            refine ⟨6449444955338569108616737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8599259940451425478155649 6449444955338569108616737)
            ·
              refine ⟨4837083716503926831462553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6449444955338569108616737 4837083716503926831462553)
              ·
                refine ⟨3627812787377945123596915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4837083716503926831462553 3627812787377945123596915)
                ·
                  refine ⟨5441719181066917685395373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3627812787377945123596915 5441719181066917685395373)
                  ·
                    refine ⟨2040644692900094132023265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5441719181066917685395373 2040644692900094132023265)
                    ·
                      refine ⟨1530483519675070599017449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2040644692900094132023265 1530483519675070599017449)
                      ·
                        rfl

theorem cell23_2980606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_2980606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980606 prefixEnd_2980606 := by exact prefixLift 2980606
  have htrace : WordTrace (prefixWord ++ tailWord_2980606) baseStart_2980606 baseEnd_2980606 := by
    simpa [prefixWord, tailWord_2980606, baseEnd_2980606] using wordTrace_append hprefix tailTrace_2980606
  have hstable : (prefixWord ++ tailWord_2980606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980606).length < 2 ^ (prefixWord ++ tailWord_2980606).sum := by decide
  have hdescent : baseEnd_2980606 < baseStart_2980606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980642 : List Nat := [3, 3, 1, 1, 2, 4, 1, 1, 7]
def baseStart_2980642 : Nat := 118140960795 + 2980642 * 2 ^ 59
def prefixEnd_2980642 : Nat := 4983230072969 + 3 ^ 40 * 2980642 * 2
def baseEnd_2980642 : Nat := 170055778330959162018587

theorem tailTrace_2980642 : CollatzResearch.WordTrace tailWord_2980642 prefixEnd_2980642 170055778330959162018587 := by
  unfold tailWord_2980642
  simp only [CollatzResearch.WordTrace]
  refine ⟨27178236216912640492730045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72475296578433707980613453 27178236216912640492730045)
  ·
    refine ⟨10191838581342240184773767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27178236216912640492730045 10191838581342240184773767)
    ·
      refine ⟨15287757872013360277160651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10191838581342240184773767 15287757872013360277160651)
      ·
        refine ⟨22931636808020040415740977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15287757872013360277160651 22931636808020040415740977)
        ·
          refine ⟨17198727606015030311805733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22931636808020040415740977 17198727606015030311805733)
          ·
            refine ⟨3224761426127818183463575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17198727606015030311805733 3224761426127818183463575)
            ·
              refine ⟨4837142139191727275195363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3224761426127818183463575 4837142139191727275195363)
              ·
                refine ⟨7255713208787590912793045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4837142139191727275195363 7255713208787590912793045)
                ·
                  refine ⟨170055778330959162018587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7255713208787590912793045 170055778330959162018587)
                  ·
                    rfl

theorem cell23_2980642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_2980642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980642 prefixEnd_2980642 := by exact prefixLift 2980642
  have htrace : WordTrace (prefixWord ++ tailWord_2980642) baseStart_2980642 baseEnd_2980642 := by
    simpa [prefixWord, tailWord_2980642, baseEnd_2980642] using wordTrace_append hprefix tailTrace_2980642
  have hstable : (prefixWord ++ tailWord_2980642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980642).length < 2 ^ (prefixWord ++ tailWord_2980642).sum := by decide
  have hdescent : baseEnd_2980642 < baseStart_2980642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980715 : List Nat := [1, 1, 1, 1, 2, 2, 6, 3, 6]
def baseStart_2980715 : Nat := 118140960795 + 2980715 * 2 ^ 59
def prefixEnd_2980715 : Nat := 4983230072969 + 3 ^ 40 * 2980715 * 2
def baseEnd_2980715 : Nat := 170059943229601185839383

theorem tailTrace_2980715 : CollatzResearch.WordTrace tailWord_2980715 prefixEnd_2980715 170059943229601185839383 := by
  unfold tailWord_2980715
  simp only [CollatzResearch.WordTrace]
  refine ⟨108715607396386095438327599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72477071597590730292218399 108715607396386095438327599)
  ·
    refine ⟨163073411094579143157491399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108715607396386095438327599 163073411094579143157491399)
    ·
      refine ⟨244610116641868714736237099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163073411094579143157491399 244610116641868714736237099)
      ·
        refine ⟨366915174962803072104355649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244610116641868714736237099 366915174962803072104355649)
        ·
          refine ⟨275186381222102304078266737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366915174962803072104355649 275186381222102304078266737)
          ·
            refine ⟨206389785916576728058700053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275186381222102304078266737 206389785916576728058700053)
            ·
              refine ⟨9674521214839534127751565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 206389785916576728058700053 9674521214839534127751565)
              ·
                refine ⟨3627945455564825297906837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9674521214839534127751565 3627945455564825297906837)
                ·
                  refine ⟨170059943229601185839383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3627945455564825297906837 170059943229601185839383)
                  ·
                    rfl

theorem cell23_2980715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 6].length) (baseStart_2980715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980715 prefixEnd_2980715 := by exact prefixLift 2980715
  have htrace : WordTrace (prefixWord ++ tailWord_2980715) baseStart_2980715 baseEnd_2980715 := by
    simpa [prefixWord, tailWord_2980715, baseEnd_2980715] using wordTrace_append hprefix tailTrace_2980715
  have hstable : (prefixWord ++ tailWord_2980715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980715).length < 2 ^ (prefixWord ++ tailWord_2980715).sum := by decide
  have hdescent : baseEnd_2980715 < baseStart_2980715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980726 : List Nat := [5, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_2980726 : Nat := 118140960795 + 2980726 * 2 ^ 59
def prefixEnd_2980726 : Nat := 4983230072969 + 3 ^ 40 * 2980726 * 2
def baseEnd_2980726 : Nat := 1530545137353610129516897

theorem tailTrace_2980726 : CollatzResearch.WordTrace tailWord_2980726 prefixEnd_2980726 1530545137353610129516897 := by
  unfold tailWord_2980726
  simp only [CollatzResearch.WordTrace]
  refine ⟨6794750537459140269811127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72477339066230829544652021 6794750537459140269811127)
  ·
    refine ⟨10192125806188710404716691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6794750537459140269811127 10192125806188710404716691)
    ·
      refine ⟨15288188709283065607075037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10192125806188710404716691 15288188709283065607075037)
      ·
        refine ⟨5733070765981149602653139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15288188709283065607075037 5733070765981149602653139)
        ·
          refine ⟨8599606148971724403979709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5733070765981149602653139 8599606148971724403979709)
          ·
            refine ⟨3224852305864396651492391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8599606148971724403979709 3224852305864396651492391)
            ·
              refine ⟨4837278458796594977238587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3224852305864396651492391 4837278458796594977238587)
              ·
                refine ⟨7255917688194892465857881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4837278458796594977238587 7255917688194892465857881)
                ·
                  refine ⟨5441938266146169349393411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7255917688194892465857881 5441938266146169349393411)
                  ·
                    refine ⟨8162907399219254024090117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5441938266146169349393411 8162907399219254024090117)
                    ·
                      refine ⟨1530545137353610129516897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8162907399219254024090117 1530545137353610129516897)
                      ·
                        rfl

theorem cell23_2980726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_2980726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980726 prefixEnd_2980726 := by exact prefixLift 2980726
  have htrace : WordTrace (prefixWord ++ tailWord_2980726) baseStart_2980726 baseEnd_2980726 := by
    simpa [prefixWord, tailWord_2980726, baseEnd_2980726] using wordTrace_append hprefix tailTrace_2980726
  have hstable : (prefixWord ++ tailWord_2980726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980726).length < 2 ^ (prefixWord ++ tailWord_2980726).sum := by decide
  have hdescent : baseEnd_2980726 < baseStart_2980726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980729 : List Nat := [1, 2, 1, 3, 2, 5, 1, 1, 2, 2, 3]
def baseStart_2980729 : Nat := 118140960795 + 2980729 * 2 ^ 59
def prefixEnd_2980729 : Nat := 4983230072969 + 3 ^ 40 * 2980729 * 2
def baseEnd_2980729 : Nat := 1530546677795573617779383

theorem tailTrace_2980729 : CollatzResearch.WordTrace tailWord_2980729 prefixEnd_2980729 1530546677795573617779383 := by
  unfold tailWord_2980729
  simp only [CollatzResearch.WordTrace]
  refine ⟨108716118018335375829337241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72477412012223583886224827 108716118018335375829337241)
  ·
    refine ⟨81537088513751531872002931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108716118018335375829337241 81537088513751531872002931)
    ·
      refine ⟨122305632770627297808004397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81537088513751531872002931 122305632770627297808004397)
      ·
        refine ⟨45864612288985236678001649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122305632770627297808004397 45864612288985236678001649)
        ·
          refine ⟨34398459216738927508501237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45864612288985236678001649 34398459216738927508501237)
          ·
            refine ⟨3224855551569274453921991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34398459216738927508501237 3224855551569274453921991)
            ·
              refine ⟨4837283327353911680882987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3224855551569274453921991 4837283327353911680882987)
              ·
                refine ⟨7255924991030867521324481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4837283327353911680882987 7255924991030867521324481)
                ·
                  refine ⟨5441943743273150640993361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7255924991030867521324481 5441943743273150640993361)
                  ·
                    refine ⟨4081457807454862980745021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5441943743273150640993361 4081457807454862980745021)
                    ·
                      refine ⟨1530546677795573617779383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4081457807454862980745021 1530546677795573617779383)
                      ·
                        rfl

theorem cell23_2980729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_2980729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980729 prefixEnd_2980729 := by exact prefixLift 2980729
  have htrace : WordTrace (prefixWord ++ tailWord_2980729) baseStart_2980729 baseEnd_2980729 := by
    simpa [prefixWord, tailWord_2980729, baseEnd_2980729] using wordTrace_append hprefix tailTrace_2980729
  have hstable : (prefixWord ++ tailWord_2980729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980729).length < 2 ^ (prefixWord ++ tailWord_2980729).sum := by decide
  have hdescent : baseEnd_2980729 < baseStart_2980729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980759 : List Nat := [1, 1, 3, 3, 1, 2, 4, 1, 3, 1, 3]
def baseStart_2980759 : Nat := 118140960795 + 2980759 * 2 ^ 59
def prefixEnd_2980759 : Nat := 4983230072969 + 3 ^ 40 * 2980759 * 2
def baseEnd_2980759 : Nat := 1530562082215208500404245

theorem tailTrace_2980759 : CollatzResearch.WordTrace tailWord_2980759 prefixEnd_2980759 1530562082215208500404245 := by
  unfold tailWord_2980759
  simp only [CollatzResearch.WordTrace]
  refine ⟨108717212208226690952929331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72478141472151127301952887 108717212208226690952929331)
  ·
    refine ⟨163075818312340036429393997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108717212208226690952929331 163075818312340036429393997)
    ·
      refine ⟨61153431867127513661022749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163075818312340036429393997 61153431867127513661022749)
      ·
        refine ⟨22932536950172817622883531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61153431867127513661022749 22932536950172817622883531)
        ·
          refine ⟨34398805425259226434325297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22932536950172817622883531 34398805425259226434325297)
          ·
            refine ⟨25799104068944419825743973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34398805425259226434325297 25799104068944419825743973)
            ·
              refine ⟨4837332012927078717326995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25799104068944419825743973 4837332012927078717326995)
              ·
                refine ⟨7255998019390618075990493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4837332012927078717326995 7255998019390618075990493)
                ·
                  refine ⟨2720999257271481778496435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7255998019390618075990493 2720999257271481778496435)
                  ·
                    refine ⟨4081498885907222667744653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2720999257271481778496435 4081498885907222667744653)
                    ·
                      refine ⟨1530562082215208500404245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4081498885907222667744653 1530562082215208500404245)
                      ·
                        rfl

theorem cell23_2980759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_2980759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980759 prefixEnd_2980759 := by exact prefixLift 2980759
  have htrace : WordTrace (prefixWord ++ tailWord_2980759) baseStart_2980759 baseEnd_2980759 := by
    simpa [prefixWord, tailWord_2980759, baseEnd_2980759] using wordTrace_append hprefix tailTrace_2980759
  have hstable : (prefixWord ++ tailWord_2980759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980759).length < 2 ^ (prefixWord ++ tailWord_2980759).sum := by decide
  have hdescent : baseEnd_2980759 < baseStart_2980759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980769 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 1, 5, 2]
def baseStart_2980769 : Nat := 118140960795 + 2980769 * 2 ^ 59
def prefixEnd_2980769 : Nat := 4983230072969 + 3 ^ 40 * 2980769 * 2
def baseEnd_2980769 : Nat := 1530567217021753461279199

theorem tailTrace_2980769 : CollatzResearch.WordTrace tailWord_2980769 prefixEnd_2980769 1530567217021753461279199 := by
  unfold tailWord_2980769
  simp only [CollatzResearch.WordTrace]
  refine ⟨108717576938190462660793361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72478384625460308440528907 108717576938190462660793361)
  ·
    refine ⟨81538182703642846995595021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108717576938190462660793361 81538182703642846995595021)
    ·
      refine ⟨30576818513866067623348133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81538182703642846995595021 30576818513866067623348133)
      ·
        refine ⟨5733153471349887679377775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30576818513866067623348133 5733153471349887679377775)
        ·
          refine ⟨8599730207024831519066663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5733153471349887679377775 8599730207024831519066663)
          ·
            refine ⟨12899595310537247278599995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8599730207024831519066663 12899595310537247278599995)
            ·
              refine ⟨19349392965805870917899993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12899595310537247278599995 19349392965805870917899993)
              ·
                refine ⟨14512044724354403188424995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19349392965805870917899993 14512044724354403188424995)
                ·
                  refine ⟨21768067086531604782637493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14512044724354403188424995 21768067086531604782637493)
                  ·
                    refine ⟨2040756289362337948372265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21768067086531604782637493 2040756289362337948372265)
                    ·
                      refine ⟨1530567217021753461279199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2040756289362337948372265 1530567217021753461279199)
                      ·
                        rfl

theorem cell23_2980769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_2980769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980769 prefixEnd_2980769 := by exact prefixLift 2980769
  have htrace : WordTrace (prefixWord ++ tailWord_2980769) baseStart_2980769 baseEnd_2980769 := by
    simpa [prefixWord, tailWord_2980769, baseEnd_2980769] using wordTrace_append hprefix tailTrace_2980769
  have hstable : (prefixWord ++ tailWord_2980769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980769).length < 2 ^ (prefixWord ++ tailWord_2980769).sum := by decide
  have hdescent : baseEnd_2980769 < baseStart_2980769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980792 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 4, 4]
def baseStart_2980792 : Nat := 118140960795 + 2980792 * 2 ^ 59
def prefixEnd_2980792 : Nat := 4983230072969 + 3 ^ 40 * 2980792 * 2
def baseEnd_2980792 : Nat := 510193009025602290430531

theorem tailTrace_2980792 : CollatzResearch.WordTrace tailWord_2980792 prefixEnd_2980792 510193009025602290430531 := by
  unfold tailWord_2980792
  simp only [CollatzResearch.WordTrace]
  refine ⟨54359207908553568794440315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72478943878071425059253753 54359207908553568794440315)
  ·
    refine ⟨81538811862830353191660473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54359207908553568794440315 81538811862830353191660473)
    ·
      refine ⟨61154108897122764893745355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81538811862830353191660473 61154108897122764893745355)
      ·
        refine ⟨91731163345684147340618033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61154108897122764893745355 91731163345684147340618033)
        ·
          refine ⟨68798372509263110505463525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91731163345684147340618033 68798372509263110505463525)
          ·
            refine ⟨12899694845486833219774411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68798372509263110505463525 12899694845486833219774411)
            ·
              refine ⟨19349542268230249829661617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12899694845486833219774411 19349542268230249829661617)
              ·
                refine ⟨14512156701172687372246213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19349542268230249829661617 14512156701172687372246213)
                ·
                  refine ⟨2721029381469878882296165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14512156701172687372246213 2721029381469878882296165)
                  ·
                    refine ⟨510193009025602290430531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2721029381469878882296165 510193009025602290430531)
                    ·
                      rfl

theorem cell23_2980792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_2980792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980792 prefixEnd_2980792 := by exact prefixLift 2980792
  have htrace : WordTrace (prefixWord ++ tailWord_2980792) baseStart_2980792 baseEnd_2980792 := by
    simpa [prefixWord, tailWord_2980792, baseEnd_2980792] using wordTrace_append hprefix tailTrace_2980792
  have hstable : (prefixWord ++ tailWord_2980792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980792).length < 2 ^ (prefixWord ++ tailWord_2980792).sum := by decide
  have hdescent : baseEnd_2980792 < baseStart_2980792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980793 : List Nat := [1, 2, 1, 4, 2, 4, 1, 3, 1, 1, 3]
def baseStart_2980793 : Nat := 118140960795 + 2980793 * 2 ^ 59
def prefixEnd_2980793 : Nat := 4983230072969 + 3 ^ 40 * 2980793 * 2
def baseEnd_2980793 : Nat := 1530579540557461367379089

theorem tailTrace_2980793 : CollatzResearch.WordTrace tailWord_2980793 prefixEnd_2980793 1530579540557461367379089 := by
  unfold tailWord_2980793
  simp only [CollatzResearch.WordTrace]
  refine ⟨108718452290103514759667033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72478968193402343173111355 108718452290103514759667033)
  ·
    refine ⟨81538839217577636069750275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108718452290103514759667033 81538839217577636069750275)
    ·
      refine ⟨122308258826366454104625413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81538839217577636069750275 122308258826366454104625413)
      ·
        refine ⟨22932798529943710144617265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122308258826366454104625413 22932798529943710144617265)
        ·
          refine ⟨17199598897457782608462949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22932798529943710144617265 17199598897457782608462949)
          ·
            refine ⟨3224924793273334239086803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17199598897457782608462949 3224924793273334239086803)
            ·
              refine ⟨4837387189910001358630205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3224924793273334239086803 4837387189910001358630205)
              ·
                refine ⟨1814020196216250509486327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4837387189910001358630205 1814020196216250509486327)
                ·
                  refine ⟨2721030294324375764229491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1814020196216250509486327 2721030294324375764229491)
                  ·
                    refine ⟨4081545441486563646344237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2721030294324375764229491 4081545441486563646344237)
                    ·
                      refine ⟨1530579540557461367379089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4081545441486563646344237 1530579540557461367379089)
                      ·
                        rfl

theorem cell23_2980793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_2980793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980793 prefixEnd_2980793 := by exact prefixLift 2980793
  have htrace : WordTrace (prefixWord ++ tailWord_2980793) baseStart_2980793 baseEnd_2980793 := by
    simpa [prefixWord, tailWord_2980793, baseEnd_2980793] using wordTrace_append hprefix tailTrace_2980793
  have hstable : (prefixWord ++ tailWord_2980793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980793).length < 2 ^ (prefixWord ++ tailWord_2980793).sum := by decide
  have hdescent : baseEnd_2980793 < baseStart_2980793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980826 : List Nat := [3, 1, 1, 2, 4, 1, 4, 1, 2, 4]
def baseStart_2980826 : Nat := 118140960795 + 2980826 * 2 ^ 59
def prefixEnd_2980826 : Nat := 4983230072969 + 3 ^ 40 * 2980826 * 2
def baseEnd_2980826 : Nat := 510198828473019912755479

theorem tailTrace_2980826 : CollatzResearch.WordTrace tailWord_2980826 prefixEnd_2980826 510198828473019912755479 := by
  unfold tailWord_2980826
  simp only [CollatzResearch.WordTrace]
  refine ⟨27179913974745990348904583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72479770599322640930412221 27179913974745990348904583)
  ·
    refine ⟨40769870962118985523356875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27179913974745990348904583 40769870962118985523356875)
    ·
      refine ⟨61154806443178478285035313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40769870962118985523356875 61154806443178478285035313)
      ·
        refine ⟨45866104832383858713776485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61154806443178478285035313 45866104832383858713776485)
        ·
          refine ⟨8599894656071973508833091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45866104832383858713776485 8599894656071973508833091)
          ·
            refine ⟨12899841984107960263249637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8599894656071973508833091 12899841984107960263249637)
            ·
              refine ⟨2418720372020242549359307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12899841984107960263249637 2418720372020242549359307)
              ·
                refine ⟨3628080558030363824038961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2418720372020242549359307 3628080558030363824038961)
                ·
                  refine ⟨2721060418522772868029221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3628080558030363824038961 2721060418522772868029221)
                  ·
                    refine ⟨510198828473019912755479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2721060418522772868029221 510198828473019912755479)
                    ·
                      rfl

theorem cell23_2980826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 2, 4].length) (baseStart_2980826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980826 prefixEnd_2980826 := by exact prefixLift 2980826
  have htrace : WordTrace (prefixWord ++ tailWord_2980826) baseStart_2980826 baseEnd_2980826 := by
    simpa [prefixWord, tailWord_2980826, baseEnd_2980826] using wordTrace_append hprefix tailTrace_2980826
  have hstable : (prefixWord ++ tailWord_2980826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980826).length < 2 ^ (prefixWord ++ tailWord_2980826).sum := by decide
  have hdescent : baseEnd_2980826 < baseStart_2980826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980849 : List Nat := [1, 2, 2, 2, 4, 2, 1, 2, 1, 3, 3]
def baseStart_2980849 : Nat := 118140960795 + 2980849 * 2 ^ 59
def prefixEnd_2980849 : Nat := 4983230072969 + 3 ^ 40 * 2980849 * 2
def baseEnd_2980849 : Nat := 1530608295474113148278831

theorem tailTrace_2980849 : CollatzResearch.WordTrace tailWord_2980849 prefixEnd_2980849 1530608295474113148278831 := by
  unfold tailWord_2980849
  simp only [CollatzResearch.WordTrace]
  refine ⟨108720494777900636323705601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72480329851933757549137067 108720494777900636323705601)
  ·
    refine ⟨81540371083425477242779201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108720494777900636323705601 81540371083425477242779201)
    ·
      refine ⟨61155278312569107932084401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81540371083425477242779201 61155278312569107932084401)
      ·
        refine ⟨45866458734426830949063301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61155278312569107932084401 45866458734426830949063301)
        ·
          refine ⟨8599961012705030802949369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45866458734426830949063301 8599961012705030802949369)
          ·
            refine ⟨6449970759528773102212027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8599961012705030802949369 6449970759528773102212027)
            ·
              refine ⟨9674956139293159653318041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6449970759528773102212027 9674956139293159653318041)
              ·
                refine ⟨7256217104469869739988531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9674956139293159653318041 7256217104469869739988531)
                ·
                  refine ⟨10884325656704804609982797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7256217104469869739988531 10884325656704804609982797)
                  ·
                    refine ⟨4081622121264301728743549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10884325656704804609982797 4081622121264301728743549)
                    ·
                      refine ⟨1530608295474113148278831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4081622121264301728743549 1530608295474113148278831)
                      ·
                        rfl

theorem cell23_2980849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_2980849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980849 prefixEnd_2980849 := by exact prefixLift 2980849
  have htrace : WordTrace (prefixWord ++ tailWord_2980849) baseStart_2980849 baseEnd_2980849 := by
    simpa [prefixWord, tailWord_2980849, baseEnd_2980849] using wordTrace_append hprefix tailTrace_2980849
  have hstable : (prefixWord ++ tailWord_2980849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980849).length < 2 ^ (prefixWord ++ tailWord_2980849).sum := by decide
  have hdescent : baseEnd_2980849 < baseStart_2980849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980853 : List Nat := [1, 3, 5, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2980853 : Nat := 118140960795 + 2980853 * 2 ^ 59
def prefixEnd_2980853 : Nat := 4983230072969 + 3 ^ 40 * 2980853 * 2
def baseEnd_2980853 : Nat := 1530610349396731132628813

theorem tailTrace_2980853 : CollatzResearch.WordTrace tailWord_2980853 prefixEnd_2980853 1530610349396731132628813 := by
  unfold tailWord_2980853
  simp only [CollatzResearch.WordTrace]
  refine ⟨108720640669886145006851213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72480427113257430004567475 108720640669886145006851213)
  ·
    refine ⟨40770240251207304377569205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108720640669886145006851213 40770240251207304377569205)
    ·
      refine ⟨3822210023550684785397113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40770240251207304377569205 3822210023550684785397113)
      ·
        refine ⟨2866657517663013589047835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3822210023550684785397113 2866657517663013589047835)
        ·
          refine ⟨4299986276494520383571753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2866657517663013589047835 4299986276494520383571753)
          ·
            refine ⟨3224989707370890287678815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4299986276494520383571753 3224989707370890287678815)
            ·
              refine ⟨4837484561056335431518223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3224989707370890287678815 4837484561056335431518223)
              ·
                refine ⟨7256226841584503147277335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4837484561056335431518223 7256226841584503147277335)
                ·
                  refine ⟨10884340262376754720916003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7256226841584503147277335 10884340262376754720916003)
                  ·
                    refine ⟨16326510393565132081374005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10884340262376754720916003 16326510393565132081374005)
                    ·
                      refine ⟨1530610349396731132628813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16326510393565132081374005 1530610349396731132628813)
                      ·
                        rfl

theorem cell23_2980853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2980853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980853 prefixEnd_2980853 := by exact prefixLift 2980853
  have htrace : WordTrace (prefixWord ++ tailWord_2980853) baseStart_2980853 baseEnd_2980853 := by
    simpa [prefixWord, tailWord_2980853, baseEnd_2980853] using wordTrace_append hprefix tailTrace_2980853
  have hstable : (prefixWord ++ tailWord_2980853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980853).length < 2 ^ (prefixWord ++ tailWord_2980853).sum := by decide
  have hdescent : baseEnd_2980853 < baseStart_2980853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980872 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_2980872 : Nat := 118140960795 + 2980872 * 2 ^ 59
def prefixEnd_2980872 : Nat := 4983230072969 + 3 ^ 40 * 2980872 * 2
def baseEnd_2980872 : Nat := 1530620105529166558291225

theorem tailTrace_2980872 : CollatzResearch.WordTrace tailWord_2980872 prefixEnd_2980872 1530620105529166558291225 := by
  unfold tailWord_2980872
  simp only [CollatzResearch.WordTrace]
  refine ⟨54360666828408655625896435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72480889104544874167861913 54360666828408655625896435)
  ·
    refine ⟨81541000242612983438844653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54360666828408655625896435 81541000242612983438844653)
    ·
      refine ⟨30577875090979868789566745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81541000242612983438844653 30577875090979868789566745)
      ·
        refine ⟨22933406318234901592175059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30577875090979868789566745 22933406318234901592175059)
        ·
          refine ⟨34400109477352352388262589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22933406318234901592175059 34400109477352352388262589)
          ·
            refine ⟨12900041054007132145598471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34400109477352352388262589 12900041054007132145598471)
            ·
              refine ⟨19350061581010698218397707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12900041054007132145598471 19350061581010698218397707)
              ·
                refine ⟨29025092371516047327596561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19350061581010698218397707 29025092371516047327596561)
                ·
                  refine ⟨21768819278637035495697421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29025092371516047327596561 21768819278637035495697421)
                  ·
                    refine ⟨8163307229488888310886533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21768819278637035495697421 8163307229488888310886533)
                    ·
                      refine ⟨1530620105529166558291225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8163307229488888310886533 1530620105529166558291225)
                      ·
                        rfl

theorem cell23_2980872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_2980872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980872 prefixEnd_2980872 := by exact prefixLift 2980872
  have htrace : WordTrace (prefixWord ++ tailWord_2980872) baseStart_2980872 baseEnd_2980872 := by
    simpa [prefixWord, tailWord_2980872, baseEnd_2980872] using wordTrace_append hprefix tailTrace_2980872
  have hstable : (prefixWord ++ tailWord_2980872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980872).length < 2 ^ (prefixWord ++ tailWord_2980872).sum := by decide
  have hdescent : baseEnd_2980872 < baseStart_2980872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980889 : List Nat := [1, 2, 1, 2, 1, 1, 5, 3, 1, 4, 2]
def baseStart_2980889 : Nat := 118140960795 + 2980889 * 2 ^ 59
def prefixEnd_2980889 : Nat := 4983230072969 + 3 ^ 40 * 2980889 * 2
def baseEnd_2980889 : Nat := 1530628834700292991778647

theorem tailTrace_2980889 : CollatzResearch.WordTrace tailWord_2980889 prefixEnd_2980889 1530628834700292991778647 := by
  unfold tailWord_2980889
  simp only [CollatzResearch.WordTrace]
  refine ⟨108721953697755723155161721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72481302465170482103441147 108721953697755723155161721)
  ·
    refine ⟨81541465273316792366371291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108721953697755723155161721 81541465273316792366371291)
    ·
      refine ⟨122312197909975188549556937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81541465273316792366371291 122312197909975188549556937)
      ·
        refine ⟨91734148432481391412167703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122312197909975188549556937 91734148432481391412167703)
        ·
          refine ⟨137601222648722087118251555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91734148432481391412167703 137601222648722087118251555)
          ·
            refine ⟨206401833973083130677377333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137601222648722087118251555 206401833973083130677377333)
            ·
              refine ⟨19350171934976543501004125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 206401833973083130677377333 19350171934976543501004125)
              ·
                refine ⟨7256314475616203812876547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19350171934976543501004125 7256314475616203812876547)
                ·
                  refine ⟨10884471713424305719314821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7256314475616203812876547 10884471713424305719314821)
                  ·
                    refine ⟨2040838446267057322371529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10884471713424305719314821 2040838446267057322371529)
                    ·
                      refine ⟨1530628834700292991778647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2040838446267057322371529 1530628834700292991778647)
                      ·
                        rfl

theorem cell23_2980889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 4, 2].length) (baseStart_2980889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980889 prefixEnd_2980889 := by exact prefixLift 2980889
  have htrace : WordTrace (prefixWord ++ tailWord_2980889) baseStart_2980889 baseEnd_2980889 := by
    simpa [prefixWord, tailWord_2980889, baseEnd_2980889] using wordTrace_append hprefix tailTrace_2980889
  have hstable : (prefixWord ++ tailWord_2980889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980889).length < 2 ^ (prefixWord ++ tailWord_2980889).sum := by decide
  have hdescent : baseEnd_2980889 < baseStart_2980889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980942 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 3, 7]
def baseStart_2980942 : Nat := 118140960795 + 2980942 * 2 ^ 59
def prefixEnd_2980942 : Nat := 4983230072969 + 3 ^ 40 * 2980942 * 2
def baseEnd_2980942 : Nat := 510218683058327094805301

theorem tailTrace_2980942 : CollatzResearch.WordTrace tailWord_2980942 prefixEnd_2980942 510218683058327094805301 := by
  unfold tailWord_2980942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13590485845820464150855135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72482591177709142137894053 13590485845820464150855135)
  ·
    refine ⟨20385728768730696226282703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13590485845820464150855135 20385728768730696226282703)
    ·
      refine ⟨30578593153096044339424055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20385728768730696226282703 30578593153096044339424055)
      ·
        refine ⟨45867889729644066509136083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30578593153096044339424055 45867889729644066509136083)
        ·
          refine ⟨68801834594466099763704125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45867889729644066509136083 68801834594466099763704125)
          ·
            refine ⟨25800687972924787411389047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68801834594466099763704125 25800687972924787411389047)
            ·
              refine ⟨38701031959387181117083571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25800687972924787411389047 38701031959387181117083571)
              ·
                refine ⟨58051547939080771675625357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38701031959387181117083571 58051547939080771675625357)
                ·
                  refine ⟨21769330477155289378359509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58051547939080771675625357 21769330477155289378359509)
                  ·
                    refine ⟨510218683058327094805301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21769330477155289378359509 510218683058327094805301)
                    ·
                      rfl

theorem cell23_2980942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_2980942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980942 prefixEnd_2980942 := by exact prefixLift 2980942
  have htrace : WordTrace (prefixWord ++ tailWord_2980942) baseStart_2980942 baseEnd_2980942 := by
    simpa [prefixWord, tailWord_2980942, baseEnd_2980942] using wordTrace_append hprefix tailTrace_2980942
  have hstable : (prefixWord ++ tailWord_2980942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980942).length < 2 ^ (prefixWord ++ tailWord_2980942).sum := by decide
  have hdescent : baseEnd_2980942 < baseStart_2980942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980992 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 6]
def baseStart_2980992 : Nat := 118140960795 + 2980992 * 2 ^ 59
def prefixEnd_2980992 : Nat := 4983230072969 + 3 ^ 40 * 2980992 * 2
def baseEnd_2980992 : Nat := 1530681723207706088790673

theorem tailTrace_2980992 : CollatzResearch.WordTrace tailWord_2980992 prefixEnd_2980992 1530681723207706088790673 := by
  unfold tailWord_2980992
  simp only [CollatzResearch.WordTrace]
  refine ⟨54362855208191285873080615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72483806944255047830774153 54362855208191285873080615)
  ·
    refine ⟨81544282812286928809620923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54362855208191285873080615 81544282812286928809620923)
    ·
      refine ⟨122316424218430393214431385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81544282812286928809620923 122316424218430393214431385)
      ·
        refine ⟨91737318163822794910823539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122316424218430393214431385 91737318163822794910823539)
        ·
          refine ⟨137605977245734192366235309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91737318163822794910823539 137605977245734192366235309)
          ·
            refine ⟨51602241467150322137338241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137605977245734192366235309 51602241467150322137338241)
            ·
              refine ⟨38701681100362741603003681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51602241467150322137338241 38701681100362741603003681)
              ·
                refine ⟨29026260825272056202252761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38701681100362741603003681 29026260825272056202252761)
                ·
                  refine ⟨21769695618954042151689571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29026260825272056202252761 21769695618954042151689571)
                  ·
                    refine ⟨32654543428431063227534357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21769695618954042151689571 32654543428431063227534357)
                    ·
                      refine ⟨1530681723207706088790673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32654543428431063227534357 1530681723207706088790673)
                      ·
                        rfl

theorem cell23_2980992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_2980992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980992 prefixEnd_2980992 := by exact prefixLift 2980992
  have htrace : WordTrace (prefixWord ++ tailWord_2980992) baseStart_2980992 baseEnd_2980992 := by
    simpa [prefixWord, tailWord_2980992, baseEnd_2980992] using wordTrace_append hprefix tailTrace_2980992
  have hstable : (prefixWord ++ tailWord_2980992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980992).length < 2 ^ (prefixWord ++ tailWord_2980992).sum := by decide
  have hdescent : baseEnd_2980992 < baseStart_2980992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980999 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 3]
def baseStart_2980999 : Nat := 118140960795 + 2980999 * 2 ^ 59
def prefixEnd_2980999 : Nat := 4983230072969 + 3 ^ 40 * 2980999 * 2
def baseEnd_2980999 : Nat := 1530685317572287561403141

theorem tailTrace_2980999 : CollatzResearch.WordTrace tailWord_2980999 prefixEnd_2980999 1530685317572287561403141 := by
  unfold tailWord_2980999
  simp only [CollatzResearch.WordTrace]
  refine ⟨108725965727357211941666051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72483977151571474627777367 108725965727357211941666051)
  ·
    refine ⟨163088948591035817912499077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108725965727357211941666051 163088948591035817912499077)
    ·
      refine ⟨30579177860819215858593577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163088948591035817912499077 30579177860819215858593577)
      ·
        refine ⟨22934383395614411893945183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30579177860819215858593577 22934383395614411893945183)
        ·
          refine ⟨34401575093421617840917775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22934383395614411893945183 34401575093421617840917775)
          ·
            refine ⟨51602362640132426761376663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34401575093421617840917775 51602362640132426761376663)
            ·
              refine ⟨77403543960198640142064995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51602362640132426761376663 77403543960198640142064995)
              ·
                refine ⟨116105315940297960213097493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77403543960198640142064995 116105315940297960213097493)
                ·
                  refine ⟨5442436684701466884988945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116105315940297960213097493 5442436684701466884988945)
                  ·
                    refine ⟨4081827513526100163741709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5442436684701466884988945 4081827513526100163741709)
                    ·
                      refine ⟨1530685317572287561403141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4081827513526100163741709 1530685317572287561403141)
                      ·
                        rfl

theorem cell23_2980999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_2980999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2980999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2980999 prefixEnd_2980999 := by exact prefixLift 2980999
  have htrace : WordTrace (prefixWord ++ tailWord_2980999) baseStart_2980999 baseEnd_2980999 := by
    simpa [prefixWord, tailWord_2980999, baseEnd_2980999] using wordTrace_append hprefix tailTrace_2980999
  have hstable : (prefixWord ++ tailWord_2980999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980999).length < 2 ^ (prefixWord ++ tailWord_2980999).sum := by decide
  have hdescent : baseEnd_2980999 < baseStart_2980999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981016 : List Nat := [2, 1, 2, 4, 2, 1, 1, 3, 2, 2, 3]
def baseStart_2981016 : Nat := 118140960795 + 2981016 * 2 ^ 59
def prefixEnd_2981016 : Nat := 4983230072969 + 3 ^ 40 * 2981016 * 2
def baseEnd_2981016 : Nat := 1530694046743413994890563

theorem tailTrace_2981016 : CollatzResearch.WordTrace tailWord_2981016 prefixEnd_2981016 1530694046743413994890563 := by
  unfold tailWord_2981016
  simp only [CollatzResearch.WordTrace]
  refine ⟨54363292884147811922517451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72484390512197082563356601 54363292884147811922517451)
  ·
    refine ⟨81544939326221717883776177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54363292884147811922517451 81544939326221717883776177)
    ·
      refine ⟨61158704494666288412832133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81544939326221717883776177 61158704494666288412832133)
      ·
        refine ⟨11467257092749929077406025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61158704494666288412832133 11467257092749929077406025)
        ·
          refine ⟨8600442819562446808054519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11467257092749929077406025 8600442819562446808054519)
          ·
            refine ⟨12900664229343670212081779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8600442819562446808054519 12900664229343670212081779)
            ·
              refine ⟨19350996344015505318122669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12900664229343670212081779 19350996344015505318122669)
              ·
                refine ⟨7256623629005814494296001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19350996344015505318122669 7256623629005814494296001)
                ·
                  refine ⟨5442467721754360870722001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7256623629005814494296001 5442467721754360870722001)
                  ·
                    refine ⟨4081850791315770653041501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5442467721754360870722001 4081850791315770653041501)
                    ·
                      refine ⟨1530694046743413994890563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4081850791315770653041501 1530694046743413994890563)
                      ·
                        rfl

theorem cell23_2981016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_2981016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981016 prefixEnd_2981016 := by exact prefixLift 2981016
  have htrace : WordTrace (prefixWord ++ tailWord_2981016) baseStart_2981016 baseEnd_2981016 := by
    simpa [prefixWord, tailWord_2981016, baseEnd_2981016] using wordTrace_append hprefix tailTrace_2981016
  have hstable : (prefixWord ++ tailWord_2981016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981016).length < 2 ^ (prefixWord ++ tailWord_2981016).sum := by decide
  have hdescent : baseEnd_2981016 < baseStart_2981016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981049 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 3, 5]
def baseStart_2981049 : Nat := 118140960795 + 2981049 * 2 ^ 59
def prefixEnd_2981049 : Nat := 4983230072969 + 3 ^ 40 * 2981049 * 2
def baseEnd_2981049 : Nat := 510236997201670788592637

theorem tailTrace_2981049 : CollatzResearch.WordTrace tailWord_2981049 prefixEnd_2981049 510236997201670788592637 := by
  unfold tailWord_2981049
  simp only [CollatzResearch.WordTrace]
  refine ⟨108727789377176070480986201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72485192918117380320657467 108727789377176070480986201)
  ·
    refine ⟨81545842032882052860739651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108727789377176070480986201 81545842032882052860739651)
    ·
      refine ⟨122318763049323079291109477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81545842032882052860739651 122318763049323079291109477)
      ·
        refine ⟨22934768071748077367083027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122318763049323079291109477 22934768071748077367083027)
        ·
          refine ⟨34402152107622116050624541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22934768071748077367083027 34402152107622116050624541)
          ·
            refine ⟨12900807040358293518984203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34402152107622116050624541 12900807040358293518984203)
            ·
              refine ⟨19351210560537440278476305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12900807040358293518984203 19351210560537440278476305)
              ·
                refine ⟨14513407920403080208857229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19351210560537440278476305 14513407920403080208857229)
                ·
                  refine ⟨5442527970151155078321461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14513407920403080208857229 5442527970151155078321461)
                  ·
                    refine ⟨510236997201670788592637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5442527970151155078321461 510236997201670788592637)
                    ·
                      rfl

theorem cell23_2981049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 5].length) (baseStart_2981049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981049 prefixEnd_2981049 := by exact prefixLift 2981049
  have htrace : WordTrace (prefixWord ++ tailWord_2981049) baseStart_2981049 baseEnd_2981049 := by
    simpa [prefixWord, tailWord_2981049, baseEnd_2981049] using wordTrace_append hprefix tailTrace_2981049
  have hstable : (prefixWord ++ tailWord_2981049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981049).length < 2 ^ (prefixWord ++ tailWord_2981049).sum := by decide
  have hdescent : baseEnd_2981049 < baseStart_2981049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981079 : List Nat := [1, 1, 3, 2, 1, 2, 4, 2, 1, 6]
def baseStart_2981079 : Nat := 118140960795 + 2981079 * 2 ^ 59
def prefixEnd_2981079 : Nat := 4983230072969 + 3 ^ 40 * 2981079 * 2
def baseEnd_2981079 : Nat := 510242132008215749467591

theorem tailTrace_2981079 : CollatzResearch.WordTrace tailWord_2981079 prefixEnd_2981079 510242132008215749467591 := by
  unfold tailWord_2981079
  simp only [CollatzResearch.WordTrace]
  refine ⟨108728883567067385604578291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72485922378044923736385527 108728883567067385604578291)
  ·
    refine ⟨163093325350601078406867437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108728883567067385604578291 163093325350601078406867437)
    ·
      refine ⟨61159997006475404402575289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163093325350601078406867437 61159997006475404402575289)
      ·
        refine ⟨45869997754856553301931467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61159997006475404402575289 45869997754856553301931467)
        ·
          refine ⟨68804996632284829952897201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45869997754856553301931467 68804996632284829952897201)
          ·
            refine ⟨51603747474213622464672901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68804996632284829952897201 51603747474213622464672901)
            ·
              refine ⟨9675702651415054212126169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51603747474213622464672901 9675702651415054212126169)
              ·
                refine ⟨7256776988561290659094627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9675702651415054212126169 7256776988561290659094627)
                ·
                  refine ⟨10885165482841935988641941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7256776988561290659094627 10885165482841935988641941)
                  ·
                    refine ⟨510242132008215749467591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10885165482841935988641941 510242132008215749467591)
                    ·
                      rfl

theorem cell23_2981079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_2981079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981079 prefixEnd_2981079 := by exact prefixLift 2981079
  have htrace : WordTrace (prefixWord ++ tailWord_2981079) baseStart_2981079 baseEnd_2981079 := by
    simpa [prefixWord, tailWord_2981079, baseEnd_2981079] using wordTrace_append hprefix tailTrace_2981079
  have hstable : (prefixWord ++ tailWord_2981079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981079).length < 2 ^ (prefixWord ++ tailWord_2981079).sum := by decide
  have hdescent : baseEnd_2981079 < baseStart_2981079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981096 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 4, 4]
def baseStart_2981096 : Nat := 118140960795 + 2981096 * 2 ^ 59
def prefixEnd_2981096 : Nat := 4983230072969 + 3 ^ 40 * 2981096 * 2
def baseEnd_2981096 : Nat := 510245041731924560630065

theorem tailTrace_2981096 : CollatzResearch.WordTrace tailWord_2981096 prefixEnd_2981096 510245041731924560630065 := by
  unfold tailWord_2981096
  simp only [CollatzResearch.WordTrace]
  refine ⟨54364751804002898753973571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72486335738670531671964761 54364751804002898753973571)
  ·
    refine ⟨81547127706004348130960357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54364751804002898753973571 81547127706004348130960357)
    ·
      refine ⟨15290086444875815274555067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81547127706004348130960357 15290086444875815274555067)
      ·
        refine ⟨22935129667313722911832601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15290086444875815274555067 22935129667313722911832601)
        ·
          refine ⟨17201347250485292183874451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22935129667313722911832601 17201347250485292183874451)
          ·
            refine ⟨25802020875727938275811677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17201347250485292183874451 25802020875727938275811677)
            ·
              refine ⟨9675757828397976853429379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25802020875727938275811677 9675757828397976853429379)
              ·
                refine ⟨14513636742596965280144069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9675757828397976853429379 14513636742596965280144069)
                ·
                  refine ⟨2721306889236930990027013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14513636742596965280144069 2721306889236930990027013)
                  ·
                    refine ⟨510245041731924560630065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2721306889236930990027013 510245041731924560630065)
                    ·
                      rfl

theorem cell23_2981096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_2981096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981096 prefixEnd_2981096 := by exact prefixLift 2981096
  have htrace : WordTrace (prefixWord ++ tailWord_2981096) baseStart_2981096 baseEnd_2981096 := by
    simpa [prefixWord, tailWord_2981096, baseEnd_2981096] using wordTrace_append hprefix tailTrace_2981096
  have hstable : (prefixWord ++ tailWord_2981096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981096).length < 2 ^ (prefixWord ++ tailWord_2981096).sum := by decide
  have hdescent : baseEnd_2981096 < baseStart_2981096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981113 : List Nat := [1, 2, 1, 3, 1, 1, 7, 1, 2, 4]
def baseStart_2981113 : Nat := 118140960795 + 2981113 * 2 ^ 59
def prefixEnd_2981113 : Nat := 4983230072969 + 3 ^ 40 * 2981113 * 2
def baseEnd_2981113 : Nat := 510247951455633371792539

theorem tailTrace_2981113 : CollatzResearch.WordTrace tailWord_2981113 prefixEnd_2981113 510247951455633371792539 := by
  unfold tailWord_2981113
  simp only [CollatzResearch.WordTrace]
  refine ⟨108730123648944209411315993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72486749099296139607543995 108730123648944209411315993)
  ·
    refine ⟨81547592736708157058486995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108730123648944209411315993 81547592736708157058486995)
    ·
      refine ⟨122321389105062235587730493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81547592736708157058486995 122321389105062235587730493)
      ·
        refine ⟨45870520914398338345398935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122321389105062235587730493 45870520914398338345398935)
        ·
          refine ⟨68805781371597507518098403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45870520914398338345398935 68805781371597507518098403)
          ·
            refine ⟨103208672057396261277147605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68805781371597507518098403 103208672057396261277147605)
            ·
              refine ⟨2418953251345224873683147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 103208672057396261277147605 2418953251345224873683147)
              ·
                refine ⟨3628429877017837310524721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2418953251345224873683147 3628429877017837310524721)
                ·
                  refine ⟨2721322407763377982893541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3628429877017837310524721 2721322407763377982893541)
                  ·
                    refine ⟨510247951455633371792539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2721322407763377982893541 510247951455633371792539)
                    ·
                      rfl

theorem cell23_2981113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 2, 4].length) (baseStart_2981113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981113 prefixEnd_2981113 := by exact prefixLift 2981113
  have htrace : WordTrace (prefixWord ++ tailWord_2981113) baseStart_2981113 baseEnd_2981113 := by
    simpa [prefixWord, tailWord_2981113, baseEnd_2981113] using wordTrace_append hprefix tailTrace_2981113
  have hstable : (prefixWord ++ tailWord_2981113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981113).length < 2 ^ (prefixWord ++ tailWord_2981113).sum := by decide
  have hdescent : baseEnd_2981113 < baseStart_2981113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981116 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 1, 1, 6]
def baseStart_2981116 : Nat := 118140960795 + 2981116 * 2 ^ 59
def prefixEnd_2981116 : Nat := 4983230072969 + 3 ^ 40 * 2981116 * 2
def baseEnd_2981116 : Nat := 1530745394808863603640103

theorem tailTrace_2981116 : CollatzResearch.WordTrace tailWord_2981116 prefixEnd_2981116 1530745394808863603640103 := by
  unfold tailWord_2981116
  simp only [CollatzResearch.WordTrace]
  refine ⟨54365116533966670461837601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72486822045288893949116801 54365116533966670461837601)
  ·
    refine ⟨40773837400475002846378201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54365116533966670461837601 40773837400475002846378201)
    ·
      refine ⟨30580378050356252134783651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40773837400475002846378201 30580378050356252134783651)
      ·
        refine ⟨45870567075534378202175477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30580378050356252134783651 45870567075534378202175477)
        ·
          refine ⟨4300365663331347956453951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45870567075534378202175477 4300365663331347956453951)
          ·
            refine ⟨6450548494997021934680927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4300365663331347956453951 6450548494997021934680927)
            ·
              refine ⟨9675822742495532902021391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6450548494997021934680927 9675822742495532902021391)
              ·
                refine ⟨14513734113743299353032087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9675822742495532902021391 14513734113743299353032087)
                ·
                  refine ⟨21770601170614949029548131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14513734113743299353032087 21770601170614949029548131)
                  ·
                    refine ⟨32655901755922423544322197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21770601170614949029548131 32655901755922423544322197)
                    ·
                      refine ⟨1530745394808863603640103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32655901755922423544322197 1530745394808863603640103)
                      ·
                        rfl

theorem cell23_2981116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_2981116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981116 prefixEnd_2981116 := by exact prefixLift 2981116
  have htrace : WordTrace (prefixWord ++ tailWord_2981116) baseStart_2981116 baseEnd_2981116 := by
    simpa [prefixWord, tailWord_2981116, baseEnd_2981116] using wordTrace_append hprefix tailTrace_2981116
  have hstable : (prefixWord ++ tailWord_2981116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981116).length < 2 ^ (prefixWord ++ tailWord_2981116).sum := by decide
  have hdescent : baseEnd_2981116 < baseStart_2981116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981123 : List Nat := [1, 1, 1, 3, 2, 5, 2, 2, 1, 2, 3]
def baseStart_2981123 : Nat := 118140960795 + 2981123 * 2 ^ 59
def prefixEnd_2981123 : Nat := 4983230072969 + 3 ^ 40 * 2981123 * 2
def baseEnd_2981123 : Nat := 1530748989173445076252571

theorem tailTrace_2981123 : CollatzResearch.WordTrace tailWord_2981123 prefixEnd_2981123 1530748989173445076252571 := by
  unfold tailWord_2981123
  simp only [CollatzResearch.WordTrace]
  refine ⟨108730488378907981119180023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72486992252605320746120015 108730488378907981119180023)
  ·
    refine ⟨163095732568361971678770035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108730488378907981119180023 163095732568361971678770035)
    ·
      refine ⟨244643598852542957518155053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163095732568361971678770035 244643598852542957518155053)
      ·
        refine ⟨91741349569703609069308145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244643598852542957518155053 91741349569703609069308145)
        ·
          refine ⟨68806012177277706801981109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91741349569703609069308145 68806012177277706801981109)
          ·
            refine ⟨6450563641619785012685729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68806012177277706801981109 6450563641619785012685729)
            ·
              refine ⟨4837922731214838759514297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6450563641619785012685729 4837922731214838759514297)
              ·
                refine ⟨3628442048411129069635723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4837922731214838759514297 3628442048411129069635723)
                ·
                  refine ⟨5442663072616693604453585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3628442048411129069635723 5442663072616693604453585)
                  ·
                    refine ⟨4081997304462520203340189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5442663072616693604453585 4081997304462520203340189)
                    ·
                      refine ⟨1530748989173445076252571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4081997304462520203340189 1530748989173445076252571)
                      ·
                        rfl

theorem cell23_2981123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 2, 3].length) (baseStart_2981123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981123 prefixEnd_2981123 := by exact prefixLift 2981123
  have htrace : WordTrace (prefixWord ++ tailWord_2981123) baseStart_2981123 baseEnd_2981123 := by
    simpa [prefixWord, tailWord_2981123, baseEnd_2981123] using wordTrace_append hprefix tailTrace_2981123
  have hstable : (prefixWord ++ tailWord_2981123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981123).length < 2 ^ (prefixWord ++ tailWord_2981123).sum := by decide
  have hdescent : baseEnd_2981123 < baseStart_2981123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981153 : List Nat := [1, 2, 3, 2, 1, 1, 1, 6, 2, 1, 3]
def baseStart_2981153 : Nat := 118140960795 + 2981153 * 2 ^ 59
def prefixEnd_2981153 : Nat := 4983230072969 + 3 ^ 40 * 2981153 * 2
def baseEnd_2981153 : Nat := 1530764393593079958877433

theorem tailTrace_2981153 : CollatzResearch.WordTrace tailWord_2981153 prefixEnd_2981153 1530764393593079958877433 := by
  unfold tailWord_2981153
  simp only [CollatzResearch.WordTrace]
  refine ⟨108731582568799296242772113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72487721712532864161848075 108731582568799296242772113)
  ·
    refine ⟨81548686926599472182079085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108731582568799296242772113 81548686926599472182079085)
    ·
      refine ⟨30580757597474802068279657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81548686926599472182079085 30580757597474802068279657)
      ·
        refine ⟨22935568198106101551209743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30580757597474802068279657 22935568198106101551209743)
        ·
          refine ⟨34403352297159152326814615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22935568198106101551209743 34403352297159152326814615)
          ·
            refine ⟨51605028445738728490221923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34403352297159152326814615 51605028445738728490221923)
            ·
              refine ⟨77407542668608092735332885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51605028445738728490221923 77407542668608092735332885)
              ·
                refine ⟨3628478562591004346968729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77407542668608092735332885 3628478562591004346968729)
                ·
                  refine ⟨2721358921943253260226547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3628478562591004346968729 2721358921943253260226547)
                  ·
                    refine ⟨4082038382914879890339821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2721358921943253260226547 4082038382914879890339821)
                    ·
                      refine ⟨1530764393593079958877433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4082038382914879890339821 1530764393593079958877433)
                      ·
                        rfl

theorem cell23_2981153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_2981153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981153 prefixEnd_2981153 := by exact prefixLift 2981153
  have htrace : WordTrace (prefixWord ++ tailWord_2981153) baseStart_2981153 baseEnd_2981153 := by
    simpa [prefixWord, tailWord_2981153, baseEnd_2981153] using wordTrace_append hprefix tailTrace_2981153
  have hstable : (prefixWord ++ tailWord_2981153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981153).length < 2 ^ (prefixWord ++ tailWord_2981153).sum := by decide
  have hdescent : baseEnd_2981153 < baseStart_2981153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981154 : List Nat := [3, 3, 1, 1, 5, 1, 1, 1, 3, 2, 2]
def baseStart_2981154 : Nat := 118140960795 + 2981154 * 2 ^ 59
def prefixEnd_2981154 : Nat := 4983230072969 + 3 ^ 40 * 2981154 * 2
def baseEnd_2981154 : Nat := 1530764907073734454964929

theorem tailTrace_2981154 : CollatzResearch.WordTrace tailWord_2981154 prefixEnd_2981154 1530764907073734454964929 := by
  unfold tailWord_2981154
  simp only [CollatzResearch.WordTrace]
  refine ⟨27182904760448918353389629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72487746027863782275705677 27182904760448918353389629)
  ·
    refine ⟨10193589285168344382521111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27182904760448918353389629 10193589285168344382521111)
    ·
      refine ⟨15290383927752516573781667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10193589285168344382521111 15290383927752516573781667)
      ·
        refine ⟨22935575891628774860672501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15290383927752516573781667 22935575891628774860672501)
        ·
          refine ⟨2150210239840197643188047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22935575891628774860672501 2150210239840197643188047)
          ·
            refine ⟨3225315359760296464782071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150210239840197643188047 3225315359760296464782071)
            ·
              refine ⟨4837973039640444697173107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3225315359760296464782071 4837973039640444697173107)
              ·
                refine ⟨7256959559460667045759661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4837973039640444697173107 7256959559460667045759661)
                ·
                  refine ⟨2721359834797750142159873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7256959559460667045759661 2721359834797750142159873)
                  ·
                    refine ⟨2041019876098312606619905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2721359834797750142159873 2041019876098312606619905)
                    ·
                      refine ⟨1530764907073734454964929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2041019876098312606619905 1530764907073734454964929)
                      ·
                        rfl

theorem cell23_2981154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_2981154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981154 prefixEnd_2981154 := by exact prefixLift 2981154
  have htrace : WordTrace (prefixWord ++ tailWord_2981154) baseStart_2981154 baseEnd_2981154 := by
    simpa [prefixWord, tailWord_2981154, baseEnd_2981154] using wordTrace_append hprefix tailTrace_2981154
  have hstable : (prefixWord ++ tailWord_2981154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981154).length < 2 ^ (prefixWord ++ tailWord_2981154).sum := by decide
  have hdescent : baseEnd_2981154 < baseStart_2981154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981170 : List Nat := [3, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3]
def baseStart_2981170 : Nat := 118140960795 + 2981170 * 2 ^ 59
def prefixEnd_2981170 : Nat := 4983230072969 + 3 ^ 40 * 2981170 * 2
def baseEnd_2981170 : Nat := 1530773122764206392364855

theorem tailTrace_2981170 : CollatzResearch.WordTrace tailWord_2981170 prefixEnd_2981170 1530773122764206392364855 := by
  unfold tailWord_2981170
  simp only [CollatzResearch.WordTrace]
  refine ⟨27183050652434427036535241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72488135073158472097427309 27183050652434427036535241)
  ·
    refine ⟨20387287989325820277401431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27183050652434427036535241 20387287989325820277401431)
    ·
      refine ⟨30580931983988730416102147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20387287989325820277401431 30580931983988730416102147)
      ·
        refine ⟨45871397975983095624153221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30580931983988730416102147 45871397975983095624153221)
        ·
          refine ⟨8600887120496830429528729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45871397975983095624153221 8600887120496830429528729)
          ·
            refine ⟨6450665340372622822146547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8600887120496830429528729 6450665340372622822146547)
            ·
              refine ⟨9675998010558934233219821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6450665340372622822146547 9675998010558934233219821)
              ·
                refine ⟨3628499253959600337457433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9675998010558934233219821 3628499253959600337457433)
                ·
                  refine ⟨2721374440469700253093075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3628499253959600337457433 2721374440469700253093075)
                  ·
                    refine ⟨4082061660704550379639613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2721374440469700253093075 4082061660704550379639613)
                    ·
                      refine ⟨1530773122764206392364855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4082061660704550379639613 1530773122764206392364855)
                      ·
                        rfl

theorem cell23_2981170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_2981170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981170 prefixEnd_2981170 := by exact prefixLift 2981170
  have htrace : WordTrace (prefixWord ++ tailWord_2981170) baseStart_2981170 baseEnd_2981170 := by
    simpa [prefixWord, tailWord_2981170, baseEnd_2981170] using wordTrace_append hprefix tailTrace_2981170
  have hstable : (prefixWord ++ tailWord_2981170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981170).length < 2 ^ (prefixWord ++ tailWord_2981170).sum := by decide
  have hdescent : baseEnd_2981170 < baseStart_2981170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981174 : List Nat := [5, 1, 2, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_2981174 : Nat := 118140960795 + 2981174 * 2 ^ 59
def prefixEnd_2981174 : Nat := 4983230072969 + 3 ^ 40 * 2981174 * 2
def baseEnd_2981174 : Nat := 1530775176686824376714837

theorem tailTrace_2981174 : CollatzResearch.WordTrace tailWord_2981174 prefixEnd_2981174 1530775176686824376714837 := by
  unfold tailWord_2981174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6795771781357701051830411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72488232334482144552857717 6795771781357701051830411)
  ·
    refine ⟨10193657672036551577745617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6795771781357701051830411 10193657672036551577745617)
    ·
      refine ⟨7645243254027413683309213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10193657672036551577745617 7645243254027413683309213)
      ·
        refine ⟨2866966220260280131240955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7645243254027413683309213 2866966220260280131240955)
        ·
          refine ⟨4300449330390420196861433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2866966220260280131240955 4300449330390420196861433)
          ·
            refine ⟨3225336997792815147646075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4300449330390420196861433 3225336997792815147646075)
            ·
              refine ⟨4838005496689222721469113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3225336997792815147646075 4838005496689222721469113)
              ·
                refine ⟨3628504122516917041101835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4838005496689222721469113 3628504122516917041101835)
                ·
                  refine ⟨5442756183775375561652753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3628504122516917041101835 5442756183775375561652753)
                  ·
                    refine ⟨4082067137831531671239565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5442756183775375561652753 4082067137831531671239565)
                    ·
                      refine ⟨1530775176686824376714837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4082067137831531671239565 1530775176686824376714837)
                      ·
                        rfl

theorem cell23_2981174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_2981174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981174 prefixEnd_2981174 := by exact prefixLift 2981174
  have htrace : WordTrace (prefixWord ++ tailWord_2981174) baseStart_2981174 baseEnd_2981174 := by
    simpa [prefixWord, tailWord_2981174, baseEnd_2981174] using wordTrace_append hprefix tailTrace_2981174
  have hstable : (prefixWord ++ tailWord_2981174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981174).length < 2 ^ (prefixWord ++ tailWord_2981174).sum := by decide
  have hdescent : baseEnd_2981174 < baseStart_2981174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981180 : List Nat := [2, 2, 2, 2, 1, 3, 3, 2, 1, 3, 2]
def baseStart_2981180 : Nat := 118140960795 + 2981180 * 2 ^ 59
def prefixEnd_2981180 : Nat := 4983230072969 + 3 ^ 40 * 2981180 * 2
def baseEnd_2981180 : Nat := 1530778257570751353239809

theorem tailTrace_2981180 : CollatzResearch.WordTrace tailWord_2981180 prefixEnd_2981180 1530778257570751353239809 := by
  unfold tailWord_2981180
  simp only [CollatzResearch.WordTrace]
  refine ⟨54366283669850739927002497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72488378226467653236003329 54366283669850739927002497)
  ·
    refine ⟨40774712752388054945251873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54366283669850739927002497 40774712752388054945251873)
    ·
      refine ⟨30581034564291041208938905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40774712752388054945251873 30581034564291041208938905)
      ·
        refine ⟨22935775923218280906704179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30581034564291041208938905 22935775923218280906704179)
        ·
          refine ⟨34403663884827421360056269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22935775923218280906704179 34403663884827421360056269)
          ·
            refine ⟨12901373956810283010021101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34403663884827421360056269 12901373956810283010021101)
            ·
              refine ⟨4838015233803856128757913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12901373956810283010021101 4838015233803856128757913)
              ·
                refine ⟨3628511425352892096568435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4838015233803856128757913 3628511425352892096568435)
                ·
                  refine ⟨5442767138029338144852653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3628511425352892096568435 5442767138029338144852653)
                  ·
                    refine ⟨2041037676761001804319745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5442767138029338144852653 2041037676761001804319745)
                    ·
                      refine ⟨1530778257570751353239809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2041037676761001804319745 1530778257570751353239809)
                      ·
                        rfl

theorem cell23_2981180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_2981180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981180 prefixEnd_2981180 := by exact prefixLift 2981180
  have htrace : WordTrace (prefixWord ++ tailWord_2981180) baseStart_2981180 baseEnd_2981180 := by
    simpa [prefixWord, tailWord_2981180, baseEnd_2981180] using wordTrace_append hprefix tailTrace_2981180
  have hstable : (prefixWord ++ tailWord_2981180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981180).length < 2 ^ (prefixWord ++ tailWord_2981180).sum := by decide
  have hdescent : baseEnd_2981180 < baseStart_2981180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981193 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 6, 2, 2]
def baseStart_2981193 : Nat := 118140960795 + 2981193 * 2 ^ 59
def prefixEnd_2981193 : Nat := 4983230072969 + 3 ^ 40 * 2981193 * 2
def baseEnd_2981193 : Nat := 1530784932819259802377249

theorem tailTrace_2981193 : CollatzResearch.WordTrace tailWord_2981193 prefixEnd_2981193 1530784932819259802377249 := by
  unfold tailWord_2981193
  simp only [CollatzResearch.WordTrace]
  refine ⟨108733041488654383074228233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72488694325769588716152155 108733041488654383074228233)
  ·
    refine ⟨81549781116490787305671175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108733041488654383074228233 81549781116490787305671175)
    ·
      refine ⟨122324671674736180958506763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81549781116490787305671175 122324671674736180958506763)
      ·
        refine ⟨183487007512104271437760145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122324671674736180958506763 183487007512104271437760145)
        ·
          refine ⟨137615255634078203578320109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183487007512104271437760145 137615255634078203578320109)
          ·
            refine ⟨51605720862779326341870041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137615255634078203578320109 51605720862779326341870041)
            ·
              refine ⟨38704290647084494756402531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51605720862779326341870041 38704290647084494756402531)
              ·
                refine ⟨58056435970626742134603797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38704290647084494756402531 58056435970626742134603797)
                ·
                  refine ⟨2721395436123128537559553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58056435970626742134603797 2721395436123128537559553)
                  ·
                    refine ⟨2041046577092346403169665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2721395436123128537559553 2041046577092346403169665)
                    ·
                      refine ⟨1530784932819259802377249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2041046577092346403169665 1530784932819259802377249)
                      ·
                        rfl

theorem cell23_2981193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 2, 2].length) (baseStart_2981193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981193 prefixEnd_2981193 := by exact prefixLift 2981193
  have htrace : WordTrace (prefixWord ++ tailWord_2981193) baseStart_2981193 baseEnd_2981193 := by
    simpa [prefixWord, tailWord_2981193, baseEnd_2981193] using wordTrace_append hprefix tailTrace_2981193
  have hstable : (prefixWord ++ tailWord_2981193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981193).length < 2 ^ (prefixWord ++ tailWord_2981193).sum := by decide
  have hdescent : baseEnd_2981193 < baseStart_2981193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981196 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 2, 1, 5]
def baseStart_2981196 : Nat := 118140960795 + 2981196 * 2 ^ 59
def prefixEnd_2981196 : Nat := 4983230072969 + 3 ^ 40 * 2981196 * 2
def baseEnd_2981196 : Nat := 1530786473261223290639735

theorem tailTrace_2981196 : CollatzResearch.WordTrace tailWord_2981196 prefixEnd_2981196 1530786473261223290639735 := by
  unfold tailWord_2981196
  simp only [CollatzResearch.WordTrace]
  refine ⟨54366575453821757293293721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72488767271762343057724961 54366575453821757293293721)
  ·
    refine ⟨40774931590366317969970291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54366575453821757293293721 40774931590366317969970291)
    ·
      refine ⟨61162397385549476954955437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40774931590366317969970291 61162397385549476954955437)
      ·
        refine ⟨22935899019581053858108289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61162397385549476954955437 22935899019581053858108289)
        ·
          refine ⟨17201924264685790393581217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22935899019581053858108289 17201924264685790393581217)
          ·
            refine ⟨12901443198514342795185913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17201924264685790393581217 12901443198514342795185913)
            ·
              refine ⟨9676082398885757096389435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12901443198514342795185913 9676082398885757096389435)
              ·
                refine ⟨14514123598328635644584153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9676082398885757096389435 14514123598328635644584153)
                ·
                  refine ⟨10885592698746476733438115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14514123598328635644584153 10885592698746476733438115)
                  ·
                    refine ⟨16328389048119715100157173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10885592698746476733438115 16328389048119715100157173)
                    ·
                      refine ⟨1530786473261223290639735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16328389048119715100157173 1530786473261223290639735)
                      ·
                        rfl

theorem cell23_2981196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_2981196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981196 prefixEnd_2981196 := by exact prefixLift 2981196
  have htrace : WordTrace (prefixWord ++ tailWord_2981196) baseStart_2981196 baseEnd_2981196 := by
    simpa [prefixWord, tailWord_2981196, baseEnd_2981196] using wordTrace_append hprefix tailTrace_2981196
  have hstable : (prefixWord ++ tailWord_2981196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981196).length < 2 ^ (prefixWord ++ tailWord_2981196).sum := by decide
  have hdescent : baseEnd_2981196 < baseStart_2981196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981209 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 1, 2, 7]
def baseStart_2981209 : Nat := 118140960795 + 2981209 * 2 ^ 59
def prefixEnd_2981209 : Nat := 4983230072969 + 3 ^ 40 * 2981209 * 2
def baseEnd_2981209 : Nat := 1530793148509731739777175

theorem tailTrace_2981209 : CollatzResearch.WordTrace tailWord_2981209 prefixEnd_2981209 1530793148509731739777175 := by
  unfold tailWord_2981209
  simp only [CollatzResearch.WordTrace]
  refine ⟨108733625056596417806810681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72489083371064278537873787 108733625056596417806810681)
  ·
    refine ⟨81550218792447313355108011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108733625056596417806810681 81550218792447313355108011)
    ·
      refine ⟨122325328188670970032662017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81550218792447313355108011 122325328188670970032662017)
      ·
        refine ⟨91743996141503227524496513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122325328188670970032662017 91743996141503227524496513)
        ·
          refine ⟨68807997106127420643372385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91743996141503227524496513 68807997106127420643372385)
          ·
            refine ⟨51605997829595565482529289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68807997106127420643372385 51605997829595565482529289)
            ·
              refine ⟨38704498372196674111896967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51605997829595565482529289 38704498372196674111896967)
              ·
                refine ⟨58056747558295011167845451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38704498372196674111896967 58056747558295011167845451)
                ·
                  refine ⟨87085121337442516751768177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58056747558295011167845451 87085121337442516751768177)
                  ·
                    refine ⟨65313841003081887563826133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87085121337442516751768177 65313841003081887563826133)
                    ·
                      refine ⟨1530793148509731739777175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65313841003081887563826133 1530793148509731739777175)
                      ·
                        rfl

theorem cell23_2981209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_2981209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981209 prefixEnd_2981209 := by exact prefixLift 2981209
  have htrace : WordTrace (prefixWord ++ tailWord_2981209) baseStart_2981209 baseEnd_2981209 := by
    simpa [prefixWord, tailWord_2981209, baseEnd_2981209] using wordTrace_append hprefix tailTrace_2981209
  have hstable : (prefixWord ++ tailWord_2981209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981209).length < 2 ^ (prefixWord ++ tailWord_2981209).sum := by decide
  have hdescent : baseEnd_2981209 < baseStart_2981209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981210 : List Nat := [3, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2]
def baseStart_2981210 : Nat := 118140960795 + 2981210 * 2 ^ 59
def prefixEnd_2981210 : Nat := 4983230072969 + 3 ^ 40 * 2981210 * 2
def baseEnd_2981210 : Nat := 1530793661990386235864671

theorem tailTrace_2981210 : CollatzResearch.WordTrace tailWord_2981210 prefixEnd_2981210 1530793661990386235864671 := by
  unfold tailWord_2981210
  simp only [CollatzResearch.WordTrace]
  refine ⟨27183415382398198744399271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72489107686395196651731389 27183415382398198744399271)
  ·
    refine ⟨40775123073597298116598907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27183415382398198744399271 40775123073597298116598907)
    ·
      refine ⟨61162684610395947174898361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40775123073597298116598907 61162684610395947174898361)
      ·
        refine ⟨45872013457796960381173771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61162684610395947174898361 45872013457796960381173771)
        ·
          refine ⟨68808020186695440571760657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45872013457796960381173771 68808020186695440571760657)
          ·
            refine ⟨51606015140021580428820493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68808020186695440571760657 51606015140021580428820493)
            ·
              refine ⟨19352255677508092660807685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51606015140021580428820493 19352255677508092660807685)
              ·
                refine ⟨3628547939532767373901441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19352255677508092660807685 3628547939532767373901441)
                ·
                  refine ⟨2721410954649575530426081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3628547939532767373901441 2721410954649575530426081)
                  ·
                    refine ⟨2041058215987181647819561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2721410954649575530426081 2041058215987181647819561)
                    ·
                      refine ⟨1530793661990386235864671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2041058215987181647819561 1530793661990386235864671)
                      ·
                        rfl

theorem cell23_2981210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_2981210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981210 prefixEnd_2981210 := by exact prefixLift 2981210
  have htrace : WordTrace (prefixWord ++ tailWord_2981210) baseStart_2981210 baseEnd_2981210 := by
    simpa [prefixWord, tailWord_2981210, baseEnd_2981210] using wordTrace_append hprefix tailTrace_2981210
  have hstable : (prefixWord ++ tailWord_2981210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981210).length < 2 ^ (prefixWord ++ tailWord_2981210).sum := by decide
  have hdescent : baseEnd_2981210 < baseStart_2981210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981223 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_2981223 : Nat := 118140960795 + 2981223 * 2 ^ 59
def prefixEnd_2981223 : Nat := 4983230072969 + 3 ^ 40 * 2981223 * 2
def baseEnd_2981223 : Nat := 1530800337238894685002111

theorem tailTrace_2981223 : CollatzResearch.WordTrace tailWord_2981223 prefixEnd_2981223 1530800337238894685002111 := by
  unfold tailWord_2981223
  simp only [CollatzResearch.WordTrace]
  refine ⟨108734135678545698197820323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72489423785697132131880215 108734135678545698197820323)
  ·
    refine ⟨163101203517818547296730485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108734135678545698197820323 163101203517818547296730485)
    ·
      refine ⟨15290737829795488809068483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163101203517818547296730485 15290737829795488809068483)
      ·
        refine ⟨22936106744693233213602725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15290737829795488809068483 22936106744693233213602725)
        ·
          refine ⟨4300520014629981227550511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22936106744693233213602725 4300520014629981227550511)
          ·
            refine ⟨6450780021944971841325767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4300520014629981227550511 6450780021944971841325767)
            ·
              refine ⟨9676170032917457761988651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6450780021944971841325767 9676170032917457761988651)
              ·
                refine ⟨14514255049376186642982977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9676170032917457761988651 14514255049376186642982977)
                ·
                  refine ⟨10885691287032139982237233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14514255049376186642982977 10885691287032139982237233)
                  ·
                    refine ⟨8164268465274104986677925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10885691287032139982237233 8164268465274104986677925)
                    ·
                      refine ⟨1530800337238894685002111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8164268465274104986677925 1530800337238894685002111)
                      ·
                        rfl

theorem cell23_2981223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_2981223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981223 prefixEnd_2981223 := by exact prefixLift 2981223
  have htrace : WordTrace (prefixWord ++ tailWord_2981223) baseStart_2981223 baseEnd_2981223 := by
    simpa [prefixWord, tailWord_2981223, baseEnd_2981223] using wordTrace_append hprefix tailTrace_2981223
  have hstable : (prefixWord ++ tailWord_2981223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981223).length < 2 ^ (prefixWord ++ tailWord_2981223).sum := by decide
  have hdescent : baseEnd_2981223 < baseStart_2981223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981283 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 2, 4, 2]
def baseStart_2981283 : Nat := 118140960795 + 2981283 * 2 ^ 59
def prefixEnd_2981283 : Nat := 4983230072969 + 3 ^ 40 * 2981283 * 2
def baseEnd_2981283 : Nat := 1530831146078164450251835

theorem tailTrace_2981283 : CollatzResearch.WordTrace tailWord_2981283 prefixEnd_2981283 1530831146078164450251835 := by
  unfold tailWord_2981283
  simp only [CollatzResearch.WordTrace]
  refine ⟨108736324058328328445004503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72490882705552218963336335 108736324058328328445004503)
  ·
    refine ⟨163104486087492492667506755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108736324058328328445004503 163104486087492492667506755)
    ·
      refine ⟨244656729131238739001260133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163104486087492492667506755 244656729131238739001260133)
      ·
        refine ⟨45873136712107263562736275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244656729131238739001260133 45873136712107263562736275)
        ·
          refine ⟨68809705068160895344104413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45873136712107263562736275 68809705068160895344104413)
          ·
            refine ⟨25803639400560335754039155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68809705068160895344104413 25803639400560335754039155)
            ·
              refine ⟨38705459100840503631058733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25803639400560335754039155 38705459100840503631058733)
              ·
                refine ⟨14514547162815188861647025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38705459100840503631058733 14514547162815188861647025)
                ·
                  refine ⟨10885910372111391646235269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14514547162815188861647025 10885910372111391646235269)
                  ·
                    refine ⟨2041108194770885933669113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10885910372111391646235269 2041108194770885933669113)
                    ·
                      refine ⟨1530831146078164450251835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2041108194770885933669113 1530831146078164450251835)
                      ·
                        rfl

theorem cell23_2981283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_2981283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981283 prefixEnd_2981283 := by exact prefixLift 2981283
  have htrace : WordTrace (prefixWord ++ tailWord_2981283) baseStart_2981283 baseEnd_2981283 := by
    simpa [prefixWord, tailWord_2981283, baseEnd_2981283] using wordTrace_append hprefix tailTrace_2981283
  have hstable : (prefixWord ++ tailWord_2981283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981283).length < 2 ^ (prefixWord ++ tailWord_2981283).sum := by decide
  have hdescent : baseEnd_2981283 < baseStart_2981283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
