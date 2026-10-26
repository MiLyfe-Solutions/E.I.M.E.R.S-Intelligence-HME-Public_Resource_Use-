import V185TrunkScan23Chunk0731

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4329465 : List Nat := [1, 2, 1, 3, 1, 5, 3, 1, 1, 5]
def baseStart_4329465 : Nat := 118140960795 + 4329465 * 2 ^ 59
def prefixEnd_4329465 : Nat := 4983230072969 + 3 ^ 40 * 4329465 * 2
def baseEnd_4329465 : Nat := 741032173939336227325553

theorem tailTrace_4329465 : CollatzResearch.WordTrace tailWord_4329465 prefixEnd_4329465 741032173939336227325553 := by
  unfold tailWord_4329465
  simp only [CollatzResearch.WordTrace]
  refine ⟨157908561260095193599373849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105272374173396795732915899 157908561260095193599373849)
  ·
    refine ⟨118431420945071395199530387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157908561260095193599373849 118431420945071395199530387)
    ·
      refine ⟨177647131417607092799295581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118431420945071395199530387 177647131417607092799295581)
      ·
        refine ⟨66617674281602659799735843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177647131417607092799295581 66617674281602659799735843)
        ·
          refine ⟨99926511422403989699603765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66617674281602659799735843 99926511422403989699603765)
          ·
            refine ⟨9368110445850374034337853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99926511422403989699603765 9368110445850374034337853)
            ·
              refine ⟨3513041417193890262876695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9368110445850374034337853 3513041417193890262876695)
              ·
                refine ⟨5269562125790835394315043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3513041417193890262876695 5269562125790835394315043)
                ·
                  refine ⟨7904343188686253091472565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5269562125790835394315043 7904343188686253091472565)
                  ·
                    refine ⟨741032173939336227325553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7904343188686253091472565 741032173939336227325553)
                    ·
                      rfl

theorem cell23_4329465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 1, 5].length) (baseStart_4329465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329465 prefixEnd_4329465 := by exact prefixLift 4329465
  have htrace : WordTrace (prefixWord ++ tailWord_4329465) baseStart_4329465 baseEnd_4329465 := by
    simpa [prefixWord, tailWord_4329465, baseEnd_4329465] using wordTrace_append hprefix tailTrace_4329465
  have hstable : (prefixWord ++ tailWord_4329465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329465).length < 2 ^ (prefixWord ++ tailWord_4329465).sum := by decide
  have hdescent : baseEnd_4329465 < baseStart_4329465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329479 : List Nat := [1, 1, 4, 3, 1, 2, 4, 2, 1, 1, 3]
def baseStart_4329479 : Nat := 118140960795 + 4329479 * 2 ^ 59
def prefixEnd_4329479 : Nat := 4983230072969 + 3 ^ 40 * 4329479 * 2
def baseEnd_4329479 : Nat := 2223103710547171627201595

theorem tailTrace_4329479 : CollatzResearch.WordTrace tailWord_4329479 prefixEnd_4329479 2223103710547171627201595 := by
  unfold tailWord_4329479
  simp only [CollatzResearch.WordTrace]
  refine ⟨157909071882044473990383491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105272714588029649326922327 157909071882044473990383491)
  ·
    refine ⟨236863607823066710985575237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157909071882044473990383491 236863607823066710985575237)
    ·
      refine ⟨44411926466825008309795357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 236863607823066710985575237 44411926466825008309795357)
      ·
        refine ⟨16654472425059378116173259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44411926466825008309795357 16654472425059378116173259)
        ·
          refine ⟨24981708637589067174259889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16654472425059378116173259 24981708637589067174259889)
          ·
            refine ⟨18736281478191800380694917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24981708637589067174259889 18736281478191800380694917)
            ·
              refine ⟨3513052777160962571380297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18736281478191800380694917 3513052777160962571380297)
              ·
                refine ⟨2634789582870721928535223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3513052777160962571380297 2634789582870721928535223)
                ·
                  refine ⟨3952184374306082892802835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2634789582870721928535223 3952184374306082892802835)
                  ·
                    refine ⟨5928276561459124339204253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3952184374306082892802835 5928276561459124339204253)
                    ·
                      refine ⟨2223103710547171627201595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5928276561459124339204253 2223103710547171627201595)
                      ·
                        rfl

theorem cell23_4329479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_4329479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329479 prefixEnd_4329479 := by exact prefixLift 4329479
  have htrace : WordTrace (prefixWord ++ tailWord_4329479) baseStart_4329479 baseEnd_4329479 := by
    simpa [prefixWord, tailWord_4329479, baseEnd_4329479] using wordTrace_append hprefix tailTrace_4329479
  have hstable : (prefixWord ++ tailWord_4329479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329479).length < 2 ^ (prefixWord ++ tailWord_4329479).sum := by decide
  have hdescent : baseEnd_4329479 < baseStart_4329479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329491 : List Nat := [1, 1, 1, 2, 1, 4, 5, 8]
def baseStart_4329491 : Nat := 118140960795 + 4329491 * 2 ^ 59
def prefixEnd_4329491 : Nat := 4983230072969 + 3 ^ 40 * 4329491 * 2
def baseEnd_4329491 : Nat := 82337402678334280750057

theorem tailTrace_4329491 : CollatzResearch.WordTrace tailWord_4329491 prefixEnd_4329491 82337402678334280750057 := by
  unfold tailWord_4329491
  simp only [CollatzResearch.WordTrace]
  refine ⟨157909509558001000039820327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105273006372000666693213551 157909509558001000039820327)
  ·
    refine ⟨236864264337001500059730491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157909509558001000039820327 236864264337001500059730491)
    ·
      refine ⟨355296396505502250089595737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236864264337001500059730491 355296396505502250089595737)
      ·
        refine ⟨266472297379126687567196803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 355296396505502250089595737 266472297379126687567196803)
        ·
          refine ⟨399708446068690031350795205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266472297379126687567196803 399708446068690031350795205)
          ·
            refine ⟨74945333637879380878274101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 399708446068690031350795205 74945333637879380878274101)
            ·
              refine ⟨7026125028551191957338197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74945333637879380878274101 7026125028551191957338197)
              ·
                refine ⟨82337402678334280750057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7026125028551191957338197 82337402678334280750057)
                ·
                  rfl

theorem cell23_4329491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 8].length) (baseStart_4329491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329491 prefixEnd_4329491 := by exact prefixLift 4329491
  have htrace : WordTrace (prefixWord ++ tailWord_4329491) baseStart_4329491 baseEnd_4329491 := by
    simpa [prefixWord, tailWord_4329491, baseEnd_4329491] using wordTrace_append hprefix tailTrace_4329491
  have hstable : (prefixWord ++ tailWord_4329491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329491).length < 2 ^ (prefixWord ++ tailWord_4329491).sum := by decide
  have hdescent : baseEnd_4329491 < baseStart_4329491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329495 : List Nat := [1, 1, 3, 5, 2, 1, 2, 1, 1, 6]
def baseStart_4329495 : Nat := 118140960795 + 4329495 * 2 ^ 59
def prefixEnd_4329495 : Nat := 4983230072969 + 3 ^ 40 * 4329495 * 2
def baseEnd_4329495 : Nat := 741037308745881188200507

theorem tailTrace_4329495 : CollatzResearch.WordTrace tailWord_4329495 prefixEnd_4329495 741037308745881188200507 := by
  unfold tailWord_4329495
  simp only [CollatzResearch.WordTrace]
  refine ⟨157909655449986508722965939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105273103633324339148643959 157909655449986508722965939)
  ·
    refine ⟨236864483174979763084448909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157909655449986508722965939 236864483174979763084448909)
    ·
      refine ⟨88824181190617411156668341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236864483174979763084448909 88824181190617411156668341)
      ·
        refine ⟨8327266986620382295937657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88824181190617411156668341 8327266986620382295937657)
        ·
          refine ⟨6245450239965286721953243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8327266986620382295937657 6245450239965286721953243)
          ·
            refine ⟨9368175359947930082929865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6245450239965286721953243 9368175359947930082929865)
            ·
              refine ⟨7026131519960947562197399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9368175359947930082929865 7026131519960947562197399)
              ·
                refine ⟨10539197279941421343296099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7026131519960947562197399 10539197279941421343296099)
                ·
                  refine ⟨15808795919912132014944149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10539197279941421343296099 15808795919912132014944149)
                  ·
                    refine ⟨741037308745881188200507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15808795919912132014944149 741037308745881188200507)
                    ·
                      rfl

theorem cell23_4329495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_4329495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329495 prefixEnd_4329495 := by exact prefixLift 4329495
  have htrace : WordTrace (prefixWord ++ tailWord_4329495) baseStart_4329495 baseEnd_4329495 := by
    simpa [prefixWord, tailWord_4329495, baseEnd_4329495] using wordTrace_append hprefix tailTrace_4329495
  have hstable : (prefixWord ++ tailWord_4329495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329495).length < 2 ^ (prefixWord ++ tailWord_4329495).sum := by decide
  have hdescent : baseEnd_4329495 < baseStart_4329495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329498 : List Nat := [3, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4]
def baseStart_4329498 : Nat := 118140960795 + 4329498 * 2 ^ 59
def prefixEnd_4329498 : Nat := 4983230072969 + 3 ^ 40 * 4329498 * 2
def baseEnd_4329498 : Nat := 2223113466679607052864007

theorem tailTrace_4329498 : CollatzResearch.WordTrace tailWord_4329498 prefixEnd_4329498 2223113466679607052864007 := by
  unfold tailWord_4329498
  simp only [CollatzResearch.WordTrace]
  refine ⟨39477441217243910058831287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105273176579317093490216765 39477441217243910058831287)
  ·
    refine ⟨59216161825865865088246931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39477441217243910058831287 59216161825865865088246931)
    ·
      refine ⟨88824242738798797632370397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59216161825865865088246931 88824242738798797632370397)
      ·
        refine ⟨33309091027049549112138899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88824242738798797632370397 33309091027049549112138899)
        ·
          refine ⟨49963636540574323668208349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33309091027049549112138899 49963636540574323668208349)
          ·
            refine ⟨18736363702715371375578131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49963636540574323668208349 18736363702715371375578131)
            ·
              refine ⟨28104545554073057063367197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18736363702715371375578131 28104545554073057063367197)
              ·
                refine ⟨10539204582777396398762699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28104545554073057063367197 10539204582777396398762699)
                ·
                  refine ⟨15808806874166094598144049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10539204582777396398762699 15808806874166094598144049)
                  ·
                    refine ⟨11856605155624570948608037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15808806874166094598144049 11856605155624570948608037)
                    ·
                      refine ⟨2223113466679607052864007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11856605155624570948608037 2223113466679607052864007)
                      ·
                        rfl

theorem cell23_4329498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_4329498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329498 prefixEnd_4329498 := by exact prefixLift 4329498
  have htrace : WordTrace (prefixWord ++ tailWord_4329498) baseStart_4329498 baseEnd_4329498 := by
    simpa [prefixWord, tailWord_4329498, baseEnd_4329498] using wordTrace_append hprefix tailTrace_4329498
  have hstable : (prefixWord ++ tailWord_4329498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329498).length < 2 ^ (prefixWord ++ tailWord_4329498).sum := by decide
  have hdescent : baseEnd_4329498 < baseStart_4329498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329522 : List Nat := [3, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3]
def baseStart_4329522 : Nat := 118140960795 + 4329522 * 2 ^ 59
def prefixEnd_4329522 : Nat := 4983230072969 + 3 ^ 40 * 4329522 * 2
def baseEnd_4329522 : Nat := 2223125790215314958963897

theorem tailTrace_4329522 : CollatzResearch.WordTrace tailWord_4329522 prefixEnd_4329522 2223125790215314958963897 := by
  unfold tailWord_4329522
  simp only [CollatzResearch.WordTrace]
  refine ⟨39477660055222173083549705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105273760147259128222799213 39477660055222173083549705)
  ·
    refine ⟨29608245041416629812662279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39477660055222173083549705 29608245041416629812662279)
    ·
      refine ⟨44412367562124944718993419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29608245041416629812662279 44412367562124944718993419)
      ·
        refine ⟨66618551343187417078490129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44412367562124944718993419 66618551343187417078490129)
        ·
          refine ⟨49963913507390562808867597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66618551343187417078490129 49963913507390562808867597)
          ·
            refine ⟨18736467565271461053325349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49963913507390562808867597 18736467565271461053325349)
            ·
              refine ⟨3513087668488398947498503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18736467565271461053325349 3513087668488398947498503)
              ·
                refine ⟨5269631502732598421247755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3513087668488398947498503 5269631502732598421247755)
                ·
                  refine ⟨7904447254098897631871633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5269631502732598421247755 7904447254098897631871633)
                  ·
                    refine ⟨5928335440574173223903725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7904447254098897631871633 5928335440574173223903725)
                    ·
                      refine ⟨2223125790215314958963897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5928335440574173223903725 2223125790215314958963897)
                      ·
                        rfl

theorem cell23_4329522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_4329522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329522 prefixEnd_4329522 := by exact prefixLift 4329522
  have htrace : WordTrace (prefixWord ++ tailWord_4329522) baseStart_4329522 baseEnd_4329522 := by
    simpa [prefixWord, tailWord_4329522, baseEnd_4329522] using wordTrace_append hprefix tailTrace_4329522
  have hstable : (prefixWord ++ tailWord_4329522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329522).length < 2 ^ (prefixWord ++ tailWord_4329522).sum := by decide
  have hdescent : baseEnd_4329522 < baseStart_4329522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329529 : List Nat := [1, 2, 1, 5, 4, 1, 1, 2, 2, 4]
def baseStart_4329529 : Nat := 118140960795 + 4329529 * 2 ^ 59
def prefixEnd_4329529 : Nat := 4983230072969 + 3 ^ 40 * 4329529 * 2
def baseEnd_4329529 : Nat := 741043128193298810525455

theorem tailTrace_4329529 : CollatzResearch.WordTrace tailWord_4329529 prefixEnd_4329529 741043128193298810525455 := by
  unfold tailWord_4329529
  simp only [CollatzResearch.WordTrace]
  refine ⟨157910895531863332529703641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105273930354575555019802427 157910895531863332529703641)
  ·
    refine ⟨118433171648897499397277731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157910895531863332529703641 118433171648897499397277731)
    ·
      refine ⟨177649757473346249095916597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118433171648897499397277731 177649757473346249095916597)
      ·
        refine ⟨16654664763126210852742181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 177649757473346249095916597 16654664763126210852742181)
        ·
          refine ⟨3122749643086164534889159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16654664763126210852742181 3122749643086164534889159)
          ·
            refine ⟨4684124464629246802333739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3122749643086164534889159 4684124464629246802333739)
            ·
              refine ⟨7026186696943870203500609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4684124464629246802333739 7026186696943870203500609)
              ·
                refine ⟨5269640022707902652625457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7026186696943870203500609 5269640022707902652625457)
                ·
                  refine ⟨3952230017030926989469093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5269640022707902652625457 3952230017030926989469093)
                  ·
                    refine ⟨741043128193298810525455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3952230017030926989469093 741043128193298810525455)
                    ·
                      rfl

theorem cell23_4329529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 2, 4].length) (baseStart_4329529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329529 prefixEnd_4329529 := by exact prefixLift 4329529
  have htrace : WordTrace (prefixWord ++ tailWord_4329529) baseStart_4329529 baseEnd_4329529 := by
    simpa [prefixWord, tailWord_4329529, baseEnd_4329529] using wordTrace_append hprefix tailTrace_4329529
  have hstable : (prefixWord ++ tailWord_4329529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329529).length < 2 ^ (prefixWord ++ tailWord_4329529).sum := by decide
  have hdescent : baseEnd_4329529 < baseStart_4329529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329531 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 5]
def baseStart_4329531 : Nat := 118140960795 + 4329531 * 2 ^ 59
def prefixEnd_4329531 : Nat := 4983230072969 + 3 ^ 40 * 4329531 * 2
def baseEnd_4329531 : Nat := 2223130411541205423751355

theorem tailTrace_4329531 : CollatzResearch.WordTrace tailWord_4329531 prefixEnd_4329531 2223130411541205423751355 := by
  unfold tailWord_4329531
  simp only [CollatzResearch.WordTrace]
  refine ⟨157910968477856086871276447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105273978985237391247517631 157910968477856086871276447)
  ·
    refine ⟨236866452716784130306914671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157910968477856086871276447 236866452716784130306914671)
    ·
      refine ⟨355299679075176195460372007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236866452716784130306914671 355299679075176195460372007)
      ·
        refine ⟨532949518612764293190558011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355299679075176195460372007 532949518612764293190558011)
        ·
          refine ⟨799424277919146439785837017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532949518612764293190558011 799424277919146439785837017)
          ·
            refine ⟨599568208439359829839377763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 799424277919146439785837017 599568208439359829839377763)
            ·
              refine ⟨899352312659039744759066645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599568208439359829839377763 899352312659039744759066645)
              ·
                refine ⟨42157139655892488035581249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 899352312659039744759066645 42157139655892488035581249)
                ·
                  refine ⟨31617854741919366026685937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42157139655892488035581249 31617854741919366026685937)
                  ·
                    refine ⟨23713391056439524520014453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31617854741919366026685937 23713391056439524520014453)
                    ·
                      refine ⟨2223130411541205423751355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23713391056439524520014453 2223130411541205423751355)
                      ·
                        rfl

theorem cell23_4329531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 5].length) (baseStart_4329531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329531 prefixEnd_4329531 := by exact prefixLift 4329531
  have htrace : WordTrace (prefixWord ++ tailWord_4329531) baseStart_4329531 baseEnd_4329531 := by
    simpa [prefixWord, tailWord_4329531, baseEnd_4329531] using wordTrace_append hprefix tailTrace_4329531
  have hstable : (prefixWord ++ tailWord_4329531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329531).length < 2 ^ (prefixWord ++ tailWord_4329531).sum := by decide
  have hdescent : baseEnd_4329531 < baseStart_4329531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329562 : List Nat := [3, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2]
def baseStart_4329562 : Nat := 118140960795 + 4329562 * 2 ^ 59
def prefixEnd_4329562 : Nat := 4983230072969 + 3 ^ 40 * 4329562 * 2
def baseEnd_4329562 : Nat := 2223146329441494802463713

theorem tailTrace_4329562 : CollatzResearch.WordTrace tailWord_4329562 prefixEnd_4329562 2223146329441494802463713 := by
  unfold tailWord_4329562
  simp only [CollatzResearch.WordTrace]
  refine ⟨39478024785185944791413735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105274732760495852777103293 39478024785185944791413735)
  ·
    refine ⟨59217037177778917187120603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39478024785185944791413735 59217037177778917187120603)
    ·
      refine ⟨88825555766668375780680905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59217037177778917187120603 88825555766668375780680905)
      ·
        refine ⟨66619166825001281835510679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88825555766668375780680905 66619166825001281835510679)
        ·
          refine ⟨99928750237501922753266019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66619166825001281835510679 99928750237501922753266019)
          ·
            refine ⟨149893125356252884129899029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99928750237501922753266019 149893125356252884129899029)
            ·
              refine ⟨7026240251074353943589017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 149893125356252884129899029 7026240251074353943589017)
              ·
                refine ⟨5269680188305765457691763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7026240251074353943589017 5269680188305765457691763)
                ·
                  refine ⟨7904520282458648186537645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5269680188305765457691763 7904520282458648186537645)
                  ·
                    refine ⟨2964195105921993069951617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7904520282458648186537645 2964195105921993069951617)
                    ·
                      refine ⟨2223146329441494802463713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964195105921993069951617 2223146329441494802463713)
                      ·
                        rfl

theorem cell23_4329562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_4329562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329562 prefixEnd_4329562 := by exact prefixLift 4329562
  have htrace : WordTrace (prefixWord ++ tailWord_4329562) baseStart_4329562 baseEnd_4329562 := by
    simpa [prefixWord, tailWord_4329562, baseEnd_4329562] using wordTrace_append hprefix tailTrace_4329562
  have hstable : (prefixWord ++ tailWord_4329562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329562).length < 2 ^ (prefixWord ++ tailWord_4329562).sum := by decide
  have hdescent : baseEnd_4329562 < baseStart_4329562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329565 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_4329565 : Nat := 118140960795 + 4329565 * 2 ^ 59
def prefixEnd_4329565 : Nat := 4983230072969 + 3 ^ 40 * 4329565 * 2
def baseEnd_4329565 : Nat := 2223147869883458290726199

theorem tailTrace_4329565 : CollatzResearch.WordTrace tailWord_4329565 prefixEnd_4329565 2223147869883458290726199 := by
  unfold tailWord_4329565
  simp only [CollatzResearch.WordTrace]
  refine ⟨157912208559732910678014149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105274805706488607118676099 157912208559732910678014149)
  ·
    refine ⟨29608539104949920752127653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157912208559732910678014149 29608539104949920752127653)
    ·
      refine ⟨5551601082178110141023935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29608539104949920752127653 5551601082178110141023935)
      ·
        refine ⟨8327401623267165211535903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5551601082178110141023935 8327401623267165211535903)
        ·
          refine ⟨12491102434900747817303855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8327401623267165211535903 12491102434900747817303855)
          ·
            refine ⟨18736653652351121725955783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12491102434900747817303855 18736653652351121725955783)
            ·
              refine ⟨28104980478526682588933675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18736653652351121725955783 28104980478526682588933675)
              ·
                refine ⟨42157470717790023883400513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28104980478526682588933675 42157470717790023883400513)
                ·
                  refine ⟨31618103038342517912550385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42157470717790023883400513 31618103038342517912550385)
                  ·
                    refine ⟨23713577278756888434412789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31618103038342517912550385 23713577278756888434412789)
                    ·
                      refine ⟨2223147869883458290726199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23713577278756888434412789 2223147869883458290726199)
                      ·
                        rfl

theorem cell23_4329565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_4329565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329565 prefixEnd_4329565 := by exact prefixLift 4329565
  have htrace : WordTrace (prefixWord ++ tailWord_4329565) baseStart_4329565 baseEnd_4329565 := by
    simpa [prefixWord, tailWord_4329565, baseEnd_4329565] using wordTrace_append hprefix tailTrace_4329565
  have hstable : (prefixWord ++ tailWord_4329565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329565).length < 2 ^ (prefixWord ++ tailWord_4329565).sum := by decide
  have hdescent : baseEnd_4329565 < baseStart_4329565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329570 : List Nat := [3, 3, 2, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_4329570 : Nat := 118140960795 + 4329570 * 2 ^ 59
def prefixEnd_4329570 : Nat := 4983230072969 + 3 ^ 40 * 4329570 * 2
def baseEnd_4329570 : Nat := 2223150437286730771163677

theorem tailTrace_4329570 : CollatzResearch.WordTrace tailWord_4329570 prefixEnd_4329570 2223150437286730771163677 := by
  unfold tailWord_4329570
  simp only [CollatzResearch.WordTrace]
  refine ⟨39478097731178699132986541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105274927283143197687964109 39478097731178699132986541)
  ·
    refine ⟨14804286649192012174869953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39478097731178699132986541 14804286649192012174869953)
    ·
      refine ⟨11103214986894009131152465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14804286649192012174869953 11103214986894009131152465)
      ·
        refine ⟨8327411240170506848364349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11103214986894009131152465 8327411240170506848364349)
        ·
          refine ⟨3122779215063940068136631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8327411240170506848364349 3122779215063940068136631)
          ·
            refine ⟨4684168822595910102204947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3122779215063940068136631 4684168822595910102204947)
            ·
              refine ⟨7026253233893865153307421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4684168822595910102204947 7026253233893865153307421)
              ·
                refine ⟨2634844962710199432490283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7026253233893865153307421 2634844962710199432490283)
                ·
                  refine ⟨3952267444065299148735425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2634844962710199432490283 3952267444065299148735425)
                  ·
                    refine ⟨2964200583048974361551569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3952267444065299148735425 2964200583048974361551569)
                    ·
                      refine ⟨2223150437286730771163677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964200583048974361551569 2223150437286730771163677)
                      ·
                        rfl

theorem cell23_4329570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_4329570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329570 prefixEnd_4329570 := by exact prefixLift 4329570
  have htrace : WordTrace (prefixWord ++ tailWord_4329570) baseStart_4329570 baseEnd_4329570 := by
    simpa [prefixWord, tailWord_4329570, baseEnd_4329570] using wordTrace_append hprefix tailTrace_4329570
  have hstable : (prefixWord ++ tailWord_4329570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329570).length < 2 ^ (prefixWord ++ tailWord_4329570).sum := by decide
  have hdescent : baseEnd_4329570 < baseStart_4329570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329575 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 3, 4, 2]
def baseStart_4329575 : Nat := 118140960795 + 4329575 * 2 ^ 59
def prefixEnd_4329575 : Nat := 4983230072969 + 3 ^ 40 * 4329575 * 2
def baseEnd_4329575 : Nat := 2223153004690003251601153

theorem tailTrace_4329575 : CollatzResearch.WordTrace tailWord_4329575 prefixEnd_4329575 2223153004690003251601153 := by
  unfold tailWord_4329575
  simp only [CollatzResearch.WordTrace]
  refine ⟨157912573289696682385878179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105275048859797788257252119 157912573289696682385878179)
  ·
    refine ⟨236868859934545023578817269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157912573289696682385878179 236868859934545023578817269)
    ·
      refine ⟨22206455618863595960514119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 236868859934545023578817269 22206455618863595960514119)
      ·
        refine ⟨33309683428295393940771179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22206455618863595960514119 33309683428295393940771179)
        ·
          refine ⟨49964525142443090911156769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33309683428295393940771179 49964525142443090911156769)
          ·
            refine ⟨37473393856832318183367577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49964525142443090911156769 37473393856832318183367577)
            ·
              refine ⟨28105045392624238637525683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37473393856832318183367577 28105045392624238637525683)
              ·
                refine ⟨42157568088936357956288525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28105045392624238637525683 42157568088936357956288525)
                ·
                  refine ⟨15809088033351134233608197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42157568088936357956288525 15809088033351134233608197)
                  ·
                    refine ⟨2964204006253337668801537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15809088033351134233608197 2964204006253337668801537)
                    ·
                      refine ⟨2223153004690003251601153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964204006253337668801537 2223153004690003251601153)
                      ·
                        rfl

theorem cell23_4329575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_4329575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329575 prefixEnd_4329575 := by exact prefixLift 4329575
  have htrace : WordTrace (prefixWord ++ tailWord_4329575) baseStart_4329575 baseEnd_4329575 := by
    simpa [prefixWord, tailWord_4329575, baseEnd_4329575] using wordTrace_append hprefix tailTrace_4329575
  have hstable : (prefixWord ++ tailWord_4329575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329575).length < 2 ^ (prefixWord ++ tailWord_4329575).sum := by decide
  have hdescent : baseEnd_4329575 < baseStart_4329575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329592 : List Nat := [2, 1, 2, 1, 1, 1, 3, 6, 2, 2, 2]
def baseStart_4329592 : Nat := 118140960795 + 4329592 * 2 ^ 59
def prefixEnd_4329592 : Nat := 4983230072969 + 3 ^ 40 * 4329592 * 2
def baseEnd_4329592 : Nat := 2223161733861129685088575

theorem tailTrace_4329592 : CollatzResearch.WordTrace tailWord_4329592 prefixEnd_4329592 2223161733861129685088575 := by
  unfold tailWord_4329592
  simp only [CollatzResearch.WordTrace]
  refine ⟨78956596665317547144623515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105275462220423396192831353 78956596665317547144623515)
  ·
    refine ⟨118434894997976320716935273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78956596665317547144623515 118434894997976320716935273)
    ·
      refine ⟨88826171248482240537701455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118434894997976320716935273 88826171248482240537701455)
      ·
        refine ⟨133239256872723360806552183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88826171248482240537701455 133239256872723360806552183)
        ·
          refine ⟨199858885309085041209828275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133239256872723360806552183 199858885309085041209828275)
          ·
            refine ⟨299788327963627561814742413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199858885309085041209828275 299788327963627561814742413)
            ·
              refine ⟨112420622986360335680528405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 299788327963627561814742413 112420622986360335680528405)
              ·
                refine ⟨5269716702485640735024769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112420622986360335680528405 5269716702485640735024769)
                ·
                  refine ⟨3952287526864230551268577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5269716702485640735024769 3952287526864230551268577)
                  ·
                    refine ⟨2964215645148172913451433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3952287526864230551268577 2964215645148172913451433)
                    ·
                      refine ⟨2223161733861129685088575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964215645148172913451433 2223161733861129685088575)
                      ·
                        rfl

theorem cell23_4329592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 2, 2, 2].length) (baseStart_4329592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329592 prefixEnd_4329592 := by exact prefixLift 4329592
  have htrace : WordTrace (prefixWord ++ tailWord_4329592) baseStart_4329592 baseEnd_4329592 := by
    simpa [prefixWord, tailWord_4329592, baseEnd_4329592] using wordTrace_append hprefix tailTrace_4329592
  have hstable : (prefixWord ++ tailWord_4329592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329592).length < 2 ^ (prefixWord ++ tailWord_4329592).sum := by decide
  have hdescent : baseEnd_4329592 < baseStart_4329592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329675 : List Nat := [1, 1, 1, 1, 3, 2, 5, 2, 3, 4]
def baseStart_4329675 : Nat := 118140960795 + 4329675 * 2 ^ 59
def prefixEnd_4329675 : Nat := 4983230072969 + 3 ^ 40 * 4329675 * 2
def baseEnd_4329675 : Nat := 741068117585150953450231

theorem tailTrace_4329675 : CollatzResearch.WordTrace tailWord_4329675 prefixEnd_4329675 741068117585150953450231 := by
  unfold tailWord_4329675
  simp only [CollatzResearch.WordTrace]
  refine ⟨157916220589334399464518479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105277480392889599643012319 157916220589334399464518479)
  ·
    refine ⟨236874330884001599196777719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157916220589334399464518479 236874330884001599196777719)
    ·
      refine ⟨355311496326002398795166579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236874330884001599196777719 355311496326002398795166579)
      ·
        refine ⟨532967244489003598192749869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355311496326002398795166579 532967244489003598192749869)
        ·
          refine ⟨199862716683376349322281201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 532967244489003598192749869 199862716683376349322281201)
          ·
            refine ⟨149897037512532261991710901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199862716683376349322281201 149897037512532261991710901)
            ·
              refine ⟨14052847266799899561722897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 149897037512532261991710901 14052847266799899561722897)
              ·
                refine ⟨10539635450099924671292173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14052847266799899561722897 10539635450099924671292173)
                ·
                  refine ⟨3952363293787471751734565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10539635450099924671292173 3952363293787471751734565)
                  ·
                    refine ⟨741068117585150953450231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3952363293787471751734565 741068117585150953450231)
                    ·
                      rfl

theorem cell23_4329675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 4].length) (baseStart_4329675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329675 prefixEnd_4329675 := by exact prefixLift 4329675
  have htrace : WordTrace (prefixWord ++ tailWord_4329675) baseStart_4329675 baseEnd_4329675 := by
    simpa [prefixWord, tailWord_4329675, baseEnd_4329675] using wordTrace_append hprefix tailTrace_4329675
  have hstable : (prefixWord ++ tailWord_4329675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329675).length < 2 ^ (prefixWord ++ tailWord_4329675).sum := by decide
  have hdescent : baseEnd_4329675 < baseStart_4329675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329682 : List Nat := [3, 2, 2, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_4329682 : Nat := 118140960795 + 4329682 * 2 ^ 59
def prefixEnd_4329682 : Nat := 4983230072969 + 3 ^ 40 * 4329682 * 2
def baseEnd_4329682 : Nat := 2223207947120034332963161

theorem tailTrace_4329682 : CollatzResearch.WordTrace tailWord_4329682 prefixEnd_4329682 2223207947120034332963161 := by
  unfold tailWord_4329682
  simp only [CollatzResearch.WordTrace]
  refine ⟨39479118975077259915005825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105277650600206026440015533 39479118975077259915005825)
  ·
    refine ⟨29609339231307944936254369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39479118975077259915005825 29609339231307944936254369)
    ·
      refine ⟨22207004423480958702190777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29609339231307944936254369 22207004423480958702190777)
      ·
        refine ⟨16655253317610719026643083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22207004423480958702190777 16655253317610719026643083)
        ·
          refine ⟨24982879976416078539964625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16655253317610719026643083 24982879976416078539964625)
          ·
            refine ⟨18737159982312058904973469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24982879976416078539964625 18737159982312058904973469)
            ·
              refine ⟨7026434993367022089365051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18737159982312058904973469 7026434993367022089365051)
              ·
                refine ⟨10539652490050533134047577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7026434993367022089365051 10539652490050533134047577)
                ·
                  refine ⟨7904739367537899850535683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10539652490050533134047577 7904739367537899850535683)
                  ·
                    refine ⟨11857109051306849775803525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7904739367537899850535683 11857109051306849775803525)
                    ·
                      refine ⟨2223207947120034332963161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11857109051306849775803525 2223207947120034332963161)
                      ·
                        rfl

theorem cell23_4329682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_4329682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329682 prefixEnd_4329682 := by exact prefixLift 4329682
  have htrace : WordTrace (prefixWord ++ tailWord_4329682) baseStart_4329682 baseEnd_4329682 := by
    simpa [prefixWord, tailWord_4329682, baseEnd_4329682] using wordTrace_append hprefix tailTrace_4329682
  have hstable : (prefixWord ++ tailWord_4329682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329682).length < 2 ^ (prefixWord ++ tailWord_4329682).sum := by decide
  have hdescent : baseEnd_4329682 < baseStart_4329682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329708 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 8]
def baseStart_4329708 : Nat := 118140960795 + 4329708 * 2 ^ 59
def prefixEnd_4329708 : Nat := 4983230072969 + 3 ^ 40 * 4329708 * 2
def baseEnd_4329708 : Nat := 2223221297617051231238041

theorem tailTrace_4329708 : CollatzResearch.WordTrace tailWord_4329708 prefixEnd_4329708 2223221297617051231238041 := by
  unfold tailWord_4329708
  simp only [CollatzResearch.WordTrace]
  refine ⟨78958712099107423050234889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105278282798809897400313185 78958712099107423050234889)
  ·
    refine ⟨59219034074330567287676167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78958712099107423050234889 59219034074330567287676167)
    ·
      refine ⟨88828551111495850931514251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59219034074330567287676167 88828551111495850931514251)
      ·
        refine ⟨133242826667243776397271377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88828551111495850931514251 133242826667243776397271377)
        ·
          refine ⟨99932120000432832297953533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133242826667243776397271377 99932120000432832297953533)
          ·
            refine ⟨37474545000162312111732575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99932120000432832297953533 37474545000162312111732575)
            ·
              refine ⟨56211817500243468167598863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37474545000162312111732575 56211817500243468167598863)
              ·
                refine ⟨84317726250365202251398295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56211817500243468167598863 84317726250365202251398295)
                ·
                  refine ⟨126476589375547803377097443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84317726250365202251398295 126476589375547803377097443)
                  ·
                    refine ⟨189714884063321705065646165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 126476589375547803377097443 189714884063321705065646165)
                    ·
                      refine ⟨2223221297617051231238041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 189714884063321705065646165 2223221297617051231238041)
                      ·
                        rfl

theorem cell23_4329708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_4329708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329708 prefixEnd_4329708 := by exact prefixLift 4329708
  have htrace : WordTrace (prefixWord ++ tailWord_4329708) baseStart_4329708 baseEnd_4329708 := by
    simpa [prefixWord, tailWord_4329708, baseEnd_4329708] using wordTrace_append hprefix tailTrace_4329708
  have hstable : (prefixWord ++ tailWord_4329708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329708).length < 2 ^ (prefixWord ++ tailWord_4329708).sum := by decide
  have hdescent : baseEnd_4329708 < baseStart_4329708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329709 : List Nat := [1, 5, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_4329709 : Nat := 118140960795 + 4329709 * 2 ^ 59
def prefixEnd_4329709 : Nat := 4983230072969 + 3 ^ 40 * 4329709 * 2
def baseEnd_4329709 : Nat := 741073937032568575775179

theorem tailTrace_4329709 : CollatzResearch.WordTrace tailWord_4329709 prefixEnd_4329709 741073937032568575775179 := by
  unfold tailWord_4329709
  simp only [CollatzResearch.WordTrace]
  refine ⟨157917460671211223271256181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105278307114140815514170787 157917460671211223271256181)
  ·
    refine ⟨14804761937926052181680267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157917460671211223271256181 14804761937926052181680267)
    ·
      refine ⟨22207142906889078272520401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14804761937926052181680267 22207142906889078272520401)
      ·
        refine ⟨16655357180166808704390301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22207142906889078272520401 16655357180166808704390301)
        ·
          refine ⟨6245758942562553264146363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16655357180166808704390301 6245758942562553264146363)
          ·
            refine ⟨9368638413843829896219545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6245758942562553264146363 9368638413843829896219545)
            ·
              refine ⟨7026478810382872422164659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9368638413843829896219545 7026478810382872422164659)
              ·
                refine ⟨10539718215574308633246989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7026478810382872422164659 10539718215574308633246989)
                ·
                  refine ⟨3952394330840365737467621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10539718215574308633246989 3952394330840365737467621)
                  ·
                    refine ⟨741073937032568575775179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3952394330840365737467621 741073937032568575775179)
                    ·
                      rfl

theorem cell23_4329709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_4329709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329709 prefixEnd_4329709 := by exact prefixLift 4329709
  have htrace : WordTrace (prefixWord ++ tailWord_4329709) baseStart_4329709 baseEnd_4329709 := by
    simpa [prefixWord, tailWord_4329709, baseEnd_4329709] using wordTrace_append hprefix tailTrace_4329709
  have hstable : (prefixWord ++ tailWord_4329709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329709).length < 2 ^ (prefixWord ++ tailWord_4329709).sum := by decide
  have hdescent : baseEnd_4329709 < baseStart_4329709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329722 : List Nat := [3, 1, 1, 1, 1, 6, 3, 1, 6]
def baseStart_4329722 : Nat := 118140960795 + 4329722 * 2 ^ 59
def prefixEnd_4329722 : Nat := 4983230072969 + 3 ^ 40 * 4329722 * 2
def baseEnd_4329722 : Nat := 247025387371801575162553

theorem tailTrace_4329722 : CollatzResearch.WordTrace tailWord_4329722 prefixEnd_4329722 247025387371801575162553 := by
  unfold tailWord_4329722
  simp only [CollatzResearch.WordTrace]
  refine ⟨39479483705041031622869855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105278623213442750994319613 39479483705041031622869855)
  ·
    refine ⟨59219225557561547434304783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39479483705041031622869855 59219225557561547434304783)
    ·
      refine ⟨88828838336342321151457175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59219225557561547434304783 88828838336342321151457175)
      ·
        refine ⟨133243257504513481727185763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88828838336342321151457175 133243257504513481727185763)
        ·
          refine ⟨199864886256770222590778645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133243257504513481727185763 199864886256770222590778645)
          ·
            refine ⟨9368666543286104183942749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 199864886256770222590778645 9368666543286104183942749)
            ·
              refine ⟨3513249953732289068978531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9368666543286104183942749 3513249953732289068978531)
              ·
                refine ⟨5269874930598433603467797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3513249953732289068978531 5269874930598433603467797)
                ·
                  refine ⟨247025387371801575162553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5269874930598433603467797 247025387371801575162553)
                  ·
                    rfl

theorem cell23_4329722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 6].length) (baseStart_4329722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329722 prefixEnd_4329722 := by exact prefixLift 4329722
  have htrace : WordTrace (prefixWord ++ tailWord_4329722) baseStart_4329722 baseEnd_4329722 := by
    simpa [prefixWord, tailWord_4329722, baseEnd_4329722] using wordTrace_append hprefix tailTrace_4329722
  have hstable : (prefixWord ++ tailWord_4329722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329722).length < 2 ^ (prefixWord ++ tailWord_4329722).sum := by decide
  have hdescent : baseEnd_4329722 < baseStart_4329722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329728 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 7]
def baseStart_4329728 : Nat := 118140960795 + 4329728 * 2 ^ 59
def prefixEnd_4329728 : Nat := 4983230072969 + 3 ^ 40 * 4329728 * 2
def baseEnd_4329728 : Nat := 2223231567230141152987949

theorem tailTrace_4329728 : CollatzResearch.WordTrace tailWord_4329728 prefixEnd_4329728 2223231567230141152987949 := by
  unfold tailWord_4329728
  simp only [CollatzResearch.WordTrace]
  refine ⟨78959076829071194758098919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105278769105428259677465225 78959076829071194758098919)
  ·
    refine ⟨118438615243606792137148379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78959076829071194758098919 118438615243606792137148379)
    ·
      refine ⟨177657922865410188205722569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118438615243606792137148379 177657922865410188205722569)
      ·
        refine ⟨133243442149057641154291927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177657922865410188205722569 133243442149057641154291927)
        ·
          refine ⟨199865163223586461731437891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133243442149057641154291927 199865163223586461731437891)
          ·
            refine ⟨299797744835379692597156837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199865163223586461731437891 299797744835379692597156837)
            ·
              refine ⟨56212077156633692361966907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 299797744835379692597156837 56212077156633692361966907)
              ·
                refine ⟨84318115734950538542950361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56212077156633692361966907 84318115734950538542950361)
                ·
                  refine ⟨63238586801212903907212771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84318115734950538542950361 63238586801212903907212771)
                  ·
                    refine ⟨94857880201819355860819157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63238586801212903907212771 94857880201819355860819157)
                    ·
                      refine ⟨2223231567230141152987949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94857880201819355860819157 2223231567230141152987949)
                      ·
                        rfl

theorem cell23_4329728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_4329728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329728 prefixEnd_4329728 := by exact prefixLift 4329728
  have htrace : WordTrace (prefixWord ++ tailWord_4329728) baseStart_4329728 baseEnd_4329728 := by
    simpa [prefixWord, tailWord_4329728, baseEnd_4329728] using wordTrace_append hprefix tailTrace_4329728
  have hstable : (prefixWord ++ tailWord_4329728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329728).length < 2 ^ (prefixWord ++ tailWord_4329728).sum := by decide
  have hdescent : baseEnd_4329728 < baseStart_4329728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329742 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2]
def baseStart_4329742 : Nat := 118140960795 + 4329742 * 2 ^ 59
def prefixEnd_4329742 : Nat := 4983230072969 + 3 ^ 40 * 4329742 * 2
def baseEnd_4329742 : Nat := 2223238755959304098212885

theorem tailTrace_4329742 : CollatzResearch.WordTrace tailWord_4329742 prefixEnd_4329742 2223238755959304098212885 := by
  unfold tailWord_4329742
  simp only [CollatzResearch.WordTrace]
  refine ⟨19739833035011458738400935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105279109520061113271471653 19739833035011458738400935)
  ·
    refine ⟨29609749552517188107601403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19739833035011458738400935 29609749552517188107601403)
    ·
      refine ⟨44414624328775782161402105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29609749552517188107601403 44414624328775782161402105)
      ·
        refine ⟨33310968246581836621051579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44414624328775782161402105 33310968246581836621051579)
        ·
          refine ⟨49966452369872754931577369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33310968246581836621051579 49966452369872754931577369)
          ·
            refine ⟨37474839277404566198683027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49966452369872754931577369 37474839277404566198683027)
            ·
              refine ⟨56212258916106849298024541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37474839277404566198683027 56212258916106849298024541)
              ·
                refine ⟨21079597093540068486759203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56212258916106849298024541 21079597093540068486759203)
                ·
                  refine ⟨31619395640310102730138805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21079597093540068486759203 31619395640310102730138805)
                  ·
                    refine ⟨2964318341279072130950513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31619395640310102730138805 2964318341279072130950513)
                    ·
                      refine ⟨2223238755959304098212885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964318341279072130950513 2223238755959304098212885)
                      ·
                        rfl

theorem cell23_4329742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_4329742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329742 prefixEnd_4329742 := by exact prefixLift 4329742
  have htrace : WordTrace (prefixWord ++ tailWord_4329742) baseStart_4329742 baseEnd_4329742 := by
    simpa [prefixWord, tailWord_4329742, baseEnd_4329742] using wordTrace_append hprefix tailTrace_4329742
  have hstable : (prefixWord ++ tailWord_4329742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329742).length < 2 ^ (prefixWord ++ tailWord_4329742).sum := by decide
  have hdescent : baseEnd_4329742 < baseStart_4329742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329759 : List Nat := [1, 1, 2, 4, 3, 2, 1, 2, 2, 3, 2]
def baseStart_4329759 : Nat := 118140960795 + 4329759 * 2 ^ 59
def prefixEnd_4329759 : Nat := 4983230072969 + 3 ^ 40 * 4329759 * 2
def baseEnd_4329759 : Nat := 2223247485130430531700307

theorem tailTrace_4329759 : CollatzResearch.WordTrace tailWord_4329759 prefixEnd_4329759 2223247485130430531700307 := by
  unfold tailWord_4329759
  simp only [CollatzResearch.WordTrace]
  refine ⟨157919284321030081810576331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105279522880686721207050887 157919284321030081810576331)
  ·
    refine ⟨236878926481545122715864497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157919284321030081810576331 236878926481545122715864497)
    ·
      refine ⟨177659194861158842036898373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236878926481545122715864497 177659194861158842036898373)
      ·
        refine ⟨33311099036467282881918445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177659194861158842036898373 33311099036467282881918445)
        ·
          refine ⟨12491662138675231080719417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33311099036467282881918445 12491662138675231080719417)
          ·
            refine ⟨9368746604006423310539563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12491662138675231080719417 9368746604006423310539563)
            ·
              refine ⟨14053119906009634965809345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9368746604006423310539563 14053119906009634965809345)
              ·
                refine ⟨10539839929507226224357009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14053119906009634965809345 10539839929507226224357009)
                ·
                  refine ⟨7904879947130419668267757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10539839929507226224357009 7904879947130419668267757)
                  ·
                    refine ⟨2964329980173907375600409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7904879947130419668267757 2964329980173907375600409)
                    ·
                      refine ⟨2223247485130430531700307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964329980173907375600409 2223247485130430531700307)
                      ·
                        rfl

theorem cell23_4329759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_4329759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329759 prefixEnd_4329759 := by exact prefixLift 4329759
  have htrace : WordTrace (prefixWord ++ tailWord_4329759) baseStart_4329759 baseEnd_4329759 := by
    simpa [prefixWord, tailWord_4329759, baseEnd_4329759] using wordTrace_append hprefix tailTrace_4329759
  have hstable : (prefixWord ++ tailWord_4329759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329759).length < 2 ^ (prefixWord ++ tailWord_4329759).sum := by decide
  have hdescent : baseEnd_4329759 < baseStart_4329759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329773 : List Nat := [1, 5, 3, 1, 3, 1, 2, 1, 6]
def baseStart_4329773 : Nat := 118140960795 + 4329773 * 2 ^ 59
def prefixEnd_4329773 : Nat := 4983230072969 + 3 ^ 40 * 4329773 * 2
def baseEnd_4329773 : Nat := 247028297095510386325027

theorem tailTrace_4329773 : CollatzResearch.WordTrace tailWord_4329773 prefixEnd_4329773 247028297095510386325027 := by
  unfold tailWord_4329773
  simp only [CollatzResearch.WordTrace]
  refine ⟨157919794942979362201585973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105279863295319574801057315 157919794942979362201585973)
  ·
    refine ⟨14804980775904315206398685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157919794942979362201585973 14804980775904315206398685)
    ·
      refine ⟨5551867790964118202399507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14804980775904315206398685 5551867790964118202399507)
      ·
        refine ⟨8327801686446177303599261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5551867790964118202399507 8327801686446177303599261)
        ·
          refine ⟨3122925632417316488849723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8327801686446177303599261 3122925632417316488849723)
          ·
            refine ⟨4684388448625974733274585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3122925632417316488849723 4684388448625974733274585)
            ·
              refine ⟨3513291336469481049955939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4684388448625974733274585 3513291336469481049955939)
              ·
                refine ⟨5269937004704221574933909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3513291336469481049955939 5269937004704221574933909)
                ·
                  refine ⟨247028297095510386325027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5269937004704221574933909 247028297095510386325027)
                  ·
                    rfl

theorem cell23_4329773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_4329773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329773 prefixEnd_4329773 := by exact prefixLift 4329773
  have htrace : WordTrace (prefixWord ++ tailWord_4329773) baseStart_4329773 baseEnd_4329773 := by
    simpa [prefixWord, tailWord_4329773, baseEnd_4329773] using wordTrace_append hprefix tailTrace_4329773
  have hstable : (prefixWord ++ tailWord_4329773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329773).length < 2 ^ (prefixWord ++ tailWord_4329773).sum := by decide
  have hdescent : baseEnd_4329773 < baseStart_4329773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329775 : List Nat := [1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 5]
def baseStart_4329775 : Nat := 118140960795 + 4329775 * 2 ^ 59
def prefixEnd_4329775 : Nat := 4983230072969 + 3 ^ 40 * 4329775 * 2
def baseEnd_4329775 : Nat := 2223255700820902469100233

theorem tailTrace_4329775 : CollatzResearch.WordTrace tailWord_4329775 prefixEnd_4329775 2223255700820902469100233 := by
  unfold tailWord_4329775
  simp only [CollatzResearch.WordTrace]
  refine ⟨157919867888972116543158779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105279911925981411028772519 157919867888972116543158779)
  ·
    refine ⟨236879801833458174814738169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157919867888972116543158779 236879801833458174814738169)
    ·
      refine ⟨177659851375093631111053627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236879801833458174814738169 177659851375093631111053627)
      ·
        refine ⟨266489777062640446666580441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177659851375093631111053627 266489777062640446666580441)
        ·
          refine ⟨199867332796980334999935331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266489777062640446666580441 199867332796980334999935331)
          ·
            refine ⟨299800999195470502499902997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199867332796980334999935331 299800999195470502499902997)
            ·
              refine ⟨14053171837287679804682953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 299800999195470502499902997 14053171837287679804682953)
              ·
                refine ⟨10539878877965759853512215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14053171837287679804682953 10539878877965759853512215)
                ·
                  refine ⟨15809818316948639780268323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10539878877965759853512215 15809818316948639780268323)
                  ·
                    refine ⟨23714727475422959670402485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15809818316948639780268323 23714727475422959670402485)
                    ·
                      refine ⟨2223255700820902469100233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23714727475422959670402485 2223255700820902469100233)
                      ·
                        rfl

theorem cell23_4329775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 5].length) (baseStart_4329775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329775 prefixEnd_4329775 := by exact prefixLift 4329775
  have htrace : WordTrace (prefixWord ++ tailWord_4329775) baseStart_4329775 baseEnd_4329775 := by
    simpa [prefixWord, tailWord_4329775, baseEnd_4329775] using wordTrace_append hprefix tailTrace_4329775
  have hstable : (prefixWord ++ tailWord_4329775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329775).length < 2 ^ (prefixWord ++ tailWord_4329775).sum := by decide
  have hdescent : baseEnd_4329775 < baseStart_4329775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329792 : List Nat := [2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 3]
def baseStart_4329792 : Nat := 118140960795 + 4329792 * 2 ^ 59
def prefixEnd_4329792 : Nat := 4983230072969 + 3 ^ 40 * 4329792 * 2
def baseEnd_4329792 : Nat := 2223264429992028902587655

theorem tailTrace_4329792 : CollatzResearch.WordTrace tailWord_4329792 prefixEnd_4329792 2223264429992028902587655 := by
  unfold tailWord_4329792
  simp only [CollatzResearch.WordTrace]
  refine ⟨78960243964955264223263815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105280325286607018964351753 78960243964955264223263815)
  ·
    refine ⟨118440365947432896334895723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78960243964955264223263815 118440365947432896334895723)
    ·
      refine ⟨177660548921149344502343585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118440365947432896334895723 177660548921149344502343585)
      ·
        refine ⟨133245411690862008376757689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177660548921149344502343585 133245411690862008376757689)
        ·
          refine ⟨99934058768146506282568267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133245411690862008376757689 99934058768146506282568267)
          ·
            refine ⟨149901088152219759423852401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99934058768146506282568267 149901088152219759423852401)
            ·
              refine ⟨112425816114164819567889301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149901088152219759423852401 112425816114164819567889301)
              ·
                refine ⟨5269960130351475917244811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112425816114164819567889301 5269960130351475917244811)
                ·
                  refine ⟨7904940195527213875867217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5269960130351475917244811 7904940195527213875867217)
                  ·
                    refine ⟨5928705146645410406900413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7904940195527213875867217 5928705146645410406900413)
                    ·
                      refine ⟨2223264429992028902587655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5928705146645410406900413 2223264429992028902587655)
                      ·
                        rfl

theorem cell23_4329792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 3].length) (baseStart_4329792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329792 prefixEnd_4329792 := by exact prefixLift 4329792
  have htrace : WordTrace (prefixWord ++ tailWord_4329792) baseStart_4329792 baseEnd_4329792 := by
    simpa [prefixWord, tailWord_4329792, baseEnd_4329792] using wordTrace_append hprefix tailTrace_4329792
  have hstable : (prefixWord ++ tailWord_4329792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329792).length < 2 ^ (prefixWord ++ tailWord_4329792).sum := by decide
  have hdescent : baseEnd_4329792 < baseStart_4329792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329823 : List Nat := [1, 1, 2, 3, 1, 2, 6, 2, 1, 2, 2]
def baseStart_4329823 : Nat := 118140960795 + 4329823 * 2 ^ 59
def prefixEnd_4329823 : Nat := 4983230072969 + 3 ^ 40 * 4329823 * 2
def baseEnd_4329823 : Nat := 2223280347892318281300013

theorem tailTrace_4329823 : CollatzResearch.WordTrace tailWord_4329823 prefixEnd_4329823 2223280347892318281300013 := by
  unfold tailWord_4329823
  simp only [CollatzResearch.WordTrace]
  refine ⟨157921618592798220740906123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105281079061865480493937415 157921618592798220740906123)
  ·
    refine ⟨236882427889197331111359185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157921618592798220740906123 236882427889197331111359185)
    ·
      refine ⟨177661820916897998333519389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236882427889197331111359185 177661820916897998333519389)
      ·
        refine ⟨66623182843836749375069771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177661820916897998333519389 66623182843836749375069771)
        ·
          refine ⟨99934774265755124062604657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66623182843836749375069771 99934774265755124062604657)
          ·
            refine ⟨74951080699316343046953493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99934774265755124062604657 74951080699316343046953493)
            ·
              refine ⟨3513331907780453580325945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74951080699316343046953493 3513331907780453580325945)
              ·
                refine ⟨2634998930835340185244459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3513331907780453580325945 2634998930835340185244459)
                ·
                  refine ⟨3952498396253010277866689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2634998930835340185244459 3952498396253010277866689)
                  ·
                    refine ⟨2964373797189757708400017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3952498396253010277866689 2964373797189757708400017)
                    ·
                      refine ⟨2223280347892318281300013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964373797189757708400017 2223280347892318281300013)
                      ·
                        rfl

theorem cell23_4329823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 1, 2, 2].length) (baseStart_4329823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329823 prefixEnd_4329823 := by exact prefixLift 4329823
  have htrace : WordTrace (prefixWord ++ tailWord_4329823) baseStart_4329823 baseEnd_4329823 := by
    simpa [prefixWord, tailWord_4329823, baseEnd_4329823] using wordTrace_append hprefix tailTrace_4329823
  have hstable : (prefixWord ++ tailWord_4329823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329823).length < 2 ^ (prefixWord ++ tailWord_4329823).sum := by decide
  have hdescent : baseEnd_4329823 < baseStart_4329823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329846 : List Nat := [5, 1, 1, 4, 1, 1, 3, 7]
def baseStart_4329846 : Nat := 118140960795 + 4329846 * 2 ^ 59
def prefixEnd_4329846 : Nat := 4983230072969 + 3 ^ 40 * 4329846 * 2
def baseEnd_4329846 : Nat := 82344153998050803381941

theorem tailTrace_4329846 : CollatzResearch.WordTrace tailWord_4329846 prefixEnd_4329846 82344153998050803381941 := by
  unfold tailWord_4329846
  simp only [CollatzResearch.WordTrace]
  refine ⟨9870153591982180979312087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105281638314476597112662261 9870153591982180979312087)
  ·
    refine ⟨14805230387973271468968131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9870153591982180979312087 14805230387973271468968131)
    ·
      refine ⟨22207845581959907203452197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14805230387973271468968131 22207845581959907203452197)
      ·
        refine ⟨4163971046617482600647287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22207845581959907203452197 4163971046617482600647287)
        ·
          refine ⟨6245956569926223900970931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4163971046617482600647287 6245956569926223900970931)
          ·
            refine ⟨9368934854889335851456397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6245956569926223900970931 9368934854889335851456397)
            ·
              refine ⟨3513350570583500944296149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9368934854889335851456397 3513350570583500944296149)
              ·
                refine ⟨82344153998050803381941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3513350570583500944296149 82344153998050803381941)
                ·
                  rfl

theorem cell23_4329846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_4329846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329846 prefixEnd_4329846 := by exact prefixLift 4329846
  have htrace : WordTrace (prefixWord ++ tailWord_4329846) baseStart_4329846 baseEnd_4329846 := by
    simpa [prefixWord, tailWord_4329846, baseEnd_4329846] using wordTrace_append hprefix tailTrace_4329846
  have hstable : (prefixWord ++ tailWord_4329846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329846).length < 2 ^ (prefixWord ++ tailWord_4329846).sum := by decide
  have hdescent : baseEnd_4329846 < baseStart_4329846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329849 : List Nat := [1, 2, 1, 3, 2, 1, 1, 6, 1, 3, 2]
def baseStart_4329849 : Nat := 118140960795 + 4329849 * 2 ^ 59
def prefixEnd_4329849 : Nat := 4983230072969 + 3 ^ 40 * 4329849 * 2
def baseEnd_4329849 : Nat := 2223293698389335179574893

theorem tailTrace_4329849 : CollatzResearch.WordTrace tailWord_4329849 prefixEnd_4329849 2223293698389335179574893 := by
  unfold tailWord_4329849
  simp only [CollatzResearch.WordTrace]
  refine ⟨157922566890704027181352601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105281711260469351454235067 157922566890704027181352601)
  ·
    refine ⟨118441925168028020386014451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157922566890704027181352601 118441925168028020386014451)
    ·
      refine ⟨177662887752042030579021677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118441925168028020386014451 177662887752042030579021677)
      ·
        refine ⟨66623582907015761467133129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177662887752042030579021677 66623582907015761467133129)
        ·
          refine ⟨49967687180261821100349847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66623582907015761467133129 49967687180261821100349847)
          ·
            refine ⟨74951530770392731650524771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49967687180261821100349847 74951530770392731650524771)
            ·
              refine ⟨112427296155589097475787157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74951530770392731650524771 112427296155589097475787157)
              ·
                refine ⟨5270029507293238944177523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112427296155589097475787157 5270029507293238944177523)
                ·
                  refine ⟨7905044260939858416266285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5270029507293238944177523 7905044260939858416266285)
                  ·
                    refine ⟨2964391597852446906099857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7905044260939858416266285 2964391597852446906099857)
                    ·
                      refine ⟨2223293698389335179574893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964391597852446906099857 2223293698389335179574893)
                      ·
                        rfl

theorem cell23_4329849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_4329849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329849 prefixEnd_4329849 := by exact prefixLift 4329849
  have htrace : WordTrace (prefixWord ++ tailWord_4329849) baseStart_4329849 baseEnd_4329849 := by
    simpa [prefixWord, tailWord_4329849, baseEnd_4329849] using wordTrace_append hprefix tailTrace_4329849
  have hstable : (prefixWord ++ tailWord_4329849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329849).length < 2 ^ (prefixWord ++ tailWord_4329849).sum := by decide
  have hdescent : baseEnd_4329849 < baseStart_4329849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329892 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_4329892 : Nat := 118140960795 + 4329892 * 2 ^ 59
def prefixEnd_4329892 : Nat := 4983230072969 + 3 ^ 40 * 4329892 * 2
def baseEnd_4329892 : Nat := 2223315778057478511337195

theorem tailTrace_4329892 : CollatzResearch.WordTrace tailWord_4329892 prefixEnd_4329892 2223315778057478511337195 := by
  unfold tailWord_4329892
  simp only [CollatzResearch.WordTrace]
  refine ⟨78962067614774122762583965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105282756819698830350111953 78962067614774122762583965)
  ·
    refine ⟨29610775355540296035968987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78962067614774122762583965 29610775355540296035968987)
    ·
      refine ⟨44416163033310444053953481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29610775355540296035968987 44416163033310444053953481)
      ·
        refine ⟨33312122274982833040465111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44416163033310444053953481 33312122274982833040465111)
        ·
          refine ⟨49968183412474249560697667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33312122274982833040465111 49968183412474249560697667)
          ·
            refine ⟨74952275118711374341046501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49968183412474249560697667 74952275118711374341046501)
            ·
              refine ⟨14053551584758382688946219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74952275118711374341046501 14053551584758382688946219)
              ·
                refine ⟨21080327377137574033419329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14053551584758382688946219 21080327377137574033419329)
                ·
                  refine ⟨15810245532853180525064497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21080327377137574033419329 15810245532853180525064497)
                  ·
                    refine ⟨11857684149639885393798373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15810245532853180525064497 11857684149639885393798373)
                    ·
                      refine ⟨2223315778057478511337195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11857684149639885393798373 2223315778057478511337195)
                      ·
                        rfl

theorem cell23_4329892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_4329892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329892 prefixEnd_4329892 := by exact prefixLift 4329892
  have htrace : WordTrace (prefixWord ++ tailWord_4329892) baseStart_4329892 baseEnd_4329892 := by
    simpa [prefixWord, tailWord_4329892, baseEnd_4329892] using wordTrace_append hprefix tailTrace_4329892
  have hstable : (prefixWord ++ tailWord_4329892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329892).length < 2 ^ (prefixWord ++ tailWord_4329892).sum := by decide
  have hdescent : baseEnd_4329892 < baseStart_4329892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329925 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 5, 1, 7]
def baseStart_4329925 : Nat := 118140960795 + 4329925 * 2 ^ 59
def prefixEnd_4329925 : Nat := 4983230072969 + 3 ^ 40 * 4329925 * 2
def baseEnd_4329925 : Nat := 2223332722919076882224543

theorem tailTrace_4329925 : CollatzResearch.WordTrace tailWord_4329925 prefixEnd_4329925 2223332722919076882224543 := by
  unfold tailWord_4329925
  simp only [CollatzResearch.WordTrace]
  refine ⟨157925338838428692161119229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105283559225619128107412819 157925338838428692161119229)
  ·
    refine ⟨59222002064410759560419711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157925338838428692161119229 59222002064410759560419711)
    ·
      refine ⟨88833003096616139340629567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59222002064410759560419711 88833003096616139340629567)
      ·
        refine ⟨133249504644924209010944351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88833003096616139340629567 133249504644924209010944351)
        ·
          refine ⟨199874256967386313516416527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133249504644924209010944351 199874256967386313516416527)
          ·
            refine ⟨299811385451079470274624791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199874256967386313516416527 299811385451079470274624791)
            ·
              refine ⟨449717078176619205411937187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299811385451079470274624791 449717078176619205411937187)
              ·
                refine ⟨674575617264928808117905781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449717078176619205411937187 674575617264928808117905781)
                ·
                  refine ⟨63241464118587075761053667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 674575617264928808117905781 63241464118587075761053667)
                  ·
                    refine ⟨94862196177880613641580501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63241464118587075761053667 94862196177880613641580501)
                    ·
                      refine ⟨2223332722919076882224543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94862196177880613641580501 2223332722919076882224543)
                      ·
                        rfl

theorem cell23_4329925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_4329925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329925 prefixEnd_4329925 := by exact prefixLift 4329925
  have htrace : WordTrace (prefixWord ++ tailWord_4329925) baseStart_4329925 baseEnd_4329925 := by
    simpa [prefixWord, tailWord_4329925, baseEnd_4329925] using wordTrace_append hprefix tailTrace_4329925
  have hstable : (prefixWord ++ tailWord_4329925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329925).length < 2 ^ (prefixWord ++ tailWord_4329925).sum := by decide
  have hdescent : baseEnd_4329925 < baseStart_4329925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329952 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 4]
def baseStart_4329952 : Nat := 118140960795 + 4329952 * 2 ^ 59
def prefixEnd_4329952 : Nat := 4983230072969 + 3 ^ 40 * 4329952 * 2
def baseEnd_4329952 : Nat := 2223346586896748276586919

theorem tailTrace_4329952 : CollatzResearch.WordTrace tailWord_4329952 prefixEnd_4329952 2223346586896748276586919 := by
  unfold tailWord_4329952
  simp only [CollatzResearch.WordTrace]
  refine ⟨78963161804665437886176055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105284215739553917181568073 78963161804665437886176055)
  ·
    refine ⟨118444742706998156829264083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78963161804665437886176055 118444742706998156829264083)
    ·
      refine ⟨177667114060497235243896125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118444742706998156829264083 177667114060497235243896125)
      ·
        refine ⟨66625167772686463216461047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177667114060497235243896125 66625167772686463216461047)
        ·
          refine ⟨99937751659029694824691571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66625167772686463216461047 99937751659029694824691571)
          ·
            refine ⟨149906627488544542237037357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99937751659029694824691571 149906627488544542237037357)
            ·
              refine ⟨56214985308204203338889009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149906627488544542237037357 56214985308204203338889009)
              ·
                refine ⟨42161238981153152504166757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56214985308204203338889009 42161238981153152504166757)
                ·
                  refine ⟨7905232308966216094531267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42161238981153152504166757 7905232308966216094531267)
                  ·
                    refine ⟨11857848463449324141796901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7905232308966216094531267 11857848463449324141796901)
                    ·
                      refine ⟨2223346586896748276586919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11857848463449324141796901 2223346586896748276586919)
                      ·
                        rfl

theorem cell23_4329952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_4329952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329952 prefixEnd_4329952 := by exact prefixLift 4329952
  have htrace : WordTrace (prefixWord ++ tailWord_4329952) baseStart_4329952 baseEnd_4329952 := by
    simpa [prefixWord, tailWord_4329952, baseEnd_4329952] using wordTrace_append hprefix tailTrace_4329952
  have hstable : (prefixWord ++ tailWord_4329952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329952).length < 2 ^ (prefixWord ++ tailWord_4329952).sum := by decide
  have hdescent : baseEnd_4329952 < baseStart_4329952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329969 : List Nat := [1, 2, 2, 2, 3, 1, 4, 1, 2, 1, 4]
def baseStart_4329969 : Nat := 118140960795 + 4329969 * 2 ^ 59
def prefixEnd_4329969 : Nat := 4983230072969 + 3 ^ 40 * 4329969 * 2
def baseEnd_4329969 : Nat := 2223355316067874710074341

theorem tailTrace_4329969 : CollatzResearch.WordTrace tailWord_4329969 prefixEnd_4329969 2223355316067874710074341 := by
  unfold tailWord_4329969
  simp only [CollatzResearch.WordTrace]
  refine ⟨157926943650269287675720961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105284629100179525117147307 157926943650269287675720961)
  ·
    refine ⟨118445207737701965756790721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157926943650269287675720961 118445207737701965756790721)
    ·
      refine ⟨88833905803276474317593041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118445207737701965756790721 88833905803276474317593041)
      ·
        refine ⟨66625429352457355738194781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88833905803276474317593041 66625429352457355738194781)
        ·
          refine ⟨24984536007171508401823043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66625429352457355738194781 24984536007171508401823043)
          ·
            refine ⟨37476804010757262602734565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24984536007171508401823043 37476804010757262602734565)
            ·
              refine ⟨7026900752016986738012731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37476804010757262602734565 7026900752016986738012731)
              ·
                refine ⟨10540351128025480107019097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7026900752016986738012731 10540351128025480107019097)
                ·
                  refine ⟨7905263346019110080264323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10540351128025480107019097 7905263346019110080264323)
                  ·
                    refine ⟨11857895019028665120396485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7905263346019110080264323 11857895019028665120396485)
                    ·
                      refine ⟨2223355316067874710074341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11857895019028665120396485 2223355316067874710074341)
                      ·
                        rfl

theorem cell23_4329969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_4329969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329969 prefixEnd_4329969 := by exact prefixLift 4329969
  have htrace : WordTrace (prefixWord ++ tailWord_4329969) baseStart_4329969 baseEnd_4329969 := by
    simpa [prefixWord, tailWord_4329969, baseEnd_4329969] using wordTrace_append hprefix tailTrace_4329969
  have hstable : (prefixWord ++ tailWord_4329969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329969).length < 2 ^ (prefixWord ++ tailWord_4329969).sum := by decide
  have hdescent : baseEnd_4329969 < baseStart_4329969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329989 : List Nat := [1, 3, 1, 1, 2, 2, 4, 2, 2, 2, 3]
def baseStart_4329989 : Nat := 118140960795 + 4329989 * 2 ^ 59
def prefixEnd_4329989 : Nat := 4983230072969 + 3 ^ 40 * 4329989 * 2
def baseEnd_4329989 : Nat := 2223365585680964631824249

theorem tailTrace_4329989 : CollatzResearch.WordTrace tailWord_4329989 prefixEnd_4329989 2223365585680964631824249 := by
  unfold tailWord_4329989
  simp only [CollatzResearch.WordTrace]
  refine ⟨157927673110196831091449021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105285115406797887394299347 157927673110196831091449021)
  ·
    refine ⟨59222877416323811659293383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157927673110196831091449021 59222877416323811659293383)
    ·
      refine ⟨88834316124485717488940075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59222877416323811659293383 88834316124485717488940075)
      ·
        refine ⟨133251474186728576233410113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88834316124485717488940075 133251474186728576233410113)
        ·
          refine ⟨99938605640046432175057585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133251474186728576233410113 99938605640046432175057585)
          ·
            refine ⟨74953954230034824131293189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99938605640046432175057585 74953954230034824131293189)
            ·
              refine ⟨14053866418131529524617473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74953954230034824131293189 14053866418131529524617473)
              ·
                refine ⟨10540399813598647143463105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14053866418131529524617473 10540399813598647143463105)
                ·
                  refine ⟨7905299860198985357597329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10540399813598647143463105 7905299860198985357597329)
                  ·
                    refine ⟨5928974895149239018197997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7905299860198985357597329 5928974895149239018197997)
                    ·
                      refine ⟨2223365585680964631824249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5928974895149239018197997 2223365585680964631824249)
                      ·
                        rfl

theorem cell23_4329989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_4329989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329989 prefixEnd_4329989 := by exact prefixLift 4329989
  have htrace : WordTrace (prefixWord ++ tailWord_4329989) baseStart_4329989 baseEnd_4329989 := by
    simpa [prefixWord, tailWord_4329989, baseEnd_4329989] using wordTrace_append hprefix tailTrace_4329989
  have hstable : (prefixWord ++ tailWord_4329989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329989).length < 2 ^ (prefixWord ++ tailWord_4329989).sum := by decide
  have hdescent : baseEnd_4329989 < baseStart_4329989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329990 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_4329990 : Nat := 118140960795 + 4329990 * 2 ^ 59
def prefixEnd_4329990 : Nat := 4983230072969 + 3 ^ 40 * 4329990 * 2
def baseEnd_4329990 : Nat := 2223366099161619127911745

theorem tailTrace_4329990 : CollatzResearch.WordTrace tailWord_4329990 prefixEnd_4329990 2223366099161619127911745 := by
  unfold tailWord_4329990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4935240924474787758194857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 105285139722128805508156949 4935240924474787758194857)
  ·
    refine ⟨3701430693356090818646143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4935240924474787758194857 3701430693356090818646143)
    ·
      refine ⟨5552146040034136227969215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3701430693356090818646143 5552146040034136227969215)
      ·
        refine ⟨8328219060051204341953823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5552146040034136227969215 8328219060051204341953823)
        ·
          refine ⟨12492328590076806512930735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8328219060051204341953823 12492328590076806512930735)
          ·
            refine ⟨18738492885115209769396103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12492328590076806512930735 18738492885115209769396103)
            ·
              refine ⟨28107739327672814654094155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18738492885115209769396103 28107739327672814654094155)
              ·
                refine ⟨42161608991509221981141233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28107739327672814654094155 42161608991509221981141233)
                ·
                  refine ⟨31621206743631916485855925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42161608991509221981141233 31621206743631916485855925)
                  ·
                    refine ⟨2964488132215492170548993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31621206743631916485855925 2964488132215492170548993)
                    ·
                      refine ⟨2223366099161619127911745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964488132215492170548993 2223366099161619127911745)
                      ·
                        rfl

theorem cell23_4329990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_4329990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329990 prefixEnd_4329990 := by exact prefixLift 4329990
  have htrace : WordTrace (prefixWord ++ tailWord_4329990) baseStart_4329990 baseEnd_4329990 := by
    simpa [prefixWord, tailWord_4329990, baseEnd_4329990] using wordTrace_append hprefix tailTrace_4329990
  have hstable : (prefixWord ++ tailWord_4329990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329990).length < 2 ^ (prefixWord ++ tailWord_4329990).sum := by decide
  have hdescent : baseEnd_4329990 < baseStart_4329990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330020 : List Nat := [2, 3, 1, 5, 2, 1, 1, 1, 2, 1, 4]
def baseStart_4330020 : Nat := 118140960795 + 4330020 * 2 ^ 59
def prefixEnd_4330020 : Nat := 4983230072969 + 3 ^ 40 * 4330020 * 2
def baseEnd_4330020 : Nat := 2223381503581254010536607

theorem tailTrace_4330020 : CollatzResearch.WordTrace tailWord_4330020 prefixEnd_4330020 2223381503581254010536607 := by
  unfold tailWord_4330020
  simp only [CollatzResearch.WordTrace]
  refine ⟨78964401886542261692913757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105285869182056348923885009 78964401886542261692913757)
  ·
    refine ⟨29611650707453348134842659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78964401886542261692913757 29611650707453348134842659)
    ·
      refine ⟨44417476061180022202263989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29611650707453348134842659 44417476061180022202263989)
      ·
        refine ⟨4164138380735627081462249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44417476061180022202263989 4164138380735627081462249)
        ·
          refine ⟨3123103785551720311096687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4164138380735627081462249 3123103785551720311096687)
          ·
            refine ⟨4684655678327580466645031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3123103785551720311096687 4684655678327580466645031)
            ·
              refine ⟨7026983517491370699967547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4684655678327580466645031 7026983517491370699967547)
              ·
                refine ⟨10540475276237056049951321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7026983517491370699967547 10540475276237056049951321)
                ·
                  refine ⟨7905356457177792037463491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10540475276237056049951321 7905356457177792037463491)
                  ·
                    refine ⟨11858034685766688056195237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7905356457177792037463491 11858034685766688056195237)
                    ·
                      refine ⟨2223381503581254010536607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11858034685766688056195237 2223381503581254010536607)
                      ·
                        rfl

theorem cell23_4330020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_4330020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330020 prefixEnd_4330020 := by exact prefixLift 4330020
  have htrace : WordTrace (prefixWord ++ tailWord_4330020) baseStart_4330020 baseEnd_4330020 := by
    simpa [prefixWord, tailWord_4330020, baseEnd_4330020] using wordTrace_append hprefix tailTrace_4330020
  have hstable : (prefixWord ++ tailWord_4330020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330020).length < 2 ^ (prefixWord ++ tailWord_4330020).sum := by decide
  have hdescent : baseEnd_4330020 < baseStart_4330020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330023 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_4330023 : Nat := 118140960795 + 4330023 * 2 ^ 59
def prefixEnd_4330023 : Nat := 4983230072969 + 3 ^ 40 * 4330023 * 2
def baseEnd_4330023 : Nat := 2223383044023217498799093

theorem tailTrace_4330023 : CollatzResearch.WordTrace tailWord_4330023 prefixEnd_4330023 2223383044023217498799093 := by
  unfold tailWord_4330023
  simp only [CollatzResearch.WordTrace]
  refine ⟨157928913192073654898186723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105285942128049103265457815 157928913192073654898186723)
  ·
    refine ⟨236893369788110482347280085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157928913192073654898186723 236893369788110482347280085)
    ·
      refine ⟨5552188354408839430014377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 236893369788110482347280085 5552188354408839430014377)
      ·
        refine ⟨4164141265806629572510783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5552188354408839430014377 4164141265806629572510783)
        ·
          refine ⟨6246211898709944358766175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4164141265806629572510783 6246211898709944358766175)
          ·
            refine ⟨9369317848064916538149263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6246211898709944358766175 9369317848064916538149263)
            ·
              refine ⟨14053976772097374807223895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9369317848064916538149263 14053976772097374807223895)
              ·
                refine ⟨21080965158146062210835843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14053976772097374807223895 21080965158146062210835843)
                ·
                  refine ⟨31621447737219093316253765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21080965158146062210835843 31621447737219093316253765)
                  ·
                    refine ⟨5929021450728579996797581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31621447737219093316253765 5929021450728579996797581)
                    ·
                      refine ⟨2223383044023217498799093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5929021450728579996797581 2223383044023217498799093)
                      ·
                        rfl

theorem cell23_4330023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_4330023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330023 prefixEnd_4330023 := by exact prefixLift 4330023
  have htrace : WordTrace (prefixWord ++ tailWord_4330023) baseStart_4330023 baseEnd_4330023 := by
    simpa [prefixWord, tailWord_4330023, baseEnd_4330023] using wordTrace_append hprefix tailTrace_4330023
  have hstable : (prefixWord ++ tailWord_4330023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330023).length < 2 ^ (prefixWord ++ tailWord_4330023).sum := by decide
  have hdescent : baseEnd_4330023 < baseStart_4330023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330030 : List Nat := [4, 1, 3, 1, 3, 1, 2, 3, 1, 4]
def baseStart_4330030 : Nat := 118140960795 + 4330030 * 2 ^ 59
def prefixEnd_4330030 : Nat := 4983230072969 + 3 ^ 40 * 4330030 * 2
def baseEnd_4330030 : Nat := 741128879462599657137187

theorem tailTrace_4330030 : CollatzResearch.WordTrace tailWord_4330030 prefixEnd_4330030 741128879462599657137187 := by
  unfold tailWord_4330030
  simp only [CollatzResearch.WordTrace]
  refine ⟨19741146062881036886711443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105286112335365530062461029 19741146062881036886711443)
  ·
    refine ⟨29611719094321555330067165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19741146062881036886711443 29611719094321555330067165)
    ·
      refine ⟨11104394660370583248775187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29611719094321555330067165 11104394660370583248775187)
      ·
        refine ⟨16656591990555874873162781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11104394660370583248775187 16656591990555874873162781)
        ·
          refine ⟨6246221996458453077436043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16656591990555874873162781 6246221996458453077436043)
          ·
            refine ⟨9369332994687679616154065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6246221996458453077436043 9369332994687679616154065)
            ·
              refine ⟨7026999746015759712115549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9369332994687679616154065 7026999746015759712115549)
              ·
                refine ⟨2635124904755909892043331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7026999746015759712115549 2635124904755909892043331)
                ·
                  refine ⟨3952687357133864838064997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2635124904755909892043331 3952687357133864838064997)
                  ·
                    refine ⟨741128879462599657137187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3952687357133864838064997 741128879462599657137187)
                    ·
                      rfl

theorem cell23_4330030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_4330030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330030 prefixEnd_4330030 := by exact prefixLift 4330030
  have htrace : WordTrace (prefixWord ++ tailWord_4330030) baseStart_4330030 baseEnd_4330030 := by
    simpa [prefixWord, tailWord_4330030, baseEnd_4330030] using wordTrace_append hprefix tailTrace_4330030
  have hstable : (prefixWord ++ tailWord_4330030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330030).length < 2 ^ (prefixWord ++ tailWord_4330030).sum := by decide
  have hdescent : baseEnd_4330030 < baseStart_4330030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330039 : List Nat := [1, 1, 3, 1, 2, 3, 3, 3, 1, 5]
def baseStart_4330039 : Nat := 118140960795 + 4330039 * 2 ^ 59
def prefixEnd_4330039 : Nat := 4983230072969 + 3 ^ 40 * 4330039 * 2
def baseEnd_4330039 : Nat := 741130419904563145399673

theorem tailTrace_4330039 : CollatzResearch.WordTrace tailWord_4330039 prefixEnd_4330039 741130419904563145399673 := by
  unfold tailWord_4330039
  simp only [CollatzResearch.WordTrace]
  refine ⟨157929496760015689630769171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105286331173343793087179447 157929496760015689630769171)
  ·
    refine ⟨236894245140023534446153757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157929496760015689630769171 236894245140023534446153757)
    ·
      refine ⟨88835341927508825417307659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236894245140023534446153757 88835341927508825417307659)
      ·
        refine ⟨133253012891263238125961489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88835341927508825417307659 133253012891263238125961489)
        ·
          refine ⟨99939759668447428594471117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133253012891263238125961489 99939759668447428594471117)
          ·
            refine ⟨37477409875667785722926669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99939759668447428594471117 37477409875667785722926669)
            ·
              refine ⟨14054028703375419646097501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37477409875667785722926669 14054028703375419646097501)
              ·
                refine ⟨5270260763765782367286563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14054028703375419646097501 5270260763765782367286563)
                ·
                  refine ⟨7905391145648673550929845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5270260763765782367286563 7905391145648673550929845)
                  ·
                    refine ⟨741130419904563145399673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7905391145648673550929845 741130419904563145399673)
                    ·
                      rfl

theorem cell23_4330039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_4330039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330039 prefixEnd_4330039 := by exact prefixLift 4330039
  have htrace : WordTrace (prefixWord ++ tailWord_4330039) baseStart_4330039 baseEnd_4330039 := by
    simpa [prefixWord, tailWord_4330039, baseEnd_4330039] using wordTrace_append hprefix tailTrace_4330039
  have hstable : (prefixWord ++ tailWord_4330039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330039).length < 2 ^ (prefixWord ++ tailWord_4330039).sum := by decide
  have hdescent : baseEnd_4330039 < baseStart_4330039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330053 : List Nat := [1, 3, 1, 1, 1, 5, 2, 4, 1, 1, 3]
def baseStart_4330053 : Nat := 118140960795 + 4330053 * 2 ^ 59
def prefixEnd_4330053 : Nat := 4983230072969 + 3 ^ 40 * 4330053 * 2
def baseEnd_4330053 : Nat := 2223398448442852381423955

theorem tailTrace_4330053 : CollatzResearch.WordTrace tailWord_4330053 prefixEnd_4330053 2223398448442852381423955 := by
  unfold tailWord_4330053
  simp only [CollatzResearch.WordTrace]
  refine ⟨157930007381964970021778813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105286671587976646681185875 157930007381964970021778813)
  ·
    refine ⟨59223752768236863758167055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157930007381964970021778813 59223752768236863758167055)
    ·
      refine ⟨88835629152355295637250583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59223752768236863758167055 88835629152355295637250583)
      ·
        refine ⟨133253443728532943455875875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88835629152355295637250583 133253443728532943455875875)
        ·
          refine ⟨199880165592799415183813813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133253443728532943455875875 199880165592799415183813813)
          ·
            refine ⟨18738765524324945173482545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 199880165592799415183813813 18738765524324945173482545)
            ·
              refine ⟨14054074143243708880111909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18738765524324945173482545 14054074143243708880111909)
              ·
                refine ⟨2635138901858195415020983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14054074143243708880111909 2635138901858195415020983)
                ·
                  refine ⟨3952708352787293122531475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2635138901858195415020983 3952708352787293122531475)
                  ·
                    refine ⟨5929062529180939683797213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3952708352787293122531475 5929062529180939683797213)
                    ·
                      refine ⟨2223398448442852381423955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5929062529180939683797213 2223398448442852381423955)
                      ·
                        rfl

theorem cell23_4330053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 1, 1, 3].length) (baseStart_4330053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330053 prefixEnd_4330053 := by exact prefixLift 4330053
  have htrace : WordTrace (prefixWord ++ tailWord_4330053) baseStart_4330053 baseEnd_4330053 := by
    simpa [prefixWord, tailWord_4330053, baseEnd_4330053] using wordTrace_append hprefix tailTrace_4330053
  have hstable : (prefixWord ++ tailWord_4330053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330053).length < 2 ^ (prefixWord ++ tailWord_4330053).sum := by decide
  have hdescent : baseEnd_4330053 < baseStart_4330053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330069 : List Nat := [1, 3, 2, 2, 1, 1, 5, 1, 1, 6]
def baseStart_4330069 : Nat := 118140960795 + 4330069 * 2 ^ 59
def prefixEnd_4330069 : Nat := 4983230072969 + 3 ^ 40 * 4330069 * 2
def baseEnd_4330069 : Nat := 741135554711108106274627

theorem tailTrace_4330069 : CollatzResearch.WordTrace tailWord_4330069 prefixEnd_4330069 741135554711108106274627 := by
  unfold tailWord_4330069
  simp only [CollatzResearch.WordTrace]
  refine ⟨157930590949907004754361261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105287060633271336502907507 157930590949907004754361261)
  ·
    refine ⟨59223971606215126782885473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157930590949907004754361261 59223971606215126782885473)
    ·
      refine ⟨44417978704661345087164105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59223971606215126782885473 44417978704661345087164105)
      ·
        refine ⟨33313484028496008815373079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44417978704661345087164105 33313484028496008815373079)
        ·
          refine ⟨49970226042744013223059619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33313484028496008815373079 49970226042744013223059619)
          ·
            refine ⟨74955339064116019834589429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49970226042744013223059619 74955339064116019834589429)
            ·
              refine ⟨7027063037260876859492759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74955339064116019834589429 7027063037260876859492759)
              ·
                refine ⟨10540594555891315289239139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7027063037260876859492759 10540594555891315289239139)
                ·
                  refine ⟨15810891833836972933858709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10540594555891315289239139 15810891833836972933858709)
                  ·
                    refine ⟨741135554711108106274627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15810891833836972933858709 741135554711108106274627)
                    ·
                      rfl

theorem cell23_4330069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_4330069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330069 prefixEnd_4330069 := by exact prefixLift 4330069
  have htrace : WordTrace (prefixWord ++ tailWord_4330069) baseStart_4330069 baseEnd_4330069 := by
    simpa [prefixWord, tailWord_4330069, baseEnd_4330069] using wordTrace_append hprefix tailTrace_4330069
  have hstable : (prefixWord ++ tailWord_4330069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330069).length < 2 ^ (prefixWord ++ tailWord_4330069).sum := by decide
  have hdescent : baseEnd_4330069 < baseStart_4330069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330079 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 3]
def baseStart_4330079 : Nat := 118140960795 + 4330079 * 2 ^ 59
def prefixEnd_4330079 : Nat := 4983230072969 + 3 ^ 40 * 4330079 * 2
def baseEnd_4330079 : Nat := 2223411798939869279698835

theorem tailTrace_4330079 : CollatzResearch.WordTrace tailWord_4330079 prefixEnd_4330079 2223411798939869279698835 := by
  unfold tailWord_4330079
  simp only [CollatzResearch.WordTrace]
  refine ⟨157930955679870776462225291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105287303786580517641483527 157930955679870776462225291)
  ·
    refine ⟨236896433519806164693337937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157930955679870776462225291 236896433519806164693337937)
    ·
      refine ⟨177672325139854623520003453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236896433519806164693337937 177672325139854623520003453)
      ·
        refine ⟨66627121927445483820001295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177672325139854623520003453 66627121927445483820001295)
        ·
          refine ⟨99940682891168225730001943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66627121927445483820001295 99940682891168225730001943)
          ·
            refine ⟨149911024336752338595002915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99940682891168225730001943 149911024336752338595002915)
            ·
              refine ⟨224866536505128507892504373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149911024336752338595002915 224866536505128507892504373)
              ·
                refine ⟨21081237797355797614922285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 224866536505128507892504373 21081237797355797614922285)
                ·
                  refine ⟨7905464174008424105595857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21081237797355797614922285 7905464174008424105595857)
                  ·
                    refine ⟨5929098130506318079196893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7905464174008424105595857 5929098130506318079196893)
                    ·
                      refine ⟨2223411798939869279698835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5929098130506318079196893 2223411798939869279698835)
                      ·
                        rfl

theorem cell23_4330079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_4330079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330079 prefixEnd_4330079 := by exact prefixLift 4330079
  have htrace : WordTrace (prefixWord ++ tailWord_4330079) baseStart_4330079 baseEnd_4330079 := by
    simpa [prefixWord, tailWord_4330079, baseEnd_4330079] using wordTrace_append hprefix tailTrace_4330079
  have hstable : (prefixWord ++ tailWord_4330079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330079).length < 2 ^ (prefixWord ++ tailWord_4330079).sum := by decide
  have hdescent : baseEnd_4330079 < baseStart_4330079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330096 : List Nat := [2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 5]
def baseStart_4330096 : Nat := 118140960795 + 4330096 * 2 ^ 59
def prefixEnd_4330096 : Nat := 4983230072969 + 3 ^ 40 * 4330096 * 2
def baseEnd_4330096 : Nat := 2223420528110995713186257

theorem tailTrace_4330096 : CollatzResearch.WordTrace tailWord_4330096 prefixEnd_4330096 2223420528110995713186257 := by
  unfold tailWord_4330096
  simp only [CollatzResearch.WordTrace]
  refine ⟨78965787860404594182797071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105287717147206125577062761 78965787860404594182797071)
  ·
    refine ⟨118448681790606891274195607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78965787860404594182797071 118448681790606891274195607)
    ·
      refine ⟨177673022685910336911293411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118448681790606891274195607 177673022685910336911293411)
      ·
        refine ⟨266509534028865505366940117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177673022685910336911293411 266509534028865505366940117)
        ·
          refine ⟨6246317203801535282037659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 266509534028865505366940117 6246317203801535282037659)
          ·
            refine ⟨9369475805702302923056489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6246317203801535282037659 9369475805702302923056489)
            ·
              refine ⟨7027106854276727192292367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9369475805702302923056489 7027106854276727192292367)
              ·
                refine ⟨10540660281415090788438551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7027106854276727192292367 10540660281415090788438551)
                ·
                  refine ⟨15810990422122636182657827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10540660281415090788438551 15810990422122636182657827)
                  ·
                    refine ⟨23716485633183954273986741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15810990422122636182657827 23716485633183954273986741)
                    ·
                      refine ⟨2223420528110995713186257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23716485633183954273986741 2223420528110995713186257)
                      ·
                        rfl

theorem cell23_4330096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 5].length) (baseStart_4330096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330096 prefixEnd_4330096 := by exact prefixLift 4330096
  have htrace : WordTrace (prefixWord ++ tailWord_4330096) baseStart_4330096 baseEnd_4330096 := by
    simpa [prefixWord, tailWord_4330096, baseEnd_4330096] using wordTrace_append hprefix tailTrace_4330096
  have hstable : (prefixWord ++ tailWord_4330096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330096).length < 2 ^ (prefixWord ++ tailWord_4330096).sum := by decide
  have hdescent : baseEnd_4330096 < baseStart_4330096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330126 : List Nat := [4, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3]
def baseStart_4330126 : Nat := 118140960795 + 4330126 * 2 ^ 59
def prefixEnd_4330126 : Nat := 4983230072969 + 3 ^ 40 * 4330126 * 2
def baseEnd_4330126 : Nat := 2223435932530630595811119

theorem tailTrace_4330126 : CollatzResearch.WordTrace tailWord_4330126 prefixEnd_4330126 2223435932530630595811119 := by
  unfold tailWord_4330126
  simp only [CollatzResearch.WordTrace]
  refine ⟨19741583738837562936148279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105288446607133668992790821 19741583738837562936148279)
  ·
    refine ⟨29612375608256344404222419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19741583738837562936148279 29612375608256344404222419)
    ·
      refine ⟨44418563412384516606333629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29612375608256344404222419 44418563412384516606333629)
      ·
        refine ⟨16656961279644193727375111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44418563412384516606333629 16656961279644193727375111)
        ·
          refine ⟨24985441919466290591062667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16656961279644193727375111 24985441919466290591062667)
          ·
            refine ⟨37478162879199435886594001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24985441919466290591062667 37478162879199435886594001)
            ·
              refine ⟨28108622159399576914945501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37478162879199435886594001 28108622159399576914945501)
              ·
                refine ⟨10540733309774841343104563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28108622159399576914945501 10540733309774841343104563)
                ·
                  refine ⟨15811099964662262014656845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10540733309774841343104563 15811099964662262014656845)
                  ·
                    refine ⟨5929162486748348255496317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15811099964662262014656845 5929162486748348255496317)
                    ·
                      refine ⟨2223435932530630595811119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5929162486748348255496317 2223435932530630595811119)
                      ·
                        rfl

theorem cell23_4330126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_4330126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330126 prefixEnd_4330126 := by exact prefixLift 4330126
  have htrace : WordTrace (prefixWord ++ tailWord_4330126) baseStart_4330126 baseEnd_4330126 := by
    simpa [prefixWord, tailWord_4330126, baseEnd_4330126] using wordTrace_append hprefix tailTrace_4330126
  have hstable : (prefixWord ++ tailWord_4330126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330126).length < 2 ^ (prefixWord ++ tailWord_4330126).sum := by decide
  have hdescent : baseEnd_4330126 < baseStart_4330126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330130 : List Nat := [3, 2, 3, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_4330130 : Nat := 118140960795 + 4330130 * 2 ^ 59
def prefixEnd_4330130 : Nat := 4983230072969 + 3 ^ 40 * 4330130 * 2
def baseEnd_4330130 : Nat := 2223437986453248580161101

theorem tailTrace_4330130 : CollatzResearch.WordTrace tailWord_4330130 prefixEnd_4330130 2223437986453248580161101 := by
  unfold tailWord_4330130
  simp only [CollatzResearch.WordTrace]
  refine ⟨39483203950671503043082961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105288543868457341448221229 39483203950671503043082961)
  ·
    refine ⟨29612402963003627282312221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39483203950671503043082961 29612402963003627282312221)
    ·
      refine ⟨11104651111126360230867083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29612402963003627282312221 11104651111126360230867083)
      ·
        refine ⟨16656976666689540346300625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11104651111126360230867083 16656976666689540346300625)
        ·
          refine ⟨12492732500017155259725469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16656976666689540346300625 12492732500017155259725469)
          ·
            refine ⟨4684774687506433222397051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12492732500017155259725469 4684774687506433222397051)
            ·
              refine ⟨7027162031259649833595577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4684774687506433222397051 7027162031259649833595577)
              ·
                refine ⟨5270371523444737375196683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7027162031259649833595577 5270371523444737375196683)
                ·
                  refine ⟨7905557285167106062795025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5270371523444737375196683 7905557285167106062795025)
                  ·
                    refine ⟨5929167963875329547096269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7905557285167106062795025 5929167963875329547096269)
                    ·
                      refine ⟨2223437986453248580161101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5929167963875329547096269 2223437986453248580161101)
                      ·
                        rfl

theorem cell23_4330130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_4330130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330130 prefixEnd_4330130 := by exact prefixLift 4330130
  have htrace : WordTrace (prefixWord ++ tailWord_4330130) baseStart_4330130 baseEnd_4330130 := by
    simpa [prefixWord, tailWord_4330130, baseEnd_4330130] using wordTrace_append hprefix tailTrace_4330130
  have hstable : (prefixWord ++ tailWord_4330130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330130).length < 2 ^ (prefixWord ++ tailWord_4330130).sum := by decide
  have hdescent : baseEnd_4330130 < baseStart_4330130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330161 : List Nat := [1, 2, 2, 6, 1, 2, 2, 2, 1, 2, 2]
def baseStart_4330161 : Nat := 118140960795 + 4330161 * 2 ^ 59
def prefixEnd_4330161 : Nat := 4983230072969 + 3 ^ 40 * 4330161 * 2
def baseEnd_4330161 : Nat := 2223453904353537958873459

theorem tailTrace_4330161 : CollatzResearch.WordTrace tailWord_4330161 prefixEnd_4330161 2223453904353537958873459 := by
  unfold tailWord_4330161
  simp only [CollatzResearch.WordTrace]
  refine ⟨157933946465573704466710337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105289297643715802977806891 157933946465573704466710337)
  ·
    refine ⟨118450459849180278350032753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157933946465573704466710337 118450459849180278350032753)
    ·
      refine ⟨88837844886885208762524565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118450459849180278350032753 88837844886885208762524565)
      ·
        refine ⟨4164273979072744160743339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88837844886885208762524565 4164273979072744160743339)
        ·
          refine ⟨6246410968609116241115009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4164273979072744160743339 6246410968609116241115009)
          ·
            refine ⟨4684808226456837180836257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6246410968609116241115009 4684808226456837180836257)
            ·
              refine ⟨3513606169842627885627193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4684808226456837180836257 3513606169842627885627193)
              ·
                refine ⟨2635204627381970914220395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3513606169842627885627193 2635204627381970914220395)
                ·
                  refine ⟨3952806941072956371330593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2635204627381970914220395 3952806941072956371330593)
                  ·
                    refine ⟨2964605205804717278497945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3952806941072956371330593 2964605205804717278497945)
                    ·
                      refine ⟨2223453904353537958873459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964605205804717278497945 2223453904353537958873459)
                      ·
                        rfl

theorem cell23_4330161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_4330161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330161 prefixEnd_4330161 := by exact prefixLift 4330161
  have htrace : WordTrace (prefixWord ++ tailWord_4330161) baseStart_4330161 baseEnd_4330161 := by
    simpa [prefixWord, tailWord_4330161, baseEnd_4330161] using wordTrace_append hprefix tailTrace_4330161
  have hstable : (prefixWord ++ tailWord_4330161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330161).length < 2 ^ (prefixWord ++ tailWord_4330161).sum := by decide
  have hdescent : baseEnd_4330161 < baseStart_4330161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330204 : List Nat := [2, 2, 5, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_4330204 : Nat := 118140960795 + 4330204 * 2 ^ 59
def prefixEnd_4330204 : Nat := 4983230072969 + 3 ^ 40 * 4330204 * 2
def baseEnd_4330204 : Nat := 2223475984021681290635761

theorem tailTrace_4330204 : CollatzResearch.WordTrace tailWord_4330204 prefixEnd_4330204 2223475984021681290635761 := by
  unfold tailWord_4330204
  simp only [CollatzResearch.WordTrace]
  refine ⟨78967757402208961405262833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105290343202945281873683777 78967757402208961405262833)
  ·
    refine ⟨59225818051656721053947125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78967757402208961405262833 59225818051656721053947125)
    ·
      refine ⟨5552420442342817598807543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59225818051656721053947125 5552420442342817598807543)
      ·
        refine ⟨8328630663514226398211315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5552420442342817598807543 8328630663514226398211315)
        ·
          refine ⟨12492945995271339597316973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8328630663514226398211315 12492945995271339597316973)
          ·
            refine ⟨4684854748226752348993865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12492945995271339597316973 4684854748226752348993865)
            ·
              refine ⟨3513641061170064261745399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4684854748226752348993865 3513641061170064261745399)
              ·
                refine ⟨5270461591755096392618099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3513641061170064261745399 5270461591755096392618099)
                ·
                  refine ⟨7905692387632644588927149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5270461591755096392618099 7905692387632644588927149)
                  ·
                    refine ⟨2964634645362241720847681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7905692387632644588927149 2964634645362241720847681)
                    ·
                      refine ⟨2223475984021681290635761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964634645362241720847681 2223475984021681290635761)
                      ·
                        rfl

theorem cell23_4330204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_4330204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330204 prefixEnd_4330204 := by exact prefixLift 4330204
  have htrace : WordTrace (prefixWord ++ tailWord_4330204) baseStart_4330204 baseEnd_4330204 := by
    simpa [prefixWord, tailWord_4330204, baseEnd_4330204] using wordTrace_append hprefix tailTrace_4330204
  have hstable : (prefixWord ++ tailWord_4330204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330204).length < 2 ^ (prefixWord ++ tailWord_4330204).sum := by decide
  have hdescent : baseEnd_4330204 < baseStart_4330204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330219 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 4, 5]
def baseStart_4330219 : Nat := 118140960795 + 4330219 * 2 ^ 59
def prefixEnd_4330219 : Nat := 4983230072969 + 3 ^ 40 * 4330219 * 2
def baseEnd_4330219 : Nat := 741161228743832910649397

theorem tailTrace_4330219 : CollatzResearch.WordTrace tailWord_4330219 prefixEnd_4330219 741161228743832910649397 := by
  unfold tailWord_4330219
  simp only [CollatzResearch.WordTrace]
  refine ⟨157936061899363580372321711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105290707932909053581547807 157936061899363580372321711)
  ·
    refine ⟨236904092849045370558482567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157936061899363580372321711 236904092849045370558482567)
    ·
      refine ⟨355356139273568055837723851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236904092849045370558482567 355356139273568055837723851)
      ·
        refine ⟨533034208910352083756585777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355356139273568055837723851 533034208910352083756585777)
        ·
          refine ⟨399775656682764062817439333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 533034208910352083756585777 399775656682764062817439333)
          ·
            refine ⟨74957935628018261778269875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 399775656682764062817439333 74957935628018261778269875)
            ·
              refine ⟨112436903442027392667404813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74957935628018261778269875 112436903442027392667404813)
              ·
                refine ⟨42163838790760272250276805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112436903442027392667404813 42163838790760272250276805)
                ·
                  refine ⟨7905719773267551046926901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42163838790760272250276805 7905719773267551046926901)
                  ·
                    refine ⟨741161228743832910649397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7905719773267551046926901 741161228743832910649397)
                    ·
                      rfl

theorem cell23_4330219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 5].length) (baseStart_4330219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330219 prefixEnd_4330219 := by exact prefixLift 4330219
  have htrace : WordTrace (prefixWord ++ tailWord_4330219) baseStart_4330219 baseEnd_4330219 := by
    simpa [prefixWord, tailWord_4330219, baseEnd_4330219] using wordTrace_append hprefix tailTrace_4330219
  have hstable : (prefixWord ++ tailWord_4330219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330219).length < 2 ^ (prefixWord ++ tailWord_4330219).sum := by decide
  have hdescent : baseEnd_4330219 < baseStart_4330219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330296 : List Nat := [2, 1, 2, 1, 3, 2, 3, 3, 6]
def baseStart_4330296 : Nat := 118140960795 + 4330296 * 2 ^ 59
def prefixEnd_4330296 : Nat := 4983230072969 + 3 ^ 40 * 4330296 * 2
def baseEnd_4330296 : Nat := 247058136026877214520593

theorem tailTrace_4330296 : CollatzResearch.WordTrace tailWord_4330296 prefixEnd_4330296 247058136026877214520593 := by
  unfold tailWord_4330296
  simp only [CollatzResearch.WordTrace]
  refine ⟨78969435160042311261437371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105292580213389748348583161 78969435160042311261437371)
  ·
    refine ⟨118454152740063466892156057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78969435160042311261437371 118454152740063466892156057)
    ·
      refine ⟨88840614555047600169117043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118454152740063466892156057 88840614555047600169117043)
      ·
        refine ⟨133260921832571400253675565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88840614555047600169117043 133260921832571400253675565)
        ·
          refine ⟨49972845687214275095128337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133260921832571400253675565 49972845687214275095128337)
          ·
            refine ⟨37479634265410706321346253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49972845687214275095128337 37479634265410706321346253)
            ·
              refine ⟨14054862849529014870504845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37479634265410706321346253 14054862849529014870504845)
              ·
                refine ⟨5270573568573380576439317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14054862849529014870504845 5270573568573380576439317)
                ·
                  refine ⟨247058136026877214520593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5270573568573380576439317 247058136026877214520593)
                  ·
                    rfl

theorem cell23_4330296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 6].length) (baseStart_4330296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330296 prefixEnd_4330296 := by exact prefixLift 4330296
  have htrace : WordTrace (prefixWord ++ tailWord_4330296) baseStart_4330296 baseEnd_4330296 := by
    simpa [prefixWord, tailWord_4330296, baseEnd_4330296] using wordTrace_append hprefix tailTrace_4330296
  have hstable : (prefixWord ++ tailWord_4330296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330296).length < 2 ^ (prefixWord ++ tailWord_4330296).sum := by decide
  have hdescent : baseEnd_4330296 < baseStart_4330296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330319 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 7]
def baseStart_4330319 : Nat := 118140960795 + 4330319 * 2 ^ 59
def prefixEnd_4330319 : Nat := 4983230072969 + 3 ^ 40 * 4330319 * 2
def baseEnd_4330319 : Nat := 2223535034296948340697731

theorem tailTrace_4330319 : CollatzResearch.WordTrace tailWord_4330319 prefixEnd_4330319 2223535034296948340697731 := by
  unfold tailWord_4330319
  simp only [CollatzResearch.WordTrace]
  refine ⟨157939709199001297450962011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105293139466000864967308007 157939709199001297450962011)
  ·
    refine ⟨236909563798501946176443017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157939709199001297450962011 236909563798501946176443017)
    ·
      refine ⟨177682172848876459632332263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236909563798501946176443017 177682172848876459632332263)
      ·
        refine ⟨266523259273314689448498395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177682172848876459632332263 266523259273314689448498395)
        ·
          refine ⟨399784888909972034172747593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266523259273314689448498395 399784888909972034172747593)
          ·
            refine ⟨299838666682479025629560695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399784888909972034172747593 299838666682479025629560695)
            ·
              refine ⟨449758000023718538444341043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299838666682479025629560695 449758000023718538444341043)
              ·
                refine ⟨674637000035577807666511565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449758000023718538444341043 674637000035577807666511565)
                ·
                  refine ⟨252988875013341677874941837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 674637000035577807666511565 252988875013341677874941837)
                  ·
                    refine ⟨94870828130003129203103189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 252988875013341677874941837 94870828130003129203103189)
                    ·
                      refine ⟨2223535034296948340697731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94870828130003129203103189 2223535034296948340697731)
                      ·
                        rfl

theorem cell23_4330319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_4330319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330319 prefixEnd_4330319 := by exact prefixLift 4330319
  have htrace : WordTrace (prefixWord ++ tailWord_4330319) baseStart_4330319 baseEnd_4330319 := by
    simpa [prefixWord, tailWord_4330319, baseEnd_4330319] using wordTrace_append hprefix tailTrace_4330319
  have hstable : (prefixWord ++ tailWord_4330319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330319).length < 2 ^ (prefixWord ++ tailWord_4330319).sum := by decide
  have hdescent : baseEnd_4330319 < baseStart_4330319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330380 : List Nat := [2, 2, 1, 2, 1, 2, 6, 1, 1, 1, 4]
def baseStart_4330380 : Nat := 118140960795 + 4330380 * 2 ^ 59
def prefixEnd_4330380 : Nat := 4983230072969 + 3 ^ 40 * 4330380 * 2
def baseEnd_4330380 : Nat := 2223566356616872602034951

theorem tailTrace_4330380 : CollatzResearch.WordTrace tailWord_4330380 prefixEnd_4330380 2223566356616872602034951 := by
  unfold tailWord_4330380
  simp only [CollatzResearch.WordTrace]
  refine ⟨78970967025890152434466297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105294622701186869912621729 78970967025890152434466297)
  ·
    refine ⟨59228225269417614325849723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78970967025890152434466297 59228225269417614325849723)
    ·
      refine ⟨88842337904126421488774585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59228225269417614325849723 88842337904126421488774585)
      ·
        refine ⟨66631753428094816116580939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88842337904126421488774585 66631753428094816116580939)
        ·
          refine ⟨99947630142142224174871409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66631753428094816116580939 99947630142142224174871409)
          ·
            refine ⟨74960722606606668131153557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99947630142142224174871409 74960722606606668131153557)
            ·
              refine ⟨3513783872184687568647823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74960722606606668131153557 3513783872184687568647823)
              ·
                refine ⟨5270675808277031352971735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3513783872184687568647823 5270675808277031352971735)
                ·
                  refine ⟨7906013712415547029457603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5270675808277031352971735 7906013712415547029457603)
                  ·
                    refine ⟨11859020568623320544186405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7906013712415547029457603 11859020568623320544186405)
                    ·
                      refine ⟨2223566356616872602034951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11859020568623320544186405 2223566356616872602034951)
                      ·
                        rfl

theorem cell23_4330380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_4330380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330380 prefixEnd_4330380 := by exact prefixLift 4330380
  have htrace : WordTrace (prefixWord ++ tailWord_4330380) baseStart_4330380 baseEnd_4330380 := by
    simpa [prefixWord, tailWord_4330380, baseEnd_4330380] using wordTrace_append hprefix tailTrace_4330380
  have hstable : (prefixWord ++ tailWord_4330380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330380).length < 2 ^ (prefixWord ++ tailWord_4330380).sum := by decide
  have hdescent : baseEnd_4330380 < baseStart_4330380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330397 : List Nat := [1, 4, 2, 1, 2, 1, 4, 1, 3, 2, 2]
def baseStart_4330397 : Nat := 118140960795 + 4330397 * 2 ^ 59
def prefixEnd_4330397 : Nat := 4983230072969 + 3 ^ 40 * 4330397 * 2
def baseEnd_4330397 : Nat := 2223575085787999035522373

theorem tailTrace_4330397 : CollatzResearch.WordTrace tailWord_4330397 prefixEnd_4330397 2223575085787999035522373 := by
  unfold tailWord_4330397
  simp only [CollatzResearch.WordTrace]
  refine ⟨157942554092718716772301445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105295036061812477848200963 157942554092718716772301445)
  ·
    refine ⟨29614228892384759394806521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157942554092718716772301445 29614228892384759394806521)
    ·
      refine ⟨22210671669288569546104891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29614228892384759394806521 22210671669288569546104891)
      ·
        refine ⟨33316007503932854319157337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22210671669288569546104891 33316007503932854319157337)
        ·
          refine ⟨24987005627949640739368003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33316007503932854319157337 24987005627949640739368003)
          ·
            refine ⟨37480508441924461109052005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24987005627949640739368003 37480508441924461109052005)
            ·
              refine ⟨7027595332860836457947251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37480508441924461109052005 7027595332860836457947251)
              ·
                refine ⟨10541392999291254686920877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7027595332860836457947251 10541392999291254686920877)
                ·
                  refine ⟨3953022374734220507595329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10541392999291254686920877 3953022374734220507595329)
                  ·
                    refine ⟨2964766781050665380696497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3953022374734220507595329 2964766781050665380696497)
                    ·
                      refine ⟨2223575085787999035522373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964766781050665380696497 2223575085787999035522373)
                      ·
                        rfl

theorem cell23_4330397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_4330397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330397 prefixEnd_4330397 := by exact prefixLift 4330397
  have htrace : WordTrace (prefixWord ++ tailWord_4330397) baseStart_4330397 baseEnd_4330397 := by
    simpa [prefixWord, tailWord_4330397, baseEnd_4330397] using wordTrace_append hprefix tailTrace_4330397
  have hstable : (prefixWord ++ tailWord_4330397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330397).length < 2 ^ (prefixWord ++ tailWord_4330397).sum := by decide
  have hdescent : baseEnd_4330397 < baseStart_4330397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330407 : List Nat := [1, 1, 6, 1, 4, 1, 1, 1, 1, 6]
def baseStart_4330407 : Nat := 118140960795 + 4330407 * 2 ^ 59
def prefixEnd_4330407 : Nat := 4983230072969 + 3 ^ 40 * 4330407 * 2
def baseEnd_4330407 : Nat := 741193406864847998799109

theorem tailTrace_4330407 : CollatzResearch.WordTrace tailWord_4330407 prefixEnd_4330407 741193406864847998799109 := by
  unfold tailWord_4330407
  simp only [CollatzResearch.WordTrace]
  refine ⟨157942918822682488480165475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105295279215121658986776983 157942918822682488480165475)
  ·
    refine ⟨236914378234023732720248213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157942918822682488480165475 236914378234023732720248213)
    ·
      refine ⟨11105361479719862471261635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 236914378234023732720248213 11105361479719862471261635)
      ·
        refine ⟨16658042219579793706892453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11105361479719862471261635 16658042219579793706892453)
        ·
          refine ⟨3123382916171211320042335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16658042219579793706892453 3123382916171211320042335)
          ·
            refine ⟨4685074374256816980063503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3123382916171211320042335 4685074374256816980063503)
            ·
              refine ⟨7027611561385225470095255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4685074374256816980063503 7027611561385225470095255)
              ·
                refine ⟨10541417342077838205142883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7027611561385225470095255 10541417342077838205142883)
                ·
                  refine ⟨15812126013116757307714325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10541417342077838205142883 15812126013116757307714325)
                  ·
                    refine ⟨741193406864847998799109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15812126013116757307714325 741193406864847998799109)
                    ·
                      rfl

theorem cell23_4330407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_4330407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330407 prefixEnd_4330407 := by exact prefixLift 4330407
  have htrace : WordTrace (prefixWord ++ tailWord_4330407) baseStart_4330407 baseEnd_4330407 := by
    simpa [prefixWord, tailWord_4330407, baseEnd_4330407] using wordTrace_append hprefix tailTrace_4330407
  have hstable : (prefixWord ++ tailWord_4330407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330407).length < 2 ^ (prefixWord ++ tailWord_4330407).sum := by decide
  have hdescent : baseEnd_4330407 < baseStart_4330407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330417 : List Nat := [1, 2, 2, 4, 3, 1, 2, 2, 1, 2, 3]
def baseStart_4330417 : Nat := 118140960795 + 4330417 * 2 ^ 59
def prefixEnd_4330417 : Nat := 4983230072969 + 3 ^ 40 * 4330417 * 2
def baseEnd_4330417 : Nat := 2223585355401088957272281

theorem tailTrace_4330417 : CollatzResearch.WordTrace tailWord_4330417 prefixEnd_4330417 2223585355401088957272281 := by
  unfold tailWord_4330417
  simp only [CollatzResearch.WordTrace]
  refine ⟨157943283552646260188029505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105295522368430840125353003 157943283552646260188029505)
  ·
    refine ⟨118457462664484695141022129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157943283552646260188029505 118457462664484695141022129)
    ·
      refine ⟨88843096998363521355766597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118457462664484695141022129 88843096998363521355766597)
      ·
        refine ⟨16658080687193160254206237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88843096998363521355766597 16658080687193160254206237)
        ·
          refine ⟨6246780257697435095327339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16658080687193160254206237 6246780257697435095327339)
          ·
            refine ⟨9370170386546152642991009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6246780257697435095327339 9370170386546152642991009)
            ·
              refine ⟨7027627789909614482243257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9370170386546152642991009 7027627789909614482243257)
              ·
                refine ⟨5270720842432210861682443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7027627789909614482243257 5270720842432210861682443)
                ·
                  refine ⟨7906081263648316292523665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5270720842432210861682443 7906081263648316292523665)
                  ·
                    refine ⟨5929560947736237219392749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7906081263648316292523665 5929560947736237219392749)
                    ·
                      refine ⟨2223585355401088957272281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5929560947736237219392749 2223585355401088957272281)
                      ·
                        rfl

theorem cell23_4330417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_4330417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330417 prefixEnd_4330417 := by exact prefixLift 4330417
  have htrace : WordTrace (prefixWord ++ tailWord_4330417) baseStart_4330417 baseEnd_4330417 := by
    simpa [prefixWord, tailWord_4330417, baseEnd_4330417] using wordTrace_append hprefix tailTrace_4330417
  have hstable : (prefixWord ++ tailWord_4330417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330417).length < 2 ^ (prefixWord ++ tailWord_4330417).sum := by decide
  have hdescent : baseEnd_4330417 < baseStart_4330417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330420 : List Nat := [2, 5, 2, 1, 1, 2, 1, 9]
def baseStart_4330420 : Nat := 118140960795 + 4330420 * 2 ^ 59
def prefixEnd_4330420 : Nat := 4983230072969 + 3 ^ 40 * 4330420 * 2
def baseEnd_4330420 : Nat := 82355070216409349834621

theorem tailTrace_4330420 : CollatzResearch.WordTrace tailWord_4330420 prefixEnd_4330420 82355070216409349834621 := by
  unfold tailWord_4330420
  simp only [CollatzResearch.WordTrace]
  refine ⟨78971696485817695850194357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105295595314423594466925809 78971696485817695850194357)
  ·
    refine ⟨7403596545545408985955721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78971696485817695850194357 7403596545545408985955721)
    ·
      refine ⟨5552697409159056739466791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7403596545545408985955721 5552697409159056739466791)
      ·
        refine ⟨8329046113738585109200187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5552697409159056739466791 8329046113738585109200187)
        ·
          refine ⟨12493569170607877663800281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8329046113738585109200187 12493569170607877663800281)
          ·
            refine ⟨9370176877955908247850211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12493569170607877663800281 9370176877955908247850211)
            ·
              refine ⟨14055265316933862371775317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9370176877955908247850211 14055265316933862371775317)
              ·
                refine ⟨82355070216409349834621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14055265316933862371775317 82355070216409349834621)
                ·
                  rfl

theorem cell23_4330420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 9].length) (baseStart_4330420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330420 prefixEnd_4330420 := by exact prefixLift 4330420
  have htrace : WordTrace (prefixWord ++ tailWord_4330420) baseStart_4330420 baseEnd_4330420 := by
    simpa [prefixWord, tailWord_4330420, baseEnd_4330420] using wordTrace_append hprefix tailTrace_4330420
  have hstable : (prefixWord ++ tailWord_4330420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330420).length < 2 ^ (prefixWord ++ tailWord_4330420).sum := by decide
  have hdescent : baseEnd_4330420 < baseStart_4330420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330426 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5]
def baseStart_4330426 : Nat := 118140960795 + 4330426 * 2 ^ 59
def prefixEnd_4330426 : Nat := 4983230072969 + 3 ^ 40 * 4330426 * 2
def baseEnd_4330426 : Nat := 2223589976726979422059739

theorem tailTrace_4330426 : CollatzResearch.WordTrace tailWord_4330426 prefixEnd_4330426 2223589976726979422059739 := by
  unfold tailWord_4330426
  simp only [CollatzResearch.WordTrace]
  refine ⟨39485902952403413681276783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105295741206409103150071421 39485902952403413681276783)
  ·
    refine ⟨59228854428605120521915175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39485902952403413681276783 59228854428605120521915175)
    ·
      refine ⟨88843281642907680782872763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59228854428605120521915175 88843281642907680782872763)
      ·
        refine ⟨133264922464361521174309145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88843281642907680782872763 133264922464361521174309145)
        ·
          refine ⟨99948691848271140880731859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133264922464361521174309145 99948691848271140880731859)
          ·
            refine ⟨149923037772406711321097789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99948691848271140880731859 149923037772406711321097789)
            ·
              refine ⟨56221139164652516745411671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149923037772406711321097789 56221139164652516745411671)
              ·
                refine ⟨84331708746978775118117507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56221139164652516745411671 84331708746978775118117507)
                ·
                  refine ⟨126497563120468162677176261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84331708746978775118117507 126497563120468162677176261)
                  ·
                    refine ⟨23718293085087780501970549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 126497563120468162677176261 23718293085087780501970549)
                    ·
                      refine ⟨2223589976726979422059739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23718293085087780501970549 2223589976726979422059739)
                      ·
                        rfl

theorem cell23_4330426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_4330426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330426 prefixEnd_4330426 := by exact prefixLift 4330426
  have htrace : WordTrace (prefixWord ++ tailWord_4330426) baseStart_4330426 baseEnd_4330426 := by
    simpa [prefixWord, tailWord_4330426, baseEnd_4330426] using wordTrace_append hprefix tailTrace_4330426
  have hstable : (prefixWord ++ tailWord_4330426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330426).length < 2 ^ (prefixWord ++ tailWord_4330426).sum := by decide
  have hdescent : baseEnd_4330426 < baseStart_4330426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330430 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_4330430 : Nat := 118140960795 + 4330430 * 2 ^ 59
def prefixEnd_4330430 : Nat := 4983230072969 + 3 ^ 40 * 4330430 * 2
def baseEnd_4330430 : Nat := 2223592030649597406409721

theorem tailTrace_4330430 : CollatzResearch.WordTrace tailWord_4330430 prefixEnd_4330430 2223592030649597406409721 := by
  unfold tailWord_4330430
  simp only [CollatzResearch.WordTrace]
  refine ⟨19742969712699895426031593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105295838467732775605501829 19742969712699895426031593)
  ·
    refine ⟨14807227284524921569523695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19742969712699895426031593 14807227284524921569523695)
    ·
      refine ⟨22210840926787382354285543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14807227284524921569523695 22210840926787382354285543)
      ·
        refine ⟨33316261390181073531428315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22210840926787382354285543 33316261390181073531428315)
        ·
          refine ⟨49974392085271610297142473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33316261390181073531428315 49974392085271610297142473)
          ·
            refine ⟨37480794063953707722856855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49974392085271610297142473 37480794063953707722856855)
            ·
              refine ⟨56221191095930561584285283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37480794063953707722856855 56221191095930561584285283)
              ·
                refine ⟨84331786643895842376427925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56221191095930561584285283 84331786643895842376427925)
                ·
                  refine ⟨3953052498932617611395059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84331786643895842376427925 3953052498932617611395059)
                  ·
                    refine ⟨5929578748398926417092589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3953052498932617611395059 5929578748398926417092589)
                    ·
                      refine ⟨2223592030649597406409721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5929578748398926417092589 2223592030649597406409721)
                      ·
                        rfl

theorem cell23_4330430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_4330430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330430 prefixEnd_4330430 := by exact prefixLift 4330430
  have htrace : WordTrace (prefixWord ++ tailWord_4330430) baseStart_4330430 baseEnd_4330430 := by
    simpa [prefixWord, tailWord_4330430, baseEnd_4330430] using wordTrace_append hprefix tailTrace_4330430
  have hstable : (prefixWord ++ tailWord_4330430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330430).length < 2 ^ (prefixWord ++ tailWord_4330430).sum := by decide
  have hdescent : baseEnd_4330430 < baseStart_4330430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330474 : List Nat := [3, 1, 3, 1, 2, 4, 1, 2, 1, 3, 2]
def baseStart_4330474 : Nat := 118140960795 + 4330474 * 2 ^ 59
def prefixEnd_4330474 : Nat := 4983230072969 + 3 ^ 40 * 4330474 * 2
def baseEnd_4330474 : Nat := 2223614623798395234259519

theorem tailTrace_4330474 : CollatzResearch.WordTrace tailWord_4330474 prefixEnd_4330474 2223614623798395234259519 := by
  unfold tailWord_4330474
  simp only [CollatzResearch.WordTrace]
  refine ⟨39486340628359939730713619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105296908342293172615236317 39486340628359939730713619)
  ·
    refine ⟨59229510942539909596070429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39486340628359939730713619 59229510942539909596070429)
    ·
      refine ⟨22211066603452466098526411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59229510942539909596070429 22211066603452466098526411)
      ·
        refine ⟨33316599905178699147789617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22211066603452466098526411 33316599905178699147789617)
        ·
          refine ⟨24987449928884024360842213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33316599905178699147789617 24987449928884024360842213)
          ·
            refine ⟨4685146861665754567657915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24987449928884024360842213 4685146861665754567657915)
            ·
              refine ⟨7027720292498631851486873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4685146861665754567657915 7027720292498631851486873)
              ·
                refine ⟨5270790219373973888615155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7027720292498631851486873 5270790219373973888615155)
                ·
                  refine ⟨7906185329060960832922733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5270790219373973888615155 7906185329060960832922733)
                  ·
                    refine ⟨2964819498397860312346025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7906185329060960832922733 2964819498397860312346025)
                    ·
                      refine ⟨2223614623798395234259519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964819498397860312346025 2223614623798395234259519)
                      ·
                        rfl

theorem cell23_4330474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_4330474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330474 prefixEnd_4330474 := by exact prefixLift 4330474
  have htrace : WordTrace (prefixWord ++ tailWord_4330474) baseStart_4330474 baseEnd_4330474 := by
    simpa [prefixWord, tailWord_4330474, baseEnd_4330474] using wordTrace_append hprefix tailTrace_4330474
  have hstable : (prefixWord ++ tailWord_4330474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330474).length < 2 ^ (prefixWord ++ tailWord_4330474).sum := by decide
  have hdescent : baseEnd_4330474 < baseStart_4330474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330496 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 8]
def baseStart_4330496 : Nat := 118140960795 + 4330496 * 2 ^ 59
def prefixEnd_4330496 : Nat := 4983230072969 + 3 ^ 40 * 4330496 * 2
def baseEnd_4330496 : Nat := 2223625920372794148184417

theorem tailTrace_4330496 : CollatzResearch.WordTrace tailWord_4330496 prefixEnd_4330496 2223625920372794148184417 := by
  unfold tailWord_4330496
  simp only [CollatzResearch.WordTrace]
  refine ⟨78973082459680028340077671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105297443279573371120103561 78973082459680028340077671)
  ·
    refine ⟨118459623689520042510116507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78973082459680028340077671 118459623689520042510116507)
    ·
      refine ⟨177689435534280063765174761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118459623689520042510116507 177689435534280063765174761)
      ·
        refine ⟨133267076650710047823881071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177689435534280063765174761 133267076650710047823881071)
        ·
          refine ⟨199900614976065071735821607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133267076650710047823881071 199900614976065071735821607)
          ·
            refine ⟨299850922464097607603732411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199900614976065071735821607 299850922464097607603732411)
            ·
              refine ⟨449776383696146411405598617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299850922464097607603732411 449776383696146411405598617)
              ·
                refine ⟨337332287772109808554198963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 449776383696146411405598617 337332287772109808554198963)
                ·
                  refine ⟨505998431658164712831298445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 337332287772109808554198963 505998431658164712831298445)
                  ·
                    refine ⟨189749411871811767311736917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 505998431658164712831298445 189749411871811767311736917)
                    ·
                      refine ⟨2223625920372794148184417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 189749411871811767311736917 2223625920372794148184417)
                      ·
                        rfl

theorem cell23_4330496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_4330496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330496 prefixEnd_4330496 := by exact prefixLift 4330496
  have htrace : WordTrace (prefixWord ++ tailWord_4330496) baseStart_4330496 baseEnd_4330496 := by
    simpa [prefixWord, tailWord_4330496, baseEnd_4330496] using wordTrace_append hprefix tailTrace_4330496
  have hstable : (prefixWord ++ tailWord_4330496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330496).length < 2 ^ (prefixWord ++ tailWord_4330496).sum := by decide
  have hdescent : baseEnd_4330496 < baseStart_4330496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330504 : List Nat := [2, 1, 3, 2, 1, 4, 2, 2, 2, 2, 2]
def baseStart_4330504 : Nat := 118140960795 + 4330504 * 2 ^ 59
def prefixEnd_4330504 : Nat := 4983230072969 + 3 ^ 40 * 4330504 * 2
def baseEnd_4330504 : Nat := 2223630028218030116884381

theorem tailTrace_4330504 : CollatzResearch.WordTrace tailWord_4330504 prefixEnd_4330504 2223630028218030116884381 := by
  unfold tailWord_4330504
  simp only [CollatzResearch.WordTrace]
  refine ⟨78973228351665537023223283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105297637802220716030964377 78973228351665537023223283)
  ·
    refine ⟨118459842527498305534834925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78973228351665537023223283 118459842527498305534834925)
    ·
      refine ⟨44422440947811864575563097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118459842527498305534834925 44422440947811864575563097)
      ·
        refine ⟨33316830710858898431672323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44422440947811864575563097 33316830710858898431672323)
        ·
          refine ⟨49975246066288347647508485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33316830710858898431672323 49975246066288347647508485)
          ·
            refine ⟨9370358637429065183907841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49975246066288347647508485 9370358637429065183907841)
            ·
              refine ⟨7027768978071798887930881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9370358637429065183907841 7027768978071798887930881)
              ·
                refine ⟨5270826733553849165948161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7027768978071798887930881 5270826733553849165948161)
                ·
                  refine ⟨3953120050165386874461121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5270826733553849165948161 3953120050165386874461121)
                  ·
                    refine ⟨2964840037624040155845841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3953120050165386874461121 2964840037624040155845841)
                    ·
                      refine ⟨2223630028218030116884381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964840037624040155845841 2223630028218030116884381)
                      ·
                        rfl

theorem cell23_4330504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_4330504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330504 prefixEnd_4330504 := by exact prefixLift 4330504
  have htrace : WordTrace (prefixWord ++ tailWord_4330504) baseStart_4330504 baseEnd_4330504 := by
    simpa [prefixWord, tailWord_4330504, baseEnd_4330504] using wordTrace_append hprefix tailTrace_4330504
  have hstable : (prefixWord ++ tailWord_4330504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330504).length < 2 ^ (prefixWord ++ tailWord_4330504).sum := by decide
  have hdescent : baseEnd_4330504 < baseStart_4330504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330514 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 2, 6]
def baseStart_4330514 : Nat := 118140960795 + 4330514 * 2 ^ 59
def prefixEnd_4330514 : Nat := 4983230072969 + 3 ^ 40 * 4330514 * 2
def baseEnd_4330514 : Nat := 741211721008191692586445

theorem tailTrace_4330514 : CollatzResearch.WordTrace tailWord_4330514 prefixEnd_4330514 741211721008191692586445 := by
  unfold tailWord_4330514
  simp only [CollatzResearch.WordTrace]
  refine ⟨39486705358323711438577649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105297880955529897169540397 39486705358323711438577649)
  ·
    refine ⟨29615029018742783578933237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39486705358323711438577649 29615029018742783578933237)
    ·
      refine ⟨2776408970507135960524991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29615029018742783578933237 2776408970507135960524991)
      ·
        refine ⟨4164613455760703940787487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2776408970507135960524991 4164613455760703940787487)
        ·
          refine ⟨6246920183641055911181231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4164613455760703940787487 6246920183641055911181231)
          ·
            refine ⟨9370380275461583866771847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6246920183641055911181231 9370380275461583866771847)
            ·
              refine ⟨14055570413192375800157771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9370380275461583866771847 14055570413192375800157771)
              ·
                refine ⟨21083355619788563700236657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14055570413192375800157771 21083355619788563700236657)
                ·
                  refine ⟨15812516714841422775177493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21083355619788563700236657 15812516714841422775177493)
                  ·
                    refine ⟨741211721008191692586445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15812516714841422775177493 741211721008191692586445)
                    ·
                      rfl

theorem cell23_4330514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_4330514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330514 prefixEnd_4330514 := by exact prefixLift 4330514
  have htrace : WordTrace (prefixWord ++ tailWord_4330514) baseStart_4330514 baseEnd_4330514 := by
    simpa [prefixWord, tailWord_4330514, baseEnd_4330514] using wordTrace_append hprefix tailTrace_4330514
  have hstable : (prefixWord ++ tailWord_4330514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330514).length < 2 ^ (prefixWord ++ tailWord_4330514).sum := by decide
  have hdescent : baseEnd_4330514 < baseStart_4330514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330520 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 2, 3, 3]
def baseStart_4330520 : Nat := 118140960795 + 4330520 * 2 ^ 59
def prefixEnd_4330520 : Nat := 4983230072969 + 3 ^ 40 * 4330520 * 2
def baseEnd_4330520 : Nat := 2223638243908502054284307

theorem tailTrace_4330520 : CollatzResearch.WordTrace tailWord_4330520 prefixEnd_4330520 2223638243908502054284307 := by
  unfold tailWord_4330520
  simp only [CollatzResearch.WordTrace]
  refine ⟨78973520135636554389514507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105298026847515405852686009 78973520135636554389514507)
  ·
    refine ⟨118460280203454831584271761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78973520135636554389514507 118460280203454831584271761)
    ·
      refine ⟨88845210152591123688203821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118460280203454831584271761 88845210152591123688203821)
      ·
        refine ⟨33316953807221671383076433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88845210152591123688203821 33316953807221671383076433)
        ·
          refine ⟨24987715355416253537307325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33316953807221671383076433 24987715355416253537307325)
          ·
            refine ⟨9370393258281095076490247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24987715355416253537307325 9370393258281095076490247)
            ·
              refine ⟨14055589887421642614735371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9370393258281095076490247 14055589887421642614735371)
              ·
                refine ⟨21083384831132463922103057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14055589887421642614735371 21083384831132463922103057)
                ·
                  refine ⟨15812538623349347941577293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21083384831132463922103057 15812538623349347941577293)
                  ·
                    refine ⟨5929701983756005478091485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15812538623349347941577293 5929701983756005478091485)
                    ·
                      refine ⟨2223638243908502054284307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5929701983756005478091485 2223638243908502054284307)
                      ·
                        rfl

theorem cell23_4330520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_4330520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330520 prefixEnd_4330520 := by exact prefixLift 4330520
  have htrace : WordTrace (prefixWord ++ tailWord_4330520) baseStart_4330520 baseEnd_4330520 := by
    simpa [prefixWord, tailWord_4330520, baseEnd_4330520] using wordTrace_append hprefix tailTrace_4330520
  have hstable : (prefixWord ++ tailWord_4330520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330520).length < 2 ^ (prefixWord ++ tailWord_4330520).sum := by decide
  have hdescent : baseEnd_4330520 < baseStart_4330520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330560 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 4, 4, 2]
def baseStart_4330560 : Nat := 118140960795 + 4330560 * 2 ^ 59
def prefixEnd_4330560 : Nat := 4983230072969 + 3 ^ 40 * 4330560 * 2
def baseEnd_4330560 : Nat := 2223658783134681897784123

theorem tailTrace_4330560 : CollatzResearch.WordTrace tailWord_4330560 prefixEnd_4330560 2223658783134681897784123 := by
  unfold tailWord_4330560
  simp only [CollatzResearch.WordTrace]
  refine ⟨78974249595564097805242567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105298999460752130406990089 78974249595564097805242567)
  ·
    refine ⟨118461374393346146707863851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78974249595564097805242567 118461374393346146707863851)
    ·
      refine ⟨177692061590019220061795777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118461374393346146707863851 177692061590019220061795777)
      ·
        refine ⟨133269046192514415046346833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177692061590019220061795777 133269046192514415046346833)
        ·
          refine ⟨99951784644385811284760125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133269046192514415046346833 99951784644385811284760125)
          ·
            refine ⟨37481919241644679231785047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99951784644385811284760125 37481919241644679231785047)
            ·
              refine ⟨56222878862467018847677571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37481919241644679231785047 56222878862467018847677571)
              ·
                refine ⟨84334318293700528271516357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56222878862467018847677571 84334318293700528271516357)
                ·
                  refine ⟨15812684680068849050909317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84334318293700528271516357 15812684680068849050909317)
                  ·
                    refine ⟨2964878377512909197045497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15812684680068849050909317 2964878377512909197045497)
                    ·
                      refine ⟨2223658783134681897784123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964878377512909197045497 2223658783134681897784123)
                      ·
                        rfl

theorem cell23_4330560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 4, 4, 2].length) (baseStart_4330560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330560 prefixEnd_4330560 := by exact prefixLift 4330560
  have htrace : WordTrace (prefixWord ++ tailWord_4330560) baseStart_4330560 baseEnd_4330560 := by
    simpa [prefixWord, tailWord_4330560, baseEnd_4330560] using wordTrace_append hprefix tailTrace_4330560
  have hstable : (prefixWord ++ tailWord_4330560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330560).length < 2 ^ (prefixWord ++ tailWord_4330560).sum := by decide
  have hdescent : baseEnd_4330560 < baseStart_4330560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330570 : List Nat := [3, 1, 2, 1, 1, 2, 3, 3, 3, 4]
def baseStart_4330570 : Nat := 118140960795 + 4330570 * 2 ^ 59
def prefixEnd_4330570 : Nat := 4983230072969 + 3 ^ 40 * 4330570 * 2
def baseEnd_4330570 : Nat := 741221305980408952886359

theorem tailTrace_4330570 : CollatzResearch.WordTrace tailWord_4330570 prefixEnd_4330570 741221305980408952886359 := by
  unfold tailWord_4330570
  simp only [CollatzResearch.WordTrace]
  refine ⟨39487215980272991829587291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105299242614061311545566109 39487215980272991829587291)
  ·
    refine ⟨59230823970409487744380937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39487215980272991829587291 59230823970409487744380937)
    ·
      refine ⟨44423117977807115808285703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59230823970409487744380937 44423117977807115808285703)
      ·
        refine ⟨66634676966710673712428555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44423117977807115808285703 66634676966710673712428555)
        ·
          refine ⟨99952015450066010568642833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66634676966710673712428555 99952015450066010568642833)
          ·
            refine ⟨74964011587549507926482125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99952015450066010568642833 74964011587549507926482125)
            ·
              refine ⟨28111504345331065472430797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74964011587549507926482125 28111504345331065472430797)
              ·
                refine ⟨10541814129499149552161549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28111504345331065472430797 10541814129499149552161549)
                ·
                  refine ⟨3953180298562181082060581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10541814129499149552161549 3953180298562181082060581)
                  ·
                    refine ⟨741221305980408952886359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3953180298562181082060581 741221305980408952886359)
                    ·
                      rfl

theorem cell23_4330570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_4330570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330570 prefixEnd_4330570 := by exact prefixLift 4330570
  have htrace : WordTrace (prefixWord ++ tailWord_4330570) baseStart_4330570 baseEnd_4330570 := by
    simpa [prefixWord, tailWord_4330570, baseEnd_4330570] using wordTrace_append hprefix tailTrace_4330570
  have hstable : (prefixWord ++ tailWord_4330570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330570).length < 2 ^ (prefixWord ++ tailWord_4330570).sum := by decide
  have hdescent : baseEnd_4330570 < baseStart_4330570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330580 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_4330580 : Nat := 118140960795 + 4330580 * 2 ^ 59
def prefixEnd_4330580 : Nat := 4983230072969 + 3 ^ 40 * 4330580 * 2
def baseEnd_4330580 : Nat := 2223669052747771819534031

theorem tailTrace_4330580 : CollatzResearch.WordTrace tailWord_4330580 prefixEnd_4330580 2223669052747771819534031 := by
  unfold tailWord_4330580
  simp only [CollatzResearch.WordTrace]
  refine ⟨78974614325527869513106597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105299485767370492684142129 78974614325527869513106597)
  ·
    refine ⟨14807740186036475533707487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78974614325527869513106597 14807740186036475533707487)
    ·
      refine ⟨22211610279054713300561231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14807740186036475533707487 22211610279054713300561231)
      ·
        refine ⟨33317415418582069950841847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22211610279054713300561231 33317415418582069950841847)
        ·
          refine ⟨49976123127873104926262771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33317415418582069950841847 49976123127873104926262771)
          ·
            refine ⟨74964184691809657389394157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49976123127873104926262771 74964184691809657389394157)
            ·
              refine ⟨28111569259428621521022809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74964184691809657389394157 28111569259428621521022809)
              ·
                refine ⟨21083676944571466140767107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28111569259428621521022809 21083676944571466140767107)
                ·
                  refine ⟨31625515416857199211150661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21083676944571466140767107 31625515416857199211150661)
                  ·
                    refine ⟨5929784140660724852090749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31625515416857199211150661 5929784140660724852090749)
                    ·
                      refine ⟨2223669052747771819534031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5929784140660724852090749 2223669052747771819534031)
                      ·
                        rfl

theorem cell23_4330580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_4330580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330580 prefixEnd_4330580 := by exact prefixLift 4330580
  have htrace : WordTrace (prefixWord ++ tailWord_4330580) baseStart_4330580 baseEnd_4330580 := by
    simpa [prefixWord, tailWord_4330580, baseEnd_4330580] using wordTrace_append hprefix tailTrace_4330580
  have hstable : (prefixWord ++ tailWord_4330580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330580).length < 2 ^ (prefixWord ++ tailWord_4330580).sum := by decide
  have hdescent : baseEnd_4330580 < baseStart_4330580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330647 : List Nat := [1, 1, 3, 3, 3, 1, 3, 2, 1, 5]
def baseStart_4330647 : Nat := 118140960795 + 4330647 * 2 ^ 59
def prefixEnd_4330647 : Nat := 4983230072969 + 3 ^ 40 * 4330647 * 2
def baseEnd_4330647 : Nat := 741234485317207685798741

theorem tailTrace_4330647 : CollatzResearch.WordTrace tailWord_4330647 prefixEnd_4330647 741234485317207685798741 := by
  unfold tailWord_4330647
  simp only [CollatzResearch.WordTrace]
  refine ⟨157951672341813009468902195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105301114894542006312601463 157951672341813009468902195)
  ·
    refine ⟨236927508512719514203353293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157951672341813009468902195 236927508512719514203353293)
    ·
      refine ⟨88847815692269817826257485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236927508512719514203353293 88847815692269817826257485)
      ·
        refine ⟨33317930884601181684846557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88847815692269817826257485 33317930884601181684846557)
        ·
          refine ⟨12494224081725443131817459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33317930884601181684846557 12494224081725443131817459)
          ·
            refine ⟨18741336122588164697726189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12494224081725443131817459 18741336122588164697726189)
            ·
              refine ⟨7028001045970561761647321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18741336122588164697726189 7028001045970561761647321)
              ·
                refine ⟨5271000784477921321235491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7028001045970561761647321 5271000784477921321235491)
                ·
                  refine ⟨7906501176716881981853237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5271000784477921321235491 7906501176716881981853237)
                  ·
                    refine ⟨741234485317207685798741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7906501176716881981853237 741234485317207685798741)
                    ·
                      rfl

theorem cell23_4330647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_4330647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330647 prefixEnd_4330647 := by exact prefixLift 4330647
  have htrace : WordTrace (prefixWord ++ tailWord_4330647) baseStart_4330647 baseEnd_4330647 := by
    simpa [prefixWord, tailWord_4330647, baseEnd_4330647] using wordTrace_append hprefix tailTrace_4330647
  have hstable : (prefixWord ++ tailWord_4330647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330647).length < 2 ^ (prefixWord ++ tailWord_4330647).sum := by decide
  have hdescent : baseEnd_4330647 < baseStart_4330647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330660 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 3, 6]
def baseStart_4330660 : Nat := 118140960795 + 4330660 * 2 ^ 59
def prefixEnd_4330660 : Nat := 4983230072969 + 3 ^ 40 * 4330660 * 2
def baseEnd_4330660 : Nat := 741236710400043835511221

theorem tailTrace_4330660 : CollatzResearch.WordTrace tailWord_4330660 prefixEnd_4330660 741236710400043835511221 := by
  unfold tailWord_4330660
  simp only [CollatzResearch.WordTrace]
  refine ⟨78976073245382956344562717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105301430993843941792750289 78976073245382956344562717)
  ·
    refine ⟨29616027467018608629211019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78976073245382956344562717 29616027467018608629211019)
    ·
      refine ⟨44424041200527912943816529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29616027467018608629211019 44424041200527912943816529)
      ·
        refine ⟨33318030900395934707862397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44424041200527912943816529 33318030900395934707862397)
        ·
          refine ⟨12494261587648475515448399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33318030900395934707862397 12494261587648475515448399)
          ·
            refine ⟨18741392381472713273172599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12494261587648475515448399 18741392381472713273172599)
            ·
              refine ⟨28112088572209069909758899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18741392381472713273172599 28112088572209069909758899)
              ·
                refine ⟨42168132858313604864638349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28112088572209069909758899 42168132858313604864638349)
                ·
                  refine ⟨15813049821867601824239381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42168132858313604864638349 15813049821867601824239381)
                  ·
                    refine ⟨741236710400043835511221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15813049821867601824239381 741236710400043835511221)
                    ·
                      rfl

theorem cell23_4330660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_4330660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330660 prefixEnd_4330660 := by exact prefixLift 4330660
  have htrace : WordTrace (prefixWord ++ tailWord_4330660) baseStart_4330660 baseEnd_4330660 := by
    simpa [prefixWord, tailWord_4330660, baseEnd_4330660] using wordTrace_append hprefix tailTrace_4330660
  have hstable : (prefixWord ++ tailWord_4330660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330660).length < 2 ^ (prefixWord ++ tailWord_4330660).sum := by decide
  have hdescent : baseEnd_4330660 < baseStart_4330660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330683 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 7]
def baseStart_4330683 : Nat := 118140960795 + 4330683 * 2 ^ 59
def prefixEnd_4330683 : Nat := 4983230072969 + 3 ^ 40 * 4330683 * 2
def baseEnd_4330683 : Nat := 2223721941255184916546057

theorem tailTrace_4330683 : CollatzResearch.WordTrace tailWord_4330683 prefixEnd_4330683 2223721941255184916546057 := by
  unfold tailWord_4330683
  simp only [CollatzResearch.WordTrace]
  refine ⟨157952985369682587617212703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105301990246455058411475135 157952985369682587617212703)
  ·
    refine ⟨236929478054523881425819055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157952985369682587617212703 236929478054523881425819055)
    ·
      refine ⟨355394217081785822138728583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236929478054523881425819055 355394217081785822138728583)
      ·
        refine ⟨533091325622678733208092875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355394217081785822138728583 533091325622678733208092875)
        ·
          refine ⟨799636988434018099812139313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533091325622678733208092875 799636988434018099812139313)
          ·
            refine ⟨599727741325513574859104485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 799636988434018099812139313 599727741325513574859104485)
            ·
              refine ⟨112448951498533795286082091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 599727741325513574859104485 112448951498533795286082091)
              ·
                refine ⟨168673427247800692929123137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112448951498533795286082091 168673427247800692929123137)
                ·
                  refine ⟨126505070435850519696842353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168673427247800692929123137 126505070435850519696842353)
                  ·
                    refine ⟨94878802826887889772631765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 126505070435850519696842353 94878802826887889772631765)
                    ·
                      refine ⟨2223721941255184916546057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94878802826887889772631765 2223721941255184916546057)
                      ·
                        rfl

theorem cell23_4330683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 7].length) (baseStart_4330683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330683 prefixEnd_4330683 := by exact prefixLift 4330683
  have htrace : WordTrace (prefixWord ++ tailWord_4330683) baseStart_4330683 baseEnd_4330683 := by
    simpa [prefixWord, tailWord_4330683, baseEnd_4330683] using wordTrace_append hprefix tailTrace_4330683
  have hstable : (prefixWord ++ tailWord_4330683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330683).length < 2 ^ (prefixWord ++ tailWord_4330683).sum := by decide
  have hdescent : baseEnd_4330683 < baseStart_4330683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330721 : List Nat := [1, 2, 3, 1, 3, 4, 2, 1, 1, 2, 3]
def baseStart_4330721 : Nat := 118140960795 + 4330721 * 2 ^ 59
def prefixEnd_4330721 : Nat := 4983230072969 + 3 ^ 40 * 4330721 * 2
def baseEnd_4330721 : Nat := 2223741453520055767870883

theorem tailTrace_4330721 : CollatzResearch.WordTrace tailWord_4330721 prefixEnd_4330721 2223741453520055767870883 := by
  unfold tailWord_4330721
  simp only [CollatzResearch.WordTrace]
  refine ⟨157954371343544920107096017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105302914229029946738064011 157954371343544920107096017)
  ·
    refine ⟨118465778507658690080322013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157954371343544920107096017 118465778507658690080322013)
    ·
      refine ⟨44424666940372008780120755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118465778507658690080322013 44424666940372008780120755)
      ·
        refine ⟨66637000410558013170181133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44424666940372008780120755 66637000410558013170181133)
        ·
          refine ⟨24988875153959254938817925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66637000410558013170181133 24988875153959254938817925)
          ·
            refine ⟨4685414091367360301028361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24988875153959254938817925 4685414091367360301028361)
            ·
              refine ⟨3514060568525520225771271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4685414091367360301028361 3514060568525520225771271)
              ·
                refine ⟨5271090852788280338656907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3514060568525520225771271 5271090852788280338656907)
                ·
                  refine ⟨7906636279182420507985361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5271090852788280338656907 7906636279182420507985361)
                  ·
                    refine ⟨5929977209386815380989021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7906636279182420507985361 5929977209386815380989021)
                    ·
                      refine ⟨2223741453520055767870883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5929977209386815380989021 2223741453520055767870883)
                      ·
                        rfl

theorem cell23_4330721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_4330721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330721 prefixEnd_4330721 := by exact prefixLift 4330721
  have htrace : WordTrace (prefixWord ++ tailWord_4330721) baseStart_4330721 baseEnd_4330721 := by
    simpa [prefixWord, tailWord_4330721, baseEnd_4330721] using wordTrace_append hprefix tailTrace_4330721
  have hstable : (prefixWord ++ tailWord_4330721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330721).length < 2 ^ (prefixWord ++ tailWord_4330721).sum := by decide
  have hdescent : baseEnd_4330721 < baseStart_4330721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330751 : List Nat := [1, 1, 2, 2, 1, 6, 3, 1, 2, 1, 3]
def baseStart_4330751 : Nat := 118140960795 + 4330751 * 2 ^ 59
def prefixEnd_4330751 : Nat := 4983230072969 + 3 ^ 40 * 4330751 * 2
def baseEnd_4330751 : Nat := 2223756857939690650495745

theorem tailTrace_4330751 : CollatzResearch.WordTrace tailWord_4330751 prefixEnd_4330751 2223756857939690650495745 := by
  unfold tailWord_4330751
  simp only [CollatzResearch.WordTrace]
  refine ⟨157955465533436235230688107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105303643688957490153792071 157955465533436235230688107)
  ·
    refine ⟨236933198300154352846032161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157955465533436235230688107 236933198300154352846032161)
    ·
      refine ⟨177699898725115764634524121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236933198300154352846032161 177699898725115764634524121)
      ·
        refine ⟨133274924043836823475893091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177699898725115764634524121 133274924043836823475893091)
        ·
          refine ⟨199912386065755235213839637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133274924043836823475893091 199912386065755235213839637)
          ·
            refine ⟨9370893096832276650648733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 199912386065755235213839637 9370893096832276650648733)
            ·
              refine ⟨3514084911312103743993275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9370893096832276650648733 3514084911312103743993275)
              ·
                refine ⟨5271127366968155615989913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3514084911312103743993275 5271127366968155615989913)
                ·
                  refine ⟨3953345525226116711992435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5271127366968155615989913 3953345525226116711992435)
                  ·
                    refine ⟨5930018287839175067988653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3953345525226116711992435 5930018287839175067988653)
                    ·
                      refine ⟨2223756857939690650495745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5930018287839175067988653 2223756857939690650495745)
                      ·
                        rfl

theorem cell23_4330751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 2, 1, 3].length) (baseStart_4330751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330751 prefixEnd_4330751 := by exact prefixLift 4330751
  have htrace : WordTrace (prefixWord ++ tailWord_4330751) baseStart_4330751 baseEnd_4330751 := by
    simpa [prefixWord, tailWord_4330751, baseEnd_4330751] using wordTrace_append hprefix tailTrace_4330751
  have hstable : (prefixWord ++ tailWord_4330751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330751).length < 2 ^ (prefixWord ++ tailWord_4330751).sum := by decide
  have hdescent : baseEnd_4330751 < baseStart_4330751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330780 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 9]
def baseStart_4330780 : Nat := 118140960795 + 4330780 * 2 ^ 59
def prefixEnd_4330780 : Nat := 4983230072969 + 3 ^ 40 * 4330780 * 2
def baseEnd_4330780 : Nat := 247085749875407893003679

theorem tailTrace_4330780 : CollatzResearch.WordTrace tailWord_4330780 prefixEnd_4330780 247085749875407893003679 := by
  unfold tailWord_4330780
  simp only [CollatzResearch.WordTrace]
  refine ⟨78978261625165586591746897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105304348833554115455662529 78978261625165586591746897)
  ·
    refine ⟨59233696218874189943810173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78978261625165586591746897 59233696218874189943810173)
    ·
      refine ⟨22212636082077821228928815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59233696218874189943810173 22212636082077821228928815)
      ·
        refine ⟨33318954123116731843393223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22212636082077821228928815 33318954123116731843393223)
        ·
          refine ⟨49978431184675097765089835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33318954123116731843393223 49978431184675097765089835)
          ·
            refine ⟨74967646777012646647634753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49978431184675097765089835 74967646777012646647634753)
            ·
              refine ⟨56225735082759484985726065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74967646777012646647634753 56225735082759484985726065)
              ·
                refine ⟨42169301312069613739294549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56225735082759484985726065 42169301312069613739294549)
                ·
                  refine ⟨247085749875407893003679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42169301312069613739294549 247085749875407893003679)
                  ·
                    rfl

theorem cell23_4330780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 9].length) (baseStart_4330780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330780 prefixEnd_4330780 := by exact prefixLift 4330780
  have htrace : WordTrace (prefixWord ++ tailWord_4330780) baseStart_4330780 baseEnd_4330780 := by
    simpa [prefixWord, tailWord_4330780, baseEnd_4330780] using wordTrace_append hprefix tailTrace_4330780
  have hstable : (prefixWord ++ tailWord_4330780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330780).length < 2 ^ (prefixWord ++ tailWord_4330780).sum := by decide
  have hdescent : baseEnd_4330780 < baseStart_4330780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330837 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_4330837 : Nat := 118140960795 + 4330837 * 2 ^ 59
def prefixEnd_4330837 : Nat := 4983230072969 + 3 ^ 40 * 4330837 * 2
def baseEnd_4330837 : Nat := 2223801017275977314020349

theorem tailTrace_4330837 : CollatzResearch.WordTrace tailWord_4330837 prefixEnd_4330837 2223801017275977314020349 := by
  unfold tailWord_4330837
  simp only [CollatzResearch.WordTrace]
  refine ⟨157958602211124671918318765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105305734807416447945545843 157958602211124671918318765)
  ·
    refine ⟨59234475829171751969369537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157958602211124671918318765 59234475829171751969369537)
    ·
      refine ⟨44425856871878813977027153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59234475829171751969369537 44425856871878813977027153)
      ·
        refine ⟨33319392653909110482770365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44425856871878813977027153 33319392653909110482770365)
        ·
          refine ⟨12494772245215916431038887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33319392653909110482770365 12494772245215916431038887)
          ·
            refine ⟨18742158367823874646558331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12494772245215916431038887 18742158367823874646558331)
            ·
              refine ⟨28113237551735811969837497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18742158367823874646558331 28113237551735811969837497)
              ·
                refine ⟨21084928163801858977378123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28113237551735811969837497 21084928163801858977378123)
                ·
                  refine ⟨31627392245702788466067185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21084928163801858977378123 31627392245702788466067185)
                  ·
                    refine ⟨23720544184277091349550389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31627392245702788466067185 23720544184277091349550389)
                    ·
                      refine ⟨2223801017275977314020349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23720544184277091349550389 2223801017275977314020349)
                      ·
                        rfl

theorem cell23_4330837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_4330837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330837 prefixEnd_4330837 := by exact prefixLift 4330837
  have htrace : WordTrace (prefixWord ++ tailWord_4330837) baseStart_4330837 baseEnd_4330837 := by
    simpa [prefixWord, tailWord_4330837, baseEnd_4330837] using wordTrace_append hprefix tailTrace_4330837
  have hstable : (prefixWord ++ tailWord_4330837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330837).length < 2 ^ (prefixWord ++ tailWord_4330837).sum := by decide
  have hdescent : baseEnd_4330837 < baseStart_4330837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330864 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 2, 4, 2]
def baseStart_4330864 : Nat := 118140960795 + 4330864 * 2 ^ 59
def prefixEnd_4330864 : Nat := 4983230072969 + 3 ^ 40 * 4330864 * 2
def baseEnd_4330864 : Nat := 2223814881253648708382725

theorem tailTrace_4330864 : CollatzResearch.WordTrace tailWord_4330864 prefixEnd_4330864 2223814881253648708382725 := by
  unfold tailWord_4330864
  simp only [CollatzResearch.WordTrace]
  refine ⟨78979793491013427764775823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105306391321351237019701097 78979793491013427764775823)
  ·
    refine ⟨118469690236520141647163735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78979793491013427764775823 118469690236520141647163735)
    ·
      refine ⟨177704535354780212470745603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118469690236520141647163735 177704535354780212470745603)
      ·
        refine ⟨266556803032170318706118405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177704535354780212470745603 266556803032170318706118405)
        ·
          refine ⟨49979400568531934757397201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 266556803032170318706118405 49979400568531934757397201)
          ·
            refine ⟨37484550426398951068047901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49979400568531934757397201 37484550426398951068047901)
            ·
              refine ⟨14056706409899606650517963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37484550426398951068047901 14056706409899606650517963)
              ·
                refine ⟨21085059614849409975776945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14056706409899606650517963 21085059614849409975776945)
                ·
                  refine ⟨15813794711137057481832709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21085059614849409975776945 15813794711137057481832709)
                  ·
                    refine ⟨2965086508338198277843633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15813794711137057481832709 2965086508338198277843633)
                    ·
                      refine ⟨2223814881253648708382725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2965086508338198277843633 2223814881253648708382725)
                      ·
                        rfl

theorem cell23_4330864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 2, 4, 2].length) (baseStart_4330864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330864 prefixEnd_4330864 := by exact prefixLift 4330864
  have htrace : WordTrace (prefixWord ++ tailWord_4330864) baseStart_4330864 baseEnd_4330864 := by
    simpa [prefixWord, tailWord_4330864, baseEnd_4330864] using wordTrace_append hprefix tailTrace_4330864
  have hstable : (prefixWord ++ tailWord_4330864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330864).length < 2 ^ (prefixWord ++ tailWord_4330864).sum := by decide
  have hdescent : baseEnd_4330864 < baseStart_4330864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330884 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_4330884 : Nat := 118140960795 + 4330884 * 2 ^ 59
def prefixEnd_4330884 : Nat := 4983230072969 + 3 ^ 40 * 4330884 * 2
def baseEnd_4330884 : Nat := 2223825150866738630132633

theorem tailTrace_4330884 : CollatzResearch.WordTrace tailWord_4330884 prefixEnd_4330884 2223825150866738630132633 := by
  unfold tailWord_4330884
  simp only [CollatzResearch.WordTrace]
  refine ⟨78980158220977199472639853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105306877627969599296853137 78980158220977199472639853)
  ·
    refine ⟨29617559332866449802239945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78980158220977199472639853 29617559332866449802239945)
    ·
      refine ⟨22213169499649837351679959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29617559332866449802239945 22213169499649837351679959)
      ·
        refine ⟨33319754249474756027519939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22213169499649837351679959 33319754249474756027519939)
        ·
          refine ⟨49979631374212134041279909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33319754249474756027519939 49979631374212134041279909)
          ·
            refine ⟨9371180882664775132739983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49979631374212134041279909 9371180882664775132739983)
            ·
              refine ⟨14056771323997162699109975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9371180882664775132739983 14056771323997162699109975)
              ·
                refine ⟨21085156985995744048664963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14056771323997162699109975 21085156985995744048664963)
                ·
                  refine ⟨31627735478993616072997445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21085156985995744048664963 31627735478993616072997445)
                  ·
                    refine ⟨5930200402311303013687021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31627735478993616072997445 5930200402311303013687021)
                    ·
                      refine ⟨2223825150866738630132633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5930200402311303013687021 2223825150866738630132633)
                      ·
                        rfl

theorem cell23_4330884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_4330884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330884 prefixEnd_4330884 := by exact prefixLift 4330884
  have htrace : WordTrace (prefixWord ++ tailWord_4330884) baseStart_4330884 baseEnd_4330884 := by
    simpa [prefixWord, tailWord_4330884, baseEnd_4330884] using wordTrace_append hprefix tailTrace_4330884
  have hstable : (prefixWord ++ tailWord_4330884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330884).length < 2 ^ (prefixWord ++ tailWord_4330884).sum := by decide
  have hdescent : baseEnd_4330884 < baseStart_4330884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330891 : List Nat := [1, 1, 1, 1, 4, 3, 4, 3, 1, 4]
def baseStart_4330891 : Nat := 118140960795 + 4330891 * 2 ^ 59
def prefixEnd_4330891 : Nat := 4983230072969 + 3 ^ 40 * 4330891 * 2
def baseEnd_4330891 : Nat := 741276248410440034248367

theorem tailTrace_4330891 : CollatzResearch.WordTrace tailWord_4330891 prefixEnd_4330891 741276248410440034248367 := by
  unfold tailWord_4330891
  simp only [CollatzResearch.WordTrace]
  refine ⟨157960571752929039140784527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105307047835286026093856351 157960571752929039140784527)
  ·
    refine ⟨236940857629393558711176791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157960571752929039140784527 236940857629393558711176791)
    ·
      refine ⟨355411286444090338066765187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236940857629393558711176791 355411286444090338066765187)
      ·
        refine ⟨533116929666135507100147781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355411286444090338066765187 533116929666135507100147781)
        ·
          refine ⟨99959424312400407581277709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 533116929666135507100147781 99959424312400407581277709)
          ·
            refine ⟨37484784117150152842979141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99959424312400407581277709 37484784117150152842979141)
            ·
              refine ⟨7028397021965653658058589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37484784117150152842979141 7028397021965653658058589)
              ·
                refine ⟨2635648883237120121771971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7028397021965653658058589 2635648883237120121771971)
                ·
                  refine ⟨3953473324855680182657957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2635648883237120121771971 3953473324855680182657957)
                  ·
                    refine ⟨741276248410440034248367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3953473324855680182657957 741276248410440034248367)
                    ·
                      rfl

theorem cell23_4330891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 1, 4].length) (baseStart_4330891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330891 prefixEnd_4330891 := by exact prefixLift 4330891
  have htrace : WordTrace (prefixWord ++ tailWord_4330891) baseStart_4330891 baseEnd_4330891 := by
    simpa [prefixWord, tailWord_4330891, baseEnd_4330891] using wordTrace_append hprefix tailTrace_4330891
  have hstable : (prefixWord ++ tailWord_4330891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330891).length < 2 ^ (prefixWord ++ tailWord_4330891).sum := by decide
  have hdescent : baseEnd_4330891 < baseStart_4330891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330904 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 8]
def baseStart_4330904 : Nat := 118140960795 + 4330904 * 2 ^ 59
def prefixEnd_4330904 : Nat := 4983230072969 + 3 ^ 40 * 4330904 * 2
def baseEnd_4330904 : Nat := 247092824497758727986949

theorem tailTrace_4330904 : CollatzResearch.WordTrace tailWord_4330904 prefixEnd_4330904 247092824497758727986949 := by
  unfold tailWord_4330904
  simp only [CollatzResearch.WordTrace]
  refine ⟨78980522950940971180503883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105307363934587961574005177 78980522950940971180503883)
  ·
    refine ⟨118470784426411456770755825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78980522950940971180503883 118470784426411456770755825)
    ·
      refine ⟨88853088319808592578066869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118470784426411456770755825 88853088319808592578066869)
      ·
        refine ⟨8329977029982055554193769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88853088319808592578066869 8329977029982055554193769)
        ·
          refine ⟨6247482772486541665645327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8329977029982055554193769 6247482772486541665645327)
          ·
            refine ⟨9371224158729812498467991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6247482772486541665645327 9371224158729812498467991)
            ·
              refine ⟨14056836238094718747701987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9371224158729812498467991 14056836238094718747701987)
              ·
                refine ⟨21085254357142078121552981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14056836238094718747701987 21085254357142078121552981)
                ·
                  refine ⟨247092824497758727986949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21085254357142078121552981 247092824497758727986949)
                  ·
                    rfl

theorem cell23_4330904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 8].length) (baseStart_4330904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330904 prefixEnd_4330904 := by exact prefixLift 4330904
  have htrace : WordTrace (prefixWord ++ tailWord_4330904) baseStart_4330904 baseEnd_4330904 := by
    simpa [prefixWord, tailWord_4330904, baseEnd_4330904] using wordTrace_append hprefix tailTrace_4330904
  have hstable : (prefixWord ++ tailWord_4330904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330904).length < 2 ^ (prefixWord ++ tailWord_4330904).sum := by decide
  have hdescent : baseEnd_4330904 < baseStart_4330904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330908 : List Nat := [2, 2, 3, 4, 1, 1, 2, 1, 3, 4]
def baseStart_4330908 : Nat := 118140960795 + 4330908 * 2 ^ 59
def prefixEnd_4330908 : Nat := 4983230072969 + 3 ^ 40 * 4330908 * 2
def baseEnd_4330908 : Nat := 741279158134148845410841

theorem tailTrace_4330908 : CollatzResearch.WordTrace tailWord_4330908 prefixEnd_4330908 741279158134148845410841 := by
  unfold tailWord_4330908
  simp only [CollatzResearch.WordTrace]
  refine ⟨78980595896933725522076689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105307461195911634029435585 78980595896933725522076689)
  ·
    refine ⟨59235446922700294141557517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78980595896933725522076689 59235446922700294141557517)
    ·
      refine ⟨22213292596012610303084069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59235446922700294141557517 22213292596012610303084069)
      ·
        refine ⟨4164992361752364431828263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22213292596012610303084069 4164992361752364431828263)
        ·
          refine ⟨6247488542628546647742395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4164992361752364431828263 6247488542628546647742395)
          ·
            refine ⟨9371232813942819971613593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6247488542628546647742395 9371232813942819971613593)
            ·
              refine ⟨7028424610457114978710195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9371232813942819971613593 7028424610457114978710195)
              ·
                refine ⟨10542636915685672468065293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7028424610457114978710195 10542636915685672468065293)
                ·
                  refine ⟨3953488843382127175524485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10542636915685672468065293 3953488843382127175524485)
                  ·
                    refine ⟨741279158134148845410841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3953488843382127175524485 741279158134148845410841)
                    ·
                      rfl

theorem cell23_4330908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_4330908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330908 prefixEnd_4330908 := by exact prefixLift 4330908
  have htrace : WordTrace (prefixWord ++ tailWord_4330908) baseStart_4330908 baseEnd_4330908 := by
    simpa [prefixWord, tailWord_4330908, baseEnd_4330908] using wordTrace_append hprefix tailTrace_4330908
  have hstable : (prefixWord ++ tailWord_4330908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330908).length < 2 ^ (prefixWord ++ tailWord_4330908).sum := by decide
  have hdescent : baseEnd_4330908 < baseStart_4330908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330917 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 3, 5]
def baseStart_4330917 : Nat := 118140960795 + 4330917 * 2 ^ 59
def prefixEnd_4330917 : Nat := 4983230072969 + 3 ^ 40 * 4330917 * 2
def baseEnd_4330917 : Nat := 741280698576112333673327

theorem tailTrace_4330917 : CollatzResearch.WordTrace tailWord_4330917 prefixEnd_4330917 741280698576112333673327 := by
  unfold tailWord_4330917
  simp only [CollatzResearch.WordTrace]
  refine ⟨157961520050834845581231005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105307680033889897054154003 157961520050834845581231005)
  ·
    refine ⟨59235570019063067092961627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157961520050834845581231005 59235570019063067092961627)
    ·
      refine ⟨88853355028594600639442441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59235570019063067092961627 88853355028594600639442441)
      ·
        refine ⟨66640016271445950479581831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88853355028594600639442441 66640016271445950479581831)
        ·
          refine ⟨99960024407168925719372747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66640016271445950479581831 99960024407168925719372747)
          ·
            refine ⟨149940036610753388579059121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99960024407168925719372747 149940036610753388579059121)
            ·
              refine ⟨112455027458065041434294341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149940036610753388579059121 112455027458065041434294341)
              ·
                refine ⟨21085317648387195268930189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112455027458065041434294341 21085317648387195268930189)
                ·
                  refine ⟨7906994118145198225848821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21085317648387195268930189 7906994118145198225848821)
                  ·
                    refine ⟨741280698576112333673327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7906994118145198225848821 741280698576112333673327)
                    ·
                      rfl

theorem cell23_4330917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_4330917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330917 prefixEnd_4330917 := by exact prefixLift 4330917
  have htrace : WordTrace (prefixWord ++ tailWord_4330917) baseStart_4330917 baseEnd_4330917 := by
    simpa [prefixWord, tailWord_4330917, baseEnd_4330917] using wordTrace_append hprefix tailTrace_4330917
  have hstable : (prefixWord ++ tailWord_4330917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330917).length < 2 ^ (prefixWord ++ tailWord_4330917).sum := by decide
  have hdescent : baseEnd_4330917 < baseStart_4330917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330924 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 1, 5, 2]
def baseStart_4330924 : Nat := 118140960795 + 4330924 * 2 ^ 59
def prefixEnd_4330924 : Nat := 4983230072969 + 3 ^ 40 * 4330924 * 2
def baseEnd_4330924 : Nat := 2223845690092918473632449

theorem tailTrace_4330924 : CollatzResearch.WordTrace tailWord_4330924 prefixEnd_4330924 2223845690092918473632449 := by
  unfold tailWord_4330924
  simp only [CollatzResearch.WordTrace]
  refine ⟨78980887680904742888367913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105307850241206323851157217 78980887680904742888367913)
  ·
    refine ⟨59235665760678557166275935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78980887680904742888367913 59235665760678557166275935)
    ·
      refine ⟨88853498641017835749413903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59235665760678557166275935 88853498641017835749413903)
      ·
        refine ⟨133280247961526753624120855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88853498641017835749413903 133280247961526753624120855)
        ·
          refine ⟨199920371942290130436181283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133280247961526753624120855 199920371942290130436181283)
          ·
            refine ⟨299880557913435195654271925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199920371942290130436181283 299880557913435195654271925)
            ·
              refine ⟨28113802304384549592587993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 299880557913435195654271925 28113802304384549592587993)
              ·
                refine ⟨21085351728288412194440995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28113802304384549592587993 21085351728288412194440995)
                ·
                  refine ⟨31628027592432618291661493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21085351728288412194440995 31628027592432618291661493)
                  ·
                    refine ⟨2965127586790557964843265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31628027592432618291661493 2965127586790557964843265)
                    ·
                      refine ⟨2223845690092918473632449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2965127586790557964843265 2223845690092918473632449)
                      ·
                        rfl

theorem cell23_4330924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 5, 2].length) (baseStart_4330924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330924 prefixEnd_4330924 := by exact prefixLift 4330924
  have htrace : WordTrace (prefixWord ++ tailWord_4330924) baseStart_4330924 baseEnd_4330924 := by
    simpa [prefixWord, tailWord_4330924, baseEnd_4330924] using wordTrace_append hprefix tailTrace_4330924
  have hstable : (prefixWord ++ tailWord_4330924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330924).length < 2 ^ (prefixWord ++ tailWord_4330924).sum := by decide
  have hdescent : baseEnd_4330924 < baseStart_4330924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330941 : List Nat := [1, 4, 1, 2, 2, 1, 2, 3, 2, 3, 2]
def baseStart_4330941 : Nat := 118140960795 + 4330941 * 2 ^ 59
def prefixEnd_4330941 : Nat := 4983230072969 + 3 ^ 40 * 4330941 * 2
def baseEnd_4330941 : Nat := 2223854419264044907119871

theorem tailTrace_4330941 : CollatzResearch.WordTrace tailWord_4330941 prefixEnd_4330941 2223854419264044907119871 := by
  unfold tailWord_4330941
  simp only [CollatzResearch.WordTrace]
  refine ⟨157962395402747897680104677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105308263601831931786736451 157962395402747897680104677)
  ·
    refine ⟨29617949138015230815019627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157962395402747897680104677 29617949138015230815019627)
    ·
      refine ⟨44426923707022846222529441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29617949138015230815019627 44426923707022846222529441)
      ·
        refine ⟨33320192780267134666897081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44426923707022846222529441 33320192780267134666897081)
        ·
          refine ⟨24990144585200351000172811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33320192780267134666897081 24990144585200351000172811)
          ·
            refine ⟨37485216877800526500259217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24990144585200351000172811 37485216877800526500259217)
            ·
              refine ⟨28113912658350394875194413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37485216877800526500259217 28113912658350394875194413)
              ·
                refine ⟨10542717246881398078197905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28113912658350394875194413 10542717246881398078197905)
                ·
                  refine ⟨7907037935161048558648429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10542717246881398078197905 7907037935161048558648429)
                  ·
                    refine ⟨2965139225685393209493161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7907037935161048558648429 2965139225685393209493161)
                    ·
                      refine ⟨2223854419264044907119871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2965139225685393209493161 2223854419264044907119871)
                      ·
                        rfl

theorem cell23_4330941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_4330941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330941 prefixEnd_4330941 := by exact prefixLift 4330941
  have htrace : WordTrace (prefixWord ++ tailWord_4330941) baseStart_4330941 baseEnd_4330941 := by
    simpa [prefixWord, tailWord_4330941, baseEnd_4330941] using wordTrace_append hprefix tailTrace_4330941
  have hstable : (prefixWord ++ tailWord_4330941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330941).length < 2 ^ (prefixWord ++ tailWord_4330941).sum := by decide
  have hdescent : baseEnd_4330941 < baseStart_4330941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330947 : List Nat := [1, 1, 1, 3, 1, 1, 4, 4, 1, 6]
def baseStart_4330947 : Nat := 118140960795 + 4330947 * 2 ^ 59
def prefixEnd_4330947 : Nat := 4983230072969 + 3 ^ 40 * 4330947 * 2
def baseEnd_4330947 : Nat := 741285833382657294548281

theorem tailTrace_4330947 : CollatzResearch.WordTrace tailWord_4330947 prefixEnd_4330947 741285833382657294548281 := by
  unfold tailWord_4330947
  simp only [CollatzResearch.WordTrace]
  refine ⟨157962614240726160704823095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105308409493817440469882063 157962614240726160704823095)
  ·
    refine ⟨236943921361089241057234643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157962614240726160704823095 236943921361089241057234643)
    ·
      refine ⟨355415882041633861585851965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236943921361089241057234643 355415882041633861585851965)
      ·
        refine ⟨133280955765612698094694487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 355415882041633861585851965 133280955765612698094694487)
        ·
          refine ⟨199921433648419047142041731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133280955765612698094694487 199921433648419047142041731)
          ·
            refine ⟨299882150472628570713062597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199921433648419047142041731 299882150472628570713062597)
            ·
              refine ⟨56227903213617857008699237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 299882150472628570713062597 56227903213617857008699237)
              ·
                refine ⟨10542731852553348189131107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56227903213617857008699237 10542731852553348189131107)
                ·
                  refine ⟨15814097778830022283696661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10542731852553348189131107 15814097778830022283696661)
                  ·
                    refine ⟨741285833382657294548281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15814097778830022283696661 741285833382657294548281)
                    ·
                      rfl

theorem cell23_4330947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 6].length) (baseStart_4330947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330947 prefixEnd_4330947 := by exact prefixLift 4330947
  have htrace : WordTrace (prefixWord ++ tailWord_4330947) baseStart_4330947 baseEnd_4330947 := by
    simpa [prefixWord, tailWord_4330947, baseEnd_4330947] using wordTrace_append hprefix tailTrace_4330947
  have hstable : (prefixWord ++ tailWord_4330947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330947).length < 2 ^ (prefixWord ++ tailWord_4330947).sum := by decide
  have hdescent : baseEnd_4330947 < baseStart_4330947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330965 : List Nat := [1, 3, 2, 3, 1, 1, 5, 2, 1, 1, 3]
def baseStart_4330965 : Nat := 118140960795 + 4330965 * 2 ^ 59
def prefixEnd_4330965 : Nat := 4983230072969 + 3 ^ 40 * 4330965 * 2
def baseEnd_4330965 : Nat := 2223866742799752813219761

theorem tailTrace_4330965 : CollatzResearch.WordTrace tailWord_4330965 prefixEnd_4330965 2223866742799752813219761 := by
  unfold tailWord_4330965
  simp only [CollatzResearch.WordTrace]
  refine ⟨157963270754660949778978349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105308847169773966519318899 157963270754660949778978349)
  ·
    refine ⟨59236226532997856167116881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157963270754660949778978349 59236226532997856167116881)
    ·
      refine ⟨44427169899748392125337661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59236226532997856167116881 44427169899748392125337661)
      ·
        refine ⟨16660188712405647047001623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44427169899748392125337661 16660188712405647047001623)
        ·
          refine ⟨24990283068608470570502435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16660188712405647047001623 24990283068608470570502435)
          ·
            refine ⟨37485424602912705855753653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24990283068608470570502435 37485424602912705855753653)
            ·
              refine ⟨3514258556523066173976905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37485424602912705855753653 3514258556523066173976905)
              ·
                refine ⟨2635693917392299630482679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3514258556523066173976905 2635693917392299630482679)
                ·
                  refine ⟨3953540876088449445724019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2635693917392299630482679 3953540876088449445724019)
                  ·
                    refine ⟨5930311314132674168586029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3953540876088449445724019 5930311314132674168586029)
                    ·
                      refine ⟨2223866742799752813219761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5930311314132674168586029 2223866742799752813219761)
                      ·
                        rfl

theorem cell23_4330965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_4330965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330965 prefixEnd_4330965 := by exact prefixLift 4330965
  have htrace : WordTrace (prefixWord ++ tailWord_4330965) baseStart_4330965 baseEnd_4330965 := by
    simpa [prefixWord, tailWord_4330965, baseEnd_4330965] using wordTrace_append hprefix tailTrace_4330965
  have hstable : (prefixWord ++ tailWord_4330965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330965).length < 2 ^ (prefixWord ++ tailWord_4330965).sum := by decide
  have hdescent : baseEnd_4330965 < baseStart_4330965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330977 : List Nat := [1, 2, 3, 1, 2, 3, 1, 10]
def baseStart_4330977 : Nat := 118140960795 + 4330977 * 2 ^ 59
def prefixEnd_4330977 : Nat := 4983230072969 + 3 ^ 40 * 4330977 * 2
def baseEnd_4330977 : Nat := 82365663132133583935915

theorem tailTrace_4330977 : CollatzResearch.WordTrace tailWord_4330977 prefixEnd_4330977 82365663132133583935915 := by
  unfold tailWord_4330977
  simp only [CollatzResearch.WordTrace]
  refine ⟨157963708430617475828415185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105309138953744983885610123 157963708430617475828415185)
  ·
    refine ⟨118472781322963106871311389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157963708430617475828415185 118472781322963106871311389)
    ·
      refine ⟨44427292996111165076741771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118472781322963106871311389 44427292996111165076741771)
      ·
        refine ⟨66640939494166747615112657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44427292996111165076741771 66640939494166747615112657)
        ·
          refine ⟨49980704620625060711334493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66640939494166747615112657 49980704620625060711334493)
          ·
            refine ⟨18742764232734397766750435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49980704620625060711334493 18742764232734397766750435)
            ·
              refine ⟨28114146349101596650125653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18742764232734397766750435 28114146349101596650125653)
              ·
                refine ⟨82365663132133583935915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28114146349101596650125653 82365663132133583935915)
                ·
                  rfl

theorem cell23_4330977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 10].length) (baseStart_4330977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330977 prefixEnd_4330977 := by exact prefixLift 4330977
  have htrace : WordTrace (prefixWord ++ tailWord_4330977) baseStart_4330977 baseEnd_4330977 := by
    simpa [prefixWord, tailWord_4330977, baseEnd_4330977] using wordTrace_append hprefix tailTrace_4330977
  have hstable : (prefixWord ++ tailWord_4330977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330977).length < 2 ^ (prefixWord ++ tailWord_4330977).sum := by decide
  have hdescent : baseEnd_4330977 < baseStart_4330977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330984 : List Nat := [2, 1, 4, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_4330984 : Nat := 118140960795 + 4330984 * 2 ^ 59
def prefixEnd_4330984 : Nat := 4983230072969 + 3 ^ 40 * 4330984 * 2
def baseEnd_4330984 : Nat := 2223876498932188238882173

theorem tailTrace_4330984 : CollatzResearch.WordTrace tailWord_4330984 prefixEnd_4330984 2223876498932188238882173 := by
  unfold tailWord_4330984
  simp only [CollatzResearch.WordTrace]
  refine ⟨78981981870796058011960003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105309309161061410682613337 78981981870796058011960003)
  ·
    refine ⟨118472972806194087017940005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78981981870796058011960003 118472972806194087017940005)
    ·
      refine ⟨22213682401161391315863751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118472972806194087017940005 22213682401161391315863751)
      ·
        refine ⟨33320523601742086973795627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22213682401161391315863751 33320523601742086973795627)
        ·
          refine ⟨49980785402613130460693441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33320523601742086973795627 49980785402613130460693441)
          ·
            refine ⟨37485589051959847845520081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49980785402613130460693441 37485589051959847845520081)
            ·
              refine ⟨28114191788969885884140061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37485589051959847845520081 28114191788969885884140061)
              ·
                refine ⟨10542821920863707206552523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28114191788969885884140061 10542821920863707206552523)
                ·
                  refine ⟨15814232881295560809828785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10542821920863707206552523 15814232881295560809828785)
                  ·
                    refine ⟨11860674660971670607371589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15814232881295560809828785 11860674660971670607371589)
                    ·
                      refine ⟨2223876498932188238882173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11860674660971670607371589 2223876498932188238882173)
                      ·
                        rfl

theorem cell23_4330984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_4330984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330984 prefixEnd_4330984 := by exact prefixLift 4330984
  have htrace : WordTrace (prefixWord ++ tailWord_4330984) baseStart_4330984 baseEnd_4330984 := by
    simpa [prefixWord, tailWord_4330984, baseEnd_4330984] using wordTrace_append hprefix tailTrace_4330984
  have hstable : (prefixWord ++ tailWord_4330984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330984).length < 2 ^ (prefixWord ++ tailWord_4330984).sum := by decide
  have hdescent : baseEnd_4330984 < baseStart_4330984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330991 : List Nat := [1, 1, 2, 1, 4, 1, 5, 2, 1, 2, 3]
def baseStart_4330991 : Nat := 118140960795 + 4330991 * 2 ^ 59
def prefixEnd_4330991 : Nat := 4983230072969 + 3 ^ 40 * 4330991 * 2
def baseEnd_4330991 : Nat := 2223880093296769711494641

theorem tailTrace_4330991 : CollatzResearch.WordTrace tailWord_4330991 prefixEnd_4330991 2223880093296769711494641 := by
  unfold tailWord_4330991
  simp only [CollatzResearch.WordTrace]
  refine ⟨157964219052566756219424827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105309479368377837479616551 157964219052566756219424827)
  ·
    refine ⟨236946328578850134329137241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157964219052566756219424827 236946328578850134329137241)
    ·
      refine ⟨177709746434137600746852931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236946328578850134329137241 177709746434137600746852931)
      ·
        refine ⟨266564619651206401120279397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177709746434137600746852931 266564619651206401120279397)
        ·
          refine ⟨49980866184601200210052387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 266564619651206401120279397 49980866184601200210052387)
          ·
            refine ⟨74971299276901800315078581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49980866184601200210052387 74971299276901800315078581)
            ·
              refine ⟨7028559307209543779538617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74971299276901800315078581 7028559307209543779538617)
              ·
                refine ⟨5271419480407157834653963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7028559307209543779538617 5271419480407157834653963)
                ·
                  refine ⟨7907129220610736751980945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5271419480407157834653963 7907129220610736751980945)
                  ·
                    refine ⟨5930346915458052563985709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7907129220610736751980945 5930346915458052563985709)
                    ·
                      refine ⟨2223880093296769711494641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5930346915458052563985709 2223880093296769711494641)
                      ·
                        rfl

theorem cell23_4330991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 2, 3].length) (baseStart_4330991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330991 prefixEnd_4330991 := by exact prefixLift 4330991
  have htrace : WordTrace (prefixWord ++ tailWord_4330991) baseStart_4330991 baseEnd_4330991 := by
    simpa [prefixWord, tailWord_4330991, baseEnd_4330991] using wordTrace_append hprefix tailTrace_4330991
  have hstable : (prefixWord ++ tailWord_4330991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330991).length < 2 ^ (prefixWord ++ tailWord_4330991).sum := by decide
  have hdescent : baseEnd_4330991 < baseStart_4330991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4330994 : List Nat := [3, 2, 1, 4, 1, 1, 2, 9]
def baseStart_4330994 : Nat := 118140960795 + 4330994 * 2 ^ 59
def prefixEnd_4330994 : Nat := 4983230072969 + 3 ^ 40 * 4330994 * 2
def baseEnd_4330994 : Nat := 82365986434767896287301

theorem tailTrace_4330994 : CollatzResearch.WordTrace tailWord_4330994 prefixEnd_4330994 82365986434767896287301 := by
  unfold tailWord_4330994
  simp only [CollatzResearch.WordTrace]
  refine ⟨39491082117888971932946009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105309552314370591821189357 39491082117888971932946009)
  ·
    refine ⟨29618311588416728949709507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39491082117888971932946009 29618311588416728949709507)
    ·
      refine ⟨44427467382625093424564261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29618311588416728949709507 44427467382625093424564261)
      ·
        refine ⟨8330150134242205017105799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44427467382625093424564261 8330150134242205017105799)
        ·
          refine ⟨12495225201363307525658699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8330150134242205017105799 12495225201363307525658699)
          ·
            refine ⟨18742837802044961288488049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12495225201363307525658699 18742837802044961288488049)
            ·
              refine ⟨14057128351533720966366037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18742837802044961288488049 14057128351533720966366037)
              ·
                refine ⟨82365986434767896287301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14057128351533720966366037 82365986434767896287301)
                ·
                  rfl

theorem cell23_4330994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 9].length) (baseStart_4330994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4330994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4330994 prefixEnd_4330994 := by exact prefixLift 4330994
  have htrace : WordTrace (prefixWord ++ tailWord_4330994) baseStart_4330994 baseEnd_4330994 := by
    simpa [prefixWord, tailWord_4330994, baseEnd_4330994] using wordTrace_append hprefix tailTrace_4330994
  have hstable : (prefixWord ++ tailWord_4330994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4330994).length < 2 ^ (prefixWord ++ tailWord_4330994).sum := by decide
  have hdescent : baseEnd_4330994 < baseStart_4330994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4330994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331004 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 3, 3, 3]
def baseStart_4331004 : Nat := 118140960795 + 4331004 * 2 ^ 59
def prefixEnd_4331004 : Nat := 4983230072969 + 3 ^ 40 * 4331004 * 2
def baseEnd_4331004 : Nat := 2223886768545278160632081

theorem tailTrace_4331004 : CollatzResearch.WordTrace tailWord_4331004 prefixEnd_4331004 2223886768545278160632081 := by
  unfold tailWord_4331004
  simp only [CollatzResearch.WordTrace]
  refine ⟨78982346600759829719824033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105309795467679772959765377 78982346600759829719824033)
  ·
    refine ⟨59236759950569872289868025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78982346600759829719824033 59236759950569872289868025)
    ·
      refine ⟨44427569962927404217401019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59236759950569872289868025 44427569962927404217401019)
      ·
        refine ⟨66641354944391106326101529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44427569962927404217401019 66641354944391106326101529)
        ·
          refine ⟨49981016208293329744576147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66641354944391106326101529 49981016208293329744576147)
          ·
            refine ⟨74971524312439994616864221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49981016208293329744576147 74971524312439994616864221)
            ·
              refine ⟨28114321617164997981324083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74971524312439994616864221 28114321617164997981324083)
              ·
                refine ⟨42171482425747496971986125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28114321617164997981324083 42171482425747496971986125)
                ·
                  refine ⟨15814305909655311364494797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42171482425747496971986125 15814305909655311364494797)
                  ·
                    refine ⟨5930364716120741761685549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15814305909655311364494797 5930364716120741761685549)
                    ·
                      refine ⟨2223886768545278160632081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5930364716120741761685549 2223886768545278160632081)
                      ·
                        rfl

theorem cell23_4331004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_4331004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331004 prefixEnd_4331004 := by exact prefixLift 4331004
  have htrace : WordTrace (prefixWord ++ tailWord_4331004) baseStart_4331004 baseEnd_4331004 := by
    simpa [prefixWord, tailWord_4331004, baseEnd_4331004] using wordTrace_append hprefix tailTrace_4331004
  have hstable : (prefixWord ++ tailWord_4331004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331004).length < 2 ^ (prefixWord ++ tailWord_4331004).sum := by decide
  have hdescent : baseEnd_4331004 < baseStart_4331004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331022 : List Nat := [4, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2]
def baseStart_4331022 : Nat := 118140960795 + 4331022 * 2 ^ 59
def prefixEnd_4331022 : Nat := 4983230072969 + 3 ^ 40 * 4331022 * 2
def baseEnd_4331022 : Nat := 2223896011197059090206999

theorem tailTrace_4331022 : CollatzResearch.WordTrace tailWord_4331022 prefixEnd_4331022 2223896011197059090206999 := by
  unfold tailWord_4331022
  simp only [CollatzResearch.WordTrace]
  refine ⟨19745668714431806064225415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105310233143636299009202213 19745668714431806064225415)
  ·
    refine ⟨29618503071647709096338123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19745668714431806064225415 29618503071647709096338123)
    ·
      refine ⟨44427754607471563644507185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29618503071647709096338123 44427754607471563644507185)
      ·
        refine ⟨33320815955603672733380389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44427754607471563644507185 33320815955603672733380389)
        ·
          refine ⟨6247652991675688637508823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33320815955603672733380389 6247652991675688637508823)
          ·
            refine ⟨9371479487513532956263235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6247652991675688637508823 9371479487513532956263235)
            ·
              refine ⟨14057219231270299434394853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9371479487513532956263235 14057219231270299434394853)
              ·
                refine ⟨2635728605863181143949035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14057219231270299434394853 2635728605863181143949035)
                ·
                  refine ⟨3953592908794771715923553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2635728605863181143949035 3953592908794771715923553)
                  ·
                    refine ⟨2965194681596078786942665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3953592908794771715923553 2965194681596078786942665)
                    ·
                      refine ⟨2223896011197059090206999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2965194681596078786942665 2223896011197059090206999)
                      ·
                        rfl

theorem cell23_4331022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_4331022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331022 prefixEnd_4331022 := by exact prefixLift 4331022
  have htrace : WordTrace (prefixWord ++ tailWord_4331022) baseStart_4331022 baseEnd_4331022 := by
    simpa [prefixWord, tailWord_4331022, baseEnd_4331022] using wordTrace_append hprefix tailTrace_4331022
  have hstable : (prefixWord ++ tailWord_4331022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331022).length < 2 ^ (prefixWord ++ tailWord_4331022).sum := by decide
  have hdescent : baseEnd_4331022 < baseStart_4331022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331028 : List Nat := [2, 4, 3, 1, 2, 2, 1, 8]
def baseStart_4331028 : Nat := 118140960795 + 4331028 * 2 ^ 59
def prefixEnd_4331028 : Nat := 4983230072969 + 3 ^ 40 * 4331028 * 2
def baseEnd_4331028 : Nat := 82366633040036520990073

theorem tailTrace_4331028 : CollatzResearch.WordTrace tailWord_4331028 prefixEnd_4331028 82366633040036520990073 := by
  unfold tailWord_4331028
  simp only [CollatzResearch.WordTrace]
  refine ⟨78982784276716355769260869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105310379035621807692347825 78982784276716355769260869)
  ·
    refine ⟨14809272051884316706736413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78982784276716355769260869 14809272051884316706736413)
    ·
      refine ⟨5553477019456618765026155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14809272051884316706736413 5553477019456618765026155)
      ·
        refine ⟨8330215529184928147539233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5553477019456618765026155 8330215529184928147539233)
        ·
          refine ⟨6247661646888696110654425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8330215529184928147539233 6247661646888696110654425)
          ·
            refine ⟨4685746235166522082990819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6247661646888696110654425 4685746235166522082990819)
            ·
              refine ⟨7028619352749783124486229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4685746235166522082990819 7028619352749783124486229)
              ·
                refine ⟨82366633040036520990073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7028619352749783124486229 82366633040036520990073)
                ·
                  rfl

theorem cell23_4331028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 8].length) (baseStart_4331028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331028 prefixEnd_4331028 := by exact prefixLift 4331028
  have htrace : WordTrace (prefixWord ++ tailWord_4331028) baseStart_4331028 baseEnd_4331028 := by
    simpa [prefixWord, tailWord_4331028, baseEnd_4331028] using wordTrace_append hprefix tailTrace_4331028
  have hstable : (prefixWord ++ tailWord_4331028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331028).length < 2 ^ (prefixWord ++ tailWord_4331028).sum := by decide
  have hdescent : baseEnd_4331028 < baseStart_4331028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331065 : List Nat := [1, 2, 1, 5, 1, 2, 4, 1, 1, 3, 2]
def baseStart_4331065 : Nat := 118140960795 + 4331065 * 2 ^ 59
def prefixEnd_4331065 : Nat := 4983230072969 + 3 ^ 40 * 4331065 * 2
def baseEnd_4331065 : Nat := 2223918090865202421969301

theorem tailTrace_4331065 : CollatzResearch.WordTrace tailWord_4331065 prefixEnd_4331065 2223918090865202421969301 := by
  unfold tailWord_4331065
  simp only [CollatzResearch.WordTrace]
  refine ⟨157966918054298666857618649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105311278702865777905079099 157966918054298666857618649)
  ·
    refine ⟨118475188540724000143213987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157966918054298666857618649 118475188540724000143213987)
    ·
      refine ⟨177712782811086000214820981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118475188540724000143213987 177712782811086000214820981)
      ·
        refine ⟨16660573388539312520139467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 177712782811086000214820981 16660573388539312520139467)
        ·
          refine ⟨24990860082808968780209201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16660573388539312520139467 24990860082808968780209201)
          ·
            refine ⟨18743145062106726585156901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24990860082808968780209201 18743145062106726585156901)
            ·
              refine ⟨3514339699145011234716919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18743145062106726585156901 3514339699145011234716919)
              ·
                refine ⟨5271509548717516852075379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3514339699145011234716919 5271509548717516852075379)
                ·
                  refine ⟨7907264323076275278113069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5271509548717516852075379 7907264323076275278113069)
                  ·
                    refine ⟨2965224121153603229292401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7907264323076275278113069 2965224121153603229292401)
                    ·
                      refine ⟨2223918090865202421969301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2965224121153603229292401 2223918090865202421969301)
                      ·
                        rfl

theorem cell23_4331065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_4331065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331065 prefixEnd_4331065 := by exact prefixLift 4331065
  have htrace : WordTrace (prefixWord ++ tailWord_4331065) baseStart_4331065 baseEnd_4331065 := by
    simpa [prefixWord, tailWord_4331065, baseEnd_4331065] using wordTrace_append hprefix tailTrace_4331065
  have hstable : (prefixWord ++ tailWord_4331065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331065).length < 2 ^ (prefixWord ++ tailWord_4331065).sum := by decide
  have hdescent : baseEnd_4331065 < baseStart_4331065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331084 : List Nat := [2, 2, 1, 3, 1, 3, 1, 3, 7]
def baseStart_4331084 : Nat := 118140960795 + 4331084 * 2 ^ 59
def prefixEnd_4331084 : Nat := 4983230072969 + 3 ^ 40 * 4331084 * 2
def baseEnd_4331084 : Nat := 247103094110848649736857

theorem tailTrace_4331084 : CollatzResearch.WordTrace tailWord_4331084 prefixEnd_4331084 247103094110848649736857 := by
  unfold tailWord_4331084
  simp only [CollatzResearch.WordTrace]
  refine ⟨78983805520614916551280153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105311740694153222068373537 78983805520614916551280153)
  ·
    refine ⟨59237854140461187413460115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78983805520614916551280153 59237854140461187413460115)
    ·
      refine ⟨88856781210691781120190173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59237854140461187413460115 88856781210691781120190173)
      ·
        refine ⟨33321292954009417920071315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88856781210691781120190173 33321292954009417920071315)
        ·
          refine ⟨49981939431014126880106973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33321292954009417920071315 49981939431014126880106973)
          ·
            refine ⟨18743227286630297580040115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49981939431014126880106973 18743227286630297580040115)
            ·
              refine ⟨28114840929945446370060173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18743227286630297580040115 28114840929945446370060173)
              ·
                refine ⟨10543065348729542388772565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28114840929945446370060173 10543065348729542388772565)
                ·
                  refine ⟨247103094110848649736857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10543065348729542388772565 247103094110848649736857)
                  ·
                    rfl

theorem cell23_4331084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 7].length) (baseStart_4331084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331084 prefixEnd_4331084 := by exact prefixLift 4331084
  have htrace : WordTrace (prefixWord ++ tailWord_4331084) baseStart_4331084 baseEnd_4331084 := by
    simpa [prefixWord, tailWord_4331084, baseEnd_4331084] using wordTrace_append hprefix tailTrace_4331084
  have hstable : (prefixWord ++ tailWord_4331084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331084).length < 2 ^ (prefixWord ++ tailWord_4331084).sum := by decide
  have hdescent : baseEnd_4331084 < baseStart_4331084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331168 : List Nat := [2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 4]
def baseStart_4331168 : Nat := 118140960795 + 4331168 * 2 ^ 59
def prefixEnd_4331168 : Nat := 4983230072969 + 3 ^ 40 * 4331168 * 2
def baseEnd_4331168 : Nat := 2223970979372615518981327

theorem tailTrace_4331168 : CollatzResearch.WordTrace tailWord_4331168 prefixEnd_4331168 2223970979372615518981327 := by
  unfold tailWord_4331168
  simp only [CollatzResearch.WordTrace]
  refine ⟨78985337386462757724309079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105313783181950343632412105 78985337386462757724309079)
  ·
    refine ⟨118478006079694136586463619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78985337386462757724309079 118478006079694136586463619)
    ·
      refine ⟨177717009119541204879695429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118478006079694136586463619 177717009119541204879695429)
      ·
        refine ⟨33321939209913975914942893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177717009119541204879695429 33321939209913975914942893)
        ·
          refine ⟨12495727203717740968103585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33321939209913975914942893 12495727203717740968103585)
          ·
            refine ⟨9371795402788305726077689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12495727203717740968103585 9371795402788305726077689)
            ·
              refine ⟨7028846552091229294558267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9371795402788305726077689 7028846552091229294558267)
              ·
                refine ⟨10543269828136843941837401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7028846552091229294558267 10543269828136843941837401)
                ·
                  refine ⟨7907452371102632956378051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10543269828136843941837401 7907452371102632956378051)
                  ·
                    refine ⟨11861178556653949434567077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7907452371102632956378051 11861178556653949434567077)
                    ·
                      refine ⟨2223970979372615518981327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11861178556653949434567077 2223970979372615518981327)
                      ·
                        rfl

theorem cell23_4331168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_4331168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331168 prefixEnd_4331168 := by exact prefixLift 4331168
  have htrace : WordTrace (prefixWord ++ tailWord_4331168) baseStart_4331168 baseEnd_4331168 := by
    simpa [prefixWord, tailWord_4331168, baseEnd_4331168] using wordTrace_append hprefix tailTrace_4331168
  have hstable : (prefixWord ++ tailWord_4331168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331168).length < 2 ^ (prefixWord ++ tailWord_4331168).sum := by decide
  have hdescent : baseEnd_4331168 < baseStart_4331168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331181 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_4331181 : Nat := 118140960795 + 4331181 * 2 ^ 59
def prefixEnd_4331181 : Nat := 4983230072969 + 3 ^ 40 * 4331181 * 2
def baseEnd_4331181 : Nat := 2223977654621123968118767

theorem tailTrace_4331181 : CollatzResearch.WordTrace tailWord_4331181 prefixEnd_4331181 2223977654621123968118767 := by
  unfold tailWord_4331181
  simp only [CollatzResearch.WordTrace]
  refine ⟨157971148921878418668841397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105314099281252279112560931 157971148921878418668841397)
  ·
    refine ⟨14809795211426101750203881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157971148921878418668841397 14809795211426101750203881)
    ·
      refine ⟨11107346408569576312652911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14809795211426101750203881 11107346408569576312652911)
      ·
        refine ⟨16661019612854364468979367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11107346408569576312652911 16661019612854364468979367)
        ·
          refine ⟨24991529419281546703469051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16661019612854364468979367 24991529419281546703469051)
          ·
            refine ⟨37487294128922320055203577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24991529419281546703469051 37487294128922320055203577)
            ·
              refine ⟨28115470596691740041402683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37487294128922320055203577 28115470596691740041402683)
              ·
                refine ⟨42173205895037610062104025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28115470596691740041402683 42173205895037610062104025)
                ·
                  refine ⟨31629904421278207546578019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42173205895037610062104025 31629904421278207546578019)
                  ·
                    refine ⟨47444856631917311319867029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31629904421278207546578019 47444856631917311319867029)
                    ·
                      refine ⟨2223977654621123968118767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47444856631917311319867029 2223977654621123968118767)
                      ·
                        rfl

theorem cell23_4331181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_4331181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331181 prefixEnd_4331181 := by exact prefixLift 4331181
  have htrace : WordTrace (prefixWord ++ tailWord_4331181) baseStart_4331181 baseEnd_4331181 := by
    simpa [prefixWord, tailWord_4331181, baseEnd_4331181] using wordTrace_append hprefix tailTrace_4331181
  have hstable : (prefixWord ++ tailWord_4331181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331181).length < 2 ^ (prefixWord ++ tailWord_4331181).sum := by decide
  have hdescent : baseEnd_4331181 < baseStart_4331181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331191 : List Nat := [1, 1, 3, 1, 5, 1, 1, 4, 6]
def baseStart_4331191 : Nat := 118140960795 + 4331191 * 2 ^ 59
def prefixEnd_4331191 : Nat := 4983230072969 + 3 ^ 40 * 4331191 * 2
def baseEnd_4331191 : Nat := 247109198825296547665969

theorem tailTrace_4331191 : CollatzResearch.WordTrace tailWord_4331191 prefixEnd_4331191 247109198825296547665969 := by
  unfold tailWord_4331191
  simp only [CollatzResearch.WordTrace]
  refine ⟨157971513651842190376705427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105314342434561460251136951 157971513651842190376705427)
  ·
    refine ⟨236957270477763285565058141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157971513651842190376705427 236957270477763285565058141)
    ·
      refine ⟨88858976429161232086896803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236957270477763285565058141 88858976429161232086896803)
      ·
        refine ⟨133288464643741848130345205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88858976429161232086896803 133288464643741848130345205)
        ·
          refine ⟨12495793560350798262219863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 133288464643741848130345205 12495793560350798262219863)
          ·
            refine ⟨18743690340526197393329795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12495793560350798262219863 18743690340526197393329795)
            ·
              refine ⟨28115535510789296089994693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18743690340526197393329795 28115535510789296089994693)
              ·
                refine ⟨5271662908272993016874005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28115535510789296089994693 5271662908272993016874005)
                ·
                  refine ⟨247109198825296547665969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5271662908272993016874005 247109198825296547665969)
                  ·
                    rfl

theorem cell23_4331191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 6].length) (baseStart_4331191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331191 prefixEnd_4331191 := by exact prefixLift 4331191
  have htrace : WordTrace (prefixWord ++ tailWord_4331191) baseStart_4331191 baseEnd_4331191 := by
    simpa [prefixWord, tailWord_4331191, baseEnd_4331191] using wordTrace_append hprefix tailTrace_4331191
  have hstable : (prefixWord ++ tailWord_4331191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331191).length < 2 ^ (prefixWord ++ tailWord_4331191).sum := by decide
  have hdescent : baseEnd_4331191 < baseStart_4331191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331222 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_4331222 : Nat := 118140960795 + 4331222 * 2 ^ 59
def prefixEnd_4331222 : Nat := 4983230072969 + 3 ^ 40 * 4331222 * 2
def baseEnd_4331222 : Nat := 2223998707327958307706079

theorem tailTrace_4331222 : CollatzResearch.WordTrace tailWord_4331222 prefixEnd_4331222 2223998707327958307706079 := by
  unfold tailWord_4331222
  simp only [CollatzResearch.WordTrace]
  refine ⟨9873290269670617666942745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105315096209819921780722613 9873290269670617666942745)
  ·
    refine ⟨7404967702252963250207059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9873290269670617666942745 7404967702252963250207059)
    ·
      refine ⟨11107451553379444875310589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7404967702252963250207059 11107451553379444875310589)
      ·
        refine ⟨4165294332517291828241471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11107451553379444875310589 4165294332517291828241471)
        ·
          refine ⟨6247941498775937742362207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4165294332517291828241471 6247941498775937742362207)
          ·
            refine ⟨9371912248163906613543311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6247941498775937742362207 9371912248163906613543311)
            ·
              refine ⟨14057868372245859920314967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9371912248163906613543311 14057868372245859920314967)
              ·
                refine ⟨21086802558368789880472451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14057868372245859920314967 21086802558368789880472451)
                ·
                  refine ⟨31630203837553184820708677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21086802558368789880472451 31630203837553184820708677)
                  ·
                    refine ⟨5930663219541222153882877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31630203837553184820708677 5930663219541222153882877)
                    ·
                      refine ⟨2223998707327958307706079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5930663219541222153882877 2223998707327958307706079)
                      ·
                        rfl

theorem cell23_4331222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_4331222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331222 prefixEnd_4331222 := by exact prefixLift 4331222
  have htrace : WordTrace (prefixWord ++ tailWord_4331222) baseStart_4331222 baseEnd_4331222 := by
    simpa [prefixWord, tailWord_4331222, baseEnd_4331222] using wordTrace_append hprefix tailTrace_4331222
  have hstable : (prefixWord ++ tailWord_4331222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331222).length < 2 ^ (prefixWord ++ tailWord_4331222).sum := by decide
  have hdescent : baseEnd_4331222 < baseStart_4331222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331229 : List Nat := [1, 4, 3, 3, 1, 1, 2, 3, 1, 4]
def baseStart_4331229 : Nat := 118140960795 + 4331229 * 2 ^ 59
def prefixEnd_4331229 : Nat := 4983230072969 + 3 ^ 40 * 4331229 * 2
def baseEnd_4331229 : Nat := 741334100564179926772849

theorem tailTrace_4331229 : CollatzResearch.WordTrace tailWord_4331229 prefixEnd_4331229 741334100564179926772849 := by
  unfold tailWord_4331229
  simp only [CollatzResearch.WordTrace]
  refine ⟨157972899625704522866588741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105315266417136348577725827 157972899625704522866588741)
  ·
    refine ⟨29619918679819598037485389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157972899625704522866588741 29619918679819598037485389)
    ·
      refine ⟨11107469504932349264057021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29619918679819598037485389 11107469504932349264057021)
      ·
        refine ⟨4165301064349630974021383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11107469504932349264057021 4165301064349630974021383)
        ·
          refine ⟨6247951596524446461032075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4165301064349630974021383 6247951596524446461032075)
          ·
            refine ⟨9371927394786669691548113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6247951596524446461032075 9371927394786669691548113)
            ·
              refine ⟨7028945546090002268661085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9371927394786669691548113 7028945546090002268661085)
              ·
                refine ⟨2635854579783750850747907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7028945546090002268661085 2635854579783750850747907)
                ·
                  refine ⟨3953781869675626276121861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2635854579783750850747907 3953781869675626276121861)
                  ·
                    refine ⟨741334100564179926772849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3953781869675626276121861 741334100564179926772849)
                    ·
                      rfl

theorem cell23_4331229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_4331229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331229 prefixEnd_4331229 := by exact prefixLift 4331229
  have htrace : WordTrace (prefixWord ++ tailWord_4331229) baseStart_4331229 baseEnd_4331229 := by
    simpa [prefixWord, tailWord_4331229, baseEnd_4331229] using wordTrace_append hprefix tailTrace_4331229
  have hstable : (prefixWord ++ tailWord_4331229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331229).length < 2 ^ (prefixWord ++ tailWord_4331229).sum := by decide
  have hdescent : baseEnd_4331229 < baseStart_4331229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331261 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 2, 6, 3]
def baseStart_4331261 : Nat := 118140960795 + 4331261 * 2 ^ 59
def prefixEnd_4331261 : Nat := 4983230072969 + 3 ^ 40 * 4331261 * 2
def baseEnd_4331261 : Nat := 2224018733073483655118399

theorem tailTrace_4331261 : CollatzResearch.WordTrace tailWord_4331261 prefixEnd_4331261 2224018733073483655118399 := by
  unfold tailWord_4331261
  simp only [CollatzResearch.WordTrace]
  refine ⟨157974066761588592331753637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105316044507725728221169091 157974066761588592331753637)
  ·
    refine ⟨29620137517797861062203807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157974066761588592331753637 29620137517797861062203807)
    ·
      refine ⟨44430206276696791593305711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29620137517797861062203807 44430206276696791593305711)
      ·
        refine ⟨66645309415045187389958567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44430206276696791593305711 66645309415045187389958567)
        ·
          refine ⟨99967964122567781084937851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66645309415045187389958567 99967964122567781084937851)
          ·
            refine ⟨149951946183851671627406777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99967964122567781084937851 149951946183851671627406777)
            ·
              refine ⟨112463959637888753720555083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149951946183851671627406777 112463959637888753720555083)
              ·
                refine ⟨168695939456833130580832625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112463959637888753720555083 168695939456833130580832625)
                ·
                  refine ⟨126521954592624847935624469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168695939456833130580832625 126521954592624847935624469)
                  ·
                    refine ⟨5930716621529289746982397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 126521954592624847935624469 5930716621529289746982397)
                    ·
                      refine ⟨2224018733073483655118399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5930716621529289746982397 2224018733073483655118399)
                      ·
                        rfl

theorem cell23_4331261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_4331261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331261 prefixEnd_4331261 := by exact prefixLift 4331261
  have htrace : WordTrace (prefixWord ++ tailWord_4331261) baseStart_4331261 baseEnd_4331261 := by
    simpa [prefixWord, tailWord_4331261, baseEnd_4331261] using wordTrace_append hprefix tailTrace_4331261
  have hstable : (prefixWord ++ tailWord_4331261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331261).length < 2 ^ (prefixWord ++ tailWord_4331261).sum := by decide
  have hdescent : baseEnd_4331261 < baseStart_4331261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331268 : List Nat := [2, 3, 2, 2, 1, 2, 3, 1, 1, 6]
def baseStart_4331268 : Nat := 118140960795 + 4331268 * 2 ^ 59
def prefixEnd_4331268 : Nat := 4983230072969 + 3 ^ 40 * 4331268 * 2
def baseEnd_4331268 : Nat := 741340775812688375910289

theorem tailTrace_4331268 : CollatzResearch.WordTrace tailWord_4331268 prefixEnd_4331268 741340775812688375910289 := by
  unfold tailWord_4331268
  simp only [CollatzResearch.WordTrace]
  refine ⟨78987161036281616263629229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105316214715042155018172305 78987161036281616263629229)
  ·
    refine ⟨29620185388605606098860961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78987161036281616263629229 29620185388605606098860961)
    ·
      refine ⟨22215139041454204574145721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29620185388605606098860961 22215139041454204574145721)
      ·
        refine ⟨16661354281090653430609291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22215139041454204574145721 16661354281090653430609291)
        ·
          refine ⟨24992031421635980145913937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16661354281090653430609291 24992031421635980145913937)
          ·
            refine ⟨18744023566226985109435453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24992031421635980145913937 18744023566226985109435453)
            ·
              refine ⟨7029008837335119416038295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18744023566226985109435453 7029008837335119416038295)
              ·
                refine ⟨10543513256002679124057443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7029008837335119416038295 10543513256002679124057443)
                ·
                  refine ⟨15815269884004018686086165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10543513256002679124057443 15815269884004018686086165)
                  ·
                    refine ⟨741340775812688375910289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15815269884004018686086165 741340775812688375910289)
                    ·
                      rfl

theorem cell23_4331268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_4331268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331268 prefixEnd_4331268 := by exact prefixLift 4331268
  have htrace : WordTrace (prefixWord ++ tailWord_4331268) baseStart_4331268 baseEnd_4331268 := by
    simpa [prefixWord, tailWord_4331268, baseEnd_4331268] using wordTrace_append hprefix tailTrace_4331268
  have hstable : (prefixWord ++ tailWord_4331268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331268).length < 2 ^ (prefixWord ++ tailWord_4331268).sum := by decide
  have hdescent : baseEnd_4331268 < baseStart_4331268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331275 : List Nat := [1, 1, 1, 1, 5, 1, 4, 2, 3, 2, 2]
def baseStart_4331275 : Nat := 118140960795 + 4331275 * 2 ^ 59
def prefixEnd_4331275 : Nat := 4983230072969 + 3 ^ 40 * 4331275 * 2
def baseEnd_4331275 : Nat := 2224025921802646600343335

theorem tailTrace_4331275 : CollatzResearch.WordTrace tailWord_4331275 prefixEnd_4331275 2224025921802646600343335 := by
  unfold tailWord_4331275
  simp only [CollatzResearch.WordTrace]
  refine ⟨157974577383537872722763279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105316384922358581815175519 157974577383537872722763279)
  ·
    refine ⟨236961866075306809084144919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157974577383537872722763279 236961866075306809084144919)
    ·
      refine ⟨355442799112960213626217379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236961866075306809084144919 355442799112960213626217379)
      ·
        refine ⟨533164198669440320439326069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355442799112960213626217379 533164198669440320439326069)
        ·
          refine ⟨49984143625260030041186819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 533164198669440320439326069 49984143625260030041186819)
          ·
            refine ⟨74976215437890045061780229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49984143625260030041186819 74976215437890045061780229)
            ·
              refine ⟨14058040394604383449083793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74976215437890045061780229 14058040394604383449083793)
              ·
                refine ⟨10543530295953287586812845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14058040394604383449083793 10543530295953287586812845)
                ·
                  refine ⟨3953823860982482845054817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10543530295953287586812845 3953823860982482845054817)
                  ·
                    refine ⟨2965367895736862133791113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3953823860982482845054817 2965367895736862133791113)
                    ·
                      refine ⟨2224025921802646600343335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2965367895736862133791113 2224025921802646600343335)
                      ·
                        rfl

theorem cell23_4331275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 2, 2].length) (baseStart_4331275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331275 prefixEnd_4331275 := by exact prefixLift 4331275
  have htrace : WordTrace (prefixWord ++ tailWord_4331275) baseStart_4331275 baseEnd_4331275 := by
    simpa [prefixWord, tailWord_4331275, baseEnd_4331275] using wordTrace_append hprefix tailTrace_4331275
  have hstable : (prefixWord ++ tailWord_4331275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331275).length < 2 ^ (prefixWord ++ tailWord_4331275).sum := by decide
  have hdescent : baseEnd_4331275 < baseStart_4331275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331278 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3]
def baseStart_4331278 : Nat := 118140960795 + 4331278 * 2 ^ 59
def prefixEnd_4331278 : Nat := 4983230072969 + 3 ^ 40 * 4331278 * 2
def baseEnd_4331278 : Nat := 2224027462244610088605821

theorem tailTrace_4331278 : CollatzResearch.WordTrace tailWord_4331278 prefixEnd_4331278 2224027462244610088605821 := by
  unfold tailWord_4331278
  simp only [CollatzResearch.WordTrace]
  refine ⟨19746835850315875529390311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105316457868351336156748325 19746835850315875529390311)
  ·
    refine ⟨29620253775473813294085467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19746835850315875529390311 29620253775473813294085467)
    ·
      refine ⟨44430380663210719941128201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29620253775473813294085467 44430380663210719941128201)
      ·
        refine ⟨33322785497408039955846151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44430380663210719941128201 33322785497408039955846151)
        ·
          refine ⟨49984178246112059933769227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33322785497408039955846151 49984178246112059933769227)
          ·
            refine ⟨74976267369168089900653841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49984178246112059933769227 74976267369168089900653841)
            ·
              refine ⟨56232200526876067425490381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74976267369168089900653841 56232200526876067425490381)
              ·
                refine ⟨21087075197578525284558893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56232200526876067425490381 21087075197578525284558893)
                ·
                  refine ⟨7907653199091946981709585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21087075197578525284558893 7907653199091946981709585)
                  ·
                    refine ⟨5930739899318960236282189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7907653199091946981709585 5930739899318960236282189)
                    ·
                      refine ⟨2224027462244610088605821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5930739899318960236282189 2224027462244610088605821)
                      ·
                        rfl

theorem cell23_4331278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_4331278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331278 prefixEnd_4331278 := by exact prefixLift 4331278
  have htrace : WordTrace (prefixWord ++ tailWord_4331278) baseStart_4331278 baseEnd_4331278 := by
    simpa [prefixWord, tailWord_4331278, baseEnd_4331278] using wordTrace_append hprefix tailTrace_4331278
  have hstable : (prefixWord ++ tailWord_4331278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331278).length < 2 ^ (prefixWord ++ tailWord_4331278).sum := by decide
  have hdescent : baseEnd_4331278 < baseStart_4331278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331368 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_4331368 : Nat := 118140960795 + 4331368 * 2 ^ 59
def prefixEnd_4331368 : Nat := 4983230072969 + 3 ^ 40 * 4331368 * 2
def baseEnd_4331368 : Nat := 2224073675503514736480407

theorem tailTrace_4331368 : CollatzResearch.WordTrace tailWord_4331368 prefixEnd_4331368 2224073675503514736480407 := by
  unfold tailWord_4331368
  simp only [CollatzResearch.WordTrace]
  refine ⟨78988984686100474802949379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105318646248133966403932505 78988984686100474802949379)
  ·
    refine ⟨118483477029150712204424069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78988984686100474802949379 118483477029150712204424069)
    ·
      refine ⟨22215651942965758538329513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118483477029150712204424069 22215651942965758538329513)
      ·
        refine ⟨16661738957224318903747135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22215651942965758538329513 16661738957224318903747135)
        ·
          refine ⟨24992608435836478355620703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16661738957224318903747135 24992608435836478355620703)
          ·
            refine ⟨37488912653754717533431055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24992608435836478355620703 37488912653754717533431055)
            ·
              refine ⟨56233368980632076300146583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37488912653754717533431055 56233368980632076300146583)
              ·
                refine ⟨84350053470948114450219875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56233368980632076300146583 84350053470948114450219875)
                ·
                  refine ⟨126525080206422171675329813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84350053470948114450219875 126525080206422171675329813)
                  ·
                    refine ⟨5930863134676039297281085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 126525080206422171675329813 5930863134676039297281085)
                    ·
                      refine ⟨2224073675503514736480407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5930863134676039297281085 2224073675503514736480407)
                      ·
                        rfl

theorem cell23_4331368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_4331368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331368 prefixEnd_4331368 := by exact prefixLift 4331368
  have htrace : WordTrace (prefixWord ++ tailWord_4331368) baseStart_4331368 baseEnd_4331368 := by
    simpa [prefixWord, tailWord_4331368, baseEnd_4331368] using wordTrace_append hprefix tailTrace_4331368
  have hstable : (prefixWord ++ tailWord_4331368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331368).length < 2 ^ (prefixWord ++ tailWord_4331368).sum := by decide
  have hdescent : baseEnd_4331368 < baseStart_4331368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331371 : List Nat := [1, 1, 1, 1, 2, 2, 3, 5, 7]
def baseStart_4331371 : Nat := 118140960795 + 4331371 * 2 ^ 59
def prefixEnd_4331371 : Nat := 4983230072969 + 3 ^ 40 * 4331371 * 2
def baseEnd_4331371 : Nat := 247119468438386469415877

theorem tailTrace_4331371 : CollatzResearch.WordTrace tailWord_4331371 prefixEnd_4331371 247119468438386469415877 := by
  unfold tailWord_4331371
  simp only [CollatzResearch.WordTrace]
  refine ⟨157978078791190081118257967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105318719194126720745505311 157978078791190081118257967)
  ·
    refine ⟨236967118186785121677386951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157978078791190081118257967 236967118186785121677386951)
    ·
      refine ⟨355450677280177682516080427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236967118186785121677386951 355450677280177682516080427)
      ·
        refine ⟨533176015920266523774120641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355450677280177682516080427 533176015920266523774120641)
        ·
          refine ⟨399882011940199892830590481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 533176015920266523774120641 399882011940199892830590481)
          ·
            refine ⟨299911508955149919622942861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399882011940199892830590481 299911508955149919622942861)
            ·
              refine ⟨112466815858181219858603573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 299911508955149919622942861 112466815858181219858603573)
              ·
                refine ⟨10543763986704489361744085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112466815858181219858603573 10543763986704489361744085)
                ·
                  refine ⟨247119468438386469415877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10543763986704489361744085 247119468438386469415877)
                  ·
                    rfl

theorem cell23_4331371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 7].length) (baseStart_4331371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331371 prefixEnd_4331371 := by exact prefixLift 4331371
  have htrace : WordTrace (prefixWord ++ tailWord_4331371) baseStart_4331371 baseEnd_4331371 := by
    simpa [prefixWord, tailWord_4331371, baseEnd_4331371] using wordTrace_append hprefix tailTrace_4331371
  have hstable : (prefixWord ++ tailWord_4331371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331371).length < 2 ^ (prefixWord ++ tailWord_4331371).sum := by decide
  have hdescent : baseEnd_4331371 < baseStart_4331371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331515 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 1, 5, 2]
def baseStart_4331515 : Nat := 118140960795 + 4331515 * 2 ^ 59
def prefixEnd_4331515 : Nat := 4983230072969 + 3 ^ 40 * 4331515 * 2
def baseEnd_4331515 : Nat := 2224149157159725661342231

theorem tailTrace_4331515 : CollatzResearch.WordTrace tailWord_4331515 prefixEnd_4331515 2224149157159725661342231 := by
  unfold tailWord_4331515
  simp only [CollatzResearch.WordTrace]
  refine ⟨157983330902668393711499999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105322220601778929140999999 157983330902668393711499999)
  ·
    refine ⟨236974996354002590567249999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157983330902668393711499999 236974996354002590567249999)
    ·
      refine ⟨355462494531003885850874999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236974996354002590567249999 355462494531003885850874999)
      ·
        refine ⟨533193741796505828776312499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355462494531003885850874999 533193741796505828776312499)
        ·
          refine ⟨799790612694758743164468749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533193741796505828776312499 799790612694758743164468749)
          ·
            refine ⟨299921479760534528686675781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 799790612694758743164468749 299921479760534528686675781)
            ·
              refine ⟨56235277455100224128751709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 299921479760534528686675781 56235277455100224128751709)
              ·
                refine ⟨21088229045662584048281891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56235277455100224128751709 21088229045662584048281891)
                ·
                  refine ⟨31632343568493876072422837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21088229045662584048281891 31632343568493876072422837)
                  ·
                    refine ⟨2965532209546300881789641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31632343568493876072422837 2965532209546300881789641)
                    ·
                      refine ⟨2224149157159725661342231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2965532209546300881789641 2224149157159725661342231)
                      ·
                        rfl

theorem cell23_4331515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 5, 2].length) (baseStart_4331515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331515 prefixEnd_4331515 := by exact prefixLift 4331515
  have htrace : WordTrace (prefixWord ++ tailWord_4331515) baseStart_4331515 baseEnd_4331515 := by
    simpa [prefixWord, tailWord_4331515, baseEnd_4331515] using wordTrace_append hprefix tailTrace_4331515
  have hstable : (prefixWord ++ tailWord_4331515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331515).length < 2 ^ (prefixWord ++ tailWord_4331515).sum := by decide
  have hdescent : baseEnd_4331515 < baseStart_4331515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331532 : List Nat := [2, 2, 1, 2, 3, 1, 1, 4, 2, 3, 2]
def baseStart_4331532 : Nat := 118140960795 + 4331532 * 2 ^ 59
def prefixEnd_4331532 : Nat := 4983230072969 + 3 ^ 40 * 4331532 * 2
def baseEnd_4331532 : Nat := 2224157886330852094829653

theorem tailTrace_4331532 : CollatzResearch.WordTrace tailWord_4331532 prefixEnd_4331532 2224157886330852094829653 := by
  unfold tailWord_4331532
  simp only [CollatzResearch.WordTrace]
  refine ⟨78991975471803402807434425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105322633962404537076579233 78991975471803402807434425)
  ·
    refine ⟨59243981603852552105575819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78991975471803402807434425 59243981603852552105575819)
    ·
      refine ⟨88865972405778828158363729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59243981603852552105575819 88865972405778828158363729)
      ·
        refine ⟨66649479304334121118772797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88865972405778828158363729 66649479304334121118772797)
        ·
          refine ⟨24993554739125295419539799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66649479304334121118772797 24993554739125295419539799)
          ·
            refine ⟨37490332108687943129309699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24993554739125295419539799 37490332108687943129309699)
            ·
              refine ⟨56235498163031914693964549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37490332108687943129309699 56235498163031914693964549)
              ·
                refine ⟨10544155905568484005118353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56235498163031914693964549 10544155905568484005118353)
                ·
                  refine ⟨7908116929176363003838765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10544155905568484005118353 7908116929176363003838765)
                  ·
                    refine ⟨2965543848441136126439537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7908116929176363003838765 2965543848441136126439537)
                    ·
                      refine ⟨2224157886330852094829653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2965543848441136126439537 2224157886330852094829653)
                      ·
                        rfl

theorem cell23_4331532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_4331532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331532 prefixEnd_4331532 := by exact prefixLift 4331532
  have htrace : WordTrace (prefixWord ++ tailWord_4331532) baseStart_4331532 baseEnd_4331532 := by
    simpa [prefixWord, tailWord_4331532, baseEnd_4331532] using wordTrace_append hprefix tailTrace_4331532
  have hstable : (prefixWord ++ tailWord_4331532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331532).length < 2 ^ (prefixWord ++ tailWord_4331532).sum := by decide
  have hdescent : baseEnd_4331532 < baseStart_4331532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331545 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 2, 6, 2]
def baseStart_4331545 : Nat := 118140960795 + 4331545 * 2 ^ 59
def prefixEnd_4331545 : Nat := 4983230072969 + 3 ^ 40 * 4331545 * 2
def baseEnd_4331545 : Nat := 2224164561579360543967093

theorem tailTrace_4331545 : CollatzResearch.WordTrace tailWord_4331545 prefixEnd_4331545 2224164561579360543967093 := by
  unfold tailWord_4331545
  simp only [CollatzResearch.WordTrace]
  refine ⟨157984425092559708835092089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105322950061706472556728059 157984425092559708835092089)
  ·
    refine ⟨118488318819419781626319067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157984425092559708835092089 118488318819419781626319067)
    ·
      refine ⟨177732478229129672439478601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118488318819419781626319067 177732478229129672439478601)
      ·
        refine ⟨133299358671847254329608951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177732478229129672439478601 133299358671847254329608951)
        ·
          refine ⟨199949038007770881494413427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133299358671847254329608951 199949038007770881494413427)
          ·
            refine ⟨299923557011656322241620141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199949038007770881494413427 299923557011656322241620141)
            ·
              refine ⟨112471333879371120840607553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 299923557011656322241620141 112471333879371120840607553)
              ·
                refine ⟨84353500409528340630455665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112471333879371120840607553 84353500409528340630455665)
                ·
                  refine ⟨63265125307146255472841749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84353500409528340630455665 63265125307146255472841749)
                  ·
                    refine ⟨2965552748772480725289457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63265125307146255472841749 2965552748772480725289457)
                    ·
                      refine ⟨2224164561579360543967093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2965552748772480725289457 2224164561579360543967093)
                      ·
                        rfl

theorem cell23_4331545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 6, 2].length) (baseStart_4331545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331545 prefixEnd_4331545 := by exact prefixLift 4331545
  have htrace : WordTrace (prefixWord ++ tailWord_4331545) baseStart_4331545 baseEnd_4331545 := by
    simpa [prefixWord, tailWord_4331545, baseEnd_4331545] using wordTrace_append hprefix tailTrace_4331545
  have hstable : (prefixWord ++ tailWord_4331545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331545).length < 2 ^ (prefixWord ++ tailWord_4331545).sum := by decide
  have hdescent : baseEnd_4331545 < baseStart_4331545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331555 : List Nat := [1, 1, 1, 4, 3, 1, 4, 1, 1, 6]
def baseStart_4331555 : Nat := 118140960795 + 4331555 * 2 ^ 59
def prefixEnd_4331555 : Nat := 4983230072969 + 3 ^ 40 * 4331555 * 2
def baseEnd_4331555 : Nat := 741389898795301834947349

theorem tailTrace_4331555 : CollatzResearch.WordTrace tailWord_4331555 prefixEnd_4331555 741389898795301834947349 := by
  unfold tailWord_4331555
  simp only [CollatzResearch.WordTrace]
  refine ⟨157984789822523480542956119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105323193215015653695304079 157984789822523480542956119)
  ·
    refine ⟨236977184733785220814434179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157984789822523480542956119 236977184733785220814434179)
    ·
      refine ⟨355465777100677831221651269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236977184733785220814434179 355465777100677831221651269)
      ·
        refine ⟨66649833206377093354059613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 355465777100677831221651269 66649833206377093354059613)
        ·
          refine ⟨24993687452391410007772355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66649833206377093354059613 24993687452391410007772355)
          ·
            refine ⟨37490531178587115011658533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24993687452391410007772355 37490531178587115011658533)
            ·
              refine ⟨7029474595985084064685975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37490531178587115011658533 7029474595985084064685975)
              ·
                refine ⟨10544211893977626097028963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7029474595985084064685975 10544211893977626097028963)
                ·
                  refine ⟨15816317840966439145543445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10544211893977626097028963 15816317840966439145543445)
                  ·
                    refine ⟨741389898795301834947349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15816317840966439145543445 741389898795301834947349)
                    ·
                      rfl

theorem cell23_4331555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 6].length) (baseStart_4331555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331555 prefixEnd_4331555 := by exact prefixLift 4331555
  have htrace : WordTrace (prefixWord ++ tailWord_4331555) baseStart_4331555 baseEnd_4331555 := by
    simpa [prefixWord, tailWord_4331555, baseEnd_4331555] using wordTrace_append hprefix tailTrace_4331555
  have hstable : (prefixWord ++ tailWord_4331555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331555).length < 2 ^ (prefixWord ++ tailWord_4331555).sum := by decide
  have hdescent : baseEnd_4331555 < baseStart_4331555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331562 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_4331562 : Nat := 118140960795 + 4331562 * 2 ^ 59
def prefixEnd_4331562 : Nat := 4983230072969 + 3 ^ 40 * 4331562 * 2
def baseEnd_4331562 : Nat := 2224173290750486977454515

theorem tailTrace_4331562 : CollatzResearch.WordTrace tailWord_4331562 prefixEnd_4331562 2224173290750486977454515 := by
  unfold tailWord_4331562
  simp only [CollatzResearch.WordTrace]
  refine ⟨39496261283374530184615235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105323363422332080492307293 39496261283374530184615235)
  ·
    refine ⟨59244391925061795276922853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39496261283374530184615235 59244391925061795276922853)
    ·
      refine ⟨11108323485949086614423035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59244391925061795276922853 11108323485949086614423035)
      ·
        refine ⟨16662485228923629921634553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11108323485949086614423035 16662485228923629921634553)
        ·
          refine ⟨12496863921692722441225915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16662485228923629921634553 12496863921692722441225915)
          ·
            refine ⟨18745295882539083661838873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12496863921692722441225915 18745295882539083661838873)
            ·
              refine ⟨14058971911904312746379155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18745295882539083661838873 14058971911904312746379155)
              ·
                refine ⟨21088457867856469119568733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14058971911904312746379155 21088457867856469119568733)
                ·
                  refine ⟨7908171700446175919838275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21088457867856469119568733 7908171700446175919838275)
                  ·
                    refine ⟨11862257550669263879757413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7908171700446175919838275 11862257550669263879757413)
                    ·
                      refine ⟨2224173290750486977454515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11862257550669263879757413 2224173290750486977454515)
                      ·
                        rfl

theorem cell23_4331562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_4331562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331562 prefixEnd_4331562 := by exact prefixLift 4331562
  have htrace : WordTrace (prefixWord ++ tailWord_4331562) baseStart_4331562 baseEnd_4331562 := by
    simpa [prefixWord, tailWord_4331562, baseEnd_4331562] using wordTrace_append hprefix tailTrace_4331562
  have hstable : (prefixWord ++ tailWord_4331562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331562).length < 2 ^ (prefixWord ++ tailWord_4331562).sum := by decide
  have hdescent : baseEnd_4331562 < baseStart_4331562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331566 : List Nat := [4, 1, 3, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_4331566 : Nat := 118140960795 + 4331566 * 2 ^ 59
def prefixEnd_4331566 : Nat := 4983230072969 + 3 ^ 40 * 4331566 * 2
def baseEnd_4331566 : Nat := 2224175344673104961804497

theorem tailTrace_4331566 : CollatzResearch.WordTrace tailWord_4331566 prefixEnd_4331566 2224175344673104961804497 := by
  unfold tailWord_4331566
  simp only [CollatzResearch.WordTrace]
  refine ⟨19748148878185453677700819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105323460683655752947737701 19748148878185453677700819)
  ·
    refine ⟨29622223317278180516551229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19748148878185453677700819 29622223317278180516551229)
    ·
      refine ⟨11108333743979317693706711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29622223317278180516551229 11108333743979317693706711)
      ·
        refine ⟨16662500615968976540560067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11108333743979317693706711 16662500615968976540560067)
        ·
          refine ⟨24993750923953464810840101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16662500615968976540560067 24993750923953464810840101)
          ·
            refine ⟨4686328298241274652032519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24993750923953464810840101 4686328298241274652032519)
            ·
              refine ⟨7029492447361911978048779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4686328298241274652032519 7029492447361911978048779)
              ·
                refine ⟨10544238671042867967073169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7029492447361911978048779 10544238671042867967073169)
                ·
                  refine ⟨7908179003282150975304877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10544238671042867967073169 7908179003282150975304877)
                  ·
                    refine ⟨2965567126230806615739329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7908179003282150975304877 2965567126230806615739329)
                    ·
                      refine ⟨2224175344673104961804497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2965567126230806615739329 2224175344673104961804497)
                      ·
                        rfl

theorem cell23_4331566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_4331566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331566 prefixEnd_4331566 := by exact prefixLift 4331566
  have htrace : WordTrace (prefixWord ++ tailWord_4331566) baseStart_4331566 baseEnd_4331566 := by
    simpa [prefixWord, tailWord_4331566, baseEnd_4331566] using wordTrace_append hprefix tailTrace_4331566
  have hstable : (prefixWord ++ tailWord_4331566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331566).length < 2 ^ (prefixWord ++ tailWord_4331566).sum := by decide
  have hdescent : baseEnd_4331566 < baseStart_4331566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331575 : List Nat := [1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 4]
def baseStart_4331575 : Nat := 118140960795 + 4331575 * 2 ^ 59
def prefixEnd_4331575 : Nat := 4983230072969 + 3 ^ 40 * 4331575 * 2
def baseEnd_4331575 : Nat := 2224179965998995426591955

theorem tailTrace_4331575 : CollatzResearch.WordTrace tailWord_4331575 prefixEnd_4331575 2224179965998995426591955 := by
  unfold tailWord_4331575
  simp only [CollatzResearch.WordTrace]
  refine ⟨157985519282451023958684179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105323679521634015972456119 157985519282451023958684179)
  ·
    refine ⟨236978278923676535938026269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157985519282451023958684179 236978278923676535938026269)
    ·
      refine ⟨88866854596378700976759851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236978278923676535938026269 88866854596378700976759851)
      ·
        refine ⟨133300281894568051465139777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88866854596378700976759851 133300281894568051465139777)
        ·
          refine ⟨99975211420926038598854833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133300281894568051465139777 99975211420926038598854833)
          ·
            refine ⟨74981408565694528949141125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99975211420926038598854833 74981408565694528949141125)
            ·
              refine ⟨14059014106067724177963961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74981408565694528949141125 14059014106067724177963961)
              ·
                refine ⟨10544260579550793133472971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14059014106067724177963961 10544260579550793133472971)
                ·
                  refine ⟨15816390869326189700209457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10544260579550793133472971 15816390869326189700209457)
                  ·
                    refine ⟨11862293151994642275157093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15816390869326189700209457 11862293151994642275157093)
                    ·
                      refine ⟨2224179965998995426591955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11862293151994642275157093 2224179965998995426591955)
                      ·
                        rfl

theorem cell23_4331575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_4331575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331575 prefixEnd_4331575 := by exact prefixLift 4331575
  have htrace : WordTrace (prefixWord ++ tailWord_4331575) baseStart_4331575 baseEnd_4331575 := by
    simpa [prefixWord, tailWord_4331575, baseEnd_4331575] using wordTrace_append hprefix tailTrace_4331575
  have hstable : (prefixWord ++ tailWord_4331575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331575).length < 2 ^ (prefixWord ++ tailWord_4331575).sum := by decide
  have hdescent : baseEnd_4331575 < baseStart_4331575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331576 : List Nat := [2, 1, 2, 1, 7, 1, 2, 1, 1, 5]
def baseStart_4331576 : Nat := 118140960795 + 4331576 * 2 ^ 59
def prefixEnd_4331576 : Nat := 4983230072969 + 3 ^ 40 * 4331576 * 2
def baseEnd_4331576 : Nat := 741393493159883307559817

theorem tailTrace_4331576 : CollatzResearch.WordTrace tailWord_4331576 prefixEnd_4331576 741393493159883307559817 := by
  unfold tailWord_4331576
  simp only [CollatzResearch.WordTrace]
  refine ⟨78992777877723700564735291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105323703836964934086313721 78992777877723700564735291)
  ·
    refine ⟨118489166816585550847102937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78992777877723700564735291 118489166816585550847102937)
    ·
      refine ⟨88866875112439163135327203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118489166816585550847102937 88866875112439163135327203)
      ·
        refine ⟨133300312668658744702990805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88866875112439163135327203 133300312668658744702990805)
        ·
          refine ⟨3124226078171689328976347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 133300312668658744702990805 3124226078171689328976347)
          ·
            refine ⟨4686339117257533993464521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3124226078171689328976347 4686339117257533993464521)
            ·
              refine ⟨3514754337943150495098391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4686339117257533993464521 3514754337943150495098391)
              ·
                refine ⟨5272131506914725742647587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3514754337943150495098391 5272131506914725742647587)
                ·
                  refine ⟨7908197260372088613971381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5272131506914725742647587 7908197260372088613971381)
                  ·
                    refine ⟨741393493159883307559817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7908197260372088613971381 741393493159883307559817)
                    ·
                      rfl

theorem cell23_4331576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 1, 5].length) (baseStart_4331576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331576 prefixEnd_4331576 := by exact prefixLift 4331576
  have htrace : WordTrace (prefixWord ++ tailWord_4331576) baseStart_4331576 baseEnd_4331576 := by
    simpa [prefixWord, tailWord_4331576, baseEnd_4331576] using wordTrace_append hprefix tailTrace_4331576
  have hstable : (prefixWord ++ tailWord_4331576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331576).length < 2 ^ (prefixWord ++ tailWord_4331576).sum := by decide
  have hdescent : baseEnd_4331576 < baseStart_4331576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331585 : List Nat := [1, 2, 5, 1, 2, 2, 10]
def baseStart_4331585 : Nat := 118140960795 + 4331585 * 2 ^ 59
def prefixEnd_4331585 : Nat := 4983230072969 + 3 ^ 40 * 4331585 * 2
def baseEnd_4331585 : Nat := 27459075318586918363789

theorem tailTrace_4331585 : CollatzResearch.WordTrace tailWord_4331585 prefixEnd_4331585 27459075318586918363789 := by
  unfold tailWord_4331585
  simp only [CollatzResearch.WordTrace]
  refine ⟨157985884012414795666548209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105323922674943197111032139 157985884012414795666548209)
  ·
    refine ⟨118489413009311096749911157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157985884012414795666548209 118489413009311096749911157)
    ·
      refine ⟨11108382469622915320304171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118489413009311096749911157 11108382469622915320304171)
      ·
        refine ⟨16662573704434372980456257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11108382469622915320304171 16662573704434372980456257)
        ·
          refine ⟨12496930278325779735342193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16662573704434372980456257 12496930278325779735342193)
          ·
            refine ⟨9372697708744334801506645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12496930278325779735342193 9372697708744334801506645)
            ·
              refine ⟨27459075318586918363789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9372697708744334801506645 27459075318586918363789)
              ·
                rfl

theorem cell23_4331585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 10].length) (baseStart_4331585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331585 prefixEnd_4331585 := by exact prefixLift 4331585
  have htrace : WordTrace (prefixWord ++ tailWord_4331585) baseStart_4331585 baseEnd_4331585 := by
    simpa [prefixWord, tailWord_4331585, baseEnd_4331585] using wordTrace_append hprefix tailTrace_4331585
  have hstable : (prefixWord ++ tailWord_4331585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331585).length < 2 ^ (prefixWord ++ tailWord_4331585).sum := by decide
  have hdescent : baseEnd_4331585 < baseStart_4331585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331596 : List Nat := [2, 2, 1, 3, 1, 1, 4, 4, 1, 2, 2]
def baseStart_4331596 : Nat := 118140960795 + 4331596 * 2 ^ 59
def prefixEnd_4331596 : Nat := 4983230072969 + 3 ^ 40 * 4331596 * 2
def baseEnd_4331596 : Nat := 2224190749092739844429359

theorem tailTrace_4331596 : CollatzResearch.WordTrace tailWord_4331596 prefixEnd_4331596 2224190749092739844429359 := by
  unfold tailWord_4331596
  simp only [CollatzResearch.WordTrace]
  refine ⟨78993142607687472272599321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105324190143583296363465761 78993142607687472272599321)
  ·
    refine ⟨59244856955765604204449491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78993142607687472272599321 59244856955765604204449491)
    ·
      refine ⟨88867285433648406306674237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59244856955765604204449491 88867285433648406306674237)
      ·
        refine ⟨33325232037618152365002839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88867285433648406306674237 33325232037618152365002839)
        ·
          refine ⟨49987848056427228547504259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33325232037618152365002839 49987848056427228547504259)
          ·
            refine ⟨74981772084640842821256389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49987848056427228547504259 74981772084640842821256389)
            ·
              refine ⟨14059082265870158028985573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74981772084640842821256389 14059082265870158028985573)
              ·
                refine ⟨2636077924850654630434795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14059082265870158028985573 2636077924850654630434795)
                ·
                  refine ⟨3954116887275981945652193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2636077924850654630434795 3954116887275981945652193)
                  ·
                    refine ⟨2965587665456986459239145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3954116887275981945652193 2965587665456986459239145)
                    ·
                      refine ⟨2224190749092739844429359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2965587665456986459239145 2224190749092739844429359)
                      ·
                        rfl

theorem cell23_4331596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_4331596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331596 prefixEnd_4331596 := by exact prefixLift 4331596
  have htrace : WordTrace (prefixWord ++ tailWord_4331596) baseStart_4331596 baseEnd_4331596 := by
    simpa [prefixWord, tailWord_4331596, baseEnd_4331596] using wordTrace_append hprefix tailTrace_4331596
  have hstable : (prefixWord ++ tailWord_4331596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331596).length < 2 ^ (prefixWord ++ tailWord_4331596).sum := by decide
  have hdescent : baseEnd_4331596 < baseStart_4331596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331606 : List Nat := [5, 2, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_4331606 : Nat := 118140960795 + 4331606 * 2 ^ 59
def prefixEnd_4331606 : Nat := 4983230072969 + 3 ^ 40 * 4331606 * 2
def baseEnd_4331606 : Nat := 741398627966428268434771

theorem tailTrace_4331606 : CollatzResearch.WordTrace tailWord_4331606 prefixEnd_4331606 741398627966428268434771 := by
  unfold tailWord_4331606
  simp only [CollatzResearch.WordTrace]
  refine ⟨9874165621583669765816417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105324433296892477502041781 9874165621583669765816417)
  ·
    refine ⟨7405624216187752324362313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9874165621583669765816417 7405624216187752324362313)
    ·
      refine ⟨5554218162140814243271735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7405624216187752324362313 5554218162140814243271735)
      ·
        refine ⟨8331327243211221364907603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5554218162140814243271735 8331327243211221364907603)
        ·
          refine ⟨12496990864816832047361405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8331327243211221364907603 12496990864816832047361405)
          ·
            refine ⟨4686371574306312017760527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12496990864816832047361405 4686371574306312017760527)
            ·
              refine ⟨7029557361459468026640791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4686371574306312017760527 7029557361459468026640791)
              ·
                refine ⟨10544336042189202039961187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7029557361459468026640791 10544336042189202039961187)
                ·
                  refine ⟨15816504063283803059941781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10544336042189202039961187 15816504063283803059941781)
                  ·
                    refine ⟨741398627966428268434771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15816504063283803059941781 741398627966428268434771)
                    ·
                      rfl

theorem cell23_4331606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_4331606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331606 prefixEnd_4331606 := by exact prefixLift 4331606
  have htrace : WordTrace (prefixWord ++ tailWord_4331606) baseStart_4331606 baseEnd_4331606 := by
    simpa [prefixWord, tailWord_4331606, baseEnd_4331606] using wordTrace_append hprefix tailTrace_4331606
  have hstable : (prefixWord ++ tailWord_4331606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331606).length < 2 ^ (prefixWord ++ tailWord_4331606).sum := by decide
  have hdescent : baseEnd_4331606 < baseStart_4331606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331639 : List Nat := [1, 1, 3, 1, 1, 5, 2, 3, 1, 3, 2]
def baseStart_4331639 : Nat := 118140960795 + 4331639 * 2 ^ 59
def prefixEnd_4331639 : Nat := 4983230072969 + 3 ^ 40 * 4331639 * 2
def baseEnd_4331639 : Nat := 2224212828760883176191661

theorem tailTrace_4331639 : CollatzResearch.WordTrace tailWord_4331639 prefixEnd_4331639 2224212828760883176191661 := by
  unfold tailWord_4331639
  simp only [CollatzResearch.WordTrace]
  refine ⟨157987853554219162889013971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105325235702812775259342647 157987853554219162889013971)
  ·
    refine ⟨236981780331328744333520957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157987853554219162889013971 236981780331328744333520957)
    ·
      refine ⟨88868167624248279125070359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236981780331328744333520957 88868167624248279125070359)
      ·
        refine ⟨133302251436372418687605539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88868167624248279125070359 133302251436372418687605539)
        ·
          refine ⟨199953377154558628031408309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133302251436372418687605539 199953377154558628031408309)
          ·
            refine ⟨18745629108239871377944529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 199953377154558628031408309 18745629108239871377944529)
            ·
              refine ⟨14059221831179903533458397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18745629108239871377944529 14059221831179903533458397)
              ·
                refine ⟨5272208186692463825046899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14059221831179903533458397 5272208186692463825046899)
                ·
                  refine ⟨7908312280038695737570349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5272208186692463825046899 7908312280038695737570349)
                  ·
                    refine ⟨2965617105014510901588881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7908312280038695737570349 2965617105014510901588881)
                    ·
                      refine ⟨2224212828760883176191661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2965617105014510901588881 2224212828760883176191661)
                      ·
                        rfl

theorem cell23_4331639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 3, 2].length) (baseStart_4331639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331639 prefixEnd_4331639 := by exact prefixLift 4331639
  have htrace : WordTrace (prefixWord ++ tailWord_4331639) baseStart_4331639 baseEnd_4331639 := by
    simpa [prefixWord, tailWord_4331639, baseEnd_4331639] using wordTrace_append hprefix tailTrace_4331639
  have hstable : (prefixWord ++ tailWord_4331639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331639).length < 2 ^ (prefixWord ++ tailWord_4331639).sum := by decide
  have hdescent : baseEnd_4331639 < baseStart_4331639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331690 : List Nat := [3, 1, 5, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_4331690 : Nat := 118140960795 + 4331690 * 2 ^ 59
def prefixEnd_4331690 : Nat := 4983230072969 + 3 ^ 40 * 4331690 * 2
def baseEnd_4331690 : Nat := 2224239016274262476653927

theorem tailTrace_4331690 : CollatzResearch.WordTrace tailWord_4331690 prefixEnd_4331690 2224239016274262476653927 := by
  unfold tailWord_4331690
  simp only [CollatzResearch.WordTrace]
  refine ⟨39497428419258599649780131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105326475784689599066080349 39497428419258599649780131)
  ·
    refine ⟨59246142628887899474670197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39497428419258599649780131 59246142628887899474670197)
    ·
      refine ⟨5554325871458240575750331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59246142628887899474670197 5554325871458240575750331)
      ·
        refine ⟨8331488807187360863625497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5554325871458240575750331 8331488807187360863625497)
        ·
          refine ⟨6248616605390520647719123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8331488807187360863625497 6248616605390520647719123)
          ·
            refine ⟨9372924908085780971578685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6248616605390520647719123 9372924908085780971578685)
            ·
              refine ⟨3514846840532167864342007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9372924908085780971578685 3514846840532167864342007)
              ·
                refine ⟨5272270260798251796513011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3514846840532167864342007 5272270260798251796513011)
                ·
                  refine ⟨7908405391197377694769517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5272270260798251796513011 7908405391197377694769517)
                  ·
                    refine ⟨2965652021699016635538569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7908405391197377694769517 2965652021699016635538569)
                    ·
                      refine ⟨2224239016274262476653927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2965652021699016635538569 2224239016274262476653927)
                      ·
                        rfl

theorem cell23_4331690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_4331690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331690 prefixEnd_4331690 := by exact prefixLift 4331690
  have htrace : WordTrace (prefixWord ++ tailWord_4331690) baseStart_4331690 baseEnd_4331690 := by
    simpa [prefixWord, tailWord_4331690, baseEnd_4331690] using wordTrace_append hprefix tailTrace_4331690
  have hstable : (prefixWord ++ tailWord_4331690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331690).length < 2 ^ (prefixWord ++ tailWord_4331690).sum := by decide
  have hdescent : baseEnd_4331690 < baseStart_4331690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331755 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 6]
def baseStart_4331755 : Nat := 118140960795 + 4331755 * 2 ^ 59
def prefixEnd_4331755 : Nat := 4983230072969 + 3 ^ 40 * 4331755 * 2
def baseEnd_4331755 : Nat := 2224272392516804722341127

theorem tailTrace_4331755 : CollatzResearch.WordTrace tailWord_4331755 prefixEnd_4331755 2224272392516804722341127 := by
  unfold tailWord_4331755
  simp only [CollatzResearch.WordTrace]
  refine ⟨157992084421798914700236719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105328056281199276466824479 157992084421798914700236719)
  ·
    refine ⟨236988126632698372050355079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157992084421798914700236719 236988126632698372050355079)
    ·
      refine ⟨355482189949047558075532619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236988126632698372050355079 355482189949047558075532619)
      ·
        refine ⟨533223284923571337113298929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355482189949047558075532619 533223284923571337113298929)
        ·
          refine ⟨399917463692678502834974197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 533223284923571337113298929 399917463692678502834974197)
          ·
            refine ⟨37492262221188609640778831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 399917463692678502834974197 37492262221188609640778831)
            ·
              refine ⟨56238393331782914461168247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37492262221188609640778831 56238393331782914461168247)
              ·
                refine ⟨84357589997674371691752371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56238393331782914461168247 84357589997674371691752371)
                ·
                  refine ⟨126536384996511557537628557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84357589997674371691752371 126536384996511557537628557)
                  ·
                    refine ⟨47451144373691834076610709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 126536384996511557537628557 47451144373691834076610709)
                    ·
                      refine ⟨2224272392516804722341127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47451144373691834076610709 2224272392516804722341127)
                      ·
                        rfl

theorem cell23_4331755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 6].length) (baseStart_4331755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331755 prefixEnd_4331755 := by exact prefixLift 4331755
  have htrace : WordTrace (prefixWord ++ tailWord_4331755) baseStart_4331755 baseEnd_4331755 := by
    simpa [prefixWord, tailWord_4331755, baseEnd_4331755] using wordTrace_append hprefix tailTrace_4331755
  have hstable : (prefixWord ++ tailWord_4331755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331755).length < 2 ^ (prefixWord ++ tailWord_4331755).sum := by decide
  have hdescent : baseEnd_4331755 < baseStart_4331755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331759 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 2, 4, 2]
def baseStart_4331759 : Nat := 118140960795 + 4331759 * 2 ^ 59
def prefixEnd_4331759 : Nat := 4983230072969 + 3 ^ 40 * 4331759 * 2
def baseEnd_4331759 : Nat := 2224274446439422706691109

theorem tailTrace_4331759 : CollatzResearch.WordTrace tailWord_4331759 prefixEnd_4331759 2224274446439422706691109 := by
  unfold tailWord_4331759
  simp only [CollatzResearch.WordTrace]
  refine ⟨157992230313784423383382331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105328153542522948922254887 157992230313784423383382331)
  ·
    refine ⟨236988345470676635075073497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157992230313784423383382331 236988345470676635075073497)
    ·
      refine ⟨177741259103007476306305123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236988345470676635075073497 177741259103007476306305123)
      ·
        refine ⟨266611888654511214459457685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177741259103007476306305123 266611888654511214459457685)
        ·
          refine ⟨12497432280680213177787079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 266611888654511214459457685 12497432280680213177787079)
          ·
            refine ⟨18746148421020319766680619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12497432280680213177787079 18746148421020319766680619)
            ·
              refine ⟨28119222631530479650020929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18746148421020319766680619 28119222631530479650020929)
              ·
                refine ⟨21089416973647859737515697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28119222631530479650020929 21089416973647859737515697)
                ·
                  refine ⟨15817062730235894803136773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21089416973647859737515697 15817062730235894803136773)
                  ·
                    refine ⟨2965699261919230275588145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15817062730235894803136773 2965699261919230275588145)
                    ·
                      refine ⟨2224274446439422706691109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2965699261919230275588145 2224274446439422706691109)
                      ·
                        rfl

theorem cell23_4331759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 4, 2].length) (baseStart_4331759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331759 prefixEnd_4331759 := by exact prefixLift 4331759
  have htrace : WordTrace (prefixWord ++ tailWord_4331759) baseStart_4331759 baseEnd_4331759 := by
    simpa [prefixWord, tailWord_4331759, baseEnd_4331759] using wordTrace_append hprefix tailTrace_4331759
  have hstable : (prefixWord ++ tailWord_4331759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331759).length < 2 ^ (prefixWord ++ tailWord_4331759).sum := by decide
  have hdescent : baseEnd_4331759 < baseStart_4331759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331795 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 2, 9]
def baseStart_4331795 : Nat := 118140960795 + 4331795 * 2 ^ 59
def prefixEnd_4331795 : Nat := 4983230072969 + 3 ^ 40 * 4331795 * 2
def baseEnd_4331795 : Nat := 741430977247661521946981

theorem tailTrace_4331795 : CollatzResearch.WordTrace tailWord_4331795 prefixEnd_4331795 741430977247661521946981 := by
  unfold tailWord_4331795
  simp only [CollatzResearch.WordTrace]
  refine ⟨157993543341654001531692839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105329028894436001021128559 157993543341654001531692839)
  ·
    refine ⟨236990315012481002297539259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157993543341654001531692839 236990315012481002297539259)
    ·
      refine ⟨355485472518721503446308889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236990315012481002297539259 355485472518721503446308889)
      ·
        refine ⟨266614104389041127584731667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 355485472518721503446308889 266614104389041127584731667)
        ·
          refine ⟨399921156583561691377097501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266614104389041127584731667 399921156583561691377097501)
          ·
            refine ⟨149970433718835634266411563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 399921156583561691377097501 149970433718835634266411563)
            ·
              refine ⟨224955650578253451399617345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149970433718835634266411563 224955650578253451399617345)
              ·
                refine ⟨168716737933690088549713009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224955650578253451399617345 168716737933690088549713009)
                ·
                  refine ⟨126537553450267566412284757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168716737933690088549713009 126537553450267566412284757)
                  ·
                    refine ⟨741430977247661521946981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 126537553450267566412284757 741430977247661521946981)
                    ·
                      rfl

theorem cell23_4331795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 9].length) (baseStart_4331795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331795 prefixEnd_4331795 := by exact prefixLift 4331795
  have htrace : WordTrace (prefixWord ++ tailWord_4331795) baseStart_4331795 baseEnd_4331795 := by
    simpa [prefixWord, tailWord_4331795, baseEnd_4331795] using wordTrace_append hprefix tailTrace_4331795
  have hstable : (prefixWord ++ tailWord_4331795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331795).length < 2 ^ (prefixWord ++ tailWord_4331795).sum := by decide
  have hdescent : baseEnd_4331795 < baseStart_4331795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331809 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 5, 1, 3]
def baseStart_4331809 : Nat := 118140960795 + 4331809 * 2 ^ 59
def prefixEnd_4331809 : Nat := 4983230072969 + 3 ^ 40 * 4331809 * 2
def baseEnd_4331809 : Nat := 2224300120472147511065879

theorem tailTrace_4331809 : CollatzResearch.WordTrace tailWord_4331809 prefixEnd_4331809 2224300120472147511065879 := by
  unfold tailWord_4331809
  simp only [CollatzResearch.WordTrace]
  refine ⟨157994053963603281922702481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105329369309068854615134987 157994053963603281922702481)
  ·
    refine ⟨118495540472702461442026861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157994053963603281922702481 118495540472702461442026861)
    ·
      refine ⟨44435827677263423040760073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118495540472702461442026861 44435827677263423040760073)
      ·
        refine ⟨33326870757947567280570055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44435827677263423040760073 33326870757947567280570055)
        ·
          refine ⟨49990306136921350920855083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33326870757947567280570055 49990306136921350920855083)
          ·
            refine ⟨74985459205382026381282625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49990306136921350920855083 74985459205382026381282625)
            ·
              refine ⟨56239094404036519785961969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74985459205382026381282625 56239094404036519785961969)
              ·
                refine ⟨42179320803027389839471477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56239094404036519785961969 42179320803027389839471477)
                ·
                  refine ⟨3954311325283817797450451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42179320803027389839471477 3954311325283817797450451)
                  ·
                    refine ⟨5931466987925726696175677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3954311325283817797450451 5931466987925726696175677)
                    ·
                      refine ⟨2224300120472147511065879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5931466987925726696175677 2224300120472147511065879)
                      ·
                        rfl

theorem cell23_4331809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_4331809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331809 prefixEnd_4331809 := by exact prefixLift 4331809
  have htrace : WordTrace (prefixWord ++ tailWord_4331809) baseStart_4331809 baseEnd_4331809 := by
    simpa [prefixWord, tailWord_4331809, baseEnd_4331809] using wordTrace_append hprefix tailTrace_4331809
  have hstable : (prefixWord ++ tailWord_4331809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331809).length < 2 ^ (prefixWord ++ tailWord_4331809).sum := by decide
  have hdescent : baseEnd_4331809 < baseStart_4331809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331872 : List Nat := [2, 1, 1, 3, 5, 11]
def baseStart_4331872 : Nat := 118140960795 + 4331872 * 2 ^ 59
def prefixEnd_4331872 : Nat := 4983230072969 + 3 ^ 40 * 4331872 * 2
def baseEnd_4331872 : Nat := 9153631562771114257523

theorem tailTrace_4331872 : CollatzResearch.WordTrace tailWord_4331872 prefixEnd_4331872 9153631562771114257523 := by
  unfold tailWord_4331872
  simp only [CollatzResearch.WordTrace]
  refine ⟨78998175881187521841122935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105330901174916695788163913 78998175881187521841122935)
  ·
    refine ⟨118497263821781282761684403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78998175881187521841122935 118497263821781282761684403)
    ·
      refine ⟨177745895732671924142526605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118497263821781282761684403 177745895732671924142526605)
      ·
        refine ⟨66654710899751971553447477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177745895732671924142526605 66654710899751971553447477)
        ·
          refine ⟨6248879146851747333135701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66654710899751971553447477 6248879146851747333135701)
          ·
            refine ⟨9153631562771114257523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6248879146851747333135701 9153631562771114257523)
            ·
              rfl

theorem cell23_4331872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 11].length) (baseStart_4331872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331872 prefixEnd_4331872 := by exact prefixLift 4331872
  have htrace : WordTrace (prefixWord ++ tailWord_4331872) baseStart_4331872 baseEnd_4331872 := by
    simpa [prefixWord, tailWord_4331872, baseEnd_4331872] using wordTrace_append hprefix tailTrace_4331872
  have hstable : (prefixWord ++ tailWord_4331872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331872).length < 2 ^ (prefixWord ++ tailWord_4331872).sum := by decide
  have hdescent : baseEnd_4331872 < baseStart_4331872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331876 : List Nat := [2, 3, 1, 1, 3, 1, 4, 2, 2, 4]
def baseStart_4331876 : Nat := 118140960795 + 4331876 * 2 ^ 59
def prefixEnd_4331876 : Nat := 4983230072969 + 3 ^ 40 * 4331876 * 2
def baseEnd_4331876 : Nat := 741444841225332916309357

theorem tailTrace_4331876 : CollatzResearch.WordTrace tailWord_4331876 prefixEnd_4331876 741444841225332916309357 := by
  unfold tailWord_4331876
  simp only [CollatzResearch.WordTrace]
  refine ⟨78998248827180276182695741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105330998436240368243594321 78998248827180276182695741)
  ·
    refine ⟨29624343310192603568510903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78998248827180276182695741 29624343310192603568510903)
    ·
      refine ⟨44436514965288905352766355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29624343310192603568510903 44436514965288905352766355)
      ·
        refine ⟨66654772447933358029149533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44436514965288905352766355 66654772447933358029149533)
        ·
          refine ⟨24995539667975009260931075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66654772447933358029149533 24995539667975009260931075)
          ·
            refine ⟨37493309501962513891396613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24995539667975009260931075 37493309501962513891396613)
            ·
              refine ⟨7029995531617971354636865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37493309501962513891396613 7029995531617971354636865)
              ·
                refine ⟨5272496648713478515977649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7029995531617971354636865 5272496648713478515977649)
                ·
                  refine ⟨3954372486535108886983237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5272496648713478515977649 3954372486535108886983237)
                  ·
                    refine ⟨741444841225332916309357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3954372486535108886983237 741444841225332916309357)
                    ·
                      rfl

theorem cell23_4331876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_4331876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331876 prefixEnd_4331876 := by exact prefixLift 4331876
  have htrace : WordTrace (prefixWord ++ tailWord_4331876) baseStart_4331876 baseEnd_4331876 := by
    simpa [prefixWord, tailWord_4331876, baseEnd_4331876] using wordTrace_append hprefix tailTrace_4331876
  have hstable : (prefixWord ++ tailWord_4331876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331876).length < 2 ^ (prefixWord ++ tailWord_4331876).sum := by decide
  have hdescent : baseEnd_4331876 < baseStart_4331876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331883 : List Nat := [1, 1, 1, 1, 2, 2, 2, 8, 1, 2, 2]
def baseStart_4331883 : Nat := 118140960795 + 4331883 * 2 ^ 59
def prefixEnd_4331883 : Nat := 4983230072969 + 3 ^ 40 * 4331883 * 2
def baseEnd_4331883 : Nat := 2224338118040580221540539

theorem tailTrace_4331883 : CollatzResearch.WordTrace tailWord_4331883 prefixEnd_4331883 2224338118040580221540539 := by
  unfold tailWord_4331883
  simp only [CollatzResearch.WordTrace]
  refine ⟨157996752965335192560896303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105331168643556795040597535 157996752965335192560896303)
  ·
    refine ⟨236995129448002788841344455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157996752965335192560896303 236995129448002788841344455)
    ·
      refine ⟨355492694172004183262016683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236995129448002788841344455 355492694172004183262016683)
      ·
        refine ⟨533239041258006274893025025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355492694172004183262016683 533239041258006274893025025)
        ·
          refine ⟨399929280943504706169768769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 533239041258006274893025025 399929280943504706169768769)
          ·
            refine ⟨299946960707628529627326577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399929280943504706169768769 299946960707628529627326577)
            ·
              refine ⟨224960220530721397220494933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299946960707628529627326577 224960220530721397220494933)
              ·
                refine ⟨2636252584344391373677675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 224960220530721397220494933 2636252584344391373677675)
                ·
                  refine ⟨3954378876516587060516513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2636252584344391373677675 3954378876516587060516513)
                  ·
                    refine ⟨2965784157387440295387385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3954378876516587060516513 2965784157387440295387385)
                    ·
                      refine ⟨2224338118040580221540539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2965784157387440295387385 2224338118040580221540539)
                      ·
                        rfl

theorem cell23_4331883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 1, 2, 2].length) (baseStart_4331883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331883 prefixEnd_4331883 := by exact prefixLift 4331883
  have htrace : WordTrace (prefixWord ++ tailWord_4331883) baseStart_4331883 baseEnd_4331883 := by
    simpa [prefixWord, tailWord_4331883, baseEnd_4331883] using wordTrace_append hprefix tailTrace_4331883
  have hstable : (prefixWord ++ tailWord_4331883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331883).length < 2 ^ (prefixWord ++ tailWord_4331883).sum := by decide
  have hdescent : baseEnd_4331883 < baseStart_4331883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331899 : List Nat := [1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 3]
def baseStart_4331899 : Nat := 118140960795 + 4331899 * 2 ^ 59
def prefixEnd_4331899 : Nat := 4983230072969 + 3 ^ 40 * 4331899 * 2
def baseEnd_4331899 : Nat := 2224346333731052158940465

theorem tailTrace_4331899 : CollatzResearch.WordTrace tailWord_4331899 prefixEnd_4331899 2224346333731052158940465 := by
  unfold tailWord_4331899
  simp only [CollatzResearch.WordTrace]
  refine ⟨157997336533277227293478751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105331557688851484862319167 157997336533277227293478751)
  ·
    refine ⟨236996004799915840940218127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157997336533277227293478751 236996004799915840940218127)
    ·
      refine ⟨355494007199873761410327191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236996004799915840940218127 355494007199873761410327191)
      ·
        refine ⟨533241010799810642115490787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355494007199873761410327191 533241010799810642115490787)
        ·
          refine ⟨799861516199715963173236181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533241010799810642115490787 799861516199715963173236181)
          ·
            refine ⟨18746754285930842886872723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 799861516199715963173236181 18746754285930842886872723)
            ·
              refine ⟨28120131428896264330309085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18746754285930842886872723 28120131428896264330309085)
              ·
                refine ⟨10545049285836099123865907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28120131428896264330309085 10545049285836099123865907)
                ·
                  refine ⟨15817573928754148685798861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10545049285836099123865907 15817573928754148685798861)
                  ·
                    refine ⟨5931590223282805757174573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15817573928754148685798861 5931590223282805757174573)
                    ·
                      refine ⟨2224346333731052158940465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5931590223282805757174573 2224346333731052158940465)
                      ·
                        rfl

theorem cell23_4331899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 3].length) (baseStart_4331899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331899 prefixEnd_4331899 := by exact prefixLift 4331899
  have htrace : WordTrace (prefixWord ++ tailWord_4331899) baseStart_4331899 baseEnd_4331899 := by
    simpa [prefixWord, tailWord_4331899, baseEnd_4331899] using wordTrace_append hprefix tailTrace_4331899
  have hstable : (prefixWord ++ tailWord_4331899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331899).length < 2 ^ (prefixWord ++ tailWord_4331899).sum := by decide
  have hdescent : baseEnd_4331899 < baseStart_4331899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331933 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_4331933 : Nat := 118140960795 + 4331933 * 2 ^ 59
def prefixEnd_4331933 : Nat := 4983230072969 + 3 ^ 40 * 4331933 * 2
def baseEnd_4331933 : Nat := 2224363792073305025915309

theorem tailTrace_4331933 : CollatzResearch.WordTrace tailWord_4331933 prefixEnd_4331933 2224363792073305025915309 := by
  unfold tailWord_4331933
  simp only [CollatzResearch.WordTrace]
  refine ⟨157998576615154051100216453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105332384410102700733477635 157998576615154051100216453)
  ·
    refine ⟨29624733115341384581290585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157998576615154051100216453 29624733115341384581290585)
    ·
      refine ⟨22218549836506038435967939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29624733115341384581290585 22218549836506038435967939)
      ·
        refine ⟨33327824754759057653951909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22218549836506038435967939 33327824754759057653951909)
        ·
          refine ⟨6248967141517323310115983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33327824754759057653951909 6248967141517323310115983)
          ·
            refine ⟨9373450712275984965173975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6248967141517323310115983 9373450712275984965173975)
            ·
              refine ⟨14060176068413977447760963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9373450712275984965173975 14060176068413977447760963)
              ·
                refine ⟨21090264102620966171641445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14060176068413977447760963 21090264102620966171641445)
                ·
                  refine ⟨3954424519241431157182771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21090264102620966171641445 3954424519241431157182771)
                  ·
                    refine ⟨5931636778862146735774157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3954424519241431157182771 5931636778862146735774157)
                    ·
                      refine ⟨2224363792073305025915309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5931636778862146735774157 2224363792073305025915309)
                      ·
                        rfl

theorem cell23_4331933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_4331933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331933 prefixEnd_4331933 := by exact prefixLift 4331933
  have htrace : WordTrace (prefixWord ++ tailWord_4331933) baseStart_4331933 baseEnd_4331933 := by
    simpa [prefixWord, tailWord_4331933, baseEnd_4331933] using wordTrace_append hprefix tailTrace_4331933
  have hstable : (prefixWord ++ tailWord_4331933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331933).length < 2 ^ (prefixWord ++ tailWord_4331933).sum := by decide
  have hdescent : baseEnd_4331933 < baseStart_4331933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4331990 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_4331990 : Nat := 118140960795 + 4331990 * 2 ^ 59
def prefixEnd_4331990 : Nat := 4983230072969 + 3 ^ 40 * 4331990 * 2
def baseEnd_4331990 : Nat := 2224393060470611302902547

theorem tailTrace_4331990 : CollatzResearch.WordTrace tailWord_4331990 prefixEnd_4331990 2224393060470611302902547 := by
  unfold tailWord_4331990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9875040973496721864690089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105333770383965033223360949 9875040973496721864690089)
  ·
    refine ⟨7406280730122541398517567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9875040973496721864690089 7406280730122541398517567)
    ·
      refine ⟨11109421095183812097776351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7406280730122541398517567 11109421095183812097776351)
      ·
        refine ⟨16664131642775718146664527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11109421095183812097776351 16664131642775718146664527)
        ·
          refine ⟨24996197464163577219996791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16664131642775718146664527 24996197464163577219996791)
          ·
            refine ⟨37494296196245365829995187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24996197464163577219996791 37494296196245365829995187)
            ·
              refine ⟨56241444294368048744992781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37494296196245365829995187 56241444294368048744992781)
              ·
                refine ⟨21090541610388018279372293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56241444294368048744992781 21090541610388018279372293)
                ·
                  refine ⟨3954476551947753427382305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21090541610388018279372293 3954476551947753427382305)
                  ·
                    refine ⟨2965857413960815070536729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3954476551947753427382305 2965857413960815070536729)
                    ·
                      refine ⟨2224393060470611302902547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2965857413960815070536729 2224393060470611302902547)
                      ·
                        rfl

theorem cell23_4331990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_4331990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4331990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4331990 prefixEnd_4331990 := by exact prefixLift 4331990
  have htrace : WordTrace (prefixWord ++ tailWord_4331990) baseStart_4331990 baseEnd_4331990 := by
    simpa [prefixWord, tailWord_4331990, baseEnd_4331990] using wordTrace_append hprefix tailTrace_4331990
  have hstable : (prefixWord ++ tailWord_4331990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4331990).length < 2 ^ (prefixWord ++ tailWord_4331990).sum := by decide
  have hdescent : baseEnd_4331990 < baseStart_4331990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4331990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332036 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_4332036 : Nat := 118140960795 + 4332036 * 2 ^ 59
def prefixEnd_4332036 : Nat := 4983230072969 + 3 ^ 40 * 4332036 * 2
def baseEnd_4332036 : Nat := 2224416680580718122927335

theorem tailTrace_4332036 : CollatzResearch.WordTrace tailWord_4332036 prefixEnd_4332036 2224416680580718122927335 := by
  unfold tailWord_4332036
  simp only [CollatzResearch.WordTrace]
  refine ⟨79001166666890449845607981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105334888889187266460810641 79001166666890449845607981)
  ·
    refine ⟨29625437500083918692102993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79001166666890449845607981 29625437500083918692102993)
    ·
      refine ⟨22219078125062939019077245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29625437500083918692102993 22219078125062939019077245)
      ·
        refine ⟨8332154296898602132153967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22219078125062939019077245 8332154296898602132153967)
        ·
          refine ⟨12498231445347903198230951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8332154296898602132153967 12498231445347903198230951)
          ·
            refine ⟨18747347168021854797346427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12498231445347903198230951 18747347168021854797346427)
            ·
              refine ⟨28121020752032782196019641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18747347168021854797346427 28121020752032782196019641)
              ·
                refine ⟨21090765564024586647014731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28121020752032782196019641 21090765564024586647014731)
                ·
                  refine ⟨31636148346036879970522097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21090765564024586647014731 31636148346036879970522097)
                  ·
                    refine ⟨23727111259527659977891573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31636148346036879970522097 23727111259527659977891573)
                    ·
                      refine ⟨2224416680580718122927335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23727111259527659977891573 2224416680580718122927335)
                      ·
                        rfl

theorem cell23_4332036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_4332036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332036 prefixEnd_4332036 := by exact prefixLift 4332036
  have htrace : WordTrace (prefixWord ++ tailWord_4332036) baseStart_4332036 baseEnd_4332036 := by
    simpa [prefixWord, tailWord_4332036, baseEnd_4332036] using wordTrace_append hprefix tailTrace_4332036
  have hstable : (prefixWord ++ tailWord_4332036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332036).length < 2 ^ (prefixWord ++ tailWord_4332036).sum := by decide
  have hdescent : baseEnd_4332036 < baseStart_4332036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332066 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_4332066 : Nat := 118140960795 + 4332066 * 2 ^ 59
def prefixEnd_4332066 : Nat := 4983230072969 + 3 ^ 40 * 4332066 * 2
def baseEnd_4332066 : Nat := 2224432085000353005552197

theorem tailTrace_4332066 : CollatzResearch.WordTrace tailWord_4332066 prefixEnd_4332066 2224432085000353005552197 := by
  unfold tailWord_4332066
  simp only [CollatzResearch.WordTrace]
  refine ⟨39500856880918053703702013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105335618349114809876538701 39500856880918053703702013)
  ·
    refine ⟨14812821330344270138888255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39500856880918053703702013 14812821330344270138888255)
    ·
      refine ⟨22219231995516405208332383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14812821330344270138888255 22219231995516405208332383)
      ·
        refine ⟨33328847993274607812498575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22219231995516405208332383 33328847993274607812498575)
        ·
          refine ⟨49993271989911911718747863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33328847993274607812498575 49993271989911911718747863)
          ·
            refine ⟨74989907984867867578121795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49993271989911911718747863 74989907984867867578121795)
            ·
              refine ⟨112484861977301801367182693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74989907984867867578121795 112484861977301801367182693)
              ·
                refine ⟨21090911620744087756346755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112484861977301801367182693 21090911620744087756346755)
                ·
                  refine ⟨31636367431116131634520133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21090911620744087756346755 31636367431116131634520133)
                  ·
                    refine ⟨5931818893334274681472525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31636367431116131634520133 5931818893334274681472525)
                    ·
                      refine ⟨2224432085000353005552197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5931818893334274681472525 2224432085000353005552197)
                      ·
                        rfl

theorem cell23_4332066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_4332066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332066 prefixEnd_4332066 := by exact prefixLift 4332066
  have htrace : WordTrace (prefixWord ++ tailWord_4332066) baseStart_4332066 baseEnd_4332066 := by
    simpa [prefixWord, tailWord_4332066, baseEnd_4332066] using wordTrace_append hprefix tailTrace_4332066
  have hstable : (prefixWord ++ tailWord_4332066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332066).length < 2 ^ (prefixWord ++ tailWord_4332066).sum := by decide
  have hdescent : baseEnd_4332066 < baseStart_4332066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332090 : List Nat := [3, 1, 1, 1, 3, 4, 2, 3, 1, 4]
def baseStart_4332090 : Nat := 118140960795 + 4332090 * 2 ^ 59
def prefixEnd_4332090 : Nat := 4983230072969 + 3 ^ 40 * 4332090 * 2
def baseEnd_4332090 : Nat := 741481469512020303884029

theorem tailTrace_4332090 : CollatzResearch.WordTrace tailWord_4332090 prefixEnd_4332090 741481469512020303884029 := by
  unfold tailWord_4332090
  simp only [CollatzResearch.WordTrace]
  refine ⟨39501075718896316728420431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105336201917056844609121149 39501075718896316728420431)
  ·
    refine ⟨59251613578344475092630647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39501075718896316728420431 59251613578344475092630647)
    ·
      refine ⟨88877420367516712638945971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59251613578344475092630647 88877420367516712638945971)
      ·
        refine ⟨133316130551275068958418957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88877420367516712638945971 133316130551275068958418957)
        ·
          refine ⟨49993548956728150859407109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133316130551275068958418957 49993548956728150859407109)
          ·
            refine ⟨9373790429386528286138833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49993548956728150859407109 9373790429386528286138833)
            ·
              refine ⟨7030342822039896214604125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9373790429386528286138833 7030342822039896214604125)
              ·
                refine ⟨2636378558264961080476547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7030342822039896214604125 2636378558264961080476547)
                ·
                  refine ⟨3954567837397441620714821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2636378558264961080476547 3954567837397441620714821)
                  ·
                    refine ⟨741481469512020303884029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3954567837397441620714821 741481469512020303884029)
                    ·
                      rfl

theorem cell23_4332090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 1, 4].length) (baseStart_4332090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332090 prefixEnd_4332090 := by exact prefixLift 4332090
  have htrace : WordTrace (prefixWord ++ tailWord_4332090) baseStart_4332090 baseEnd_4332090 := by
    simpa [prefixWord, tailWord_4332090, baseEnd_4332090] using wordTrace_append hprefix tailTrace_4332090
  have hstable : (prefixWord ++ tailWord_4332090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332090).length < 2 ^ (prefixWord ++ tailWord_4332090).sum := by decide
  have hdescent : baseEnd_4332090 < baseStart_4332090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332103 : List Nat := [1, 1, 4, 1, 4, 3, 1, 2, 6]
def baseStart_4332103 : Nat := 118140960795 + 4332103 * 2 ^ 59
def prefixEnd_4332103 : Nat := 4983230072969 + 3 ^ 40 * 4332103 * 2
def baseEnd_4332103 : Nat := 247161231531618817865503

theorem tailTrace_4332103 : CollatzResearch.WordTrace tailWord_4332103 prefixEnd_4332103 247161231531618817865503 := by
  unfold tailWord_4332103
  simp only [CollatzResearch.WordTrace]
  refine ⟨158004777024538170133904963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105336518016358780089269975 158004777024538170133904963)
  ·
    refine ⟨237007165536807255200857445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158004777024538170133904963 237007165536807255200857445)
    ·
      refine ⟨44438843538151360350160771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237007165536807255200857445 44438843538151360350160771)
      ·
        refine ⟨66658265307227040525241157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44438843538151360350160771 66658265307227040525241157)
        ·
          refine ⟨12498424745105070098482717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66658265307227040525241157 12498424745105070098482717)
          ·
            refine ⟨4686909279414401286931019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12498424745105070098482717 4686909279414401286931019)
            ·
              refine ⟨7030363919121601930396529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4686909279414401286931019 7030363919121601930396529)
              ·
                refine ⟨5272772939341201447797397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7030363919121601930396529 5272772939341201447797397)
                ·
                  refine ⟨247161231531618817865503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5272772939341201447797397 247161231531618817865503)
                  ·
                    rfl

theorem cell23_4332103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 6].length) (baseStart_4332103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332103 prefixEnd_4332103 := by exact prefixLift 4332103
  have htrace : WordTrace (prefixWord ++ tailWord_4332103) baseStart_4332103 baseEnd_4332103 := by
    simpa [prefixWord, tailWord_4332103, baseEnd_4332103] using wordTrace_append hprefix tailTrace_4332103
  have hstable : (prefixWord ++ tailWord_4332103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332103).length < 2 ^ (prefixWord ++ tailWord_4332103).sum := by decide
  have hdescent : baseEnd_4332103 < baseStart_4332103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332113 : List Nat := [1, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3]
def baseStart_4332113 : Nat := 118140960795 + 4332113 * 2 ^ 59
def prefixEnd_4332113 : Nat := 4983230072969 + 3 ^ 40 * 4332113 * 2
def baseEnd_4332113 : Nat := 2224456218591114321664481

theorem tailTrace_4332113 : CollatzResearch.WordTrace tailWord_4332113 prefixEnd_4332113 2224456218591114321664481 := by
  unfold tailWord_4332113
  simp only [CollatzResearch.WordTrace]
  refine ⟨158005141754501941841768993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105336761169667961227845995 158005141754501941841768993)
  ·
    refine ⟨118503856315876456381326745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158005141754501941841768993 118503856315876456381326745)
    ·
      refine ⟨88877892236907342285995059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118503856315876456381326745 88877892236907342285995059)
      ·
        refine ⟨133316838355361013428992589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88877892236907342285995059 133316838355361013428992589)
        ·
          refine ⟨49993814383260380035872221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133316838355361013428992589 49993814383260380035872221)
          ·
            refine ⟨18747680393722642513452083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49993814383260380035872221 18747680393722642513452083)
            ·
              refine ⟨28121520590583963770178125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18747680393722642513452083 28121520590583963770178125)
              ·
                refine ⟨10545570221468986413816797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28121520590583963770178125 10545570221468986413816797)
                ·
                  refine ⟨3954588833050869905181299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10545570221468986413816797 3954588833050869905181299)
                  ·
                    refine ⟨5931883249576304857771949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3954588833050869905181299 5931883249576304857771949)
                    ·
                      refine ⟨2224456218591114321664481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5931883249576304857771949 2224456218591114321664481)
                      ·
                        rfl

theorem cell23_4332113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3].length) (baseStart_4332113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332113 prefixEnd_4332113 := by exact prefixLift 4332113
  have htrace : WordTrace (prefixWord ++ tailWord_4332113) baseStart_4332113 baseEnd_4332113 := by
    simpa [prefixWord, tailWord_4332113, baseEnd_4332113] using wordTrace_append hprefix tailTrace_4332113
  have hstable : (prefixWord ++ tailWord_4332113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332113).length < 2 ^ (prefixWord ++ tailWord_4332113).sum := by decide
  have hdescent : baseEnd_4332113 < baseStart_4332113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332153 : List Nat := [1, 2, 1, 3, 3, 2, 2, 3, 1, 1, 4]
def baseStart_4332153 : Nat := 118140960795 + 4332153 * 2 ^ 59
def prefixEnd_4332153 : Nat := 4983230072969 + 3 ^ 40 * 4332153 * 2
def baseEnd_4332153 : Nat := 2224476757817294165164297

theorem tailTrace_4332153 : CollatzResearch.WordTrace tailWord_4332153 prefixEnd_4332153 2224476757817294165164297 := by
  unfold tailWord_4332153
  simp only [CollatzResearch.WordTrace]
  refine ⟨158006600674357028673225113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105337733782904685782150075 158006600674357028673225113)
  ·
    refine ⟨118504950505767771504918835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158006600674357028673225113 118504950505767771504918835)
    ·
      refine ⟨177757425758651657257378253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118504950505767771504918835 177757425758651657257378253)
      ·
        refine ⟨66659034659494371471516845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177757425758651657257378253 66659034659494371471516845)
        ·
          refine ⟨24997137997310389301818817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66659034659494371471516845 24997137997310389301818817)
          ·
            refine ⟨18747853497982791976364113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24997137997310389301818817 18747853497982791976364113)
            ·
              refine ⟨14060890123487093982273085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18747853497982791976364113 14060890123487093982273085)
              ·
                refine ⟨5272833796307660243352407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14060890123487093982273085 5272833796307660243352407)
                ·
                  refine ⟨7909250694461490365028611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5272833796307660243352407 7909250694461490365028611)
                  ·
                    refine ⟨11863876041692235547542917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7909250694461490365028611 11863876041692235547542917)
                    ·
                      refine ⟨2224476757817294165164297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11863876041692235547542917 2224476757817294165164297)
                      ·
                        rfl

theorem cell23_4332153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_4332153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332153 prefixEnd_4332153 := by exact prefixLift 4332153
  have htrace : WordTrace (prefixWord ++ tailWord_4332153) baseStart_4332153 baseEnd_4332153 := by
    simpa [prefixWord, tailWord_4332153, baseEnd_4332153] using wordTrace_append hprefix tailTrace_4332153
  have hstable : (prefixWord ++ tailWord_4332153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332153).length < 2 ^ (prefixWord ++ tailWord_4332153).sum := by decide
  have hdescent : baseEnd_4332153 < baseStart_4332153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332156 : List Nat := [2, 2, 2, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_4332156 : Nat := 118140960795 + 4332156 * 2 ^ 59
def prefixEnd_4332156 : Nat := 4983230072969 + 3 ^ 40 * 4332156 * 2
def baseEnd_4332156 : Nat := 2224478298259257653426783

theorem tailTrace_4332156 : CollatzResearch.WordTrace tailWord_4332156 prefixEnd_4332156 2224478298259257653426783 := by
  unfold tailWord_4332156
  simp only [CollatzResearch.WordTrace]
  refine ⟨79003355046673080092792161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105337806728897440123722881 79003355046673080092792161)
  ·
    refine ⟨59252516285004810069594121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79003355046673080092792161 59252516285004810069594121)
    ·
      refine ⟨44439387213753607552195591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59252516285004810069594121 44439387213753607552195591)
      ·
        refine ⟨66659080820630411328293387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44439387213753607552195591 66659080820630411328293387)
        ·
          refine ⟨99988621230945616992440081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66659080820630411328293387 99988621230945616992440081)
          ·
            refine ⟨74991465923209212744330061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99988621230945616992440081 74991465923209212744330061)
            ·
              refine ⟨28121799721203454779123773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74991465923209212744330061 28121799721203454779123773)
              ·
                refine ⟨10545674895451295542171415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28121799721203454779123773 10545674895451295542171415)
                ·
                  refine ⟨15818512343176943313257123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10545674895451295542171415 15818512343176943313257123)
                  ·
                    refine ⟨23727768514765414969885685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15818512343176943313257123 23727768514765414969885685)
                    ·
                      refine ⟨2224478298259257653426783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23727768514765414969885685 2224478298259257653426783)
                      ·
                        rfl

theorem cell23_4332156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_4332156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332156 prefixEnd_4332156 := by exact prefixLift 4332156
  have htrace : WordTrace (prefixWord ++ tailWord_4332156) baseStart_4332156 baseEnd_4332156 := by
    simpa [prefixWord, tailWord_4332156, baseEnd_4332156] using wordTrace_append hprefix tailTrace_4332156
  have hstable : (prefixWord ++ tailWord_4332156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332156).length < 2 ^ (prefixWord ++ tailWord_4332156).sum := by decide
  have hdescent : baseEnd_4332156 < baseStart_4332156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332164 : List Nat := [2, 3, 2, 1, 3, 2, 3, 2, 1, 1, 3]
def baseStart_4332164 : Nat := 118140960795 + 4332164 * 2 ^ 59
def prefixEnd_4332164 : Nat := 4983230072969 + 3 ^ 40 * 4332164 * 2
def baseEnd_4332164 : Nat := 2224482406104493622126747

theorem tailTrace_4332164 : CollatzResearch.WordTrace tailWord_4332164 prefixEnd_4332164 2224482406104493622126747 := by
  unfold tailWord_4332164
  simp only [CollatzResearch.WordTrace]
  refine ⟨79003500938658588775937773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105338001251544785034583697 79003500938658588775937773)
  ·
    refine ⟨29626312851996970790976665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79003500938658588775937773 29626312851996970790976665)
    ·
      refine ⟨22219734638997728093232499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29626312851996970790976665 22219734638997728093232499)
      ·
        refine ⟨33329601958496592139848749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22219734638997728093232499 33329601958496592139848749)
        ·
          refine ⟨12498600734436222052443281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33329601958496592139848749 12498600734436222052443281)
          ·
            refine ⟨9373950550827166539332461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12498600734436222052443281 9373950550827166539332461)
            ·
              refine ⟨3515231456560187452249673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9373950550827166539332461 3515231456560187452249673)
              ·
                refine ⟨2636423592420140589187255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3515231456560187452249673 2636423592420140589187255)
                ·
                  refine ⟨3954635388630210883780883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2636423592420140589187255 3954635388630210883780883)
                  ·
                    refine ⟨5931953082945316325671325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3954635388630210883780883 5931953082945316325671325)
                    ·
                      refine ⟨2224482406104493622126747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5931953082945316325671325 2224482406104493622126747)
                      ·
                        rfl

theorem cell23_4332164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_4332164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332164 prefixEnd_4332164 := by exact prefixLift 4332164
  have htrace : WordTrace (prefixWord ++ tailWord_4332164) baseStart_4332164 baseEnd_4332164 := by
    simpa [prefixWord, tailWord_4332164, baseEnd_4332164] using wordTrace_append hprefix tailTrace_4332164
  have hstable : (prefixWord ++ tailWord_4332164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332164).length < 2 ^ (prefixWord ++ tailWord_4332164).sum := by decide
  have hdescent : baseEnd_4332164 < baseStart_4332164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332190 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_4332190 : Nat := 118140960795 + 4332190 * 2 ^ 59
def prefixEnd_4332190 : Nat := 4983230072969 + 3 ^ 40 * 4332190 * 2
def baseEnd_4332190 : Nat := 2224495756601510520401627

theorem tailTrace_4332190 : CollatzResearch.WordTrace tailWord_4332190 prefixEnd_4332190 2224495756601510520401627 := by
  unfold tailWord_4332190
  simp only [CollatzResearch.WordTrace]
  refine ⟨19750993771902872999040253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105338633450148655994881349 19750993771902872999040253)
  ·
    refine ⟨7406622664463577374640095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19750993771902872999040253 7406622664463577374640095)
    ·
      refine ⟨11109933996695366061960143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7406622664463577374640095 11109933996695366061960143)
      ·
        refine ⟨16664900995043049092940215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11109933996695366061960143 16664900995043049092940215)
        ·
          refine ⟨24997351492564573639410323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16664900995043049092940215 24997351492564573639410323)
          ·
            refine ⟨37496027238846860459115485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24997351492564573639410323 37496027238846860459115485)
            ·
              refine ⟨14061010214567572672168307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37496027238846860459115485 14061010214567572672168307)
              ·
                refine ⟨21091515321851359008252461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14061010214567572672168307 21091515321851359008252461)
                ·
                  refine ⟨7909318245694259628094673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21091515321851359008252461 7909318245694259628094673)
                  ·
                    refine ⟨5931988684270694721071005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7909318245694259628094673 5931988684270694721071005)
                    ·
                      refine ⟨2224495756601510520401627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5931988684270694721071005 2224495756601510520401627)
                      ·
                        rfl

theorem cell23_4332190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_4332190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332190 prefixEnd_4332190 := by exact prefixLift 4332190
  have htrace : WordTrace (prefixWord ++ tailWord_4332190) baseStart_4332190 baseEnd_4332190 := by
    simpa [prefixWord, tailWord_4332190, baseEnd_4332190] using wordTrace_append hprefix tailTrace_4332190
  have hstable : (prefixWord ++ tailWord_4332190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332190).length < 2 ^ (prefixWord ++ tailWord_4332190).sum := by decide
  have hdescent : baseEnd_4332190 < baseStart_4332190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332214 : List Nat := [5, 1, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_4332214 : Nat := 118140960795 + 4332214 * 2 ^ 59
def prefixEnd_4332214 : Nat := 4983230072969 + 3 ^ 40 * 4332214 * 2
def baseEnd_4332214 : Nat := 741502693379072808833839

theorem tailTrace_4332214 : CollatzResearch.WordTrace tailWord_4332214 prefixEnd_4332214 741502693379072808833839 := by
  unfold tailWord_4332214
  simp only [CollatzResearch.WordTrace]
  refine ⟨9875551595446002255699731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105339217018090690727463797 9875551595446002255699731)
  ·
    refine ⟨14813327393169003383549597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9875551595446002255699731 14813327393169003383549597)
    ·
      refine ⟨5554997772438376268831099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14813327393169003383549597 5554997772438376268831099)
      ·
        refine ⟨8332496658657564403246649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5554997772438376268831099 8332496658657564403246649)
        ·
          refine ⟨6249372493993173302434987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8332496658657564403246649 6249372493993173302434987)
          ·
            refine ⟨9374058740989759953652481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6249372493993173302434987 9374058740989759953652481)
            ·
              refine ⟨7030544055742319965239361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9374058740989759953652481 7030544055742319965239361)
              ·
                refine ⟨5272908041806739973929521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7030544055742319965239361 5272908041806739973929521)
                ·
                  refine ⟨3954681031355054980447141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5272908041806739973929521 3954681031355054980447141)
                  ·
                    refine ⟨741502693379072808833839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3954681031355054980447141 741502693379072808833839)
                    ·
                      rfl

theorem cell23_4332214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_4332214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332214 prefixEnd_4332214 := by exact prefixLift 4332214
  have htrace : WordTrace (prefixWord ++ tailWord_4332214) baseStart_4332214 baseEnd_4332214 := by
    simpa [prefixWord, tailWord_4332214, baseEnd_4332214] using wordTrace_append hprefix tailTrace_4332214
  have hstable : (prefixWord ++ tailWord_4332214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332214).length < 2 ^ (prefixWord ++ tailWord_4332214).sum := by decide
  have hdescent : baseEnd_4332214 < baseStart_4332214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332221 : List Nat := [1, 4, 1, 2, 1, 5, 2, 2, 1, 2, 2]
def baseStart_4332221 : Nat := 118140960795 + 4332221 * 2 ^ 59
def prefixEnd_4332221 : Nat := 4983230072969 + 3 ^ 40 * 4332221 * 2
def baseEnd_4332221 : Nat := 2224511674501799899113985

theorem tailTrace_4332221 : CollatzResearch.WordTrace tailWord_4332221 prefixEnd_4332221 2224511674501799899113985 := by
  unfold tailWord_4332221
  simp only [CollatzResearch.WordTrace]
  refine ⟨158009080838110676286700517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105339387225407117524467011 158009080838110676286700517)
  ·
    refine ⟨29626702657145751803756347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158009080838110676286700517 29626702657145751803756347)
    ·
      refine ⟨44440053985718627705634521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29626702657145751803756347 44440053985718627705634521)
      ·
        refine ⟨33330040489288970779225891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44440053985718627705634521 33330040489288970779225891)
        ·
          refine ⟨49995060733933456168838837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33330040489288970779225891 49995060733933456168838837)
          ·
            refine ⟨4687036943806261515828641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49995060733933456168838837 4687036943806261515828641)
            ·
              refine ⟨3515277707854696136871481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4687036943806261515828641 3515277707854696136871481)
              ·
                refine ⟨2636458280891022102653611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3515277707854696136871481 2636458280891022102653611)
                ·
                  refine ⟨3954687421336533153980417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2636458280891022102653611 3954687421336533153980417)
                  ·
                    refine ⟨2966015566002399865485313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3954687421336533153980417 2966015566002399865485313)
                    ·
                      refine ⟨2224511674501799899113985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2966015566002399865485313 2224511674501799899113985)
                      ·
                        rfl

theorem cell23_4332221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_4332221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332221 prefixEnd_4332221 := by exact prefixLift 4332221
  have htrace : WordTrace (prefixWord ++ tailWord_4332221) baseStart_4332221 baseEnd_4332221 := by
    simpa [prefixWord, tailWord_4332221, baseEnd_4332221] using wordTrace_append hprefix tailTrace_4332221
  have hstable : (prefixWord ++ tailWord_4332221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332221).length < 2 ^ (prefixWord ++ tailWord_4332221).sum := by decide
  have hdescent : baseEnd_4332221 < baseStart_4332221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332256 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 4]
def baseStart_4332256 : Nat := 118140960795 + 4332256 * 2 ^ 59
def prefixEnd_4332256 : Nat := 4983230072969 + 3 ^ 40 * 4332256 * 2
def baseEnd_4332256 : Nat := 2224529646324707262176323

theorem tailTrace_4332256 : CollatzResearch.WordTrace tailWord_4332256 prefixEnd_4332256 2224529646324707262176323 := by
  unfold tailWord_4332256
  simp only [CollatzResearch.WordTrace]
  refine ⟨79005178696491938632112311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105340238261989251509483081 79005178696491938632112311)
  ·
    refine ⟨118507768044737907948168467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79005178696491938632112311 118507768044737907948168467)
    ·
      refine ⟨177761652067106861922252701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118507768044737907948168467 177761652067106861922252701)
      ·
        refine ⟨66660619525165073220844763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177761652067106861922252701 66660619525165073220844763)
        ·
          refine ⟨99990929287747609831267145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66660619525165073220844763 99990929287747609831267145)
          ·
            refine ⟨74993196965810707373450359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99990929287747609831267145 74993196965810707373450359)
            ·
              refine ⟨112489795448716061060175539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74993196965810707373450359 112489795448716061060175539)
              ·
                refine ⟨168734693173074091590263309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112489795448716061060175539 168734693173074091590263309)
                ·
                  refine ⟨63275509939902784346348741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168734693173074091590263309 63275509939902784346348741)
                  ·
                    refine ⟨11864158113731772064940389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63275509939902784346348741 11864158113731772064940389)
                    ·
                      refine ⟨2224529646324707262176323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11864158113731772064940389 2224529646324707262176323)
                      ·
                        rfl

theorem cell23_4332256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_4332256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332256 prefixEnd_4332256 := by exact prefixLift 4332256
  have htrace : WordTrace (prefixWord ++ tailWord_4332256) baseStart_4332256 baseEnd_4332256 := by
    simpa [prefixWord, tailWord_4332256, baseEnd_4332256] using wordTrace_append hprefix tailTrace_4332256
  have hstable : (prefixWord ++ tailWord_4332256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332256).length < 2 ^ (prefixWord ++ tailWord_4332256).sum := by decide
  have hdescent : baseEnd_4332256 < baseStart_4332256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332260 : List Nat := [2, 3, 1, 1, 1, 4, 2, 2, 1, 4, 2]
def baseStart_4332260 : Nat := 118140960795 + 4332260 * 2 ^ 59
def prefixEnd_4332260 : Nat := 4983230072969 + 3 ^ 40 * 4332260 * 2
def baseEnd_4332260 : Nat := 2224531700247325246526305

theorem tailTrace_4332260 : CollatzResearch.WordTrace tailWord_4332260 prefixEnd_4332260 2224531700247325246526305 := by
  unfold tailWord_4332260
  simp only [CollatzResearch.WordTrace]
  refine ⟨79005251642484692973685117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105340335523312923964913489 79005251642484692973685117)
  ·
    refine ⟨29626969365931759865131919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79005251642484692973685117 29626969365931759865131919)
    ·
      refine ⟨44440454048897639797697879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29626969365931759865131919 44440454048897639797697879)
      ·
        refine ⟨66660681073346459696546819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44440454048897639797697879 66660681073346459696546819)
        ·
          refine ⟨99991021610019689544820229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66660681073346459696546819 99991021610019689544820229)
          ·
            refine ⟨18748316551878691789653793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99991021610019689544820229 18748316551878691789653793)
            ·
              refine ⟨14061237413909018842240345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18748316551878691789653793 14061237413909018842240345)
              ·
                refine ⟨10545928060431764131680259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14061237413909018842240345 10545928060431764131680259)
                ·
                  refine ⟨15818892090647646197520389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10545928060431764131680259 15818892090647646197520389)
                  ·
                    refine ⟨2966042266996433662035073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15818892090647646197520389 2966042266996433662035073)
                    ·
                      refine ⟨2224531700247325246526305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2966042266996433662035073 2224531700247325246526305)
                      ·
                        rfl

theorem cell23_4332260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_4332260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332260 prefixEnd_4332260 := by exact prefixLift 4332260
  have htrace : WordTrace (prefixWord ++ tailWord_4332260) baseStart_4332260 baseEnd_4332260 := by
    simpa [prefixWord, tailWord_4332260, baseEnd_4332260] using wordTrace_append hprefix tailTrace_4332260
  have hstable : (prefixWord ++ tailWord_4332260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332260).length < 2 ^ (prefixWord ++ tailWord_4332260).sum := by decide
  have hdescent : baseEnd_4332260 < baseStart_4332260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332266 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 11]
def baseStart_4332266 : Nat := 118140960795 + 4332266 * 2 ^ 59
def prefixEnd_4332266 : Nat := 4983230072969 + 3 ^ 40 * 4332266 * 2
def baseEnd_4332266 : Nat := 247170531236805802561253

theorem tailTrace_4332266 : CollatzResearch.WordTrace tailWord_4332266 prefixEnd_4332266 247170531236805802561253 := by
  unfold tailWord_4332266
  simp only [CollatzResearch.WordTrace]
  refine ⟨39502680530736912243022163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105340481415298432648059101 39502680530736912243022163)
  ·
    refine ⟨59254020796105368364533245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39502680530736912243022163 59254020796105368364533245)
    ·
      refine ⟨22220257798539513136699967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59254020796105368364533245 22220257798539513136699967)
      ·
        refine ⟨33330386697809269705049951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22220257798539513136699967 33330386697809269705049951)
        ·
          refine ⟨49995580046713904557574927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33330386697809269705049951 49995580046713904557574927)
          ·
            refine ⟨74993370070070856836362391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49995580046713904557574927 74993370070070856836362391)
            ·
              refine ⟨112490055105106285254543587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74993370070070856836362391 112490055105106285254543587)
              ·
                refine ⟨168735082657659427881815381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112490055105106285254543587 168735082657659427881815381)
                ·
                  refine ⟨247170531236805802561253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 168735082657659427881815381 247170531236805802561253)
                  ·
                    rfl

theorem cell23_4332266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 11].length) (baseStart_4332266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332266 prefixEnd_4332266 := by exact prefixLift 4332266
  have htrace : WordTrace (prefixWord ++ tailWord_4332266) baseStart_4332266 baseEnd_4332266 := by
    simpa [prefixWord, tailWord_4332266, baseEnd_4332266] using wordTrace_append hprefix tailTrace_4332266
  have hstable : (prefixWord ++ tailWord_4332266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332266).length < 2 ^ (prefixWord ++ tailWord_4332266).sum := by decide
  have hdescent : baseEnd_4332266 < baseStart_4332266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332290 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_4332290 : Nat := 118140960795 + 4332290 * 2 ^ 59
def prefixEnd_4332290 : Nat := 4983230072969 + 3 ^ 40 * 4332290 * 2
def baseEnd_4332290 : Nat := 2224547104666960129151167

theorem tailTrace_4332290 : CollatzResearch.WordTrace tailWord_4332290 prefixEnd_4332290 2224547104666960129151167 := by
  unfold tailWord_4332290
  simp only [CollatzResearch.WordTrace]
  refine ⟨39502899368715175267740581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105341064983240467380641549 39502899368715175267740581)
  ·
    refine ⟨7406793631634095362701359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39502899368715175267740581 7406793631634095362701359)
    ·
      refine ⟨11110190447451143044052039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7406793631634095362701359 11110190447451143044052039)
      ·
        refine ⟨16665285671176714566078059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11110190447451143044052039 16665285671176714566078059)
        ·
          refine ⟨24997928506765071849117089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16665285671176714566078059 24997928506765071849117089)
          ·
            refine ⟨18748446380073803886837817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24997928506765071849117089 18748446380073803886837817)
            ·
              refine ⟨14061334785055352915128363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18748446380073803886837817 14061334785055352915128363)
              ·
                refine ⟨21092002177583029372692545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14061334785055352915128363 21092002177583029372692545)
                ·
                  refine ⟨15819001633187272029519409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21092002177583029372692545 15819001633187272029519409)
                  ·
                    refine ⟨11864251224890454022139557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15819001633187272029519409 11864251224890454022139557)
                    ·
                      refine ⟨2224547104666960129151167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11864251224890454022139557 2224547104666960129151167)
                      ·
                        rfl

theorem cell23_4332290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_4332290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332290 prefixEnd_4332290 := by exact prefixLift 4332290
  have htrace : WordTrace (prefixWord ++ tailWord_4332290) baseStart_4332290 baseEnd_4332290 := by
    simpa [prefixWord, tailWord_4332290, baseEnd_4332290] using wordTrace_append hprefix tailTrace_4332290
  have hstable : (prefixWord ++ tailWord_4332290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332290).length < 2 ^ (prefixWord ++ tailWord_4332290).sum := by decide
  have hdescent : baseEnd_4332290 < baseStart_4332290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332334 : List Nat := [4, 1, 3, 2, 1, 2, 3, 2, 5]
def baseStart_4332334 : Nat := 118140960795 + 4332334 * 2 ^ 59
def prefixEnd_4332334 : Nat := 4983230072969 + 3 ^ 40 * 4332334 * 2
def baseEnd_4332334 : Nat := 247174410868417550777885

theorem tailTrace_4332334 : CollatzResearch.WordTrace tailWord_4332334 prefixEnd_4332334 247174410868417550777885 := by
  unfold tailWord_4332334
  simp only [CollatzResearch.WordTrace]
  refine ⟨19751650285837662073195507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105342134857800864390376037 19751650285837662073195507)
  ·
    refine ⟨29627475428756493109793261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19751650285837662073195507 29627475428756493109793261)
    ·
      refine ⟨11110303285783684916172473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29627475428756493109793261 11110303285783684916172473)
      ·
        refine ⟨8332727464337763687129355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11110303285783684916172473 8332727464337763687129355)
        ·
          refine ⟨12499091196506645530694033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8332727464337763687129355 12499091196506645530694033)
          ·
            refine ⟨9374318397379984148020525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12499091196506645530694033 9374318397379984148020525)
            ·
              refine ⟨3515369399017494055507697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9374318397379984148020525 3515369399017494055507697)
              ·
                refine ⟨2636527049263120541630773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3515369399017494055507697 2636527049263120541630773)
                ·
                  refine ⟨247174410868417550777885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2636527049263120541630773 247174410868417550777885)
                  ·
                    rfl

theorem cell23_4332334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_4332334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332334 prefixEnd_4332334 := by exact prefixLift 4332334
  have htrace : WordTrace (prefixWord ++ tailWord_4332334) baseStart_4332334 baseEnd_4332334 := by
    simpa [prefixWord, tailWord_4332334, baseEnd_4332334] using wordTrace_append hprefix tailTrace_4332334
  have hstable : (prefixWord ++ tailWord_4332334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332334).length < 2 ^ (prefixWord ++ tailWord_4332334).sum := by decide
  have hdescent : baseEnd_4332334 < baseStart_4332334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332403 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 3, 5]
def baseStart_4332403 : Nat := 118140960795 + 4332403 * 2 ^ 59
def prefixEnd_4332403 : Nat := 4983230072969 + 3 ^ 40 * 4332403 * 2
def baseEnd_4332403 : Nat := 741535042660306062346049

theorem tailTrace_4332403 : CollatzResearch.WordTrace tailWord_4332403 prefixEnd_4332403 741535042660306062346049 := by
  unfold tailWord_4332403
  simp only [CollatzResearch.WordTrace]
  refine ⟨158015718923451321369825863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105343812615634214246550575 158015718923451321369825863)
  ·
    refine ⟨237023578385176982054738795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158015718923451321369825863 237023578385176982054738795)
    ·
      refine ⟨355535367577765473082108193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237023578385176982054738795 355535367577765473082108193)
      ·
        refine ⟨266651525683324104811581145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 355535367577765473082108193 266651525683324104811581145)
        ·
          refine ⟨199988644262493078608685859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266651525683324104811581145 199988644262493078608685859)
          ·
            refine ⟨299982966393739617913028789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199988644262493078608685859 299982966393739617913028789)
            ·
              refine ⟨28123403099413089179346449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 299982966393739617913028789 28123403099413089179346449)
              ·
                refine ⟨21092552324559816884509837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28123403099413089179346449 21092552324559816884509837)
                ·
                  refine ⟨7909707121709931331691189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21092552324559816884509837 7909707121709931331691189)
                  ·
                    refine ⟨741535042660306062346049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7909707121709931331691189 741535042660306062346049)
                    ·
                      rfl

theorem cell23_4332403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 5].length) (baseStart_4332403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332403 prefixEnd_4332403 := by exact prefixLift 4332403
  have htrace : WordTrace (prefixWord ++ tailWord_4332403) baseStart_4332403 baseEnd_4332403 := by
    simpa [prefixWord, tailWord_4332403, baseEnd_4332403] using wordTrace_append hprefix tailTrace_4332403
  have hstable : (prefixWord ++ tailWord_4332403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332403).length < 2 ^ (prefixWord ++ tailWord_4332403).sum := by decide
  have hdescent : baseEnd_4332403 < baseStart_4332403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332410 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2]
def baseStart_4332410 : Nat := 118140960795 + 4332410 * 2 ^ 59
def prefixEnd_4332410 : Nat := 4983230072969 + 3 ^ 40 * 4332410 * 2
def baseEnd_4332410 : Nat := 2224608722345499659650615

theorem tailTrace_4332410 : CollatzResearch.WordTrace tailWord_4332410 prefixEnd_4332410 2224608722345499659650615 := by
  unfold tailWord_4332410
  simp only [CollatzResearch.WordTrace]
  refine ⟨39503993558606490391332671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105343982822950641043553789 39503993558606490391332671)
  ·
    refine ⟨59255990337909735586999007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39503993558606490391332671 59255990337909735586999007)
    ·
      refine ⟨88883985506864603380498511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59255990337909735586999007 88883985506864603380498511)
      ·
        refine ⟨133325978260296905070747767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88883985506864603380498511 133325978260296905070747767)
        ·
          refine ⟨199988967390445357606121651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133325978260296905070747767 199988967390445357606121651)
          ·
            refine ⟨299983451085668036409182477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199988967390445357606121651 299983451085668036409182477)
            ·
              refine ⟨112493794157125513653443429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 299983451085668036409182477 112493794157125513653443429)
              ·
                refine ⟨21092586404461033810020643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112493794157125513653443429 21092586404461033810020643)
                ·
                  refine ⟨31638879606691550715030965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21092586404461033810020643 31638879606691550715030965)
                  ·
                    refine ⟨2966144963127332879534153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31638879606691550715030965 2966144963127332879534153)
                    ·
                      refine ⟨2224608722345499659650615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2966144963127332879534153 2224608722345499659650615)
                      ·
                        rfl

theorem cell23_4332410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2].length) (baseStart_4332410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332410 prefixEnd_4332410 := by exact prefixLift 4332410
  have htrace : WordTrace (prefixWord ++ tailWord_4332410) baseStart_4332410 baseEnd_4332410 := by
    simpa [prefixWord, tailWord_4332410, baseEnd_4332410] using wordTrace_append hprefix tailTrace_4332410
  have hstable : (prefixWord ++ tailWord_4332410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332410).length < 2 ^ (prefixWord ++ tailWord_4332410).sum := by decide
  have hdescent : baseEnd_4332410 < baseStart_4332410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332418 : List Nat := [3, 4, 2, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_4332418 : Nat := 118140960795 + 4332418 * 2 ^ 59
def prefixEnd_4332418 : Nat := 4983230072969 + 3 ^ 40 * 4332418 * 2
def baseEnd_4332418 : Nat := 2224612830190735628350579

theorem tailTrace_4332418 : CollatzResearch.WordTrace tailWord_4332418 prefixEnd_4332418 2224612830190735628350579 := by
  unfold tailWord_4332418
  simp only [CollatzResearch.WordTrace]
  refine ⟨39504066504599244732905477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105344177345597985954414605 39504066504599244732905477)
  ·
    refine ⟨7407012469612358387419777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39504066504599244732905477 7407012469612358387419777)
    ·
      refine ⟨5555259352209268790564833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7407012469612358387419777 5555259352209268790564833)
      ·
        refine ⟨4166444514156951592923625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5555259352209268790564833 4166444514156951592923625)
        ·
          refine ⟨3124833385617713694692719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4166444514156951592923625 3124833385617713694692719)
          ·
            refine ⟨4687250078426570542039079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3124833385617713694692719 4687250078426570542039079)
            ·
              refine ⟨7030875117639855813058619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4687250078426570542039079 7030875117639855813058619)
              ·
                refine ⟨10546312676459783719587929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7030875117639855813058619 10546312676459783719587929)
                ·
                  refine ⟨7909734507344837789690947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10546312676459783719587929 7909734507344837789690947)
                  ·
                    refine ⟨11864601761017256684536421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7909734507344837789690947 11864601761017256684536421)
                    ·
                      refine ⟨2224612830190735628350579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11864601761017256684536421 2224612830190735628350579)
                      ·
                        rfl

theorem cell23_4332418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_4332418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332418 prefixEnd_4332418 := by exact prefixLift 4332418
  have htrace : WordTrace (prefixWord ++ tailWord_4332418) baseStart_4332418 baseEnd_4332418 := by
    simpa [prefixWord, tailWord_4332418, baseEnd_4332418] using wordTrace_append hprefix tailTrace_4332418
  have hstable : (prefixWord ++ tailWord_4332418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332418).length < 2 ^ (prefixWord ++ tailWord_4332418).sum := by decide
  have hdescent : baseEnd_4332418 < baseStart_4332418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332420 : List Nat := [2, 3, 2, 1, 1, 1, 1, 6, 1, 5]
def baseStart_4332420 : Nat := 118140960795 + 4332420 * 2 ^ 59
def prefixEnd_4332420 : Nat := 4983230072969 + 3 ^ 40 * 4332420 * 2
def baseEnd_4332420 : Nat := 741537952384014873508523

theorem tailTrace_4332420 : CollatzResearch.WordTrace tailWord_4332420 prefixEnd_4332420 741537952384014873508523 := by
  unfold tailWord_4332420
  simp only [CollatzResearch.WordTrace]
  refine ⟨79008169482194866636597357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105344225976259822182129809 79008169482194866636597357)
  ·
    refine ⟨29628063555823074988724009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79008169482194866636597357 29628063555823074988724009)
    ·
      refine ⟨22221047666867306241543007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29628063555823074988724009 22221047666867306241543007)
      ·
        refine ⟨33331571500300959362314511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22221047666867306241543007 33331571500300959362314511)
        ·
          refine ⟨49997357250451439043471767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33331571500300959362314511 49997357250451439043471767)
          ·
            refine ⟨74996035875677158565207651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49997357250451439043471767 74996035875677158565207651)
            ·
              refine ⟨112494053813515737847811477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74996035875677158565207651 112494053813515737847811477)
              ·
                refine ⟨5273158772508550211616163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112494053813515737847811477 5273158772508550211616163)
                ·
                  refine ⟨7909738158762825317424245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5273158772508550211616163 7909738158762825317424245)
                  ·
                    refine ⟨741537952384014873508523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7909738158762825317424245 741537952384014873508523)
                    ·
                      rfl

theorem cell23_4332420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_4332420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332420 prefixEnd_4332420 := by exact prefixLift 4332420
  have htrace : WordTrace (prefixWord ++ tailWord_4332420) baseStart_4332420 baseEnd_4332420 := by
    simpa [prefixWord, tailWord_4332420, baseEnd_4332420] using wordTrace_append hprefix tailTrace_4332420
  have hstable : (prefixWord ++ tailWord_4332420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332420).length < 2 ^ (prefixWord ++ tailWord_4332420).sum := by decide
  have hdescent : baseEnd_4332420 < baseStart_4332420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332427 : List Nat := [1, 1, 1, 1, 4, 2, 5, 1, 2, 3, 2]
def baseStart_4332427 : Nat := 118140960795 + 4332427 * 2 ^ 59
def prefixEnd_4332427 : Nat := 4983230072969 + 3 ^ 40 * 4332427 * 2
def baseEnd_4332427 : Nat := 2224617451516626093138037

theorem tailTrace_4332427 : CollatzResearch.WordTrace tailWord_4332427 prefixEnd_4332427 2224617451516626093138037 := by
  unfold tailWord_4332427
  simp only [CollatzResearch.WordTrace]
  refine ⟨158016594275364373468699535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105344396183576248979133023 158016594275364373468699535)
  ·
    refine ⟨237024891413046560203049303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158016594275364373468699535 237024891413046560203049303)
    ·
      refine ⟨355537337119569840304573955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237024891413046560203049303 355537337119569840304573955)
      ·
        refine ⟨533306005679354760456860933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355537337119569840304573955 533306005679354760456860933)
        ·
          refine ⟨99994876064879017585661425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 533306005679354760456860933 99994876064879017585661425)
          ·
            refine ⟨74996157048659263189246069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99994876064879017585661425 74996157048659263189246069)
            ·
              refine ⟨7030889723311805923991819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74996157048659263189246069 7030889723311805923991819)
              ·
                refine ⟨10546334584967708885987729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7030889723311805923991819 10546334584967708885987729)
                ·
                  refine ⟨7909750938725781664490797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10546334584967708885987729 7909750938725781664490797)
                  ·
                    refine ⟨2966156602022168124184049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7909750938725781664490797 2966156602022168124184049)
                    ·
                      refine ⟨2224617451516626093138037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2966156602022168124184049 2224617451516626093138037)
                      ·
                        rfl

theorem cell23_4332427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 3, 2].length) (baseStart_4332427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332427 prefixEnd_4332427 := by exact prefixLift 4332427
  have htrace : WordTrace (prefixWord ++ tailWord_4332427) baseStart_4332427 baseEnd_4332427 := by
    simpa [prefixWord, tailWord_4332427, baseEnd_4332427] using wordTrace_append hprefix tailTrace_4332427
  have hstable : (prefixWord ++ tailWord_4332427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332427).length < 2 ^ (prefixWord ++ tailWord_4332427).sum := by decide
  have hdescent : baseEnd_4332427 < baseStart_4332427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332437 : List Nat := [1, 3, 2, 1, 1, 4, 4, 1, 1, 5]
def baseStart_4332437 : Nat := 118140960795 + 4332437 * 2 ^ 59
def prefixEnd_4332437 : Nat := 4983230072969 + 3 ^ 40 * 4332437 * 2
def baseEnd_4332437 : Nat := 741540862107723684670997

theorem tailTrace_4332437 : CollatzResearch.WordTrace tailWord_4332437 prefixEnd_4332437 741540862107723684670997 := by
  unfold tailWord_4332437
  simp only [CollatzResearch.WordTrace]
  refine ⟨158016959005328145176563565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105344639336885430117709043 158016959005328145176563565)
  ·
    refine ⟨59256359626998054441211337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158016959005328145176563565 59256359626998054441211337)
    ·
      refine ⟨44442269720248540830908503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59256359626998054441211337 44442269720248540830908503)
      ·
        refine ⟨66663404580372811246362755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44442269720248540830908503 66663404580372811246362755)
        ·
          refine ⟨99995106870559216869544133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66663404580372811246362755 99995106870559216869544133)
          ·
            refine ⟨18749082538229853163039525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99995106870559216869544133 18749082538229853163039525)
            ·
              refine ⟨3515452975918097468069911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18749082538229853163039525 3515452975918097468069911)
              ·
                refine ⟨5273179463877146202104867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3515452975918097468069911 5273179463877146202104867)
                ·
                  refine ⟨7909769195815719303157301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5273179463877146202104867 7909769195815719303157301)
                  ·
                    refine ⟨741540862107723684670997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7909769195815719303157301 741540862107723684670997)
                    ·
                      rfl

theorem cell23_4332437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_4332437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332437 prefixEnd_4332437 := by exact prefixLift 4332437
  have htrace : WordTrace (prefixWord ++ tailWord_4332437) baseStart_4332437 baseEnd_4332437 := by
    simpa [prefixWord, tailWord_4332437, baseEnd_4332437] using wordTrace_append hprefix tailTrace_4332437
  have hstable : (prefixWord ++ tailWord_4332437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332437).length < 2 ^ (prefixWord ++ tailWord_4332437).sum := by decide
  have hdescent : baseEnd_4332437 < baseStart_4332437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332453 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 2, 6, 4]
def baseStart_4332453 : Nat := 118140960795 + 4332453 * 2 ^ 59
def prefixEnd_4332453 : Nat := 4983230072969 + 3 ^ 40 * 4332453 * 2
def baseEnd_4332453 : Nat := 2224630802013642991412917

theorem tailTrace_4332453 : CollatzResearch.WordTrace tailWord_4332453 prefixEnd_4332453 2224630802013642991412917 := by
  unfold tailWord_4332453
  simp only [CollatzResearch.WordTrace]
  refine ⟨158017542573270179909146013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105345028382180119939430675 158017542573270179909146013)
  ·
    refine ⟨59256578464976317465929755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158017542573270179909146013 59256578464976317465929755)
    ·
      refine ⟨88884867697464476198894633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59256578464976317465929755 88884867697464476198894633)
      ·
        refine ⟨66663650773098357149170975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88884867697464476198894633 66663650773098357149170975)
        ·
          refine ⟨99995476159647535723756463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66663650773098357149170975 99995476159647535723756463)
          ·
            refine ⟨149993214239471303585634695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99995476159647535723756463 149993214239471303585634695)
            ·
              refine ⟨224989821359206955378452043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149993214239471303585634695 224989821359206955378452043)
              ·
                refine ⟨337484732038810433067678065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224989821359206955378452043 337484732038810433067678065)
                ·
                  refine ⟨253113549029107824800758549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337484732038810433067678065 253113549029107824800758549)
                  ·
                    refine ⟨11864697610739429287535557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 253113549029107824800758549 11864697610739429287535557)
                    ·
                      refine ⟨2224630802013642991412917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11864697610739429287535557 2224630802013642991412917)
                      ·
                        rfl

theorem cell23_4332453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_4332453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332453 prefixEnd_4332453 := by exact prefixLift 4332453
  have htrace : WordTrace (prefixWord ++ tailWord_4332453) baseStart_4332453 baseEnd_4332453 := by
    simpa [prefixWord, tailWord_4332453, baseEnd_4332453] using wordTrace_append hprefix tailTrace_4332453
  have hstable : (prefixWord ++ tailWord_4332453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332453).length < 2 ^ (prefixWord ++ tailWord_4332453).sum := by decide
  have hdescent : baseEnd_4332453 < baseStart_4332453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332480 : List Nat := [2, 1, 1, 2, 3, 3, 4, 7]
def baseStart_4332480 : Nat := 118140960795 + 4332480 * 2 ^ 59
def prefixEnd_4332480 : Nat := 4983230072969 + 3 ^ 40 * 4332480 * 2
def baseEnd_4332480 : Nat := 82394246888567199473159

theorem tailTrace_4332480 : CollatzResearch.WordTrace tailWord_4332480 prefixEnd_4332480 82394246888567199473159 := by
  unfold tailWord_4332480
  simp only [CollatzResearch.WordTrace]
  refine ⟨79009263672086181760189447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105345684896114909013585929 79009263672086181760189447)
  ·
    refine ⟨118513895508129272640284171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79009263672086181760189447 118513895508129272640284171)
    ·
      refine ⟨177770843262193908960426257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118513895508129272640284171 177770843262193908960426257)
      ·
        refine ⟨133328132446645431720319693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177770843262193908960426257 133328132446645431720319693)
        ·
          refine ⟨49998049667492036895119885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133328132446645431720319693 49998049667492036895119885)
          ·
            refine ⟨18749268625309513835669957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49998049667492036895119885 18749268625309513835669957)
            ·
              refine ⟨3515487867245533844188117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18749268625309513835669957 3515487867245533844188117)
              ·
                refine ⟨82394246888567199473159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3515487867245533844188117 82394246888567199473159)
                ·
                  rfl

theorem cell23_4332480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 7].length) (baseStart_4332480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332480 prefixEnd_4332480 := by exact prefixLift 4332480
  have htrace : WordTrace (prefixWord ++ tailWord_4332480) baseStart_4332480 baseEnd_4332480 := by
    simpa [prefixWord, tailWord_4332480, baseEnd_4332480] using wordTrace_append hprefix tailTrace_4332480
  have hstable : (prefixWord ++ tailWord_4332480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332480).length < 2 ^ (prefixWord ++ tailWord_4332480).sum := by decide
  have hdescent : baseEnd_4332480 < baseStart_4332480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332490 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 3, 3, 3]
def baseStart_4332490 : Nat := 118140960795 + 4332490 * 2 ^ 59
def prefixEnd_4332490 : Nat := 4983230072969 + 3 ^ 40 * 4332490 * 2
def baseEnd_4332490 : Nat := 2224649800797859346650247

theorem tailTrace_4332490 : CollatzResearch.WordTrace tailWord_4332490 prefixEnd_4332490 2224649800797859346650247 := by
  unfold tailWord_4332490
  simp only [CollatzResearch.WordTrace]
  refine ⟨39504723018534033807060731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105345928049424090152161949 39504723018534033807060731)
  ·
    refine ⟨59257084527801050710591097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39504723018534033807060731 59257084527801050710591097)
    ·
      refine ⟨44442813395850788032943323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59257084527801050710591097 44442813395850788032943323)
      ·
        refine ⟨66664220093776182049414985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44442813395850788032943323 66664220093776182049414985)
        ·
          refine ⟨49998165070332136537061239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66664220093776182049414985 49998165070332136537061239)
          ·
            refine ⟨74997247605498204805591859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49998165070332136537061239 74997247605498204805591859)
            ·
              refine ⟨112495871408247307208387789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74997247605498204805591859 112495871408247307208387789)
              ·
                refine ⟨42185951778092740203145421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112495871408247307208387789 42185951778092740203145421)
                ·
                  refine ⟨15819731916784777576179533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42185951778092740203145421 15819731916784777576179533)
                  ·
                    refine ⟨5932399468794291591067325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15819731916784777576179533 5932399468794291591067325)
                    ·
                      refine ⟨2224649800797859346650247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5932399468794291591067325 2224649800797859346650247)
                      ·
                        rfl

theorem cell23_4332490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_4332490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332490 prefixEnd_4332490 := by exact prefixLift 4332490
  have htrace : WordTrace (prefixWord ++ tailWord_4332490) baseStart_4332490 baseEnd_4332490 := by
    simpa [prefixWord, tailWord_4332490, baseEnd_4332490] using wordTrace_append hprefix tailTrace_4332490
  have hstable : (prefixWord ++ tailWord_4332490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332490).length < 2 ^ (prefixWord ++ tailWord_4332490).sum := by decide
  have hdescent : baseEnd_4332490 < baseStart_4332490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332491 : List Nat := [1, 1, 1, 1, 3, 5, 3, 3, 1, 2, 2]
def baseStart_4332491 : Nat := 118140960795 + 4332491 * 2 ^ 59
def prefixEnd_4332491 : Nat := 4983230072969 + 3 ^ 40 * 4332491 * 2
def baseEnd_4332491 : Nat := 2224650314278513842737743

theorem tailTrace_4332491 : CollatzResearch.WordTrace tailWord_4332491 prefixEnd_4332491 2224650314278513842737743 := by
  unfold tailWord_4332491
  simp only [CollatzResearch.WordTrace]
  refine ⟨158018928547132512399029327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105345952364755008266019551 158018928547132512399029327)
  ·
    refine ⟨237028392820698768598543991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158018928547132512399029327 237028392820698768598543991)
    ·
      refine ⟨355542589231048152897815987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237028392820698768598543991 355542589231048152897815987)
      ·
        refine ⟨533313883846572229346723981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355542589231048152897815987 533313883846572229346723981)
        ·
          refine ⟨199992706442464586005021493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 533313883846572229346723981 199992706442464586005021493)
          ·
            refine ⟨18749316228981054937970765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 199992706442464586005021493 18749316228981054937970765)
            ·
              refine ⟨7030993585867895601739037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18749316228981054937970765 7030993585867895601739037)
              ·
                refine ⟨2636622594700460850652139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7030993585867895601739037 2636622594700460850652139)
                ·
                  refine ⟨3954933892050691275978209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2636622594700460850652139 3954933892050691275978209)
                  ·
                    refine ⟨2966200419038018456983657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3954933892050691275978209 2966200419038018456983657)
                    ·
                      refine ⟨2224650314278513842737743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2966200419038018456983657 2224650314278513842737743)
                      ·
                        rfl

theorem cell23_4332491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 1, 2, 2].length) (baseStart_4332491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332491 prefixEnd_4332491 := by exact prefixLift 4332491
  have htrace : WordTrace (prefixWord ++ tailWord_4332491) baseStart_4332491 baseEnd_4332491 := by
    simpa [prefixWord, tailWord_4332491, baseEnd_4332491] using wordTrace_append hprefix tailTrace_4332491
  have hstable : (prefixWord ++ tailWord_4332491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332491).length < 2 ^ (prefixWord ++ tailWord_4332491).sum := by decide
  have hdescent : baseEnd_4332491 < baseStart_4332491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332551 : List Nat := [1, 1, 4, 3, 1, 1, 5, 1, 1, 3, 2]
def baseStart_4332551 : Nat := 118140960795 + 4332551 * 2 ^ 59
def prefixEnd_4332551 : Nat := 4983230072969 + 3 ^ 40 * 4332551 * 2
def baseEnd_4332551 : Nat := 2224681123117783607987467

theorem tailTrace_4332551 : CollatzResearch.WordTrace tailWord_4332551 prefixEnd_4332551 2224681123117783607987467 := by
  unfold tailWord_4332551
  simp only [CollatzResearch.WordTrace]
  refine ⟨158021116926915142646213507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105347411284610095097475671 158021116926915142646213507)
  ·
    refine ⟨237031675390372713969320261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158021116926915142646213507 237031675390372713969320261)
    ·
      refine ⟨44443439135694883869247549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237031675390372713969320261 44443439135694883869247549)
      ·
        refine ⟨16666289675885581450967831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44443439135694883869247549 16666289675885581450967831)
        ·
          refine ⟨24999434513828372176451747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16666289675885581450967831 24999434513828372176451747)
          ·
            refine ⟨37499151770742558264677621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24999434513828372176451747 37499151770742558264677621)
            ·
              refine ⟨3515545478507114837313527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37499151770742558264677621 3515545478507114837313527)
              ·
                refine ⟨5273318217760672255970291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3515545478507114837313527 5273318217760672255970291)
                ·
                  refine ⟨7909977326641008383955437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5273318217760672255970291 7909977326641008383955437)
                  ·
                    refine ⟨2966241497490378143983289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7909977326641008383955437 2966241497490378143983289)
                    ·
                      refine ⟨2224681123117783607987467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2966241497490378143983289 2224681123117783607987467)
                      ·
                        rfl

theorem cell23_4332551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_4332551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332551 prefixEnd_4332551 := by exact prefixLift 4332551
  have htrace : WordTrace (prefixWord ++ tailWord_4332551) baseStart_4332551 baseEnd_4332551 := by
    simpa [prefixWord, tailWord_4332551, baseEnd_4332551] using wordTrace_append hprefix tailTrace_4332551
  have hstable : (prefixWord ++ tailWord_4332551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332551).length < 2 ^ (prefixWord ++ tailWord_4332551).sum := by decide
  have hdescent : baseEnd_4332551 < baseStart_4332551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332567 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 3]
def baseStart_4332567 : Nat := 118140960795 + 4332567 * 2 ^ 59
def prefixEnd_4332567 : Nat := 4983230072969 + 3 ^ 40 * 4332567 * 2
def baseEnd_4332567 : Nat := 2224689338808255545387393

theorem tailTrace_4332567 : CollatzResearch.WordTrace tailWord_4332567 prefixEnd_4332567 2224689338808255545387393 := by
  unfold tailWord_4332567
  simp only [CollatzResearch.WordTrace]
  refine ⟨158021700494857177378795955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105347800329904784919197303 158021700494857177378795955)
  ·
    refine ⟨237032550742285766068193933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158021700494857177378795955 237032550742285766068193933)
    ·
      refine ⟨88887206528357162275572725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237032550742285766068193933 88887206528357162275572725)
      ·
        refine ⟨8333175612033483963334943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88887206528357162275572725 8333175612033483963334943)
        ·
          refine ⟨12499763418050225945002415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8333175612033483963334943 12499763418050225945002415)
          ·
            refine ⟨18749645127075338917503623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12499763418050225945002415 18749645127075338917503623)
            ·
              refine ⟨28124467690613008376255435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18749645127075338917503623 28124467690613008376255435)
              ·
                refine ⟨42186701535919512564383153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28124467690613008376255435 42186701535919512564383153)
                ·
                  refine ⟨31640026151939634423287365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42186701535919512564383153 31640026151939634423287365)
                  ·
                    refine ⟨5932504903488681454366381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31640026151939634423287365 5932504903488681454366381)
                    ·
                      refine ⟨2224689338808255545387393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5932504903488681454366381 2224689338808255545387393)
                      ·
                        rfl

theorem cell23_4332567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_4332567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332567 prefixEnd_4332567 := by exact prefixLift 4332567
  have htrace : WordTrace (prefixWord ++ tailWord_4332567) baseStart_4332567 baseEnd_4332567 := by
    simpa [prefixWord, tailWord_4332567, baseEnd_4332567] using wordTrace_append hprefix tailTrace_4332567
  have hstable : (prefixWord ++ tailWord_4332567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332567).length < 2 ^ (prefixWord ++ tailWord_4332567).sum := by decide
  have hdescent : baseEnd_4332567 < baseStart_4332567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332570 : List Nat := [3, 1, 1, 3, 1, 2, 2, 3, 7]
def baseStart_4332570 : Nat := 118140960795 + 4332570 * 2 ^ 59
def prefixEnd_4332570 : Nat := 4983230072969 + 3 ^ 40 * 4332570 * 2
def baseEnd_4332570 : Nat := 247187875472246559294431

theorem tailTrace_4332570 : CollatzResearch.WordTrace tailWord_4332570 prefixEnd_4332570 247187875472246559294431 := by
  unfold tailWord_4332570
  simp only [CollatzResearch.WordTrace]
  refine ⟨39505452478461577222788791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105347873275897539260770109 39505452478461577222788791)
  ·
    refine ⟨59258178717692365834183187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39505452478461577222788791 59258178717692365834183187)
    ·
      refine ⟨88887268076538548751274781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59258178717692365834183187 88887268076538548751274781)
      ·
        refine ⟨33332725528701955781728043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88887268076538548751274781 33332725528701955781728043)
        ·
          refine ⟨49999088293052933672592065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33332725528701955781728043 49999088293052933672592065)
          ·
            refine ⟨37499316219789700254444049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49999088293052933672592065 37499316219789700254444049)
            ·
              refine ⟨28124487164842275190833037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37499316219789700254444049 28124487164842275190833037)
              ·
                refine ⟨10546682686815853196562389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28124487164842275190833037 10546682686815853196562389)
                ·
                  refine ⟨247187875472246559294431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10546682686815853196562389 247187875472246559294431)
                  ·
                    rfl

theorem cell23_4332570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 7].length) (baseStart_4332570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332570 prefixEnd_4332570 := by exact prefixLift 4332570
  have htrace : WordTrace (prefixWord ++ tailWord_4332570) baseStart_4332570 baseEnd_4332570 := by
    simpa [prefixWord, tailWord_4332570, baseEnd_4332570] using wordTrace_append hprefix tailTrace_4332570
  have hstable : (prefixWord ++ tailWord_4332570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332570).length < 2 ^ (prefixWord ++ tailWord_4332570).sum := by decide
  have hdescent : baseEnd_4332570 < baseStart_4332570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332577 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_4332577 : Nat := 118140960795 + 4332577 * 2 ^ 59
def prefixEnd_4332577 : Nat := 4983230072969 + 3 ^ 40 * 4332577 * 2
def baseEnd_4332577 : Nat := 2224694473614800506262347

theorem tailTrace_4332577 : CollatzResearch.WordTrace tailWord_4332577 prefixEnd_4332577 2224694473614800506262347 := by
  unfold tailWord_4332577
  simp only [CollatzResearch.WordTrace]
  refine ⟨158022065224820949086659985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105348043483213966057773323 158022065224820949086659985)
  ·
    refine ⟨118516548918615711814994989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158022065224820949086659985 118516548918615711814994989)
    ·
      refine ⟨44443705844480891930623121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118516548918615711814994989 44443705844480891930623121)
      ·
        refine ⟨33332779383360668947967341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44443705844480891930623121 33332779383360668947967341)
        ·
          refine ⟨12499792268760250855487753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33332779383360668947967341 12499792268760250855487753)
          ·
            refine ⟨9374844201570188141615815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12499792268760250855487753 9374844201570188141615815)
            ·
              refine ⟨14062266302355282212423723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9374844201570188141615815 14062266302355282212423723)
              ·
                refine ⟨21093399453532923318635585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14062266302355282212423723 21093399453532923318635585)
                ·
                  refine ⟨15820049590149692488976689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21093399453532923318635585 15820049590149692488976689)
                  ·
                    refine ⟨11865037192612269366732517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15820049590149692488976689 11865037192612269366732517)
                    ·
                      refine ⟨2224694473614800506262347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11865037192612269366732517 2224694473614800506262347)
                      ·
                        rfl

theorem cell23_4332577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_4332577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332577 prefixEnd_4332577 := by exact prefixLift 4332577
  have htrace : WordTrace (prefixWord ++ tailWord_4332577) baseStart_4332577 baseEnd_4332577 := by
    simpa [prefixWord, tailWord_4332577, baseEnd_4332577] using wordTrace_append hprefix tailTrace_4332577
  have hstable : (prefixWord ++ tailWord_4332577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332577).length < 2 ^ (prefixWord ++ tailWord_4332577).sum := by decide
  have hdescent : baseEnd_4332577 < baseStart_4332577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332604 : List Nat := [2, 2, 2, 2, 2, 3, 2, 3, 5]
def baseStart_4332604 : Nat := 118140960795 + 4332604 * 2 ^ 59
def prefixEnd_4332604 : Nat := 4983230072969 + 3 ^ 40 * 4332604 * 2
def baseEnd_4332604 : Nat := 247189815288052433402747

theorem tailTrace_4332604 : CollatzResearch.WordTrace tailWord_4332604 prefixEnd_4332604 247189815288052433402747 := by
  unfold tailWord_4332604
  simp only [CollatzResearch.WordTrace]
  refine ⟨79011524997861566348946433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105348699997148755131928577 79011524997861566348946433)
  ·
    refine ⟨59258643748396174761709825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79011524997861566348946433 59258643748396174761709825)
    ·
      refine ⟨44443982811297131071282369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59258643748396174761709825 44443982811297131071282369)
      ·
        refine ⟨33332987108472848303461777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44443982811297131071282369 33332987108472848303461777)
        ·
          refine ⟨24999740331354636227596333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33332987108472848303461777 24999740331354636227596333)
          ·
            refine ⟨9374902624257988585348625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24999740331354636227596333 9374902624257988585348625)
            ·
              refine ⟨7031176968193491439011469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9374902624257988585348625 7031176968193491439011469)
              ·
                refine ⟨2636691363072559289629301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7031176968193491439011469 2636691363072559289629301)
                ·
                  refine ⟨247189815288052433402747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2636691363072559289629301 247189815288052433402747)
                  ·
                    rfl

theorem cell23_4332604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 5].length) (baseStart_4332604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332604 prefixEnd_4332604 := by exact prefixLift 4332604
  have htrace : WordTrace (prefixWord ++ tailWord_4332604) baseStart_4332604 baseEnd_4332604 := by
    simpa [prefixWord, tailWord_4332604, baseEnd_4332604] using wordTrace_append hprefix tailTrace_4332604
  have hstable : (prefixWord ++ tailWord_4332604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332604).length < 2 ^ (prefixWord ++ tailWord_4332604).sum := by decide
  have hdescent : baseEnd_4332604 < baseStart_4332604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332704 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 5, 1, 3]
def baseStart_4332704 : Nat := 118140960795 + 4332704 * 2 ^ 59
def prefixEnd_4332704 : Nat := 4983230072969 + 3 ^ 40 * 4332704 * 2
def baseEnd_4332704 : Nat := 2224759685657921509374263

theorem tailTrace_4332704 : CollatzResearch.WordTrace tailWord_4332704 prefixEnd_4332704 2224759685657921509374263 := by
  unfold tailWord_4332704
  simp only [CollatzResearch.WordTrace]
  refine ⟨79013348647680424888266583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105351131530240566517688777 79013348647680424888266583)
  ·
    refine ⟨118520022971520637332399875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79013348647680424888266583 118520022971520637332399875)
    ·
      refine ⟨177780034457280955998599813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118520022971520637332399875 177780034457280955998599813)
      ·
        refine ⟨33333756460740179249737465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177780034457280955998599813 33333756460740179249737465)
        ·
          refine ⟨25000317345555134437303099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33333756460740179249737465 25000317345555134437303099)
          ·
            refine ⟨37500476018332701655954649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25000317345555134437303099 37500476018332701655954649)
            ·
              refine ⟨28125357013749526241965987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37500476018332701655954649 28125357013749526241965987)
              ·
                refine ⟨42188035520624289362948981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28125357013749526241965987 42188035520624289362948981)
                ·
                  refine ⟨3955128330058527127776467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42188035520624289362948981 3955128330058527127776467)
                  ·
                    refine ⟨5932692495087790691664701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3955128330058527127776467 5932692495087790691664701)
                    ·
                      refine ⟨2224759685657921509374263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5932692495087790691664701 2224759685657921509374263)
                      ·
                        rfl

theorem cell23_4332704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_4332704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332704 prefixEnd_4332704 := by exact prefixLift 4332704
  have htrace : WordTrace (prefixWord ++ tailWord_4332704) baseStart_4332704 baseEnd_4332704 := by
    simpa [prefixWord, tailWord_4332704, baseEnd_4332704] using wordTrace_append hprefix tailTrace_4332704
  have hstable : (prefixWord ++ tailWord_4332704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332704).length < 2 ^ (prefixWord ++ tailWord_4332704).sum := by decide
  have hdescent : baseEnd_4332704 < baseStart_4332704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332754 : List Nat := [3, 2, 2, 2, 1, 1, 4, 1, 1, 6]
def baseStart_4332754 : Nat := 118140960795 + 4332754 * 2 ^ 59
def prefixEnd_4332754 : Nat := 4983230072969 + 3 ^ 40 * 4332754 * 2
def baseEnd_4332754 : Nat := 741595119896882104583011

theorem tailTrace_4332754 : CollatzResearch.WordTrace tailWord_4332754 prefixEnd_4332754 741595119896882104583011 := by
  unfold tailWord_4332754
  simp only [CollatzResearch.WordTrace]
  refine ⟨39507130236294927078963329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105352347296786472210568877 39507130236294927078963329)
  ·
    refine ⟨29630347677221195309222497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39507130236294927078963329 29630347677221195309222497)
    ·
      refine ⟨22222760757915896481916873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29630347677221195309222497 22222760757915896481916873)
      ·
        refine ⟨16667070568436922361437655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22222760757915896481916873 16667070568436922361437655)
        ·
          refine ⟨25000605852655383542156483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16667070568436922361437655 25000605852655383542156483)
          ·
            refine ⟨37500908778983075313234725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25000605852655383542156483 37500908778983075313234725)
            ·
              refine ⟨7031420396059326621231511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37500908778983075313234725 7031420396059326621231511)
              ·
                refine ⟨10547130594088989931847267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7031420396059326621231511 10547130594088989931847267)
                ·
                  refine ⟨15820695891133484897770901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10547130594088989931847267 15820695891133484897770901)
                  ·
                    refine ⟨741595119896882104583011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15820695891133484897770901 741595119896882104583011)
                    ·
                      rfl

theorem cell23_4332754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_4332754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332754 prefixEnd_4332754 := by exact prefixLift 4332754
  have htrace : WordTrace (prefixWord ++ tailWord_4332754) baseStart_4332754 baseEnd_4332754 := by
    simpa [prefixWord, tailWord_4332754, baseEnd_4332754] using wordTrace_append hprefix tailTrace_4332754
  have hstable : (prefixWord ++ tailWord_4332754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332754).length < 2 ^ (prefixWord ++ tailWord_4332754).sum := by decide
  have hdescent : baseEnd_4332754 < baseStart_4332754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332765 : List Nat := [1, 4, 3, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_4332765 : Nat := 118140960795 + 4332765 * 2 ^ 59
def prefixEnd_4332765 : Nat := 4983230072969 + 3 ^ 40 * 4332765 * 2
def baseEnd_4332765 : Nat := 2224791007977845770711483

theorem tailTrace_4332765 : CollatzResearch.WordTrace tailWord_4332765 prefixEnd_4332765 2224791007977845770711483 := by
  unfold tailWord_4332765
  simp only [CollatzResearch.WordTrace]
  refine ⟨158028922148139857194503749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105352614765426571463002499 158028922148139857194503749)
  ·
    refine ⟨29630422902776223223969453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158028922148139857194503749 29630422902776223223969453)
    ·
      refine ⟨11111408588541083708988545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29630422902776223223969453 11111408588541083708988545)
      ·
        refine ⟨8333556441405812781741409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11111408588541083708988545 8333556441405812781741409)
        ·
          refine ⟨6250167331054359586306057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8333556441405812781741409 6250167331054359586306057)
          ·
            refine ⟨4687625498290769689729543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6250167331054359586306057 4687625498290769689729543)
            ·
              refine ⟨7031438247436154534594315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4687625498290769689729543 7031438247436154534594315)
              ·
                refine ⟨10547157371154231801891473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7031438247436154534594315 10547157371154231801891473)
                ·
                  refine ⟨7910368028365673851418605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10547157371154231801891473 7910368028365673851418605)
                  ·
                    refine ⟨2966388010637127694281977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7910368028365673851418605 2966388010637127694281977)
                    ·
                      refine ⟨2224791007977845770711483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2966388010637127694281977 2224791007977845770711483)
                      ·
                        rfl

theorem cell23_4332765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_4332765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332765 prefixEnd_4332765 := by exact prefixLift 4332765
  have htrace : WordTrace (prefixWord ++ tailWord_4332765) baseStart_4332765 baseEnd_4332765 := by
    simpa [prefixWord, tailWord_4332765, baseEnd_4332765] using wordTrace_append hprefix tailTrace_4332765
  have hstable : (prefixWord ++ tailWord_4332765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332765).length < 2 ^ (prefixWord ++ tailWord_4332765).sum := by decide
  have hdescent : baseEnd_4332765 < baseStart_4332765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332775 : List Nat := [1, 1, 5, 3, 3, 1, 2, 1, 1, 5]
def baseStart_4332775 : Nat := 118140960795 + 4332775 * 2 ^ 59
def prefixEnd_4332775 : Nat := 4983230072969 + 3 ^ 40 * 4332775 * 2
def baseEnd_4332775 : Nat := 741598714261463577195479

theorem tailTrace_4332775 : CollatzResearch.WordTrace tailWord_4332775 prefixEnd_4332775 741598714261463577195479 := by
  unfold tailWord_4332775
  simp only [CollatzResearch.WordTrace]
  refine ⟨158029286878103628902367779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105352857918735752601578519 158029286878103628902367779)
  ·
    refine ⟨237043930317155443353551669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158029286878103628902367779 237043930317155443353551669)
    ·
      refine ⟨22222868467233322814395469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 237043930317155443353551669 22222868467233322814395469)
      ·
        refine ⟨8333575675212496055398301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22222868467233322814395469 8333575675212496055398301)
        ·
          refine ⟨3125090878204686020774363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8333575675212496055398301 3125090878204686020774363)
          ·
            refine ⟨4687636317307029031161545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3125090878204686020774363 4687636317307029031161545)
            ·
              refine ⟨3515727237980271773371159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4687636317307029031161545 3515727237980271773371159)
              ·
                refine ⟨5273590856970407660056739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3515727237980271773371159 5273590856970407660056739)
                ·
                  refine ⟨7910386285455611490085109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5273590856970407660056739 7910386285455611490085109)
                  ·
                    refine ⟨741598714261463577195479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7910386285455611490085109 741598714261463577195479)
                    ·
                      rfl

theorem cell23_4332775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_4332775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332775 prefixEnd_4332775 := by exact prefixLift 4332775
  have htrace : WordTrace (prefixWord ++ tailWord_4332775) baseStart_4332775 baseEnd_4332775 := by
    simpa [prefixWord, tailWord_4332775, baseEnd_4332775] using wordTrace_append hprefix tailTrace_4332775
  have hstable : (prefixWord ++ tailWord_4332775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332775).length < 2 ^ (prefixWord ++ tailWord_4332775).sum := by decide
  have hdescent : baseEnd_4332775 < baseStart_4332775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332778 : List Nat := [3, 1, 3, 1, 1, 5, 2, 1, 1, 1, 4]
def baseStart_4332778 : Nat := 118140960795 + 4332778 * 2 ^ 59
def prefixEnd_4332778 : Nat := 4983230072969 + 3 ^ 40 * 4332778 * 2
def baseEnd_4332778 : Nat := 2224797683226354219848923

theorem tailTrace_4332778 : CollatzResearch.WordTrace tailWord_4332778 prefixEnd_4332778 2224797683226354219848923 := by
  unfold tailWord_4332778
  simp only [CollatzResearch.WordTrace]
  refine ⟨39507349074273190103681747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105352930864728506943151325 39507349074273190103681747)
  ·
    refine ⟨59261023611409785155522621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39507349074273190103681747 59261023611409785155522621)
    ·
      refine ⟨22222883854278669433320983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59261023611409785155522621 22222883854278669433320983)
      ·
        refine ⟨33334325781418004149981475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22222883854278669433320983 33334325781418004149981475)
        ·
          refine ⟨50001488672127006224972213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33334325781418004149981475 50001488672127006224972213)
          ·
            refine ⟨4687639563011906833591145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50001488672127006224972213 4687639563011906833591145)
            ·
              refine ⟨3515729672258930125193359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4687639563011906833591145 3515729672258930125193359)
              ·
                refine ⟨5273594508388395187790039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3515729672258930125193359 5273594508388395187790039)
                ·
                  refine ⟨7910391762582592781685059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5273594508388395187790039 7910391762582592781685059)
                  ·
                    refine ⟨11865587643873889172527589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7910391762582592781685059 11865587643873889172527589)
                    ·
                      refine ⟨2224797683226354219848923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11865587643873889172527589 2224797683226354219848923)
                      ·
                        rfl

theorem cell23_4332778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_4332778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332778 prefixEnd_4332778 := by exact prefixLift 4332778
  have htrace : WordTrace (prefixWord ++ tailWord_4332778) baseStart_4332778 baseEnd_4332778 := by
    simpa [prefixWord, tailWord_4332778, baseEnd_4332778] using wordTrace_append hprefix tailTrace_4332778
  have hstable : (prefixWord ++ tailWord_4332778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332778).length < 2 ^ (prefixWord ++ tailWord_4332778).sum := by decide
  have hdescent : baseEnd_4332778 < baseStart_4332778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332808 : List Nat := [2, 1, 3, 2, 5, 1, 1, 1, 1, 2, 4]
def baseStart_4332808 : Nat := 118140960795 + 4332808 * 2 ^ 59
def prefixEnd_4332808 : Nat := 4983230072969 + 3 ^ 40 * 4332808 * 2
def baseEnd_4332808 : Nat := 2224813087645989102473785

theorem tailTrace_4332808 : CollatzResearch.WordTrace tailWord_4332808 prefixEnd_4332808 2224813087645989102473785 := by
  unfold tailWord_4332808
  simp only [CollatzResearch.WordTrace]
  refine ⟨79015245243492037769159539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105353660324656050358879385 79015245243492037769159539)
  ·
    refine ⟨118522867865238056653739309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79015245243492037769159539 118522867865238056653739309)
    ·
      refine ⟨44446075449464271245152241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118522867865238056653739309 44446075449464271245152241)
      ·
        refine ⟨33334556587098203433864181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44446075449464271245152241 33334556587098203433864181)
        ·
          refine ⟨3125114680040456571924767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33334556587098203433864181 3125114680040456571924767)
          ·
            refine ⟨4687672020060684857887151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3125114680040456571924767 4687672020060684857887151)
            ·
              refine ⟨7031508030091027286830727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4687672020060684857887151 7031508030091027286830727)
              ·
                refine ⟨10547262045136540930246091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7031508030091027286830727 10547262045136540930246091)
                ·
                  refine ⟨15820893067704811395369137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10547262045136540930246091 15820893067704811395369137)
                  ·
                    refine ⟨11865669800778608546526853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15820893067704811395369137 11865669800778608546526853)
                    ·
                      refine ⟨2224813087645989102473785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11865669800778608546526853 2224813087645989102473785)
                      ·
                        rfl

theorem cell23_4332808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_4332808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332808 prefixEnd_4332808 := by exact prefixLift 4332808
  have htrace : WordTrace (prefixWord ++ tailWord_4332808) baseStart_4332808 baseEnd_4332808 := by
    simpa [prefixWord, tailWord_4332808, baseEnd_4332808] using wordTrace_append hprefix tailTrace_4332808
  have hstable : (prefixWord ++ tailWord_4332808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332808).length < 2 ^ (prefixWord ++ tailWord_4332808).sum := by decide
  have hdescent : baseEnd_4332808 < baseStart_4332808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332811 : List Nat := [1, 1, 1, 1, 5, 5, 1, 1, 1, 3, 3]
def baseStart_4332811 : Nat := 118140960795 + 4332811 * 2 ^ 59
def prefixEnd_4332811 : Nat := 4983230072969 + 3 ^ 40 * 4332811 * 2
def baseEnd_4332811 : Nat := 2224814628087952590736271

theorem tailTrace_4332811 : CollatzResearch.WordTrace tailWord_4332811 prefixEnd_4332811 2224814628087952590736271 := by
  unfold tailWord_4332811
  simp only [CollatzResearch.WordTrace]
  refine ⟨158030599905973207050678287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105353733270648804700452191 158030599905973207050678287)
  ·
    refine ⟨237045899858959810576017431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158030599905973207050678287 237045899858959810576017431)
    ·
      refine ⟨355568849788439715864026147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237045899858959810576017431 355568849788439715864026147)
      ·
        refine ⟨533353274682659573796039221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355568849788439715864026147 533353274682659573796039221)
        ·
          refine ⟨50001869501499335043378677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 533353274682659573796039221 50001869501499335043378677)
          ·
            refine ⟨4687675265765562660316751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50001869501499335043378677 4687675265765562660316751)
            ·
              refine ⟨7031512898648343990475127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4687675265765562660316751 7031512898648343990475127)
              ·
                refine ⟨10547269347972515985712691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7031512898648343990475127 10547269347972515985712691)
                ·
                  refine ⟨15820904021958773978569037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10547269347972515985712691 15820904021958773978569037)
                  ·
                    refine ⟨5932839008234540241963389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15820904021958773978569037 5932839008234540241963389)
                    ·
                      refine ⟨2224814628087952590736271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5932839008234540241963389 2224814628087952590736271)
                      ·
                        rfl

theorem cell23_4332811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 3, 3].length) (baseStart_4332811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332811 prefixEnd_4332811 := by exact prefixLift 4332811
  have htrace : WordTrace (prefixWord ++ tailWord_4332811) baseStart_4332811 baseEnd_4332811 := by
    simpa [prefixWord, tailWord_4332811, baseEnd_4332811] using wordTrace_append hprefix tailTrace_4332811
  have hstable : (prefixWord ++ tailWord_4332811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332811).length < 2 ^ (prefixWord ++ tailWord_4332811).sum := by decide
  have hdescent : baseEnd_4332811 < baseStart_4332811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332907 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 8]
def baseStart_4332907 : Nat := 118140960795 + 4332907 * 2 ^ 59
def prefixEnd_4332907 : Nat := 4983230072969 + 3 ^ 40 * 4332907 * 2
def baseEnd_4332907 : Nat := 2224863922230784215135829

theorem tailTrace_4332907 : CollatzResearch.WordTrace tailWord_4332907 prefixEnd_4332907 2224863922230784215135829 := by
  unfold tailWord_4332907
  simp only [CollatzResearch.WordTrace]
  refine ⟨158034101313625415446172975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105356067542416943630781983 158034101313625415446172975)
  ·
    refine ⟨237051151970438123169259463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158034101313625415446172975 237051151970438123169259463)
    ·
      refine ⟨355576727955657184753889195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237051151970438123169259463 355576727955657184753889195)
      ·
        refine ⟨533365091933485777130833793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355576727955657184753889195 533365091933485777130833793)
        ·
          refine ⟨400023818950114332848125345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 533365091933485777130833793 400023818950114332848125345)
          ·
            refine ⟨300017864212585749636094009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 400023818950114332848125345 300017864212585749636094009)
            ·
              refine ⟨225013398159439312227070507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300017864212585749636094009 225013398159439312227070507)
              ·
                refine ⟨337520097239158968340605761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225013398159439312227070507 337520097239158968340605761)
                ·
                  refine ⟨253140072929369226255454321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337520097239158968340605761 253140072929369226255454321)
                  ·
                    refine ⟨189855054697026919691590741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 253140072929369226255454321 189855054697026919691590741)
                    ·
                      refine ⟨2224863922230784215135829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 189855054697026919691590741 2224863922230784215135829)
                      ·
                        rfl

theorem cell23_4332907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 8].length) (baseStart_4332907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332907 prefixEnd_4332907 := by exact prefixLift 4332907
  have htrace : WordTrace (prefixWord ++ tailWord_4332907) baseStart_4332907 baseEnd_4332907 := by
    simpa [prefixWord, tailWord_4332907, baseEnd_4332907] using wordTrace_append hprefix tailTrace_4332907
  have hstable : (prefixWord ++ tailWord_4332907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332907).length < 2 ^ (prefixWord ++ tailWord_4332907).sum := by decide
  have hdescent : baseEnd_4332907 < baseStart_4332907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332908 : List Nat := [2, 2, 1, 1, 5, 1, 4, 2, 5]
def baseStart_4332908 : Nat := 118140960795 + 4332908 * 2 ^ 59
def prefixEnd_4332908 : Nat := 4983230072969 + 3 ^ 40 * 4332908 * 2
def baseEnd_4332908 : Nat := 247207159523493190135925

theorem tailTrace_4332908 : CollatzResearch.WordTrace tailWord_4332908 prefixEnd_4332908 247207159523493190135925 := by
  unfold tailWord_4332908
  simp only [CollatzResearch.WordTrace]
  refine ⟨79017068893310896308479689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105356091857747861744639585 79017068893310896308479689)
  ·
    refine ⟨59262801669983172231359767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79017068893310896308479689 59262801669983172231359767)
    ·
      refine ⟨88894202504974758347039651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59262801669983172231359767 88894202504974758347039651)
      ·
        refine ⟨133341303757462137520559477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88894202504974758347039651 133341303757462137520559477)
        ·
          refine ⟨12500747227262075392552451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 133341303757462137520559477 12500747227262075392552451)
          ·
            refine ⟨18751120840893113088828677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12500747227262075392552451 18751120840893113088828677)
            ·
              refine ⟨3515835157667458704155377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18751120840893113088828677 3515835157667458704155377)
              ·
                refine ⟨2636876368250594028116533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3515835157667458704155377 2636876368250594028116533)
                ·
                  refine ⟨247207159523493190135925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2636876368250594028116533 247207159523493190135925)
                  ·
                    rfl

theorem cell23_4332908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 5].length) (baseStart_4332908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332908 prefixEnd_4332908 := by exact prefixLift 4332908
  have htrace : WordTrace (prefixWord ++ tailWord_4332908) baseStart_4332908 baseEnd_4332908 := by
    simpa [prefixWord, tailWord_4332908, baseEnd_4332908] using wordTrace_append hprefix tailTrace_4332908
  have hstable : (prefixWord ++ tailWord_4332908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332908).length < 2 ^ (prefixWord ++ tailWord_4332908).sum := by decide
  have hdescent : baseEnd_4332908 < baseStart_4332908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332914 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_4332914 : Nat := 118140960795 + 4332914 * 2 ^ 59
def prefixEnd_4332914 : Nat := 4983230072969 + 3 ^ 40 * 4332914 * 2
def baseEnd_4332914 : Nat := 2224867516595365687748297

theorem tailTrace_4332914 : CollatzResearch.WordTrace tailWord_4332914 prefixEnd_4332914 2224867516595365687748297 := by
  unfold tailWord_4332914
  simp only [CollatzResearch.WordTrace]
  refine ⟨39508589156150013910419449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105356237749733370427785197 39508589156150013910419449)
  ·
    refine ⟨29631441867112510432814587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39508589156150013910419449 29631441867112510432814587)
    ·
      refine ⟨44447162800668765649221881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29631441867112510432814587 44447162800668765649221881)
      ·
        refine ⟨33335372100501574236916411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44447162800668765649221881 33335372100501574236916411)
        ·
          refine ⟨50003058150752361355374617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33335372100501574236916411 50003058150752361355374617)
          ·
            refine ⟨37502293613064271016530963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50003058150752361355374617 37502293613064271016530963)
            ·
              refine ⟨56253440419596406524796445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37502293613064271016530963 56253440419596406524796445)
              ·
                refine ⟨21095040157348652446798667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56253440419596406524796445 21095040157348652446798667)
                ·
                  refine ⟨31642560236022978670198001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21095040157348652446798667 31642560236022978670198001)
                  ·
                    refine ⟨23731920177017234002648501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31642560236022978670198001 23731920177017234002648501)
                    ·
                      refine ⟨2224867516595365687748297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23731920177017234002648501 2224867516595365687748297)
                      ·
                        rfl

theorem cell23_4332914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_4332914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332914 prefixEnd_4332914 := by exact prefixLift 4332914
  have htrace : WordTrace (prefixWord ++ tailWord_4332914) baseStart_4332914 baseEnd_4332914 := by
    simpa [prefixWord, tailWord_4332914, baseEnd_4332914] using wordTrace_append hprefix tailTrace_4332914
  have hstable : (prefixWord ++ tailWord_4332914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332914).length < 2 ^ (prefixWord ++ tailWord_4332914).sum := by decide
  have hdescent : baseEnd_4332914 < baseStart_4332914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332924 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_4332924 : Nat := 118140960795 + 4332924 * 2 ^ 59
def prefixEnd_4332924 : Nat := 4983230072969 + 3 ^ 40 * 4332924 * 2
def baseEnd_4332924 : Nat := 2224872651401910648623251

theorem tailTrace_4332924 : CollatzResearch.WordTrace tailWord_4332924 prefixEnd_4332924 2224872651401910648623251 := by
  unfold tailWord_4332924
  simp only [CollatzResearch.WordTrace]
  refine ⟨79017360677281913674770913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105356480903042551566361217 79017360677281913674770913)
  ·
    refine ⟨59263020507961435256078185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79017360677281913674770913 59263020507961435256078185)
    ·
      refine ⟨44447265380971076442058639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59263020507961435256078185 44447265380971076442058639)
      ·
        refine ⟨66670898071456614663087959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44447265380971076442058639 66670898071456614663087959)
        ·
          refine ⟨100006347107184921994631939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66670898071456614663087959 100006347107184921994631939)
          ·
            refine ⟨150009520660777382991947909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100006347107184921994631939 150009520660777382991947909)
            ·
              refine ⟨28126785123895759310990233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 150009520660777382991947909 28126785123895759310990233)
              ·
                refine ⟨21095088842921819483242675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28126785123895759310990233 21095088842921819483242675)
                ·
                  refine ⟨31642633264382729224864013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21095088842921819483242675 31642633264382729224864013)
                  ·
                    refine ⟨11865987474143523459324005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31642633264382729224864013 11865987474143523459324005)
                    ·
                      refine ⟨2224872651401910648623251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11865987474143523459324005 2224872651401910648623251)
                      ·
                        rfl

theorem cell23_4332924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_4332924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332924 prefixEnd_4332924 := by exact prefixLift 4332924
  have htrace : WordTrace (prefixWord ++ tailWord_4332924) baseStart_4332924 baseEnd_4332924 := by
    simpa [prefixWord, tailWord_4332924, baseEnd_4332924] using wordTrace_append hprefix tailTrace_4332924
  have hstable : (prefixWord ++ tailWord_4332924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332924).length < 2 ^ (prefixWord ++ tailWord_4332924).sum := by decide
  have hdescent : baseEnd_4332924 < baseStart_4332924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4332954 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6]
def baseStart_4332954 : Nat := 118140960795 + 4332954 * 2 ^ 59
def prefixEnd_4332954 : Nat := 4983230072969 + 3 ^ 40 * 4332954 * 2
def baseEnd_4332954 : Nat := 2224888055821545531248113

theorem tailTrace_4332954 : CollatzResearch.WordTrace tailWord_4332954 prefixEnd_4332954 2224888055821545531248113 := by
  unfold tailWord_4332954
  simp only [CollatzResearch.WordTrace]
  refine ⟨39508953886113785618283479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105357210362970094982089277 39508953886113785618283479)
  ·
    refine ⟨59263430829170678427425219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39508953886113785618283479 59263430829170678427425219)
    ·
      refine ⟨88895146243756017641137829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59263430829170678427425219 88895146243756017641137829)
      ·
        refine ⟨16667839920704253307713343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88895146243756017641137829 16667839920704253307713343)
        ·
          refine ⟨25001759881056379961570015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16667839920704253307713343 25001759881056379961570015)
          ·
            refine ⟨37502639821584569942355023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25001759881056379961570015 37502639821584569942355023)
            ·
              refine ⟨56253959732376854913532535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37502639821584569942355023 56253959732376854913532535)
              ·
                refine ⟨84380939598565282370298803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56253959732376854913532535 84380939598565282370298803)
                ·
                  refine ⟨126571409397847923555448205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84380939598565282370298803 126571409397847923555448205)
                  ·
                    refine ⟨47464278524192971333293077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 126571409397847923555448205 47464278524192971333293077)
                    ·
                      refine ⟨2224888055821545531248113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47464278524192971333293077 2224888055821545531248113)
                      ·
                        rfl

theorem cell23_4332954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_4332954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4332954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4332954 prefixEnd_4332954 := by exact prefixLift 4332954
  have htrace : WordTrace (prefixWord ++ tailWord_4332954) baseStart_4332954 baseEnd_4332954 := by
    simpa [prefixWord, tailWord_4332954, baseEnd_4332954] using wordTrace_append hprefix tailTrace_4332954
  have hstable : (prefixWord ++ tailWord_4332954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4332954).length < 2 ^ (prefixWord ++ tailWord_4332954).sum := by decide
  have hdescent : baseEnd_4332954 < baseStart_4332954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4332954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333018 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2]
def baseStart_4333018 : Nat := 118140960795 + 4333018 * 2 ^ 59
def prefixEnd_4333018 : Nat := 4983230072969 + 3 ^ 40 * 4333018 * 2
def baseEnd_4333018 : Nat := 2224920918583433280847819

theorem tailTrace_4333018 : CollatzResearch.WordTrace tailWord_4333018 prefixEnd_4333018 2224920918583433280847819 := by
  unfold tailWord_4333018
  simp only [CollatzResearch.WordTrace]
  refine ⟨39509537454055820350865927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105358766544148854268975805 39509537454055820350865927)
  ·
    refine ⟨59264306181083730526298891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39509537454055820350865927 59264306181083730526298891)
    ·
      refine ⟨88896459271625595789448337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59264306181083730526298891 88896459271625595789448337)
      ·
        refine ⟨66672344453719196842086253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88896459271625595789448337 66672344453719196842086253)
        ·
          refine ⟨25002129170144698815782345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66672344453719196842086253 25002129170144698815782345)
          ·
            refine ⟨18751596877608524111836759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25002129170144698815782345 18751596877608524111836759)
            ·
              refine ⟨28127395316412786167755139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18751596877608524111836759 28127395316412786167755139)
              ·
                refine ⟨42191092974619179251632709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28127395316412786167755139 42191092974619179251632709)
                ·
                  refine ⟨7910829932741096109681133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42191092974619179251632709 7910829932741096109681133)
                  ·
                    refine ⟨2966561224777911041130425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7910829932741096109681133 2966561224777911041130425)
                    ·
                      refine ⟨2224920918583433280847819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2966561224777911041130425 2224920918583433280847819)
                      ·
                        rfl

theorem cell23_4333018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_4333018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333018 prefixEnd_4333018 := by exact prefixLift 4333018
  have htrace : WordTrace (prefixWord ++ tailWord_4333018) baseStart_4333018 baseEnd_4333018 := by
    simpa [prefixWord, tailWord_4333018, baseEnd_4333018] using wordTrace_append hprefix tailTrace_4333018
  have hstable : (prefixWord ++ tailWord_4333018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333018).length < 2 ^ (prefixWord ++ tailWord_4333018).sum := by decide
  have hdescent : baseEnd_4333018 < baseStart_4333018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333024 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 5, 6]
def baseStart_4333024 : Nat := 118140960795 + 4333024 * 2 ^ 59
def prefixEnd_4333024 : Nat := 4983230072969 + 3 ^ 40 * 4333024 * 2
def baseEnd_4333024 : Nat := 741641333155786752457597

theorem tailTrace_4333024 : CollatzResearch.WordTrace tailWord_4333024 prefixEnd_4333024 741641333155786752457597 := by
  unfold tailWord_4333024
  simp only [CollatzResearch.WordTrace]
  refine ⟨79019184327100772214091063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105358912436134362952121417 79019184327100772214091063)
  ·
    refine ⟨118528776490651158321136595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79019184327100772214091063 118528776490651158321136595)
    ·
      refine ⟨177793164735976737481704893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118528776490651158321136595 177793164735976737481704893)
      ·
        refine ⟨66672436775991276555639335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177793164735976737481704893 66672436775991276555639335)
        ·
          refine ⟨100008655163986914833459003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66672436775991276555639335 100008655163986914833459003)
          ·
            refine ⟨150012982745980372250188505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100008655163986914833459003 150012982745980372250188505)
            ·
              refine ⟨112509737059485279187641379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150012982745980372250188505 112509737059485279187641379)
              ·
                refine ⟨168764605589227918781462069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112509737059485279187641379 168764605589227918781462069)
                ·
                  refine ⟨15821681773990117385762069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 168764605589227918781462069 15821681773990117385762069)
                  ·
                    refine ⟨741641333155786752457597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15821681773990117385762069 741641333155786752457597)
                    ·
                      rfl

theorem cell23_4333024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5, 6].length) (baseStart_4333024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333024 prefixEnd_4333024 := by exact prefixLift 4333024
  have htrace : WordTrace (prefixWord ++ tailWord_4333024) baseStart_4333024 baseEnd_4333024 := by
    simpa [prefixWord, tailWord_4333024, baseEnd_4333024] using wordTrace_append hprefix tailTrace_4333024
  have hstable : (prefixWord ++ tailWord_4333024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333024).length < 2 ^ (prefixWord ++ tailWord_4333024).sum := by decide
  have hdescent : baseEnd_4333024 < baseStart_4333024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333025 : List Nat := [1, 2, 3, 1, 2, 5, 1, 1, 3, 1, 3]
def baseStart_4333025 : Nat := 118140960795 + 4333025 * 2 ^ 59
def prefixEnd_4333025 : Nat := 4983230072969 + 3 ^ 40 * 4333025 * 2
def baseEnd_4333025 : Nat := 2224924512948014753460287

theorem tailTrace_4333025 : CollatzResearch.WordTrace tailWord_4333025 prefixEnd_4333025 2224924512948014753460287 := by
  unfold tailWord_4333025
  simp only [CollatzResearch.WordTrace]
  refine ⟨158038405127197921598968529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105358936751465281065979019 158038405127197921598968529)
  ·
    refine ⟨118528803845398441199226397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158038405127197921598968529 118528803845398441199226397)
    ·
      refine ⟨44448301442024415449709899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118528803845398441199226397 44448301442024415449709899)
      ·
        refine ⟨66672452163036623174564849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44448301442024415449709899 66672452163036623174564849)
        ·
          refine ⟨50004339122277467380923637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66672452163036623174564849 50004339122277467380923637)
          ·
            refine ⟨4687906792713512566961591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50004339122277467380923637 4687906792713512566961591)
            ·
              refine ⟨7031860189070268850442387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4687906792713512566961591 7031860189070268850442387)
              ·
                refine ⟨10547790283605403275663581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7031860189070268850442387 10547790283605403275663581)
                ·
                  refine ⟨3955421356352026228373843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10547790283605403275663581 3955421356352026228373843)
                  ·
                    refine ⟨5933132034528039342560765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3955421356352026228373843 5933132034528039342560765)
                    ·
                      refine ⟨2224924512948014753460287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5933132034528039342560765 2224924512948014753460287)
                      ·
                        rfl

theorem cell23_4333025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_4333025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333025 prefixEnd_4333025 := by exact prefixLift 4333025
  have htrace : WordTrace (prefixWord ++ tailWord_4333025) baseStart_4333025 baseEnd_4333025 := by
    simpa [prefixWord, tailWord_4333025, baseEnd_4333025] using wordTrace_append hprefix tailTrace_4333025
  have hstable : (prefixWord ++ tailWord_4333025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333025).length < 2 ^ (prefixWord ++ tailWord_4333025).sum := by decide
  have hdescent : baseEnd_4333025 < baseStart_4333025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333045 : List Nat := [1, 3, 5, 1, 1, 1, 3, 2, 1, 5]
def baseStart_4333045 : Nat := 118140960795 + 4333045 * 2 ^ 59
def prefixEnd_4333045 : Nat := 4983230072969 + 3 ^ 40 * 4333045 * 2
def baseEnd_4333045 : Nat := 741644927520368225070065

theorem tailTrace_4333045 : CollatzResearch.WordTrace tailWord_4333045 prefixEnd_4333045 741644927520368225070065 := by
  unfold tailWord_4333045
  simp only [CollatzResearch.WordTrace]
  refine ⟨158039134587125465014696589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105359423058083643343131059 158039134587125465014696589)
  ·
    refine ⟨59264675470172049380511221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158039134587125465014696589 59264675470172049380511221)
    ·
      refine ⟨5556063325328629629422927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59264675470172049380511221 5556063325328629629422927)
      ·
        refine ⟨8334094987992944444134391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5556063325328629629422927 8334094987992944444134391)
        ·
          refine ⟨12501142481989416666201587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8334094987992944444134391 12501142481989416666201587)
          ·
            refine ⟨18751713722984124999302381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12501142481989416666201587 18751713722984124999302381)
            ·
              refine ⟨7031892646119046874738393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18751713722984124999302381 7031892646119046874738393)
              ·
                refine ⟨5273919484589285156053795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7031892646119046874738393 5273919484589285156053795)
                ·
                  refine ⟨7910879226883927734080693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5273919484589285156053795 7910879226883927734080693)
                  ·
                    refine ⟨741644927520368225070065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7910879226883927734080693 741644927520368225070065)
                    ·
                      rfl

theorem cell23_4333045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_4333045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333045 prefixEnd_4333045 := by exact prefixLift 4333045
  have htrace : WordTrace (prefixWord ++ tailWord_4333045) baseStart_4333045 baseEnd_4333045 := by
    simpa [prefixWord, tailWord_4333045, baseEnd_4333045] using wordTrace_append hprefix tailTrace_4333045
  have hstable : (prefixWord ++ tailWord_4333045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333045).length < 2 ^ (prefixWord ++ tailWord_4333045).sum := by decide
  have hdescent : baseEnd_4333045 < baseStart_4333045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333048 : List Nat := [2, 1, 2, 1, 1, 5, 3, 2, 1, 1, 4]
def baseStart_4333048 : Nat := 118140960795 + 4333048 * 2 ^ 59
def prefixEnd_4333048 : Nat := 4983230072969 + 3 ^ 40 * 4333048 * 2
def baseEnd_4333048 : Nat := 2224936323003068163472681

theorem tailTrace_4333048 : CollatzResearch.WordTrace tailWord_4333048 prefixEnd_4333048 2224936323003068163472681 := by
  unfold tailWord_4333048
  simp only [CollatzResearch.WordTrace]
  refine ⟨79019622003057298263527899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105359496004076397684703865 79019622003057298263527899)
  ·
    refine ⟨118529433004585947395291849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79019622003057298263527899 118529433004585947395291849)
    ·
      refine ⟨88897074753439460546468887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118529433004585947395291849 88897074753439460546468887)
      ·
        refine ⟨133345612130159190819703331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88897074753439460546468887 133345612130159190819703331)
        ·
          refine ⟨200018418195238786229554997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133345612130159190819703331 200018418195238786229554997)
          ·
            refine ⟨18751726705803636209020781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 200018418195238786229554997 18751726705803636209020781)
            ·
              refine ⟨7031897514676363578382793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18751726705803636209020781 7031897514676363578382793)
              ·
                refine ⟨5273923136007272683787095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7031897514676363578382793 5273923136007272683787095)
                ·
                  refine ⟨7910884704010909025680643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5273923136007272683787095 7910884704010909025680643)
                  ·
                    refine ⟨11866327056016363538520965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7910884704010909025680643 11866327056016363538520965)
                    ·
                      refine ⟨2224936323003068163472681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11866327056016363538520965 2224936323003068163472681)
                      ·
                        rfl

theorem cell23_4333048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 1, 1, 4].length) (baseStart_4333048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333048 prefixEnd_4333048 := by exact prefixLift 4333048
  have htrace : WordTrace (prefixWord ++ tailWord_4333048) baseStart_4333048 baseEnd_4333048 := by
    simpa [prefixWord, tailWord_4333048, baseEnd_4333048] using wordTrace_append hprefix tailTrace_4333048
  have hstable : (prefixWord ++ tailWord_4333048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333048).length < 2 ^ (prefixWord ++ tailWord_4333048).sum := by decide
  have hdescent : baseEnd_4333048 < baseStart_4333048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333051 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 3]
def baseStart_4333051 : Nat := 118140960795 + 4333051 * 2 ^ 59
def prefixEnd_4333051 : Nat := 4983230072969 + 3 ^ 40 * 4333051 * 2
def baseEnd_4333051 : Nat := 2224937863445031651735167

theorem tailTrace_4333051 : CollatzResearch.WordTrace tailWord_4333051 prefixEnd_4333051 2224937863445031651735167 := by
  unfold tailWord_4333051
  simp only [CollatzResearch.WordTrace]
  refine ⟨158039353425103728039415007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105359568950069152026276671 158039353425103728039415007)
  ·
    refine ⟨237059030137655592059122511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158039353425103728039415007 237059030137655592059122511)
    ·
      refine ⟨355588545206483388088683767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237059030137655592059122511 355588545206483388088683767)
      ·
        refine ⟨533382817809725082133025651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355588545206483388088683767 533382817809725082133025651)
        ·
          refine ⟨800074226714587623199538477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533382817809725082133025651 800074226714587623199538477)
          ·
            refine ⟨300027835017970358699826929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 800074226714587623199538477 300027835017970358699826929)
            ·
              refine ⟨225020876263477769024870197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300027835017970358699826929 225020876263477769024870197)
              ·
                refine ⟨21095707149701040846081581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 225020876263477769024870197 21095707149701040846081581)
                ·
                  refine ⟨7910890181137890317280593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21095707149701040846081581 7910890181137890317280593)
                  ·
                    refine ⟨5933167635853417737960445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7910890181137890317280593 5933167635853417737960445)
                    ·
                      refine ⟨2224937863445031651735167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5933167635853417737960445 2224937863445031651735167)
                      ·
                        rfl

theorem cell23_4333051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 3].length) (baseStart_4333051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333051 prefixEnd_4333051 := by exact prefixLift 4333051
  have htrace : WordTrace (prefixWord ++ tailWord_4333051) baseStart_4333051 baseEnd_4333051 := by
    simpa [prefixWord, tailWord_4333051, baseEnd_4333051] using wordTrace_append hprefix tailTrace_4333051
  have hstable : (prefixWord ++ tailWord_4333051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333051).length < 2 ^ (prefixWord ++ tailWord_4333051).sum := by decide
  have hdescent : baseEnd_4333051 < baseStart_4333051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333058 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_4333058 : Nat := 118140960795 + 4333058 * 2 ^ 59
def prefixEnd_4333058 : Nat := 4983230072969 + 3 ^ 40 * 4333058 * 2
def baseEnd_4333058 : Nat := 741647152603204374782545

theorem tailTrace_4333058 : CollatzResearch.WordTrace tailWord_4333058 prefixEnd_4333058 741647152603204374782545 := by
  unfold tailWord_4333058
  simp only [CollatzResearch.WordTrace]
  refine ⟨39509902184019592058729957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105359739157385578823279885 39509902184019592058729957)
  ·
    refine ⟨7408106659503673511011867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39509902184019592058729957 7408106659503673511011867)
    ·
      refine ⟨11112159989255510266517801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7408106659503673511011867 11112159989255510266517801)
      ·
        refine ⟨8334119991941632699888351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11112159989255510266517801 8334119991941632699888351)
        ·
          refine ⟨12501179987912449049832527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8334119991941632699888351 12501179987912449049832527)
          ·
            refine ⟨18751769981868673574748791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12501179987912449049832527 18751769981868673574748791)
            ·
              refine ⟨28127654972803010362123187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18751769981868673574748791 28127654972803010362123187)
              ·
                refine ⟨42191482459204515543184781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28127654972803010362123187 42191482459204515543184781)
                ·
                  refine ⟨15821805922201693328694293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42191482459204515543184781 15821805922201693328694293)
                  ·
                    refine ⟨741647152603204374782545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15821805922201693328694293 741647152603204374782545)
                    ·
                      rfl

theorem cell23_4333058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_4333058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333058 prefixEnd_4333058 := by exact prefixLift 4333058
  have htrace : WordTrace (prefixWord ++ tailWord_4333058) baseStart_4333058 baseEnd_4333058 := by
    simpa [prefixWord, tailWord_4333058, baseEnd_4333058] using wordTrace_append hprefix tailTrace_4333058
  have hstable : (prefixWord ++ tailWord_4333058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333058).length < 2 ^ (prefixWord ++ tailWord_4333058).sum := by decide
  have hdescent : baseEnd_4333058 < baseStart_4333058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333088 : List Nat := [2, 1, 1, 6, 1, 3, 1, 8]
def baseStart_4333088 : Nat := 118140960795 + 4333088 * 2 ^ 59
def prefixEnd_4333088 : Nat := 4983230072969 + 3 ^ 40 * 4333088 * 2
def baseEnd_4333088 : Nat := 82405809712194370628611

theorem tailTrace_4333088 : CollatzResearch.WordTrace tailWord_4333088 prefixEnd_4333088 82405809712194370628611 := by
  unfold tailWord_4333088
  simp only [CollatzResearch.WordTrace]
  refine ⟨79020351462984841679255959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105360468617313122239007945 79020351462984841679255959)
  ·
    refine ⟨118530527194477262518883939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79020351462984841679255959 118530527194477262518883939)
    ·
      refine ⟨177795790791715893778325909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118530527194477262518883939 177795790791715893778325909)
      ·
        refine ⟨8334177693361682520859027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 177795790791715893778325909 8334177693361682520859027)
        ·
          refine ⟨12501266540042523781288541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8334177693361682520859027 12501266540042523781288541)
          ·
            refine ⟨4687974952515946417983203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12501266540042523781288541 4687974952515946417983203)
            ·
              refine ⟨7031962428773919626974805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4687974952515946417983203 7031962428773919626974805)
              ·
                refine ⟨82405809712194370628611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7031962428773919626974805 82405809712194370628611)
                ·
                  rfl

theorem cell23_4333088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 8].length) (baseStart_4333088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333088 prefixEnd_4333088 := by exact prefixLift 4333088
  have htrace : WordTrace (prefixWord ++ tailWord_4333088) baseStart_4333088 baseEnd_4333088 := by
    simpa [prefixWord, tailWord_4333088, baseEnd_4333088] using wordTrace_append hprefix tailTrace_4333088
  have hstable : (prefixWord ++ tailWord_4333088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333088).length < 2 ^ (prefixWord ++ tailWord_4333088).sum := by decide
  have hdescent : baseEnd_4333088 < baseStart_4333088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333125 : List Nat := [1, 3, 1, 1, 1, 4, 3, 3, 1, 3, 2]
def baseStart_4333125 : Nat := 118140960795 + 4333125 * 2 ^ 59
def prefixEnd_4333125 : Nat := 4983230072969 + 3 ^ 40 * 4333125 * 2
def baseEnd_4333125 : Nat := 2224975861013464362209827

theorem tailTrace_4333125 : CollatzResearch.WordTrace tailWord_4333125 prefixEnd_4333125 2224975861013464362209827 := by
  unfold tailWord_4333125
  simp only [CollatzResearch.WordTrace]
  refine ⟨158042052426835638677608829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105361368284557092451739219 158042052426835638677608829)
  ·
    refine ⟨59265769660063364504103311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158042052426835638677608829 59265769660063364504103311)
    ·
      refine ⟨88898654490095046756154967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59265769660063364504103311 88898654490095046756154967)
      ·
        refine ⟨133347981735142570134232451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88898654490095046756154967 133347981735142570134232451)
        ·
          refine ⟨200021972602713855201348677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133347981735142570134232451 200021972602713855201348677)
          ·
            refine ⟨37504119863008847850252877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 200021972602713855201348677 37504119863008847850252877)
            ·
              refine ⟨14064044948628317943844829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37504119863008847850252877 14064044948628317943844829)
              ·
                refine ⟨5274016855735619228941811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14064044948628317943844829 5274016855735619228941811)
                ·
                  refine ⟨7911025283603428843412717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5274016855735619228941811 7911025283603428843412717)
                  ·
                    refine ⟨2966634481351285816279769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7911025283603428843412717 2966634481351285816279769)
                    ·
                      refine ⟨2224975861013464362209827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2966634481351285816279769 2224975861013464362209827)
                      ·
                        rfl

theorem cell23_4333125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 3, 2].length) (baseStart_4333125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333125 prefixEnd_4333125 := by exact prefixLift 4333125
  have htrace : WordTrace (prefixWord ++ tailWord_4333125) baseStart_4333125 baseEnd_4333125 := by
    simpa [prefixWord, tailWord_4333125, baseEnd_4333125] using wordTrace_append hprefix tailTrace_4333125
  have hstable : (prefixWord ++ tailWord_4333125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333125).length < 2 ^ (prefixWord ++ tailWord_4333125).sum := by decide
  have hdescent : baseEnd_4333125 < baseStart_4333125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333126 : List Nat := [6, 1, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_4333126 : Nat := 118140960795 + 4333126 * 2 ^ 59
def prefixEnd_4333126 : Nat := 4983230072969 + 3 ^ 40 * 4333126 * 2
def baseEnd_4333126 : Nat := 741658791498039619432441

theorem tailTrace_4333126 : CollatzResearch.WordTrace tailWord_4333126 prefixEnd_4333126 741658791498039619432441 := by
  unfold tailWord_4333126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4938815278119750495262351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 105361392599888010565596821 4938815278119750495262351)
  ·
    refine ⟨7408222917179625742893527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4938815278119750495262351 7408222917179625742893527)
    ·
      refine ⟨11112334375769438614340291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7408222917179625742893527 11112334375769438614340291)
      ·
        refine ⟨16668501563654157921510437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11112334375769438614340291 16668501563654157921510437)
        ·
          refine ⟨3125344043185154610283207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16668501563654157921510437 3125344043185154610283207)
          ·
            refine ⟨4688016064777731915424811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3125344043185154610283207 4688016064777731915424811)
            ·
              refine ⟨7032024097166597873137217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4688016064777731915424811 7032024097166597873137217)
              ·
                refine ⟨5274018072874948404852913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7032024097166597873137217 5274018072874948404852913)
                ·
                  refine ⟨3955513554656211303639685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5274018072874948404852913 3955513554656211303639685)
                  ·
                    refine ⟨741658791498039619432441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3955513554656211303639685 741658791498039619432441)
                    ·
                      rfl

theorem cell23_4333126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_4333126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333126 prefixEnd_4333126 := by exact prefixLift 4333126
  have htrace : WordTrace (prefixWord ++ tailWord_4333126) baseStart_4333126 baseEnd_4333126 := by
    simpa [prefixWord, tailWord_4333126, baseEnd_4333126] using wordTrace_append hprefix tailTrace_4333126
  have hstable : (prefixWord ++ tailWord_4333126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333126).length < 2 ^ (prefixWord ++ tailWord_4333126).sum := by decide
  have hdescent : baseEnd_4333126 < baseStart_4333126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333132 : List Nat := [2, 2, 1, 3, 1, 5, 1, 2, 2, 1, 3]
def baseStart_4333132 : Nat := 118140960795 + 4333132 * 2 ^ 59
def prefixEnd_4333132 : Nat := 4983230072969 + 3 ^ 40 * 4333132 * 2
def baseEnd_4333132 : Nat := 2224979455378045834822295

theorem tailTrace_4333132 : CollatzResearch.WordTrace tailWord_4333132 prefixEnd_4333132 2224979455378045834822295 := by
  unfold tailWord_4333132
  simp only [CollatzResearch.WordTrace]
  refine ⟨79021153868905139436556825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105361538491873519248742433 79021153868905139436556825)
  ·
    refine ⟨59265865401678854577417619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79021153868905139436556825 59265865401678854577417619)
    ·
      refine ⟨88898798102518281866126429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59265865401678854577417619 88898798102518281866126429)
      ·
        refine ⟨33337049288444355699797411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88898798102518281866126429 33337049288444355699797411)
        ·
          refine ⟨50005573932666533549696117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33337049288444355699797411 50005573932666533549696117)
          ·
            refine ⟨4688022556187487520284011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50005573932666533549696117 4688022556187487520284011)
            ·
              refine ⟨7032033834281231280426017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4688022556187487520284011 7032033834281231280426017)
              ·
                refine ⟨5274025375710923460319513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7032033834281231280426017 5274025375710923460319513)
                ·
                  refine ⟨3955519031783192595239635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5274025375710923460319513 3955519031783192595239635)
                  ·
                    refine ⟨5933278547674788892859453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3955519031783192595239635 5933278547674788892859453)
                    ·
                      refine ⟨2224979455378045834822295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5933278547674788892859453 2224979455378045834822295)
                      ·
                        rfl

theorem cell23_4333132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_4333132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333132 prefixEnd_4333132 := by exact prefixLift 4333132
  have htrace : WordTrace (prefixWord ++ tailWord_4333132) baseStart_4333132 baseEnd_4333132 := by
    simpa [prefixWord, tailWord_4333132, baseEnd_4333132] using wordTrace_append hprefix tailTrace_4333132
  have hstable : (prefixWord ++ tailWord_4333132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333132).length < 2 ^ (prefixWord ++ tailWord_4333132).sum := by decide
  have hdescent : baseEnd_4333132 < baseStart_4333132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333141 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_4333141 : Nat := 118140960795 + 4333141 * 2 ^ 59
def prefixEnd_4333141 : Nat := 4983230072969 + 3 ^ 40 * 4333141 * 2
def baseEnd_4333141 : Nat := 2224984076703936299609753

theorem tailTrace_4333141 : CollatzResearch.WordTrace tailWord_4333141 prefixEnd_4333141 2224984076703936299609753 := by
  unfold tailWord_4333141
  simp only [CollatzResearch.WordTrace]
  refine ⟨158042635994777673410191277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105361757329851782273460851 158042635994777673410191277)
  ·
    refine ⟨59265988498041627528821729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158042635994777673410191277 59265988498041627528821729)
    ·
      refine ⟨44449491373531220646616297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59265988498041627528821729 44449491373531220646616297)
      ·
        refine ⟨33337118530148415484962223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44449491373531220646616297 33337118530148415484962223)
        ·
          refine ⟨50005677795222623227443335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33337118530148415484962223 50005677795222623227443335)
          ·
            refine ⟨75008516692833934841165003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50005677795222623227443335 75008516692833934841165003)
            ·
              refine ⟨112512775039250902261747505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75008516692833934841165003 112512775039250902261747505)
              ·
                refine ⟨84384581279438176696310629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112512775039250902261747505 84384581279438176696310629)
                ·
                  refine ⟨15822108989894658130558243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84384581279438176696310629 15822108989894658130558243)
                  ·
                    refine ⟨23733163484841987195837365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15822108989894658130558243 23733163484841987195837365)
                    ·
                      refine ⟨2224984076703936299609753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23733163484841987195837365 2224984076703936299609753)
                      ·
                        rfl

theorem cell23_4333141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_4333141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333141 prefixEnd_4333141 := by exact prefixLift 4333141
  have htrace : WordTrace (prefixWord ++ tailWord_4333141) baseStart_4333141 baseEnd_4333141 := by
    simpa [prefixWord, tailWord_4333141, baseEnd_4333141] using wordTrace_append hprefix tailTrace_4333141
  have hstable : (prefixWord ++ tailWord_4333141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333141).length < 2 ^ (prefixWord ++ tailWord_4333141).sum := by decide
  have hdescent : baseEnd_4333141 < baseStart_4333141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333148 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 2, 6]
def baseStart_4333148 : Nat := 118140960795 + 4333148 * 2 ^ 59
def prefixEnd_4333148 : Nat := 4983230072969 + 3 ^ 40 * 4333148 * 2
def baseEnd_4333148 : Nat := 741662557022839257407407

theorem tailTrace_4333148 : CollatzResearch.WordTrace tailWord_4333148 prefixEnd_4333148 741662557022839257407407 := by
  unfold tailWord_4333148
  simp only [CollatzResearch.WordTrace]
  refine ⟨79021445652876156802848049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105361927537168209070464065 79021445652876156802848049)
  ·
    refine ⟨59266084239657117602136037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79021445652876156802848049 59266084239657117602136037)
    ·
      refine ⟨11112390794935709550400507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59266084239657117602136037 11112390794935709550400507)
      ·
        refine ⟨16668586192403564325600761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11112390794935709550400507 16668586192403564325600761)
        ·
          refine ⟨12501439644302673244200571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16668586192403564325600761 12501439644302673244200571)
          ·
            refine ⟨18752159466454009866300857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12501439644302673244200571 18752159466454009866300857)
            ·
              refine ⟨14064119599840507399725643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18752159466454009866300857 14064119599840507399725643)
              ·
                refine ⟨21096179399760761099588465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14064119599840507399725643 21096179399760761099588465)
                ·
                  refine ⟨15822134549820570824691349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21096179399760761099588465 15822134549820570824691349)
                  ·
                    refine ⟨741662557022839257407407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15822134549820570824691349 741662557022839257407407)
                    ·
                      rfl

theorem cell23_4333148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_4333148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333148 prefixEnd_4333148 := by exact prefixLift 4333148
  have htrace : WordTrace (prefixWord ++ tailWord_4333148) baseStart_4333148 baseEnd_4333148 := by
    simpa [prefixWord, tailWord_4333148, baseEnd_4333148] using wordTrace_append hprefix tailTrace_4333148
  have hstable : (prefixWord ++ tailWord_4333148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333148).length < 2 ^ (prefixWord ++ tailWord_4333148).sum := by decide
  have hdescent : baseEnd_4333148 < baseStart_4333148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333149 : List Nat := [1, 4, 4, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_4333149 : Nat := 118140960795 + 4333149 * 2 ^ 59
def prefixEnd_4333149 : Nat := 4983230072969 + 3 ^ 40 * 4333149 * 2
def baseEnd_4333149 : Nat := 2224988184549172268309717

theorem tailTrace_4333149 : CollatzResearch.WordTrace tailWord_4333149 prefixEnd_4333149 2224988184549172268309717 := by
  unfold tailWord_4333149
  simp only [CollatzResearch.WordTrace]
  refine ⟨158042927778748690776482501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105361951852499127184321667 158042927778748690776482501)
  ·
    refine ⟨29633048958515379520590469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158042927778748690776482501 29633048958515379520590469)
    ·
      refine ⟨5556196679721633660110713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29633048958515379520590469 5556196679721633660110713)
      ·
        refine ⟨4167147509791225245083035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5556196679721633660110713 4167147509791225245083035)
        ·
          refine ⟨6250721264686837867624553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4167147509791225245083035 6250721264686837867624553)
          ·
            refine ⟨4688040948515128400718415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6250721264686837867624553 4688040948515128400718415)
            ·
              refine ⟨7032061422772692601077623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4688040948515128400718415 7032061422772692601077623)
              ·
                refine ⟨10548092134159038901616435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7032061422772692601077623 10548092134159038901616435)
                ·
                  refine ⟨15822138201238558352424653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10548092134159038901616435 15822138201238558352424653)
                  ·
                    refine ⟨5933301825464459382159245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15822138201238558352424653 5933301825464459382159245)
                    ·
                      refine ⟨2224988184549172268309717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5933301825464459382159245 2224988184549172268309717)
                      ·
                        rfl

theorem cell23_4333149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_4333149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333149 prefixEnd_4333149 := by exact prefixLift 4333149
  have htrace : WordTrace (prefixWord ++ tailWord_4333149) baseStart_4333149 baseEnd_4333149 := by
    simpa [prefixWord, tailWord_4333149, baseEnd_4333149] using wordTrace_append hprefix tailTrace_4333149
  have hstable : (prefixWord ++ tailWord_4333149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333149).length < 2 ^ (prefixWord ++ tailWord_4333149).sum := by decide
  have hdescent : baseEnd_4333149 < baseStart_4333149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333155 : List Nat := [1, 1, 1, 5, 1, 3, 3, 1, 1, 4, 2]
def baseStart_4333155 : Nat := 118140960795 + 4333155 * 2 ^ 59
def prefixEnd_4333155 : Nat := 4983230072969 + 3 ^ 40 * 4333155 * 2
def baseEnd_4333155 : Nat := 2224991265433099244834689

theorem tailTrace_4333155 : CollatzResearch.WordTrace tailWord_4333155 prefixEnd_4333155 2224991265433099244834689 := by
  unfold tailWord_4333155
  simp only [CollatzResearch.WordTrace]
  refine ⟨158043146616726953801200919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105362097744484635867467279 158043146616726953801200919)
  ·
    refine ⟨237064719925090430701801379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158043146616726953801200919 237064719925090430701801379)
    ·
      refine ⟨355597079887635646052702069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237064719925090430701801379 355597079887635646052702069)
      ·
        refine ⟨33337226239465841817440819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 355597079887635646052702069 33337226239465841817440819)
        ·
          refine ⟨50005839359198762726161229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33337226239465841817440819 50005839359198762726161229)
          ·
            refine ⟨18752189759699536022310461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50005839359198762726161229 18752189759699536022310461)
            ·
              refine ⟨7032071159887326008366423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18752189759699536022310461 7032071159887326008366423)
              ·
                refine ⟨10548106739830989012549635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7032071159887326008366423 10548106739830989012549635)
                ·
                  refine ⟨15822160109746483518824453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10548106739830989012549635 15822160109746483518824453)
                  ·
                    refine ⟨2966655020577465659779585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15822160109746483518824453 2966655020577465659779585)
                    ·
                      refine ⟨2224991265433099244834689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2966655020577465659779585 2224991265433099244834689)
                      ·
                        rfl

theorem cell23_4333155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_4333155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333155 prefixEnd_4333155 := by exact prefixLift 4333155
  have htrace : WordTrace (prefixWord ++ tailWord_4333155) baseStart_4333155 baseEnd_4333155 := by
    simpa [prefixWord, tailWord_4333155, baseEnd_4333155] using wordTrace_append hprefix tailTrace_4333155
  have hstable : (prefixWord ++ tailWord_4333155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333155).length < 2 ^ (prefixWord ++ tailWord_4333155).sum := by decide
  have hdescent : baseEnd_4333155 < baseStart_4333155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333161 : List Nat := [1, 2, 1, 1, 1, 4, 4, 2, 7]
def baseStart_4333161 : Nat := 118140960795 + 4333161 * 2 ^ 59
def prefixEnd_4333161 : Nat := 4983230072969 + 3 ^ 40 * 4333161 * 2
def baseEnd_4333161 : Nat := 247221594035225135706629

theorem tailTrace_4333161 : CollatzResearch.WordTrace tailWord_4333161 prefixEnd_4333161 247221594035225135706629 := by
  unfold tailWord_4333161
  simp only [CollatzResearch.WordTrace]
  refine ⟨158043365454705216825919337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105362243636470144550612891 158043365454705216825919337)
  ·
    refine ⟨118532524091028912619439503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158043365454705216825919337 118532524091028912619439503)
    ·
      refine ⟨177798786136543368929159255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118532524091028912619439503 177798786136543368929159255)
      ·
        refine ⟨266698179204815053393738883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177798786136543368929159255 266698179204815053393738883)
        ·
          refine ⟨400047268807222580090608325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266698179204815053393738883 400047268807222580090608325)
          ·
            refine ⟨75008862901354233766989061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 400047268807222580090608325 75008862901354233766989061)
            ·
              refine ⟨14064161794003918831310449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75008862901354233766989061 14064161794003918831310449)
              ·
                refine ⟨10548121345502939123482837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14064161794003918831310449 10548121345502939123482837)
                ·
                  refine ⟨247221594035225135706629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10548121345502939123482837 247221594035225135706629)
                  ·
                    rfl

theorem cell23_4333161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 7].length) (baseStart_4333161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333161 prefixEnd_4333161 := by exact prefixLift 4333161
  have htrace : WordTrace (prefixWord ++ tailWord_4333161) baseStart_4333161 baseEnd_4333161 := by
    simpa [prefixWord, tailWord_4333161, baseEnd_4333161] using wordTrace_append hprefix tailTrace_4333161
  have hstable : (prefixWord ++ tailWord_4333161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333161).length < 2 ^ (prefixWord ++ tailWord_4333161).sum := by decide
  have hdescent : baseEnd_4333161 < baseStart_4333161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333178 : List Nat := [3, 1, 1, 1, 1, 1, 1, 9, 5]
def baseStart_4333178 : Nat := 118140960795 + 4333178 * 2 ^ 59
def prefixEnd_4333178 : Nat := 4983230072969 + 3 ^ 40 * 4333178 * 2
def baseEnd_4333178 : Nat := 247222563943128072760787

theorem tailTrace_4333178 : CollatzResearch.WordTrace tailWord_4333178 prefixEnd_4333178 247222563943128072760787 := by
  unfold tailWord_4333178
  simp only [CollatzResearch.WordTrace]
  refine ⟨39510996373910907182322047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105362656997095752486192125 39510996373910907182322047)
  ·
    refine ⟨59266494560866360773483071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39510996373910907182322047 59266494560866360773483071)
    ·
      refine ⟨88899741841299541160224607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59266494560866360773483071 88899741841299541160224607)
      ·
        refine ⟨133349612761949311740336911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88899741841299541160224607 133349612761949311740336911)
        ·
          refine ⟨200024419142923967610505367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133349612761949311740336911 200024419142923967610505367)
          ·
            refine ⟨300036628714385951415758051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200024419142923967610505367 300036628714385951415758051)
            ·
              refine ⟨450054943071578927123637077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300036628714385951415758051 450054943071578927123637077)
              ·
                refine ⟨2637040682060032776115061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 450054943071578927123637077 2637040682060032776115061)
                ·
                  refine ⟨247222563943128072760787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2637040682060032776115061 247222563943128072760787)
                  ·
                    rfl

theorem cell23_4333178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 5].length) (baseStart_4333178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333178 prefixEnd_4333178 := by exact prefixLift 4333178
  have htrace : WordTrace (prefixWord ++ tailWord_4333178) baseStart_4333178 baseEnd_4333178 := by
    simpa [prefixWord, tailWord_4333178, baseEnd_4333178] using wordTrace_append hprefix tailTrace_4333178
  have hstable : (prefixWord ++ tailWord_4333178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333178).length < 2 ^ (prefixWord ++ tailWord_4333178).sum := by decide
  have hdescent : baseEnd_4333178 < baseStart_4333178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333195 : List Nat := [1, 1, 1, 1, 4, 1, 7, 2, 5]
def baseStart_4333195 : Nat := 118140960795 + 4333195 * 2 ^ 59
def prefixEnd_4333195 : Nat := 4983230072969 + 3 ^ 40 * 4333195 * 2
def baseEnd_4333195 : Nat := 247223533851031009814945

theorem tailTrace_4333195 : CollatzResearch.WordTrace tailWord_4333195 prefixEnd_4333195 247223533851031009814945 := by
  unfold tailWord_4333195
  simp only [CollatzResearch.WordTrace]
  refine ⟨158044605536582040632657039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105363070357721360421771359 158044605536582040632657039)
  ·
    refine ⟨237066908304873060948985559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158044605536582040632657039 237066908304873060948985559)
    ·
      refine ⟨355600362457309591423478339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237066908304873060948985559 355600362457309591423478339)
      ·
        refine ⟨533400543685964387135217509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355600362457309591423478339 533400543685964387135217509)
        ·
          refine ⟨100012601941118322587853283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 533400543685964387135217509 100012601941118322587853283)
          ·
            refine ⟨150018902911677483881779925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100012601941118322587853283 150018902911677483881779925)
            ·
              refine ⟨3516068036992441028479217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 150018902911677483881779925 3516068036992441028479217)
              ·
                refine ⟨2637051027744330771359413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3516068036992441028479217 2637051027744330771359413)
                ·
                  refine ⟨247223533851031009814945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2637051027744330771359413 247223533851031009814945)
                  ·
                    rfl

theorem cell23_4333195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 5].length) (baseStart_4333195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333195 prefixEnd_4333195 := by exact prefixLift 4333195
  have htrace : WordTrace (prefixWord ++ tailWord_4333195) baseStart_4333195 baseEnd_4333195 := by
    simpa [prefixWord, tailWord_4333195, baseEnd_4333195] using wordTrace_append hprefix tailTrace_4333195
  have hstable : (prefixWord ++ tailWord_4333195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333195).length < 2 ^ (prefixWord ++ tailWord_4333195).sum := by decide
  have hdescent : baseEnd_4333195 < baseStart_4333195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333221 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 2, 8]
def baseStart_4333221 : Nat := 118140960795 + 4333221 * 2 ^ 59
def prefixEnd_4333221 : Nat := 4983230072969 + 3 ^ 40 * 4333221 * 2
def baseEnd_4333221 : Nat := 741675051718765328869795

theorem tailTrace_4333221 : CollatzResearch.WordTrace tailWord_4333221 prefixEnd_4333221 741675051718765328869795 := by
  unfold tailWord_4333221
  simp only [CollatzResearch.WordTrace]
  refine ⟨158045553834487847073103517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105363702556325231382069011 158045553834487847073103517)
  ·
    refine ⟨59267082687932942652413819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158045553834487847073103517 59267082687932942652413819)
    ·
      refine ⟨88900624031899413978620729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59267082687932942652413819 88900624031899413978620729)
      ·
        refine ⟨66675468023924560483965547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88900624031899413978620729 66675468023924560483965547)
        ·
          refine ⟨100013202035886840725948321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66675468023924560483965547 100013202035886840725948321)
          ·
            refine ⟨75009901526915130544461241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100013202035886840725948321 75009901526915130544461241)
            ·
              refine ⟨56257426145186347908345931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75009901526915130544461241 56257426145186347908345931)
              ·
                refine ⟨84386139217779521862518897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56257426145186347908345931 84386139217779521862518897)
                ·
                  refine ⟨63289604413334641396889173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84386139217779521862518897 63289604413334641396889173)
                  ·
                    refine ⟨741675051718765328869795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63289604413334641396889173 741675051718765328869795)
                    ·
                      rfl

theorem cell23_4333221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_4333221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333221 prefixEnd_4333221 := by exact prefixLift 4333221
  have htrace : WordTrace (prefixWord ++ tailWord_4333221) baseStart_4333221 baseEnd_4333221 := by
    simpa [prefixWord, tailWord_4333221, baseEnd_4333221] using wordTrace_append hprefix tailTrace_4333221
  have hstable : (prefixWord ++ tailWord_4333221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333221).length < 2 ^ (prefixWord ++ tailWord_4333221).sum := by decide
  have hdescent : baseEnd_4333221 < baseStart_4333221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333245 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 2, 4, 2]
def baseStart_4333245 : Nat := 118140960795 + 4333245 * 2 ^ 59
def prefixEnd_4333245 : Nat := 4983230072969 + 3 ^ 40 * 4333245 * 2
def baseEnd_4333245 : Nat := 2225037478692003892709275

theorem tailTrace_4333245 : CollatzResearch.WordTrace tailWord_4333245 prefixEnd_4333245 2225037478692003892709275 := by
  unfold tailWord_4333245
  simp only [CollatzResearch.WordTrace]
  refine ⟨158046429186400899171977189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105364286124267266114651459 158046429186400899171977189)
  ·
    refine ⟨29633705472450168594745723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158046429186400899171977189 29633705472450168594745723)
    ·
      refine ⟨44450558208675252892118585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29633705472450168594745723 44450558208675252892118585)
      ·
        refine ⟨33337918656506439669088939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44450558208675252892118585 33337918656506439669088939)
        ·
          refine ⟨50006877984759659503633409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33337918656506439669088939 50006877984759659503633409)
          ·
            refine ⟨37505158488569744627725057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50006877984759659503633409 37505158488569744627725057)
            ·
              refine ⟨28128868866427308470793793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37505158488569744627725057 28128868866427308470793793)
              ·
                refine ⟨21096651649820481353095345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28128868866427308470793793 21096651649820481353095345)
                ·
                  refine ⟨15822488737365361014821509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21096651649820481353095345 15822488737365361014821509)
                  ·
                    refine ⟨2966716638256005190279033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15822488737365361014821509 2966716638256005190279033)
                    ·
                      refine ⟨2225037478692003892709275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2966716638256005190279033 2225037478692003892709275)
                      ·
                        rfl

theorem cell23_4333245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_4333245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333245 prefixEnd_4333245 := by exact prefixLift 4333245
  have htrace : WordTrace (prefixWord ++ tailWord_4333245) baseStart_4333245 baseEnd_4333245 := by
    simpa [prefixWord, tailWord_4333245, baseEnd_4333245] using wordTrace_append hprefix tailTrace_4333245
  have hstable : (prefixWord ++ tailWord_4333245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333245).length < 2 ^ (prefixWord ++ tailWord_4333245).sum := by decide
  have hdescent : baseEnd_4333245 < baseStart_4333245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333295 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 5, 1, 3]
def baseStart_4333295 : Nat := 118140960795 + 4333295 * 2 ^ 59
def prefixEnd_4333295 : Nat := 4983230072969 + 3 ^ 40 * 4333295 * 2
def baseEnd_4333295 : Nat := 2225063152724728697084045

theorem tailTrace_4333295 : CollatzResearch.WordTrace tailWord_4333295 prefixEnd_4333295 2225063152724728697084045 := by
  unfold tailWord_4333295
  simp only [CollatzResearch.WordTrace]
  refine ⟨158048252836219757711297339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105365501890813171807531559 158048252836219757711297339)
  ·
    refine ⟨237072379254329636566946009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158048252836219757711297339 237072379254329636566946009)
    ·
      refine ⟨177804284440747227425209507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237072379254329636566946009 177804284440747227425209507)
      ·
        refine ⟨266706426661120841137814261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177804284440747227425209507 266706426661120841137814261)
        ·
          refine ⟨25003727499480078856670087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 266706426661120841137814261 25003727499480078856670087)
          ·
            refine ⟨37505591249220118285005131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25003727499480078856670087 37505591249220118285005131)
            ·
              refine ⟨56258386873830177427507697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37505591249220118285005131 56258386873830177427507697)
              ·
                refine ⟨42193790155372633070630773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56258386873830177427507697 42193790155372633070630773)
                ·
                  refine ⟨3955667827066184350371635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42193790155372633070630773 3955667827066184350371635)
                  ·
                    refine ⟨5933501740599276525557453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3955667827066184350371635 5933501740599276525557453)
                    ·
                      refine ⟨2225063152724728697084045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5933501740599276525557453 2225063152724728697084045)
                      ·
                        rfl

theorem cell23_4333295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 1, 3].length) (baseStart_4333295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333295 prefixEnd_4333295 := by exact prefixLift 4333295
  have htrace : WordTrace (prefixWord ++ tailWord_4333295) baseStart_4333295 baseEnd_4333295 := by
    simpa [prefixWord, tailWord_4333295, baseEnd_4333295] using wordTrace_append hprefix tailTrace_4333295
  have hstable : (prefixWord ++ tailWord_4333295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333295).length < 2 ^ (prefixWord ++ tailWord_4333295).sum := by decide
  have hdescent : baseEnd_4333295 < baseStart_4333295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333302 : List Nat := [5, 1, 1, 1, 1, 5, 1, 2, 6]
def baseStart_4333302 : Nat := 118140960795 + 4333302 * 2 ^ 59
def prefixEnd_4333302 : Nat := 4983230072969 + 3 ^ 40 * 4333302 * 2
def baseEnd_4333302 : Nat := 247229638565478907744057

theorem tailTrace_4333302 : CollatzResearch.WordTrace tailWord_4333302 prefixEnd_4333302 247229638565478907744057 := by
  unfold tailWord_4333302
  simp only [CollatzResearch.WordTrace]
  refine ⟨9878031759199649869175135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105365672098129598604534773 9878031759199649869175135)
  ·
    refine ⟨14817047638799474803762703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9878031759199649869175135 14817047638799474803762703)
    ·
      refine ⟨22225571458199212205644055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14817047638799474803762703 22225571458199212205644055)
      ·
        refine ⟨33338357187298818308466083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22225571458199212205644055 33338357187298818308466083)
        ·
          refine ⟨50007535780948227462699125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33338357187298818308466083 50007535780948227462699125)
          ·
            refine ⟨4688206479463896324628043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50007535780948227462699125 4688206479463896324628043)
            ·
              refine ⟨7032309719195844486942065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4688206479463896324628043 7032309719195844486942065)
              ·
                refine ⟨5274232289396883365206549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7032309719195844486942065 5274232289396883365206549)
                ·
                  refine ⟨247229638565478907744057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5274232289396883365206549 247229638565478907744057)
                  ·
                    rfl

theorem cell23_4333302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_4333302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333302 prefixEnd_4333302 := by exact prefixLift 4333302
  have htrace : WordTrace (prefixWord ++ tailWord_4333302) baseStart_4333302 baseEnd_4333302 := by
    simpa [prefixWord, tailWord_4333302, baseEnd_4333302] using wordTrace_append hprefix tailTrace_4333302
  have hstable : (prefixWord ++ tailWord_4333302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333302).length < 2 ^ (prefixWord ++ tailWord_4333302).sum := by decide
  have hdescent : baseEnd_4333302 < baseStart_4333302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333345 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 4, 4]
def baseStart_4333345 : Nat := 118140960795 + 4333345 * 2 ^ 59
def prefixEnd_4333345 : Nat := 4983230072969 + 3 ^ 40 * 4333345 * 2
def baseEnd_4333345 : Nat := 741696275585817833819605

theorem tailTrace_4333345 : CollatzResearch.WordTrace tailWord_4333345 prefixEnd_4333345 741696275585817833819605 := by
  unfold tailWord_4333345
  simp only [CollatzResearch.WordTrace]
  refine ⟨158050076486038616250617489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105366717657359077500411659 158050076486038616250617489)
  ·
    refine ⟨118537557364528962187963117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158050076486038616250617489 118537557364528962187963117)
    ·
      refine ⟨44451584011698360820486169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118537557364528962187963117 44451584011698360820486169)
      ·
        refine ⟨33338688008773770615364627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44451584011698360820486169 33338688008773770615364627)
        ·
          refine ⟨50008032013160655923046941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33338688008773770615364627 50008032013160655923046941)
          ·
            refine ⟨18753012004935245971142603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50008032013160655923046941 18753012004935245971142603)
            ·
              refine ⟨28129518007402868956713905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18753012004935245971142603 28129518007402868956713905)
              ·
                refine ⟨21097138505552151717535429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28129518007402868956713905 21097138505552151717535429)
                ·
                  refine ⟨3955713469791028447037893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21097138505552151717535429 3955713469791028447037893)
                  ·
                    refine ⟨741696275585817833819605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3955713469791028447037893 741696275585817833819605)
                    ·
                      rfl

theorem cell23_4333345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_4333345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333345 prefixEnd_4333345 := by exact prefixLift 4333345
  have htrace : WordTrace (prefixWord ++ tailWord_4333345) baseStart_4333345 baseEnd_4333345 := by
    simpa [prefixWord, tailWord_4333345, baseEnd_4333345] using wordTrace_append hprefix tailTrace_4333345
  have hstable : (prefixWord ++ tailWord_4333345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333345).length < 2 ^ (prefixWord ++ tailWord_4333345).sum := by decide
  have hdescent : baseEnd_4333345 < baseStart_4333345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333352 : List Nat := [2, 1, 5, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_4333352 : Nat := 118140960795 + 4333352 * 2 ^ 59
def prefixEnd_4333352 : Nat := 4983230072969 + 3 ^ 40 * 4333352 * 2
def baseEnd_4333352 : Nat := 2225092421122034974071283

theorem tailTrace_4333352 : CollatzResearch.WordTrace tailWord_4333352 prefixEnd_4333352 2225092421122034974071283 := by
  unfold tailWord_4333352
  simp only [CollatzResearch.WordTrace]
  refine ⟨79025165898506628223061155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105366887864675504297414873 79025165898506628223061155)
  ·
    refine ⟨118537748847759942334591733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79025165898506628223061155 118537748847759942334591733)
    ·
      refine ⟨11112913954477494593867975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118537748847759942334591733 11112913954477494593867975)
      ·
        refine ⟨16669370931716241890801963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11112913954477494593867975 16669370931716241890801963)
        ·
          refine ⟨25004056397574362836202945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16669370931716241890801963 25004056397574362836202945)
          ·
            refine ⟨18753042298180772127152209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25004056397574362836202945 18753042298180772127152209)
            ·
              refine ⟨14064781723635579095364157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18753042298180772127152209 14064781723635579095364157)
              ·
                refine ⟨5274293146363342160761559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14064781723635579095364157 5274293146363342160761559)
                ·
                  refine ⟨7911439719545013241142339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5274293146363342160761559 7911439719545013241142339)
                  ·
                    refine ⟨11867159579317519861713509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7911439719545013241142339 11867159579317519861713509)
                    ·
                      refine ⟨2225092421122034974071283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11867159579317519861713509 2225092421122034974071283)
                      ·
                        rfl

theorem cell23_4333352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_4333352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333352 prefixEnd_4333352 := by exact prefixLift 4333352
  have htrace : WordTrace (prefixWord ++ tailWord_4333352) baseStart_4333352 baseEnd_4333352 := by
    simpa [prefixWord, tailWord_4333352, baseEnd_4333352] using wordTrace_append hprefix tailTrace_4333352
  have hstable : (prefixWord ++ tailWord_4333352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333352).length < 2 ^ (prefixWord ++ tailWord_4333352).sum := by decide
  have hdescent : baseEnd_4333352 < baseStart_4333352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333375 : List Nat := [1, 1, 2, 2, 6, 1, 2, 8]
def baseStart_4333375 : Nat := 118140960795 + 4333375 * 2 ^ 59
def prefixEnd_4333375 : Nat := 4983230072969 + 3 ^ 40 * 4333375 * 2
def baseEnd_4333375 : Nat := 82411267821373643854951

theorem tailTrace_4333375 : CollatzResearch.WordTrace tailWord_4333375 prefixEnd_4333375 82411267821373643854951 := by
  unfold tailWord_4333375
  simp only [CollatzResearch.WordTrace]
  refine ⟨158051170675929931374209579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105367447117286620916139719 158051170675929931374209579)
  ·
    refine ⟨237076756013894897061314369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158051170675929931374209579 237076756013894897061314369)
    ·
      refine ⟨177807567010421172795985777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237076756013894897061314369 177807567010421172795985777)
      ·
        refine ⟨133355675257815879596989333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177807567010421172795985777 133355675257815879596989333)
        ·
          refine ⟨6251047277710119356108875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 133355675257815879596989333 6251047277710119356108875)
          ·
            refine ⟨9376570916565179034163313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6251047277710119356108875 9376570916565179034163313)
            ·
              refine ⟨7032428187423884275622485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9376570916565179034163313 7032428187423884275622485)
              ·
                refine ⟨82411267821373643854951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7032428187423884275622485 82411267821373643854951)
                ·
                  rfl

theorem cell23_4333375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 8].length) (baseStart_4333375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333375 prefixEnd_4333375 := by exact prefixLift 4333375
  have htrace : WordTrace (prefixWord ++ tailWord_4333375) baseStart_4333375 baseEnd_4333375 := by
    simpa [prefixWord, tailWord_4333375, baseEnd_4333375] using wordTrace_append hprefix tailTrace_4333375
  have hstable : (prefixWord ++ tailWord_4333375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333375).length < 2 ^ (prefixWord ++ tailWord_4333375).sum := by decide
  have hdescent : baseEnd_4333375 < baseStart_4333375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333379 : List Nat := [1, 1, 1, 3, 1, 7, 2, 1, 2, 4]
def baseStart_4333379 : Nat := 118140960795 + 4333379 * 2 ^ 59
def prefixEnd_4333379 : Nat := 4983230072969 + 3 ^ 40 * 4333379 * 2
def baseEnd_4333379 : Nat := 741702095033235456144553

theorem tailTrace_4333379 : CollatzResearch.WordTrace tailWord_4333379 prefixEnd_4333379 741702095033235456144553 := by
  unfold tailWord_4333379
  simp only [CollatzResearch.WordTrace]
  refine ⟨158051316567915440057355191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105367544378610293371570127 158051316567915440057355191)
  ·
    refine ⟨237076974851873160086032787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158051316567915440057355191 237076974851873160086032787)
    ·
      refine ⟨355615462277809740129049181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237076974851873160086032787 355615462277809740129049181)
      ·
        refine ⟨133355798354178652548393443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 355615462277809740129049181 133355798354178652548393443)
        ·
          refine ⟨200033697531267978822590165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133355798354178652548393443 200033697531267978822590165)
          ·
            refine ⟨4688289785889093253654457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 200033697531267978822590165 4688289785889093253654457)
            ·
              refine ⟨3516217339416819940240843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4688289785889093253654457 3516217339416819940240843)
              ·
                refine ⟨5274326009125229910361265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3516217339416819940240843 5274326009125229910361265)
                ·
                  refine ⟨3955744506843922432770949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5274326009125229910361265 3955744506843922432770949)
                  ·
                    refine ⟨741702095033235456144553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3955744506843922432770949 741702095033235456144553)
                    ·
                      rfl

theorem cell23_4333379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 2, 4].length) (baseStart_4333379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333379 prefixEnd_4333379 := by exact prefixLift 4333379
  have htrace : WordTrace (prefixWord ++ tailWord_4333379) baseStart_4333379 baseEnd_4333379 := by
    simpa [prefixWord, tailWord_4333379, baseEnd_4333379] using wordTrace_append hprefix tailTrace_4333379
  have hstable : (prefixWord ++ tailWord_4333379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333379).length < 2 ^ (prefixWord ++ tailWord_4333379).sum := by decide
  have hdescent : baseEnd_4333379 < baseStart_4333379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333385 : List Nat := [1, 2, 1, 1, 2, 4, 2, 3, 1, 3, 3]
def baseStart_4333385 : Nat := 118140960795 + 4333385 * 2 ^ 59
def prefixEnd_4333385 : Nat := 4983230072969 + 3 ^ 40 * 4333385 * 2
def baseEnd_4333385 : Nat := 2225109365983633344958631

theorem tailTrace_4333385 : CollatzResearch.WordTrace tailWord_4333385 prefixEnd_4333385 2225109365983633344958631 := by
  unfold tailWord_4333385
  simp only [CollatzResearch.WordTrace]
  refine ⟨158051535405893703082073609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105367690270595802054715739 158051535405893703082073609)
  ·
    refine ⟨118538651554420277311555207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158051535405893703082073609 118538651554420277311555207)
    ·
      refine ⟨177807977331630415967332811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118538651554420277311555207 177807977331630415967332811)
      ·
        refine ⟨266711965997445623950999217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177807977331630415967332811 266711965997445623950999217)
        ·
          refine ⟨200033974498084217963249413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266711965997445623950999217 200033974498084217963249413)
          ·
            refine ⟨37506370218390790868109265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 200033974498084217963249413 37506370218390790868109265)
            ·
              refine ⟨28129777663793093151081949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37506370218390790868109265 28129777663793093151081949)
              ·
                refine ⟨10548666623922409931655731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28129777663793093151081949 10548666623922409931655731)
                ·
                  refine ⟨15822999935883614897483597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10548666623922409931655731 15822999935883614897483597)
                  ·
                    refine ⟨5933624975956355586556349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15822999935883614897483597 5933624975956355586556349)
                    ·
                      refine ⟨2225109365983633344958631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5933624975956355586556349 2225109365983633344958631)
                      ·
                        rfl

theorem cell23_4333385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 3, 3].length) (baseStart_4333385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333385 prefixEnd_4333385 := by exact prefixLift 4333385
  have htrace : WordTrace (prefixWord ++ tailWord_4333385) baseStart_4333385 baseEnd_4333385 := by
    simpa [prefixWord, tailWord_4333385, baseEnd_4333385] using wordTrace_append hprefix tailTrace_4333385
  have hstable : (prefixWord ++ tailWord_4333385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333385).length < 2 ^ (prefixWord ++ tailWord_4333385).sum := by decide
  have hdescent : baseEnd_4333385 < baseStart_4333385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333389 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_4333389 : Nat := 118140960795 + 4333389 * 2 ^ 59
def prefixEnd_4333389 : Nat := 4983230072969 + 3 ^ 40 * 4333389 * 2
def baseEnd_4333389 : Nat := 2225111419906251329308613

theorem tailTrace_4333389 : CollatzResearch.WordTrace tailWord_4333389 prefixEnd_4333389 2225111419906251329308613 := by
  unfold tailWord_4333389
  simp only [CollatzResearch.WordTrace]
  refine ⟨158051681297879211765219221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105367787531919474510146147 158051681297879211765219221)
  ·
    refine ⟨7408672560838088051494651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 158051681297879211765219221 7408672560838088051494651)
    ·
      refine ⟨11113008841257132077241977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7408672560838088051494651 11113008841257132077241977)
      ·
        refine ⟨8334756630942849057931483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11113008841257132077241977 8334756630942849057931483)
        ·
          refine ⟨12502134946414273586897225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8334756630942849057931483 12502134946414273586897225)
          ·
            refine ⟨9376601209810705190172919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12502134946414273586897225 9376601209810705190172919)
            ·
              refine ⟨14064901814716057785259379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9376601209810705190172919 14064901814716057785259379)
              ·
                refine ⟨21097352722074086677889069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14064901814716057785259379 21097352722074086677889069)
                ·
                  refine ⟨7911507270777782504208401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21097352722074086677889069 7911507270777782504208401)
                  ·
                    refine ⟨5933630453083336878156301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7911507270777782504208401 5933630453083336878156301)
                    ·
                      refine ⟨2225111419906251329308613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5933630453083336878156301 2225111419906251329308613)
                      ·
                        rfl

theorem cell23_4333389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_4333389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333389 prefixEnd_4333389 := by exact prefixLift 4333389
  have htrace : WordTrace (prefixWord ++ tailWord_4333389) baseStart_4333389 baseEnd_4333389 := by
    simpa [prefixWord, tailWord_4333389, baseEnd_4333389] using wordTrace_append hprefix tailTrace_4333389
  have hstable : (prefixWord ++ tailWord_4333389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333389).length < 2 ^ (prefixWord ++ tailWord_4333389).sum := by decide
  have hdescent : baseEnd_4333389 < baseStart_4333389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333445 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 2, 4, 3]
def baseStart_4333445 : Nat := 118140960795 + 4333445 * 2 ^ 59
def prefixEnd_4333445 : Nat := 4983230072969 + 3 ^ 40 * 4333445 * 2
def baseEnd_4333445 : Nat := 2225140174822903110208355

theorem tailTrace_4333445 : CollatzResearch.WordTrace tailWord_4333445 prefixEnd_4333445 2225140174822903110208355 := by
  unfold tailWord_4333445
  simp only [CollatzResearch.WordTrace]
  refine ⟨158053723785676333329257789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105369149190450888886171859 158053723785676333329257789)
  ·
    refine ⟨59270146419628624998471671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158053723785676333329257789 59270146419628624998471671)
    ·
      refine ⟨88905219629442937497707507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59270146419628624998471671 88905219629442937497707507)
      ·
        refine ⟨133357829444164406246561261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88905219629442937497707507 133357829444164406246561261)
        ·
          refine ⟨50009186041561652342460473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133357829444164406246561261 50009186041561652342460473)
          ·
            refine ⟨37506889531171239256845355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50009186041561652342460473 37506889531171239256845355)
            ·
              refine ⟨56260334296756858885268033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37506889531171239256845355 56260334296756858885268033)
              ·
                refine ⟨42195250722567644163951025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56260334296756858885268033 42195250722567644163951025)
                ·
                  refine ⟨31646438041925733122963269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42195250722567644163951025 31646438041925733122963269)
                  ·
                    refine ⟨5933707132861074960555613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31646438041925733122963269 5933707132861074960555613)
                    ·
                      refine ⟨2225140174822903110208355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5933707132861074960555613 2225140174822903110208355)
                      ·
                        rfl

theorem cell23_4333445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_4333445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333445 prefixEnd_4333445 := by exact prefixLift 4333445
  have htrace : WordTrace (prefixWord ++ tailWord_4333445) baseStart_4333445 baseEnd_4333445 := by
    simpa [prefixWord, tailWord_4333445, baseEnd_4333445] using wordTrace_append hprefix tailTrace_4333445
  have hstable : (prefixWord ++ tailWord_4333445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333445).length < 2 ^ (prefixWord ++ tailWord_4333445).sum := by decide
  have hdescent : baseEnd_4333445 < baseStart_4333445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333470 : List Nat := [4, 3, 1, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_4333470 : Nat := 118140960795 + 4333470 * 2 ^ 59
def prefixEnd_4333470 : Nat := 4983230072969 + 3 ^ 40 * 4333470 * 2
def baseEnd_4333470 : Nat := 2225153011839265512395741

theorem tailTrace_4333470 : CollatzResearch.WordTrace tailWord_4333470 prefixEnd_4333470 2225153011839265512395741 := by
  unfold tailWord_4333470
  simp only [CollatzResearch.WordTrace]
  refine ⟨19756829451323220324864733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105369757073723841732611909 19756829451323220324864733)
  ·
    refine ⟨7408811044246207621824275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19756829451323220324864733 7408811044246207621824275)
    ·
      refine ⟨11113216566369311432736413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7408811044246207621824275 11113216566369311432736413)
      ·
        refine ⟨4167456212388491787276155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11113216566369311432736413 4167456212388491787276155)
        ·
          refine ⟨6251184318582737680914233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4167456212388491787276155 6251184318582737680914233)
          ·
            refine ⟨4688388238937053260685675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6251184318582737680914233 4688388238937053260685675)
            ·
              refine ⟨7032582358405579891028513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4688388238937053260685675 7032582358405579891028513)
              ·
                refine ⟨5274436768804184918271385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7032582358405579891028513 5274436768804184918271385)
                ·
                  refine ⟨3955827576603138688703539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5274436768804184918271385 3955827576603138688703539)
                  ·
                    refine ⟨5933741364904708033055309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3955827576603138688703539 5933741364904708033055309)
                    ·
                      refine ⟨2225153011839265512395741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5933741364904708033055309 2225153011839265512395741)
                      ·
                        rfl

theorem cell23_4333470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_4333470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333470 prefixEnd_4333470 := by exact prefixLift 4333470
  have htrace : WordTrace (prefixWord ++ tailWord_4333470) baseStart_4333470 baseEnd_4333470 := by
    simpa [prefixWord, tailWord_4333470, baseEnd_4333470] using wordTrace_append hprefix tailTrace_4333470
  have hstable : (prefixWord ++ tailWord_4333470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333470).length < 2 ^ (prefixWord ++ tailWord_4333470).sum := by decide
  have hdescent : baseEnd_4333470 < baseStart_4333470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333476 : List Nat := [2, 3, 1, 2, 1, 3, 3, 2, 2, 2, 2]
def baseStart_4333476 : Nat := 118140960795 + 4333476 * 2 ^ 59
def prefixEnd_4333476 : Nat := 4983230072969 + 3 ^ 40 * 4333476 * 2
def baseEnd_4333476 : Nat := 2225156092723192488920713

theorem tailTrace_4333476 : CollatzResearch.WordTrace tailWord_4333476 prefixEnd_4333476 2225156092723192488920713 := by
  unfold tailWord_4333476
  simp only [CollatzResearch.WordTrace]
  refine ⟨79027427224282012811818141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105369902965709350415757521 79027427224282012811818141)
  ·
    refine ⟨29635285209105754804431803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79027427224282012811818141 29635285209105754804431803)
    ·
      refine ⟨44452927813658632206647705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29635285209105754804431803 44452927813658632206647705)
      ·
        refine ⟨33339695860243974154985779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44452927813658632206647705 33339695860243974154985779)
        ·
          refine ⟨50009543790365961232478669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33339695860243974154985779 50009543790365961232478669)
          ·
            refine ⟨18753578921387235462179501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50009543790365961232478669 18753578921387235462179501)
            ·
              refine ⟨7032592095520213298317313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18753578921387235462179501 7032592095520213298317313)
              ·
                refine ⟨5274444071640159973737985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7032592095520213298317313 5274444071640159973737985)
                ·
                  refine ⟨3955833053730119980303489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5274444071640159973737985 3955833053730119980303489)
                  ·
                    refine ⟨2966874790297589985227617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3955833053730119980303489 2966874790297589985227617)
                    ·
                      refine ⟨2225156092723192488920713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2966874790297589985227617 2225156092723192488920713)
                      ·
                        rfl

theorem cell23_4333476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_4333476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333476 prefixEnd_4333476 := by exact prefixLift 4333476
  have htrace : WordTrace (prefixWord ++ tailWord_4333476) baseStart_4333476 baseEnd_4333476 := by
    simpa [prefixWord, tailWord_4333476, baseEnd_4333476] using wordTrace_append hprefix tailTrace_4333476
  have hstable : (prefixWord ++ tailWord_4333476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333476).length < 2 ^ (prefixWord ++ tailWord_4333476).sum := by decide
  have hdescent : baseEnd_4333476 < baseStart_4333476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333493 : List Nat := [1, 3, 3, 2, 1, 3, 3, 1, 2, 2, 2]
def baseStart_4333493 : Nat := 118140960795 + 4333493 * 2 ^ 59
def prefixEnd_4333493 : Nat := 4983230072969 + 3 ^ 40 * 4333493 * 2
def baseEnd_4333493 : Nat := 2225164821894318922408135

theorem tailTrace_4333493 : CollatzResearch.WordTrace tailWord_4333493 prefixEnd_4333493 2225164821894318922408135 := by
  unfold tailWord_4333493
  simp only [CollatzResearch.WordTrace]
  refine ⟨158055474489502437527005133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105370316326334958351336755 158055474489502437527005133)
  ·
    refine ⟨59270802933563414072626925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158055474489502437527005133 59270802933563414072626925)
    ·
      refine ⟨22226551100086280277235097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59270802933563414072626925 22226551100086280277235097)
      ·
        refine ⟨16669913325064710207926323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22226551100086280277235097 16669913325064710207926323)
        ·
          refine ⟨25004869987597065311889485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16669913325064710207926323 25004869987597065311889485)
          ·
            refine ⟨9376826245348899491958557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25004869987597065311889485 9376826245348899491958557)
            ·
              refine ⟨3516309842005837309484459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9376826245348899491958557 3516309842005837309484459)
              ·
                refine ⟨5274464763008755964226689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3516309842005837309484459 5274464763008755964226689)
                ·
                  refine ⟨3955848572256566973170017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5274464763008755964226689 3955848572256566973170017)
                  ·
                    refine ⟨2966886429192425229877513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3955848572256566973170017 2966886429192425229877513)
                    ·
                      refine ⟨2225164821894318922408135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2966886429192425229877513 2225164821894318922408135)
                      ·
                        rfl

theorem cell23_4333493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_4333493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333493 prefixEnd_4333493 := by exact prefixLift 4333493
  have htrace : WordTrace (prefixWord ++ tailWord_4333493) baseStart_4333493 baseEnd_4333493 := by
    simpa [prefixWord, tailWord_4333493, baseEnd_4333493] using wordTrace_append hprefix tailTrace_4333493
  have hstable : (prefixWord ++ tailWord_4333493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333493).length < 2 ^ (prefixWord ++ tailWord_4333493).sum := by decide
  have hdescent : baseEnd_4333493 < baseStart_4333493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333515 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 4]
def baseStart_4333515 : Nat := 118140960795 + 4333515 * 2 ^ 59
def prefixEnd_4333515 : Nat := 4983230072969 + 3 ^ 40 * 4333515 * 2
def baseEnd_4333515 : Nat := 2225176118468717836333033

theorem tailTrace_4333515 : CollatzResearch.WordTrace tailWord_4333515 prefixEnd_4333515 2225176118468717836333033 := by
  unfold tailWord_4333515
  simp only [CollatzResearch.WordTrace]
  refine ⟨158056276895422735284305999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105370851263615156856203999 158056276895422735284305999)
  ·
    refine ⟨237084415343134102926458999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158056276895422735284305999 237084415343134102926458999)
    ·
      refine ⟨355626623014701154389688499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237084415343134102926458999 355626623014701154389688499)
      ·
        refine ⟨533439934522051731584532749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355626623014701154389688499 533439934522051731584532749)
        ·
          refine ⟨200039975445769399344199781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 533439934522051731584532749 200039975445769399344199781)
          ·
            refine ⟨37507495396081762377037459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 200039975445769399344199781 37507495396081762377037459)
            ·
              refine ⟨56261243094122643565556189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37507495396081762377037459 56261243094122643565556189)
              ·
                refine ⟨21097966160295991337083571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56261243094122643565556189 21097966160295991337083571)
                ·
                  refine ⟨31646949240443987005625357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21097966160295991337083571 31646949240443987005625357)
                  ·
                    refine ⟨11867605965166495127109509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31646949240443987005625357 11867605965166495127109509)
                    ·
                      refine ⟨2225176118468717836333033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11867605965166495127109509 2225176118468717836333033)
                      ·
                        rfl

theorem cell23_4333515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 4].length) (baseStart_4333515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333515 prefixEnd_4333515 := by exact prefixLift 4333515
  have htrace : WordTrace (prefixWord ++ tailWord_4333515) baseStart_4333515 baseEnd_4333515 := by
    simpa [prefixWord, tailWord_4333515, baseEnd_4333515] using wordTrace_append hprefix tailTrace_4333515
  have hstable : (prefixWord ++ tailWord_4333515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333515).length < 2 ^ (prefixWord ++ tailWord_4333515).sum := by decide
  have hdescent : baseEnd_4333515 < baseStart_4333515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333566 : List Nat := [4, 2, 2, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_4333566 : Nat := 118140960795 + 4333566 * 2 ^ 59
def prefixEnd_4333566 : Nat := 4983230072969 + 3 ^ 40 * 4333566 * 2
def baseEnd_4333566 : Nat := 2225202305982097136795299

theorem tailTrace_4333566 : CollatzResearch.WordTrace tailWord_4333566 prefixEnd_4333566 2225202305982097136795299 := by
  unfold tailWord_4333566
  simp only [CollatzResearch.WordTrace]
  refine ⟨19757267127279746374301569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105372091345491980662941701 19757267127279746374301569)
  ·
    refine ⟨14817950345459809780726177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19757267127279746374301569 14817950345459809780726177)
    ·
      refine ⟨11113462759094857335544633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14817950345459809780726177 11113462759094857335544633)
      ·
        refine ⟨8335097069321143001658475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11113462759094857335544633 8335097069321143001658475)
        ·
          refine ⟨12502645603981714502487713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8335097069321143001658475 12502645603981714502487713)
          ·
            refine ⟨9376984202986285876865785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12502645603981714502487713 9376984202986285876865785)
            ·
              refine ⟨7032738152239714407649339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9376984202986285876865785 7032738152239714407649339)
              ·
                refine ⟨10549107228359571611474009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7032738152239714407649339 10549107228359571611474009)
                ·
                  refine ⟨7911830421269678708605507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10549107228359571611474009 7911830421269678708605507)
                  ·
                    refine ⟨11867745631904518062908261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7911830421269678708605507 11867745631904518062908261)
                    ·
                      refine ⟨2225202305982097136795299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11867745631904518062908261 2225202305982097136795299)
                      ·
                        rfl

theorem cell23_4333566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_4333566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333566 prefixEnd_4333566 := by exact prefixLift 4333566
  have htrace : WordTrace (prefixWord ++ tailWord_4333566) baseStart_4333566 baseEnd_4333566 := by
    simpa [prefixWord, tailWord_4333566, baseEnd_4333566] using wordTrace_append hprefix tailTrace_4333566
  have hstable : (prefixWord ++ tailWord_4333566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333566).length < 2 ^ (prefixWord ++ tailWord_4333566).sum := by decide
  have hdescent : baseEnd_4333566 < baseStart_4333566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333569 : List Nat := [1, 2, 4, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_4333569 : Nat := 118140960795 + 4333569 * 2 ^ 59
def prefixEnd_4333569 : Nat := 4983230072969 + 3 ^ 40 * 4333569 * 2
def baseEnd_4333569 : Nat := 2225203846424060625057785

theorem tailTrace_4333569 : CollatzResearch.WordTrace tailWord_4333569 prefixEnd_4333569 2225203846424060625057785 := by
  unfold tailWord_4333569
  simp only [CollatzResearch.WordTrace]
  refine ⟨158058246437227102506771761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105372164291484735004514507 158058246437227102506771761)
  ·
    refine ⟨118543684827920326880078821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158058246437227102506771761 118543684827920326880078821)
    ·
      refine ⟨22226940905235061290014779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118543684827920326880078821 22226940905235061290014779)
      ·
        refine ⟨33340411357852591935022169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22226940905235061290014779 33340411357852591935022169)
        ·
          refine ⟨25005308518389443951266627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33340411357852591935022169 25005308518389443951266627)
          ·
            refine ⟨37507962777584165926899941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25005308518389443951266627 37507962777584165926899941)
            ·
              refine ⟨7032743020797031111293739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37507962777584165926899941 7032743020797031111293739)
              ·
                refine ⟨10549114531195546666940609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7032743020797031111293739 10549114531195546666940609)
                ·
                  refine ⟨7911835898396660000205457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10549114531195546666940609 7911835898396660000205457)
                  ·
                    refine ⟨5933876923797495000154093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7911835898396660000205457 5933876923797495000154093)
                    ·
                      refine ⟨2225203846424060625057785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5933876923797495000154093 2225203846424060625057785)
                      ·
                        rfl

theorem cell23_4333569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_4333569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333569 prefixEnd_4333569 := by exact prefixLift 4333569
  have htrace : WordTrace (prefixWord ++ tailWord_4333569) baseStart_4333569 baseEnd_4333569 := by
    simpa [prefixWord, tailWord_4333569, baseEnd_4333569] using wordTrace_append hprefix tailTrace_4333569
  have hstable : (prefixWord ++ tailWord_4333569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333569).length < 2 ^ (prefixWord ++ tailWord_4333569).sum := by decide
  have hdescent : baseEnd_4333569 < baseStart_4333569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333589 : List Nat := [1, 3, 2, 1, 5, 1, 2, 2, 6]
def baseStart_4333589 : Nat := 118140960795 + 4333589 * 2 ^ 59
def prefixEnd_4333589 : Nat := 4983230072969 + 3 ^ 40 * 4333589 * 2
def baseEnd_4333589 : Nat := 247246012893016727423077

theorem tailTrace_4333589 : CollatzResearch.WordTrace tailWord_4333589 prefixEnd_4333589 247246012893016727423077 := by
  unfold tailWord_4333589
  simp only [CollatzResearch.WordTrace]
  refine ⟨158058975897154645922499821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105372650598103097281666547 158058975897154645922499821)
  ·
    refine ⟨59272115961432992220937433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158058975897154645922499821 59272115961432992220937433)
    ·
      refine ⟨44454086971074744165703075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59272115961432992220937433 44454086971074744165703075)
      ·
        refine ⟨66681130456612116248554613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44454086971074744165703075 66681130456612116248554613)
        ·
          refine ⟨6251355980307385898301995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66681130456612116248554613 6251355980307385898301995)
          ·
            refine ⟨9377033970461078847452993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6251355980307385898301995 9377033970461078847452993)
            ·
              refine ⟨7032775477845809135589745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9377033970461078847452993 7032775477845809135589745)
              ·
                refine ⟨5274581608384356851692309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7032775477845809135589745 5274581608384356851692309)
                ·
                  refine ⟨247246012893016727423077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5274581608384356851692309 247246012893016727423077)
                  ·
                    rfl

theorem cell23_4333589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 6].length) (baseStart_4333589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333589 prefixEnd_4333589 := by exact prefixLift 4333589
  have htrace : WordTrace (prefixWord ++ tailWord_4333589) baseStart_4333589 baseEnd_4333589 := by
    simpa [prefixWord, tailWord_4333589, baseEnd_4333589] using wordTrace_append hprefix tailTrace_4333589
  have hstable : (prefixWord ++ tailWord_4333589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333589).length < 2 ^ (prefixWord ++ tailWord_4333589).sum := by decide
  have hdescent : baseEnd_4333589 < baseStart_4333589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333599 : List Nat := [1, 1, 2, 4, 1, 2, 2, 3, 3, 1, 3]
def baseStart_4333599 : Nat := 118140960795 + 4333599 * 2 ^ 59
def prefixEnd_4333599 : Nat := 4983230072969 + 3 ^ 40 * 4333599 * 2
def baseEnd_4333599 : Nat := 2225219250843695507682647

theorem tailTrace_4333599 : CollatzResearch.WordTrace tailWord_4333599 prefixEnd_4333599 2225219250843695507682647 := by
  unfold tailWord_4333599
  simp only [CollatzResearch.WordTrace]
  refine ⟨158059340627118417630363851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105372893751412278420242567 158059340627118417630363851)
  ·
    refine ⟨237089010940677626445545777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158059340627118417630363851 237089010940677626445545777)
    ·
      refine ⟨177816758205508219834159333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237089010940677626445545777 177816758205508219834159333)
      ·
        refine ⟨33340642163532791218904875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177816758205508219834159333 33340642163532791218904875)
        ·
          refine ⟨50010963245299186828357313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33340642163532791218904875 50010963245299186828357313)
          ·
            refine ⟨37508222433974390121267985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50010963245299186828357313 37508222433974390121267985)
            ·
              refine ⟨28131166825480792590950989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37508222433974390121267985 28131166825480792590950989)
              ·
                refine ⟨10549187559555297221606621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28131166825480792590950989 10549187559555297221606621)
                ·
                  refine ⟨3955945334833236458102483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10549187559555297221606621 3955945334833236458102483)
                  ·
                    refine ⟨5933918002249854687153725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3955945334833236458102483 5933918002249854687153725)
                    ·
                      refine ⟨2225219250843695507682647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5933918002249854687153725 2225219250843695507682647)
                      ·
                        rfl

theorem cell23_4333599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_4333599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333599 prefixEnd_4333599 := by exact prefixLift 4333599
  have htrace : WordTrace (prefixWord ++ tailWord_4333599) baseStart_4333599 baseEnd_4333599 := by
    simpa [prefixWord, tailWord_4333599, baseEnd_4333599] using wordTrace_append hprefix tailTrace_4333599
  have hstable : (prefixWord ++ tailWord_4333599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333599).length < 2 ^ (prefixWord ++ tailWord_4333599).sum := by decide
  have hdescent : baseEnd_4333599 < baseStart_4333599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333602 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_4333602 : Nat := 118140960795 + 4333602 * 2 ^ 59
def prefixEnd_4333602 : Nat := 4983230072969 + 3 ^ 40 * 4333602 * 2
def baseEnd_4333602 : Nat := 741740263761886331981711

theorem tailTrace_4333602 : CollatzResearch.WordTrace tailWord_4333602 prefixEnd_4333602 741740263761886331981711 := by
  unfold tailWord_4333602
  simp only [CollatzResearch.WordTrace]
  refine ⟨39514862511526887285680765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105372966697405032761815373 39514862511526887285680765)
  ·
    refine ⟨14818073441822582732130287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39514862511526887285680765 14818073441822582732130287)
    ·
      refine ⟨22227110162733874098195431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14818073441822582732130287 22227110162733874098195431)
      ·
        refine ⟨33340665244100811147293147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22227110162733874098195431 33340665244100811147293147)
        ·
          refine ⟨50010997866151216720939721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33340665244100811147293147 50010997866151216720939721)
          ·
            refine ⟨37508248399613412540704791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50010997866151216720939721 37508248399613412540704791)
            ·
              refine ⟨56262372599420118811057187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37508248399613412540704791 56262372599420118811057187)
              ·
                refine ⟨84393558899130178216585781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56262372599420118811057187 84393558899130178216585781)
                ·
                  refine ⟨7911896146793454207804917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84393558899130178216585781 7911896146793454207804917)
                  ·
                    refine ⟨741740263761886331981711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7911896146793454207804917 741740263761886331981711)
                    ·
                      rfl

theorem cell23_4333602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_4333602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333602 prefixEnd_4333602 := by exact prefixLift 4333602
  have htrace : WordTrace (prefixWord ++ tailWord_4333602) baseStart_4333602 baseEnd_4333602 := by
    simpa [prefixWord, tailWord_4333602, baseEnd_4333602] using wordTrace_append hprefix tailTrace_4333602
  have hstable : (prefixWord ++ tailWord_4333602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333602).length < 2 ^ (prefixWord ++ tailWord_4333602).sum := by decide
  have hdescent : baseEnd_4333602 < baseStart_4333602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333620 : List Nat := [2, 5, 1, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_4333620 : Nat := 118140960795 + 4333620 * 2 ^ 59
def prefixEnd_4333620 : Nat := 4983230072969 + 3 ^ 40 * 4333620 * 2
def baseEnd_4333620 : Nat := 2225230033937439925520051

theorem tailTrace_4333620 : CollatzResearch.WordTrace tailWord_4333620 prefixEnd_4333620 2225230033937439925520051 := by
  unfold tailWord_4333620
  simp only [CollatzResearch.WordTrace]
  refine ⟨79030053280021169108439157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105373404373361558811252209 79030053280021169108439157)
  ·
    refine ⟨7409067495001984603916171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79030053280021169108439157 7409067495001984603916171)
    ·
      refine ⟨11113601242502976905874257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7409067495001984603916171 11113601242502976905874257)
      ·
        refine ⟨8335200931877232679405693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11113601242502976905874257 8335200931877232679405693)
        ·
          refine ⟨3125700349453962254777135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8335200931877232679405693 3125700349453962254777135)
          ·
            refine ⟨4688550524180943382165703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3125700349453962254777135 4688550524180943382165703)
            ·
              refine ⟨7032825786271415073248555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4688550524180943382165703 7032825786271415073248555)
              ·
                refine ⟨10549238679407122609872833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7032825786271415073248555 10549238679407122609872833)
                ·
                  refine ⟨7911929009555341957404625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10549238679407122609872833 7911929009555341957404625)
                  ·
                    refine ⟨5933946757166506468053469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7911929009555341957404625 5933946757166506468053469)
                    ·
                      refine ⟨2225230033937439925520051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5933946757166506468053469 2225230033937439925520051)
                      ·
                        rfl

theorem cell23_4333620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_4333620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333620 prefixEnd_4333620 := by exact prefixLift 4333620
  have htrace : WordTrace (prefixWord ++ tailWord_4333620) baseStart_4333620 baseEnd_4333620 := by
    simpa [prefixWord, tailWord_4333620, baseEnd_4333620] using wordTrace_append hprefix tailTrace_4333620
  have hstable : (prefixWord ++ tailWord_4333620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333620).length < 2 ^ (prefixWord ++ tailWord_4333620).sum := by decide
  have hdescent : baseEnd_4333620 < baseStart_4333620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333632 : List Nat := [2, 1, 1, 2, 2, 4, 2, 2, 1, 6]
def baseStart_4333632 : Nat := 118140960795 + 4333632 * 2 ^ 59
def prefixEnd_4333632 : Nat := 4983230072969 + 3 ^ 40 * 4333632 * 2
def baseEnd_4333632 : Nat := 741745398568431292856665

theorem tailTrace_4333632 : CollatzResearch.WordTrace tailWord_4333632 prefixEnd_4333632 741745398568431292856665 := by
  unfold tailWord_4333632
  simp only [CollatzResearch.WordTrace]
  refine ⟨79030272117999432133157575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105373696157332576177543433 79030272117999432133157575)
  ·
    refine ⟨118545408176999148199736363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79030272117999432133157575 118545408176999148199736363)
    ·
      refine ⟨177818112265498722299604545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118545408176999148199736363 177818112265498722299604545)
      ·
        refine ⟨133363584199124041724703409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177818112265498722299604545 133363584199124041724703409)
        ·
          refine ⟨100022688149343031293527557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133363584199124041724703409 100022688149343031293527557)
          ·
            refine ⟨18754254028001818367536417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100022688149343031293527557 18754254028001818367536417)
            ·
              refine ⟨14065690521001363775652313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18754254028001818367536417 14065690521001363775652313)
              ·
                refine ⟨10549267890751022831739235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14065690521001363775652313 10549267890751022831739235)
                ·
                  refine ⟨15823901836126534247608853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10549267890751022831739235 15823901836126534247608853)
                  ·
                    refine ⟨741745398568431292856665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15823901836126534247608853 741745398568431292856665)
                    ·
                      rfl

theorem cell23_4333632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 1, 6].length) (baseStart_4333632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333632 prefixEnd_4333632 := by exact prefixLift 4333632
  have htrace : WordTrace (prefixWord ++ tailWord_4333632) baseStart_4333632 baseEnd_4333632 := by
    simpa [prefixWord, tailWord_4333632, baseEnd_4333632] using wordTrace_append hprefix tailTrace_4333632
  have hstable : (prefixWord ++ tailWord_4333632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333632).length < 2 ^ (prefixWord ++ tailWord_4333632).sum := by decide
  have hdescent : baseEnd_4333632 < baseStart_4333632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333633 : List Nat := [1, 2, 5, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_4333633 : Nat := 118140960795 + 4333633 * 2 ^ 59
def prefixEnd_4333633 : Nat := 4983230072969 + 3 ^ 40 * 4333633 * 2
def baseEnd_4333633 : Nat := 2225236709185948374657491

theorem tailTrace_4333633 : CollatzResearch.WordTrace tailWord_4333633 prefixEnd_4333633 2225236709185948374657491 := by
  unfold tailWord_4333633
  simp only [CollatzResearch.WordTrace]
  refine ⟨158060580708995241437101553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105373720472663494291401035 158060580708995241437101553)
  ·
    refine ⟨118545435531746431077826165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158060580708995241437101553 118545435531746431077826165)
    ·
      refine ⟨11113634581101227913546203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118545435531746431077826165 11113634581101227913546203)
      ·
        refine ⟨16670451871651841870319305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11113634581101227913546203 16670451871651841870319305)
        ·
          refine ⟨12502838903738881402739479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16670451871651841870319305 12502838903738881402739479)
          ·
            refine ⟨18754258355608322104109219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12502838903738881402739479 18754258355608322104109219)
            ·
              refine ⟨28131387533412483156163829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18754258355608322104109219 28131387533412483156163829)
              ·
                refine ⟨2637317581257420295890359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28131387533412483156163829 2637317581257420295890359)
                ·
                  refine ⟨3955976371886130443835539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2637317581257420295890359 3955976371886130443835539)
                  ·
                    refine ⟨5933964557829195665753309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3955976371886130443835539 5933964557829195665753309)
                    ·
                      refine ⟨2225236709185948374657491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5933964557829195665753309 2225236709185948374657491)
                      ·
                        rfl

theorem cell23_4333633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_4333633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333633 prefixEnd_4333633 := by exact prefixLift 4333633
  have htrace : WordTrace (prefixWord ++ tailWord_4333633) baseStart_4333633 baseEnd_4333633 := by
    simpa [prefixWord, tailWord_4333633, baseEnd_4333633] using wordTrace_append hprefix tailTrace_4333633
  have hstable : (prefixWord ++ tailWord_4333633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333633).length < 2 ^ (prefixWord ++ tailWord_4333633).sum := by decide
  have hdescent : baseEnd_4333633 < baseStart_4333633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333639 : List Nat := [1, 1, 4, 1, 3, 1, 3, 3, 1, 1, 4]
def baseStart_4333639 : Nat := 118140960795 + 4333639 * 2 ^ 59
def prefixEnd_4333639 : Nat := 4983230072969 + 3 ^ 40 * 4333639 * 2
def baseEnd_4333639 : Nat := 2225239790069875351182463

theorem tailTrace_4333639 : CollatzResearch.WordTrace tailWord_4333639 prefixEnd_4333639 2225239790069875351182463 := by
  unfold tailWord_4333639
  simp only [CollatzResearch.WordTrace]
  refine ⟨158060799546973504461819971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105373866364649002974546647 158060799546973504461819971)
  ·
    refine ⟨237091199320460256692729957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158060799546973504461819971 237091199320460256692729957)
    ·
      refine ⟨44454599872586298129886867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237091199320460256692729957 44454599872586298129886867)
      ·
        refine ⟨66681899808879447194830301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44454599872586298129886867 66681899808879447194830301)
        ·
          refine ⟨25005712428329792698061363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66681899808879447194830301 25005712428329792698061363)
          ·
            refine ⟨37508568642494689047092045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25005712428329792698061363 37508568642494689047092045)
            ·
              refine ⟨14065713240935508392659517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37508568642494689047092045 14065713240935508392659517)
              ·
                refine ⟨5274642465350815647247319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14065713240935508392659517 5274642465350815647247319)
                ·
                  refine ⟨7911963698026223470870979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5274642465350815647247319 7911963698026223470870979)
                  ·
                    refine ⟨11867945547039335206306469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7911963698026223470870979 11867945547039335206306469)
                    ·
                      refine ⟨2225239790069875351182463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11867945547039335206306469 2225239790069875351182463)
                      ·
                        rfl

theorem cell23_4333639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_4333639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333639 prefixEnd_4333639 := by exact prefixLift 4333639
  have htrace : WordTrace (prefixWord ++ tailWord_4333639) baseStart_4333639 baseEnd_4333639 := by
    simpa [prefixWord, tailWord_4333639, baseEnd_4333639] using wordTrace_append hprefix tailTrace_4333639
  have hstable : (prefixWord ++ tailWord_4333639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333639).length < 2 ^ (prefixWord ++ tailWord_4333639).sum := by decide
  have hdescent : baseEnd_4333639 < baseStart_4333639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333642 : List Nat := [3, 1, 2, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_4333642 : Nat := 118140960795 + 4333642 * 2 ^ 59
def prefixEnd_4333642 : Nat := 4983230072969 + 3 ^ 40 * 4333642 * 2
def baseEnd_4333642 : Nat := 2225241330511838839444949

theorem tailTrace_4333642 : CollatzResearch.WordTrace tailWord_4333642 prefixEnd_4333642 2225241330511838839444949 := by
  unfold tailWord_4333642
  simp only [CollatzResearch.WordTrace]
  refine ⟨39515227241490658993544795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105373939310641757316119453 39515227241490658993544795)
  ·
    refine ⟨59272840862235988490317193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39515227241490658993544795 59272840862235988490317193)
    ·
      refine ⟨44454630646676991367737895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59272840862235988490317193 44454630646676991367737895)
      ·
        refine ⟨66681945970015487051606843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44454630646676991367737895 66681945970015487051606843)
        ·
          refine ⟨100022918955023230577410265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66681945970015487051606843 100022918955023230577410265)
          ·
            refine ⟨75017189216267422933057699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100022918955023230577410265 75017189216267422933057699)
            ·
              refine ⟨112525783824401134399586549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75017189216267422933057699 112525783824401134399586549)
              ·
                refine ⟨10549292233537606349961239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112525783824401134399586549 10549292233537606349961239)
                ·
                  refine ⟨15823938350306409524941859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10549292233537606349961239 15823938350306409524941859)
                  ·
                    refine ⟨23735907525459614287412789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15823938350306409524941859 23735907525459614287412789)
                    ·
                      refine ⟨2225241330511838839444949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23735907525459614287412789 2225241330511838839444949)
                      ·
                        rfl

theorem cell23_4333642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_4333642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333642 prefixEnd_4333642 := by exact prefixLift 4333642
  have htrace : WordTrace (prefixWord ++ tailWord_4333642) baseStart_4333642 baseEnd_4333642 := by
    simpa [prefixWord, tailWord_4333642, baseEnd_4333642] using wordTrace_append hprefix tailTrace_4333642
  have hstable : (prefixWord ++ tailWord_4333642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333642).length < 2 ^ (prefixWord ++ tailWord_4333642).sum := by decide
  have hdescent : baseEnd_4333642 < baseStart_4333642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333652 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_4333652 : Nat := 118140960795 + 4333652 * 2 ^ 59
def prefixEnd_4333652 : Nat := 4983230072969 + 3 ^ 40 * 4333652 * 2
def baseEnd_4333652 : Nat := 2225246465318383800319903

theorem tailTrace_4333652 : CollatzResearch.WordTrace tailWord_4333652 prefixEnd_4333652 2225246465318383800319903 := by
  unfold tailWord_4333652
  simp only [CollatzResearch.WordTrace]
  refine ⟨79030636847963203841021605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105374182463950938454695473 79030636847963203841021605)
  ·
    refine ⟨14818244408993100720191551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79030636847963203841021605 14818244408993100720191551)
    ·
      refine ⟨22227366613489651080287327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14818244408993100720191551 22227366613489651080287327)
      ·
        refine ⟨33341049920234476620430991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22227366613489651080287327 33341049920234476620430991)
        ·
          refine ⟨50011574880351714930646487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33341049920234476620430991 50011574880351714930646487)
          ·
            refine ⟨75017362320527572395969731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50011574880351714930646487 75017362320527572395969731)
            ·
              refine ⟨112526043480791358593954597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75017362320527572395969731 112526043480791358593954597)
              ·
                refine ⟨21098633152648379736366487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112526043480791358593954597 21098633152648379736366487)
                ·
                  refine ⟨31647949728972569604549731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21098633152648379736366487 31647949728972569604549731)
                  ·
                    refine ⟨47471924593458854406824597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31647949728972569604549731 47471924593458854406824597)
                    ·
                      refine ⟨2225246465318383800319903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47471924593458854406824597 2225246465318383800319903)
                      ·
                        rfl

theorem cell23_4333652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_4333652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333652 prefixEnd_4333652 := by exact prefixLift 4333652
  have htrace : WordTrace (prefixWord ++ tailWord_4333652) baseStart_4333652 baseEnd_4333652 := by
    simpa [prefixWord, tailWord_4333652, baseEnd_4333652] using wordTrace_append hprefix tailTrace_4333652
  have hstable : (prefixWord ++ tailWord_4333652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333652).length < 2 ^ (prefixWord ++ tailWord_4333652).sum := by decide
  have hdescent : baseEnd_4333652 < baseStart_4333652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333656 : List Nat := [2, 1, 2, 2, 1, 4, 1, 3, 3, 2, 2]
def baseStart_4333656 : Nat := 118140960795 + 4333656 * 2 ^ 59
def prefixEnd_4333656 : Nat := 4983230072969 + 3 ^ 40 * 4333656 * 2
def baseEnd_4333656 : Nat := 2225248519241001784669885

theorem tailTrace_4333656 : CollatzResearch.WordTrace tailWord_4333656 prefixEnd_4333656 2225248519241001784669885 := by
  unfold tailWord_4333656
  simp only [CollatzResearch.WordTrace]
  refine ⟨79030709793955958182594411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105374279725274610910125881 79030709793955958182594411)
  ·
    refine ⟨118546064690933937273891617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79030709793955958182594411 118546064690933937273891617)
    ·
      refine ⟨88909548518200452955418713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118546064690933937273891617 88909548518200452955418713)
      ·
        refine ⟨66682161388650339716564035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88909548518200452955418713 66682161388650339716564035)
        ·
          refine ⟨100023242082975509574846053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66682161388650339716564035 100023242082975509574846053)
          ·
            refine ⟨18754357890557908045283635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100023242082975509574846053 18754357890557908045283635)
            ·
              refine ⟨28131536835836862067925453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18754357890557908045283635 28131536835836862067925453)
              ·
                refine ⟨10549326313438823275472045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28131536835836862067925453 10549326313438823275472045)
                ·
                  refine ⟨3955997367539558728302017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10549326313438823275472045 3955997367539558728302017)
                  ·
                    refine ⟨2966998025654669046226513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3955997367539558728302017 2966998025654669046226513)
                    ·
                      refine ⟨2225248519241001784669885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2966998025654669046226513 2225248519241001784669885)
                      ·
                        rfl

theorem cell23_4333656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_4333656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333656 prefixEnd_4333656 := by exact prefixLift 4333656
  have htrace : WordTrace (prefixWord ++ tailWord_4333656) baseStart_4333656 baseEnd_4333656 := by
    simpa [prefixWord, tailWord_4333656, baseEnd_4333656] using wordTrace_append hprefix tailTrace_4333656
  have hstable : (prefixWord ++ tailWord_4333656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333656).length < 2 ^ (prefixWord ++ tailWord_4333656).sum := by decide
  have hdescent : baseEnd_4333656 < baseStart_4333656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333669 : List Nat := [1, 3, 1, 3, 2, 2, 3, 1, 1, 2, 4]
def baseStart_4333669 : Nat := 118140960795 + 4333669 * 2 ^ 59
def prefixEnd_4333669 : Nat := 4983230072969 + 3 ^ 40 * 4333669 * 2
def baseEnd_4333669 : Nat := 2225255194489510233807325

theorem tailTrace_4333669 : CollatzResearch.WordTrace tailWord_4333669 prefixEnd_4333669 2225255194489510233807325 := by
  unfold tailWord_4333669
  simp only [CollatzResearch.WordTrace]
  refine ⟨158061893736864819585412061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105374595824576546390274707 158061893736864819585412061)
  ·
    refine ⟨59273210151324307344529523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158061893736864819585412061 59273210151324307344529523)
    ·
      refine ⟨88909815226986461016794285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59273210151324307344529523 88909815226986461016794285)
      ·
        refine ⟨33341180710119922881297857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88909815226986461016794285 33341180710119922881297857)
        ·
          refine ⟨25005885532589942160973393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33341180710119922881297857 25005885532589942160973393)
          ·
            refine ⟨18754414149442456620730045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25005885532589942160973393 18754414149442456620730045)
            ·
              refine ⟨7032905306040921232773767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18754414149442456620730045 7032905306040921232773767)
              ·
                refine ⟨10549357959061381849160651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7032905306040921232773767 10549357959061381849160651)
                ·
                  refine ⟨15824036938592072773740977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10549357959061381849160651 15824036938592072773740977)
                  ·
                    refine ⟨11868027703944054580305733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15824036938592072773740977 11868027703944054580305733)
                    ·
                      refine ⟨2225255194489510233807325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11868027703944054580305733 2225255194489510233807325)
                      ·
                        rfl

theorem cell23_4333669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_4333669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333669 prefixEnd_4333669 := by exact prefixLift 4333669
  have htrace : WordTrace (prefixWord ++ tailWord_4333669) baseStart_4333669 baseEnd_4333669 := by
    simpa [prefixWord, tailWord_4333669, baseEnd_4333669] using wordTrace_append hprefix tailTrace_4333669
  have hstable : (prefixWord ++ tailWord_4333669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333669).length < 2 ^ (prefixWord ++ tailWord_4333669).sum := by decide
  have hdescent : baseEnd_4333669 < baseStart_4333669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333676 : List Nat := [2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 3]
def baseStart_4333676 : Nat := 118140960795 + 4333676 * 2 ^ 59
def prefixEnd_4333676 : Nat := 4983230072969 + 3 ^ 40 * 4333676 * 2
def baseEnd_4333676 : Nat := 2225258788854091706419793

theorem tailTrace_4333676 : CollatzResearch.WordTrace tailWord_4333676 prefixEnd_4333676 2225258788854091706419793 := by
  unfold tailWord_4333676
  simp only [CollatzResearch.WordTrace]
  refine ⟨79031074523919729890458441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105374766031892973187277921 79031074523919729890458441)
  ·
    refine ⟨59273305892939797417843831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79031074523919729890458441 59273305892939797417843831)
    ·
      refine ⟨88909958839409696126765747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59273305892939797417843831 88909958839409696126765747)
      ·
        refine ⟨133364938259114544190148621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88909958839409696126765747 133364938259114544190148621)
        ·
          refine ⟨50011851847167954071305733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133364938259114544190148621 50011851847167954071305733)
          ·
            refine ⟨9377222221343991388369825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50011851847167954071305733 9377222221343991388369825)
            ·
              refine ⟨7032916666007993541277369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9377222221343991388369825 7032916666007993541277369)
              ·
                refine ⟨5274687499505995155958027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7032916666007993541277369 5274687499505995155958027)
                ·
                  refine ⟨7912031249258992733937041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5274687499505995155958027 7912031249258992733937041)
                  ·
                    refine ⟨5934023436944244550452781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7912031249258992733937041 5934023436944244550452781)
                    ·
                      refine ⟨2225258788854091706419793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5934023436944244550452781 2225258788854091706419793)
                      ·
                        rfl

theorem cell23_4333676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 3].length) (baseStart_4333676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333676 prefixEnd_4333676 := by exact prefixLift 4333676
  have htrace : WordTrace (prefixWord ++ tailWord_4333676) baseStart_4333676 baseEnd_4333676 := by
    simpa [prefixWord, tailWord_4333676, baseEnd_4333676] using wordTrace_append hprefix tailTrace_4333676
  have hstable : (prefixWord ++ tailWord_4333676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333676).length < 2 ^ (prefixWord ++ tailWord_4333676).sum := by decide
  have hdescent : baseEnd_4333676 < baseStart_4333676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333679 : List Nat := [1, 1, 2, 1, 3, 6, 2, 7]
def baseStart_4333679 : Nat := 118140960795 + 4333679 * 2 ^ 59
def prefixEnd_4333679 : Nat := 4983230072969 + 3 ^ 40 * 4333679 * 2
def baseEnd_4333679 : Nat := 82417049233187229432677

theorem tailTrace_4333679 : CollatzResearch.WordTrace tailWord_4333679 prefixEnd_4333679 82417049233187229432677 := by
  unfold tailWord_4333679
  simp only [CollatzResearch.WordTrace]
  refine ⟨158062258466828591293276091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105374838977885727528850727 158062258466828591293276091)
  ·
    refine ⟨237093387700242886939914137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158062258466828591293276091 237093387700242886939914137)
    ·
      refine ⟨177820040775182165204935603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237093387700242886939914137 177820040775182165204935603)
      ·
        refine ⟨266730061162773247807403405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177820040775182165204935603 266730061162773247807403405)
        ·
          refine ⟨100023772936039967927776277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 266730061162773247807403405 100023772936039967927776277)
          ·
            refine ⟨4688614356376873496614513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 100023772936039967927776277 4688614356376873496614513)
            ·
              refine ⟨3516460767282655122460885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4688614356376873496614513 3516460767282655122460885)
              ·
                refine ⟨82417049233187229432677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3516460767282655122460885 82417049233187229432677)
                ·
                  rfl

theorem cell23_4333679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 7].length) (baseStart_4333679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333679 prefixEnd_4333679 := by exact prefixLift 4333679
  have htrace : WordTrace (prefixWord ++ tailWord_4333679) baseStart_4333679 baseEnd_4333679 := by
    simpa [prefixWord, tailWord_4333679, baseEnd_4333679] using wordTrace_append hprefix tailTrace_4333679
  have hstable : (prefixWord ++ tailWord_4333679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333679).length < 2 ^ (prefixWord ++ tailWord_4333679).sum := by decide
  have hdescent : baseEnd_4333679 < baseStart_4333679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333706 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 4, 1, 3]
def baseStart_4333706 : Nat := 118140960795 + 4333706 * 2 ^ 59
def prefixEnd_4333706 : Nat := 4983230072969 + 3 ^ 40 * 4333706 * 2
def baseEnd_4333706 : Nat := 2225274193273726589044655

theorem tailTrace_4333706 : CollatzResearch.WordTrace tailWord_4333706 prefixEnd_4333706 2225274193273726589044655 := by
  unfold tailWord_4333706
  simp only [CollatzResearch.WordTrace]
  refine ⟨39515810809432693726127243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105375495491820516603005981 39515810809432693726127243)
  ·
    refine ⟨59273716214149040589190865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39515810809432693726127243 59273716214149040589190865)
    ·
      refine ⟨44455287160611780441893149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59273716214149040589190865 44455287160611780441893149)
      ·
        refine ⟨16670732685229417665709931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44455287160611780441893149 16670732685229417665709931)
        ·
          refine ⟨25006099027844126498564897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16670732685229417665709931 25006099027844126498564897)
          ·
            refine ⟨18754574270883094873923673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25006099027844126498564897 18754574270883094873923673)
            ·
              refine ⟨14065930703162321155442755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18754574270883094873923673 14065930703162321155442755)
              ·
                refine ⟨21098896054743481733164133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14065930703162321155442755 21098896054743481733164133)
                ·
                  refine ⟨3956043010264402824968275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21098896054743481733164133 3956043010264402824968275)
                  ·
                    refine ⟨5934064515396604237452413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3956043010264402824968275 5934064515396604237452413)
                    ·
                      refine ⟨2225274193273726589044655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5934064515396604237452413 2225274193273726589044655)
                      ·
                        rfl

theorem cell23_4333706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_4333706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333706 prefixEnd_4333706 := by exact prefixLift 4333706
  have htrace : WordTrace (prefixWord ++ tailWord_4333706) baseStart_4333706 baseEnd_4333706 := by
    simpa [prefixWord, tailWord_4333706, baseEnd_4333706] using wordTrace_append hprefix tailTrace_4333706
  have hstable : (prefixWord ++ tailWord_4333706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333706).length < 2 ^ (prefixWord ++ tailWord_4333706).sum := by decide
  have hdescent : baseEnd_4333706 < baseStart_4333706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333712 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 4]
def baseStart_4333712 : Nat := 118140960795 + 4333712 * 2 ^ 59
def prefixEnd_4333712 : Nat := 4983230072969 + 3 ^ 40 * 4333712 * 2
def baseEnd_4333712 : Nat := 2225277274157653565569627

theorem tailTrace_4333712 : CollatzResearch.WordTrace tailWord_4333712 prefixEnd_4333712 2225277274157653565569627 := by
  unfold tailWord_4333712
  simp only [CollatzResearch.WordTrace]
  refine ⟨79031731037854518964613695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105375641383806025286151593 79031731037854518964613695)
  ·
    refine ⟨118547596556781778446920543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79031731037854518964613695 118547596556781778446920543)
    ·
      refine ⟨177821394835172667670380815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118547596556781778446920543 177821394835172667670380815)
      ·
        refine ⟨266732092252759001505571223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177821394835172667670380815 266732092252759001505571223)
        ·
          refine ⟨400098138379138502258356835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266732092252759001505571223 400098138379138502258356835)
          ·
            refine ⟨600147207568707753387535253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400098138379138502258356835 600147207568707753387535253)
            ·
              refine ⟨28131900354783175940040715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 600147207568707753387535253 28131900354783175940040715)
              ·
                refine ⟨42197850532174763910061073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28131900354783175940040715 42197850532174763910061073)
                ·
                  refine ⟨31648387899131072932545805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42197850532174763910061073 31648387899131072932545805)
                  ·
                    refine ⟨11868145462174152349704677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31648387899131072932545805 11868145462174152349704677)
                    ·
                      refine ⟨2225277274157653565569627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11868145462174152349704677 2225277274157653565569627)
                      ·
                        rfl

theorem cell23_4333712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_4333712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333712 prefixEnd_4333712 := by exact prefixLift 4333712
  have htrace : WordTrace (prefixWord ++ tailWord_4333712) baseStart_4333712 baseEnd_4333712 := by
    simpa [prefixWord, tailWord_4333712, baseEnd_4333712] using wordTrace_append hprefix tailTrace_4333712
  have hstable : (prefixWord ++ tailWord_4333712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333712).length < 2 ^ (prefixWord ++ tailWord_4333712).sum := by decide
  have hdescent : baseEnd_4333712 < baseStart_4333712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333746 : List Nat := [3, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2]
def baseStart_4333746 : Nat := 118140960795 + 4333746 * 2 ^ 59
def prefixEnd_4333746 : Nat := 4983230072969 + 3 ^ 40 * 4333746 * 2
def baseEnd_4333746 : Nat := 2225294732499906432544471

theorem tailTrace_4333746 : CollatzResearch.WordTrace tailWord_4333746 prefixEnd_4333746 2225294732499906432544471 := by
  unfold tailWord_4333746
  simp only [CollatzResearch.WordTrace]
  refine ⟨39516175539396465433991273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105376468105057241157310061 39516175539396465433991273)
  ·
    refine ⟨29637131654547349075493455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39516175539396465433991273 29637131654547349075493455)
    ·
      refine ⟨44455697481821023613240183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29637131654547349075493455 44455697481821023613240183)
      ·
        refine ⟨66683546222731535419860275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44455697481821023613240183 66683546222731535419860275)
        ·
          refine ⟨100025319334097303129790413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66683546222731535419860275 100025319334097303129790413)
          ·
            refine ⟨37509494750286488673671405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100025319334097303129790413 37509494750286488673671405)
            ·
              refine ⟨14066060531357433252626777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37509494750286488673671405 14066060531357433252626777)
              ·
                refine ⟨10549545398518074939470083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14066060531357433252626777 10549545398518074939470083)
                ·
                  refine ⟨15824318097777112409205125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10549545398518074939470083 15824318097777112409205125)
                  ·
                    refine ⟨2967059643333208576725961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15824318097777112409205125 2967059643333208576725961)
                    ·
                      refine ⟨2225294732499906432544471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2967059643333208576725961 2225294732499906432544471)
                      ·
                        rfl

theorem cell23_4333746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_4333746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333746 prefixEnd_4333746 := by exact prefixLift 4333746
  have htrace : WordTrace (prefixWord ++ tailWord_4333746) baseStart_4333746 baseEnd_4333746 := by
    simpa [prefixWord, tailWord_4333746, baseEnd_4333746] using wordTrace_append hprefix tailTrace_4333746
  have hstable : (prefixWord ++ tailWord_4333746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333746).length < 2 ^ (prefixWord ++ tailWord_4333746).sum := by decide
  have hdescent : baseEnd_4333746 < baseStart_4333746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333836 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 2, 4, 2]
def baseStart_4333836 : Nat := 118140960795 + 4333836 * 2 ^ 59
def prefixEnd_4333836 : Nat := 4983230072969 + 3 ^ 40 * 4333836 * 2
def baseEnd_4333836 : Nat := 2225340945758811080419057

theorem tailTrace_4333836 : CollatzResearch.WordTrace tailWord_4333836 prefixEnd_4333836 2225340945758811080419057 := by
  unfold tailWord_4333836
  simp only [CollatzResearch.WordTrace]
  refine ⟨79033992363629903553370681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105378656484839871404494241 79033992363629903553370681)
  ·
    refine ⟨59275494272722427665028011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79033992363629903553370681 59275494272722427665028011)
    ·
      refine ⟨88913241409083641497542017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59275494272722427665028011 88913241409083641497542017)
      ·
        refine ⟨66684931056812731123156513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88913241409083641497542017 66684931056812731123156513)
        ·
          refine ⟨50013698292609548342367385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66684931056812731123156513 50013698292609548342367385)
          ·
            refine ⟨37510273719457161256775539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50013698292609548342367385 37510273719457161256775539)
            ·
              refine ⟨56265410579185741885163309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37510273719457161256775539 56265410579185741885163309)
              ·
                refine ⟨21099528967194653206936241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56265410579185741885163309 21099528967194653206936241)
                ·
                  refine ⟨15824646725395989905202181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21099528967194653206936241 15824646725395989905202181)
                  ·
                    refine ⟨2967121261011748107225409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15824646725395989905202181 2967121261011748107225409)
                    ·
                      refine ⟨2225340945758811080419057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2967121261011748107225409 2225340945758811080419057)
                      ·
                        rfl

theorem cell23_4333836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_4333836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333836 prefixEnd_4333836 := by exact prefixLift 4333836
  have htrace : WordTrace (prefixWord ++ tailWord_4333836) baseStart_4333836 baseEnd_4333836 := by
    simpa [prefixWord, tailWord_4333836, baseEnd_4333836] using wordTrace_append hprefix tailTrace_4333836
  have hstable : (prefixWord ++ tailWord_4333836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333836).length < 2 ^ (prefixWord ++ tailWord_4333836).sum := by decide
  have hdescent : baseEnd_4333836 < baseStart_4333836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333856 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 3]
def baseStart_4333856 : Nat := 118140960795 + 4333856 * 2 ^ 59
def prefixEnd_4333856 : Nat := 4983230072969 + 3 ^ 40 * 4333856 * 2
def baseEnd_4333856 : Nat := 2225351215371901002168965

theorem tailTrace_4333856 : CollatzResearch.WordTrace tailWord_4333856 prefixEnd_4333856 2225351215371901002168965 := by
  unfold tailWord_4333856
  simp only [CollatzResearch.WordTrace]
  refine ⟨79034357093593675261234711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105379142791458233681646281 79034357093593675261234711)
  ·
    refine ⟨118551535640390512891852067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79034357093593675261234711 118551535640390512891852067)
    ·
      refine ⟨177827303460585769337778101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118551535640390512891852067 177827303460585769337778101)
      ·
        refine ⟨16671309699429915875416697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 177827303460585769337778101 16671309699429915875416697)
        ·
          refine ⟨12503482274572436906562523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16671309699429915875416697 12503482274572436906562523)
          ·
            refine ⟨18755223411858655359843785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12503482274572436906562523 18755223411858655359843785)
            ·
              refine ⟨14066417558893991519882839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18755223411858655359843785 14066417558893991519882839)
              ·
                refine ⟨21099626338340987279824259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14066417558893991519882839 21099626338340987279824259)
                ·
                  refine ⟨31649439507511480919736389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21099626338340987279824259 31649439507511480919736389)
                  ·
                    refine ⟨5934269907658402672450573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31649439507511480919736389 5934269907658402672450573)
                    ·
                      refine ⟨2225351215371901002168965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5934269907658402672450573 2225351215371901002168965)
                      ·
                        rfl

theorem cell23_4333856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_4333856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333856 prefixEnd_4333856 := by exact prefixLift 4333856
  have htrace : WordTrace (prefixWord ++ tailWord_4333856) baseStart_4333856 baseEnd_4333856 := by
    simpa [prefixWord, tailWord_4333856, baseEnd_4333856] using wordTrace_append hprefix tailTrace_4333856
  have hstable : (prefixWord ++ tailWord_4333856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333856).length < 2 ^ (prefixWord ++ tailWord_4333856).sum := by decide
  have hdescent : baseEnd_4333856 < baseStart_4333856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333870 : List Nat := [4, 1, 3, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_4333870 : Nat := 118140960795 + 4333870 * 2 ^ 59
def prefixEnd_4333870 : Nat := 4983230072969 + 3 ^ 40 * 4333870 * 2
def baseEnd_4333870 : Nat := 2225358404101063947393901

theorem tailTrace_4333870 : CollatzResearch.WordTrace tailWord_4333870 prefixEnd_4333870 2225358404101063947393901 := by
  unfold tailWord_4333870
  simp only [CollatzResearch.WordTrace]
  refine ⟨19758653101142078864184883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105379483206091087275652709 19758653101142078864184883)
  ·
    refine ⟨29637979651713118296277325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19758653101142078864184883 29637979651713118296277325)
    ·
      refine ⟨11114242369392419361103997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29637979651713118296277325 11114242369392419361103997)
      ·
        refine ⟨4167840888522157260413999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11114242369392419361103997 4167840888522157260413999)
        ·
          refine ⟨6251761332783235890620999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4167840888522157260413999 6251761332783235890620999)
          ·
            refine ⟨9377641999174853835931499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6251761332783235890620999 9377641999174853835931499)
            ·
              refine ⟨14066462998762280753897249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9377641999174853835931499 14066462998762280753897249)
              ·
                refine ⟨10549847249071710565422937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14066462998762280753897249 10549847249071710565422937)
                ·
                  refine ⟨7912385436803782924067203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10549847249071710565422937 7912385436803782924067203)
                  ·
                    refine ⟨11868578155205674386100805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7912385436803782924067203 11868578155205674386100805)
                    ·
                      refine ⟨2225358404101063947393901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11868578155205674386100805 2225358404101063947393901)
                      ·
                        rfl

theorem cell23_4333870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_4333870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333870 prefixEnd_4333870 := by exact prefixLift 4333870
  have htrace : WordTrace (prefixWord ++ tailWord_4333870) baseStart_4333870 baseEnd_4333870 := by
    simpa [prefixWord, tailWord_4333870, baseEnd_4333870] using wordTrace_append hprefix tailTrace_4333870
  have hstable : (prefixWord ++ tailWord_4333870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333870).length < 2 ^ (prefixWord ++ tailWord_4333870).sum := by decide
  have hdescent : baseEnd_4333870 < baseStart_4333870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333873 : List Nat := [1, 2, 2, 3, 4, 1, 1, 2, 2, 2, 3]
def baseStart_4333873 : Nat := 118140960795 + 4333873 * 2 ^ 59
def prefixEnd_4333873 : Nat := 4983230072969 + 3 ^ 40 * 4333873 * 2
def baseEnd_4333873 : Nat := 2225359944543027435656387

theorem tailTrace_4333873 : CollatzResearch.WordTrace tailWord_4333873 prefixEnd_4333873 2225359944543027435656387 := by
  unfold tailWord_4333873
  simp only [CollatzResearch.WordTrace]
  refine ⟨158069334228125762425838273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105379556152083841617225515 158069334228125762425838273)
  ·
    refine ⟨118552000671094321819378705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158069334228125762425838273 118552000671094321819378705)
    ·
      refine ⟨88914000503320741364534029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118552000671094321819378705 88914000503320741364534029)
      ·
        refine ⟨33342750188745278011700261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88914000503320741364534029 33342750188745278011700261)
        ·
          refine ⟨6251765660389739627193799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33342750188745278011700261 6251765660389739627193799)
          ·
            refine ⟨9377648490584609440790699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6251765660389739627193799 9377648490584609440790699)
            ·
              refine ⟨14066472735876914161186049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9377648490584609440790699 14066472735876914161186049)
              ·
                refine ⟨10549854551907685620889537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14066472735876914161186049 10549854551907685620889537)
                ·
                  refine ⟨7912390913930764215667153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10549854551907685620889537 7912390913930764215667153)
                  ·
                    refine ⟨5934293185448073161750365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7912390913930764215667153 5934293185448073161750365)
                    ·
                      refine ⟨2225359944543027435656387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5934293185448073161750365 2225359944543027435656387)
                      ·
                        rfl

theorem cell23_4333873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_4333873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333873 prefixEnd_4333873 := by exact prefixLift 4333873
  have htrace : WordTrace (prefixWord ++ tailWord_4333873) baseStart_4333873 baseEnd_4333873 := by
    simpa [prefixWord, tailWord_4333873, baseEnd_4333873] using wordTrace_append hprefix tailTrace_4333873
  have hstable : (prefixWord ++ tailWord_4333873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333873).length < 2 ^ (prefixWord ++ tailWord_4333873).sum := by decide
  have hdescent : baseEnd_4333873 < baseStart_4333873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333876 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 8]
def baseStart_4333876 : Nat := 118140960795 + 4333876 * 2 ^ 59
def prefixEnd_4333876 : Nat := 4983230072969 + 3 ^ 40 * 4333876 * 2
def baseEnd_4333876 : Nat := 247262387220554547102097

theorem tailTrace_4333876 : CollatzResearch.WordTrace tailWord_4333876 prefixEnd_4333876 247262387220554547102097 := by
  unfold tailWord_4333876
  simp only [CollatzResearch.WordTrace]
  refine ⟨79034721823557446969098741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105379629098076595958798321 79034721823557446969098741)
  ·
    refine ⟨7409505170958510653353007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79034721823557446969098741 7409505170958510653353007)
    ·
      refine ⟨11114257756437765980029511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7409505170958510653353007 11114257756437765980029511)
      ·
        refine ⟨16671386634656648970044267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11114257756437765980029511 16671386634656648970044267)
        ·
          refine ⟨25007079951984973455066401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16671386634656648970044267 25007079951984973455066401)
          ·
            refine ⟨18755309963988730091299801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25007079951984973455066401 18755309963988730091299801)
            ·
              refine ⟨14066482472991547568474851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18755309963988730091299801 14066482472991547568474851)
              ·
                refine ⟨21099723709487321352712277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14066482472991547568474851 21099723709487321352712277)
                ·
                  refine ⟨247262387220554547102097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21099723709487321352712277 247262387220554547102097)
                  ·
                    rfl

theorem cell23_4333876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_4333876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333876 prefixEnd_4333876 := by exact prefixLift 4333876
  have htrace : WordTrace (prefixWord ++ tailWord_4333876) baseStart_4333876 baseEnd_4333876 := by
    simpa [prefixWord, tailWord_4333876, baseEnd_4333876] using wordTrace_append hprefix tailTrace_4333876
  have hstable : (prefixWord ++ tailWord_4333876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333876).length < 2 ^ (prefixWord ++ tailWord_4333876).sum := by decide
  have hdescent : baseEnd_4333876 < baseStart_4333876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333896 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 3, 5, 2]
def baseStart_4333896 : Nat := 118140960795 + 4333896 * 2 ^ 59
def prefixEnd_4333896 : Nat := 4983230072969 + 3 ^ 40 * 4333896 * 2
def baseEnd_4333896 : Nat := 2225371754598080845668781

theorem tailTrace_4333896 : CollatzResearch.WordTrace tailWord_4333896 prefixEnd_4333896 2225371754598080845668781 := by
  unfold tailWord_4333896
  simp only [CollatzResearch.WordTrace]
  refine ⟨79035086553521218676962771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105380115404694958235950361 79035086553521218676962771)
  ·
    refine ⟨118552629830281828015444157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79035086553521218676962771 118552629830281828015444157)
    ·
      refine ⟨44457236186355685505791559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118552629830281828015444157 44457236186355685505791559)
      ·
        refine ⟨66685854279533528258687339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44457236186355685505791559 66685854279533528258687339)
        ·
          refine ⟨100028781419300292388031009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66685854279533528258687339 100028781419300292388031009)
          ·
            refine ⟨75021586064475219291023257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100028781419300292388031009 75021586064475219291023257)
            ·
              refine ⟨56266189548356414468267443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75021586064475219291023257 56266189548356414468267443)
              ·
                refine ⟨84399284322534621702401165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56266189548356414468267443 84399284322534621702401165)
                ·
                  refine ⟨31649731620950483138400437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84399284322534621702401165 31649731620950483138400437)
                  ·
                    refine ⟨2967162339464107794225041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31649731620950483138400437 2967162339464107794225041)
                    ·
                      refine ⟨2225371754598080845668781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2967162339464107794225041 2225371754598080845668781)
                      ·
                        rfl

theorem cell23_4333896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_4333896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333896 prefixEnd_4333896 := by exact prefixLift 4333896
  have htrace : WordTrace (prefixWord ++ tailWord_4333896) baseStart_4333896 baseEnd_4333896 := by
    simpa [prefixWord, tailWord_4333896, baseEnd_4333896] using wordTrace_append hprefix tailTrace_4333896
  have hstable : (prefixWord ++ tailWord_4333896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333896).length < 2 ^ (prefixWord ++ tailWord_4333896).sum := by decide
  have hdescent : baseEnd_4333896 < baseStart_4333896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333919 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 3, 6]
def baseStart_4333919 : Nat := 118140960795 + 4333919 * 2 ^ 59
def prefixEnd_4333919 : Nat := 4983230072969 + 3 ^ 40 * 4333919 * 2
def baseEnd_4333919 : Nat := 741794521551044751893725

theorem tailTrace_4333919 : CollatzResearch.WordTrace tailWord_4333919 prefixEnd_4333919 741794521551044751893725 := by
  unfold tailWord_4333919
  simp only [CollatzResearch.WordTrace]
  refine ⟨158071011985959112282012811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105380674657306074854675207 158071011985959112282012811)
  ·
    refine ⟨237106517978938668423019217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158071011985959112282012811 237106517978938668423019217)
    ·
      refine ⟨177829888484204001317264413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237106517978938668423019217 177829888484204001317264413)
      ·
        refine ⟨66686208181576500493974155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177829888484204001317264413 66686208181576500493974155)
        ·
          refine ⟨100029312272364750740961233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66686208181576500493974155 100029312272364750740961233)
          ·
            refine ⟨75021984204273563055720925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100029312272364750740961233 75021984204273563055720925)
            ·
              refine ⟨28133244076602586145895347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75021984204273563055720925 28133244076602586145895347)
              ·
                refine ⟨42199866114903879218843021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28133244076602586145895347 42199866114903879218843021)
                ·
                  refine ⟨15824949793088954707066133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42199866114903879218843021 15824949793088954707066133)
                  ·
                    refine ⟨741794521551044751893725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15824949793088954707066133 741794521551044751893725)
                    ·
                      rfl

theorem cell23_4333919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 6].length) (baseStart_4333919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333919 prefixEnd_4333919 := by exact prefixLift 4333919
  have htrace : WordTrace (prefixWord ++ tailWord_4333919) baseStart_4333919 baseEnd_4333919 := by
    simpa [prefixWord, tailWord_4333919, baseEnd_4333919] using wordTrace_append hprefix tailTrace_4333919
  have hstable : (prefixWord ++ tailWord_4333919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333919).length < 2 ^ (prefixWord ++ tailWord_4333919).sum := by decide
  have hdescent : baseEnd_4333919 < baseStart_4333919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333923 : List Nat := [1, 1, 1, 5, 2, 1, 5, 1, 1, 5]
def baseStart_4333923 : Nat := 118140960795 + 4333923 * 2 ^ 59
def prefixEnd_4333923 : Nat := 4983230072969 + 3 ^ 40 * 4333923 * 2
def baseEnd_4333923 : Nat := 741795206191917413343719

theorem tailTrace_4333923 : CollatzResearch.WordTrace tailWord_4333923 prefixEnd_4333923 741795206191917413343719 := by
  unfold tailWord_4333923
  simp only [CollatzResearch.WordTrace]
  refine ⟨158071157877944620965158423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105380771918629747310105615 158071157877944620965158423)
  ·
    refine ⟨237106736816916931447737635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158071157877944620965158423 237106736816916931447737635)
    ·
      refine ⟨355660105225375397171606453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237106736816916931447737635 355660105225375397171606453)
      ·
        refine ⟨33343134864878943484838105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 355660105225375397171606453 33343134864878943484838105)
        ·
          refine ⟨25007351148659207613628579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33343134864878943484838105 25007351148659207613628579)
          ·
            refine ⟨37511026722988811420442869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25007351148659207613628579 37511026722988811420442869)
            ·
              refine ⟨3516658755280201070666519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37511026722988811420442869 3516658755280201070666519)
              ·
                refine ⟨5274988132920301605999779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3516658755280201070666519 5274988132920301605999779)
                ·
                  refine ⟨7912482199380452408999669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5274988132920301605999779 7912482199380452408999669)
                  ·
                    refine ⟨741795206191917413343719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7912482199380452408999669 741795206191917413343719)
                    ·
                      rfl

theorem cell23_4333923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 1, 5].length) (baseStart_4333923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333923 prefixEnd_4333923 := by exact prefixLift 4333923
  have htrace : WordTrace (prefixWord ++ tailWord_4333923) baseStart_4333923 baseEnd_4333923 := by
    simpa [prefixWord, tailWord_4333923, baseEnd_4333923] using wordTrace_append hprefix tailTrace_4333923
  have hstable : (prefixWord ++ tailWord_4333923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333923).length < 2 ^ (prefixWord ++ tailWord_4333923).sum := by decide
  have hdescent : baseEnd_4333923 < baseStart_4333923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333930 : List Nat := [3, 1, 3, 3, 1, 1, 2, 2, 2, 3, 2]
def baseStart_4333930 : Nat := 118140960795 + 4333930 * 2 ^ 59
def prefixEnd_4333930 : Nat := 4983230072969 + 3 ^ 40 * 4333930 * 2
def baseEnd_4333930 : Nat := 2225389212940333712643625

theorem tailTrace_4333930 : CollatzResearch.WordTrace tailWord_4333930 prefixEnd_4333930 2225389212940333712643625 := by
  unfold tailWord_4333930
  simp only [CollatzResearch.WordTrace]
  refine ⟨39517853297229815290165811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105380942125946174107108829 39517853297229815290165811)
  ·
    refine ⟨59276779945844722935248717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39517853297229815290165811 59276779945844722935248717)
    ·
      refine ⟨22228792479691771100718269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59276779945844722935248717 22228792479691771100718269)
      ·
        refine ⟨8335797179884414162769351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22228792479691771100718269 8335797179884414162769351)
        ·
          refine ⟨12503695769826621244154027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8335797179884414162769351 12503695769826621244154027)
          ·
            refine ⟨18755543654739931866231041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12503695769826621244154027 18755543654739931866231041)
            ·
              refine ⟨14066657741054948899673281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18755543654739931866231041 14066657741054948899673281)
              ·
                refine ⟨10549993305791211674754961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14066657741054948899673281 10549993305791211674754961)
                ·
                  refine ⟨7912494979343408756066221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10549993305791211674754961 7912494979343408756066221)
                  ·
                    refine ⟨2967185617253778283524833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7912494979343408756066221 2967185617253778283524833)
                    ·
                      refine ⟨2225389212940333712643625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2967185617253778283524833 2225389212940333712643625)
                      ·
                        rfl

theorem cell23_4333930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_4333930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333930 prefixEnd_4333930 := by exact prefixLift 4333930
  have htrace : WordTrace (prefixWord ++ tailWord_4333930) baseStart_4333930 baseEnd_4333930 := by
    simpa [prefixWord, tailWord_4333930, baseEnd_4333930] using wordTrace_append hprefix tailTrace_4333930
  have hstable : (prefixWord ++ tailWord_4333930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333930).length < 2 ^ (prefixWord ++ tailWord_4333930).sum := by decide
  have hdescent : baseEnd_4333930 < baseStart_4333930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333953 : List Nat := [1, 2, 4, 3, 1, 2, 2, 1, 1, 6]
def baseStart_4333953 : Nat := 118140960795 + 4333953 * 2 ^ 59
def prefixEnd_4333953 : Nat := 4983230072969 + 3 ^ 40 * 4333953 * 2
def baseEnd_4333953 : Nat := 741800340998462374218673

theorem tailTrace_4333953 : CollatzResearch.WordTrace tailWord_4333953 prefixEnd_4333953 741800340998462374218673 := by
  unfold tailWord_4333953
  simp only [CollatzResearch.WordTrace]
  refine ⟨158072252067835936088750513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105381501378557290725833675 158072252067835936088750513)
  ·
    refine ⟨118554189050876952066562885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158072252067835936088750513 118554189050876952066562885)
    ·
      refine ⟨22228910447039428512480541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118554189050876952066562885 22228910447039428512480541)
      ·
        refine ⟨8335841417639785692180203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22228910447039428512480541 8335841417639785692180203)
        ·
          refine ⟨12503762126459678538270305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8335841417639785692180203 12503762126459678538270305)
          ·
            refine ⟨9377821594844758903702729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12503762126459678538270305 9377821594844758903702729)
            ·
              refine ⟨7033366196133569177777047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9377821594844758903702729 7033366196133569177777047)
              ·
                refine ⟨10550049294200353766665571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7033366196133569177777047 10550049294200353766665571)
                ·
                  refine ⟨15825073941300530649998357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10550049294200353766665571 15825073941300530649998357)
                  ·
                    refine ⟨741800340998462374218673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15825073941300530649998357 741800340998462374218673)
                    ·
                      rfl

theorem cell23_4333953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_4333953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333953 prefixEnd_4333953 := by exact prefixLift 4333953
  have htrace : WordTrace (prefixWord ++ tailWord_4333953) baseStart_4333953 baseEnd_4333953 := by
    simpa [prefixWord, tailWord_4333953, baseEnd_4333953] using wordTrace_append hprefix tailTrace_4333953
  have hstable : (prefixWord ++ tailWord_4333953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333953).length < 2 ^ (prefixWord ++ tailWord_4333953).sum := by decide
  have hdescent : baseEnd_4333953 < baseStart_4333953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333960 : List Nat := [2, 1, 3, 3, 1, 1, 3, 2, 3, 2, 2]
def baseStart_4333960 : Nat := 118140960795 + 4333960 * 2 ^ 59
def prefixEnd_4333960 : Nat := 4983230072969 + 3 ^ 40 * 4333960 * 2
def baseEnd_4333960 : Nat := 2225404617359968595268487

theorem tailTrace_4333960 : CollatzResearch.WordTrace tailWord_4333960 prefixEnd_4333960 2225404617359968595268487 := by
  unfold tailWord_4333960
  simp only [CollatzResearch.WordTrace]
  refine ⟨79036253689405288142127667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105381671585873717522836889 79036253689405288142127667)
  ·
    refine ⟨118554380534107932213191501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79036253689405288142127667 118554380534107932213191501)
    ·
      refine ⟨44457892700290474579946813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118554380534107932213191501 44457892700290474579946813)
      ·
        refine ⟨16671709762608927967480055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44457892700290474579946813 16671709762608927967480055)
        ·
          refine ⟨25007564643913391951220083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16671709762608927967480055 25007564643913391951220083)
          ·
            refine ⟨37511346965870087926830125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25007564643913391951220083 37511346965870087926830125)
            ·
              refine ⟨14066755112201282972561297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37511346965870087926830125 14066755112201282972561297)
              ·
                refine ⟨10550066334150962229420973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14066755112201282972561297 10550066334150962229420973)
                ·
                  refine ⟨3956274875306610836032865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10550066334150962229420973 3956274875306610836032865)
                  ·
                    refine ⟨2967206156479958127024649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3956274875306610836032865 2967206156479958127024649)
                    ·
                      refine ⟨2225404617359968595268487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2967206156479958127024649 2225404617359968595268487)
                      ·
                        rfl

theorem cell23_4333960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_4333960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333960 prefixEnd_4333960 := by exact prefixLift 4333960
  have htrace : WordTrace (prefixWord ++ tailWord_4333960) baseStart_4333960 baseEnd_4333960 := by
    simpa [prefixWord, tailWord_4333960, baseEnd_4333960] using wordTrace_append hprefix tailTrace_4333960
  have hstable : (prefixWord ++ tailWord_4333960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333960).length < 2 ^ (prefixWord ++ tailWord_4333960).sum := by decide
  have hdescent : baseEnd_4333960 < baseStart_4333960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333974 : List Nat := [5, 3, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_4333974 : Nat := 118140960795 + 4333974 * 2 ^ 59
def prefixEnd_4333974 : Nat := 4983230072969 + 3 ^ 40 * 4333974 * 2
def baseEnd_4333974 : Nat := 741803935363043846831141

theorem tailTrace_4333974 : CollatzResearch.WordTrace tailWord_4333974 prefixEnd_4333974 741803935363043846831141 := by
  unfold tailWord_4333974
  simp only [CollatzResearch.WordTrace]
  refine ⟨9879563625047491042204061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105382012000506571116843317 9879563625047491042204061)
  ·
    refine ⟨3704836359392809140826523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9879563625047491042204061 3704836359392809140826523)
    ·
      refine ⟨5557254539089213711239785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3704836359392809140826523 5557254539089213711239785)
      ·
        refine ⟨4167940904316910283429839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5557254539089213711239785 4167940904316910283429839)
        ·
          refine ⟨6251911356475365425144759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4167940904316910283429839 6251911356475365425144759)
          ·
            refine ⟨9377867034713048137717139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6251911356475365425144759 9377867034713048137717139)
            ·
              refine ⟨14066800552069572206575709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9377867034713048137717139 14066800552069572206575709)
              ·
                refine ⟨5275050207026089577465891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14066800552069572206575709 5275050207026089577465891)
                ·
                  refine ⟨7912575310539134366198837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5275050207026089577465891 7912575310539134366198837)
                  ·
                    refine ⟨741803935363043846831141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7912575310539134366198837 741803935363043846831141)
                    ·
                      rfl

theorem cell23_4333974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_4333974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333974 prefixEnd_4333974 := by exact prefixLift 4333974
  have htrace : WordTrace (prefixWord ++ tailWord_4333974) baseStart_4333974 baseEnd_4333974 := by
    simpa [prefixWord, tailWord_4333974, baseEnd_4333974] using wordTrace_append hprefix tailTrace_4333974
  have hstable : (prefixWord ++ tailWord_4333974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333974).length < 2 ^ (prefixWord ++ tailWord_4333974).sum := by decide
  have hdescent : baseEnd_4333974 < baseStart_4333974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4333977 : List Nat := [1, 2, 1, 2, 1, 4, 4, 3, 1, 2, 2]
def baseStart_4333977 : Nat := 118140960795 + 4333977 * 2 ^ 59
def prefixEnd_4333977 : Nat := 4983230072969 + 3 ^ 40 * 4333977 * 2
def baseEnd_4333977 : Nat := 2225413346531095028755909

theorem tailTrace_4333977 : CollatzResearch.WordTrace tailWord_4333977 prefixEnd_4333977 2225413346531095028755909 := by
  unfold tailWord_4333977
  simp only [CollatzResearch.WordTrace]
  refine ⟨158073127419748988187624185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105382084946499325458416123 158073127419748988187624185)
  ·
    refine ⟨118554845564811741140718139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158073127419748988187624185 118554845564811741140718139)
    ·
      refine ⟨177832268347217611711077209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118554845564811741140718139 177832268347217611711077209)
      ·
        refine ⟨133374201260413208783307907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177832268347217611711077209 133374201260413208783307907)
        ·
          refine ⟨200061301890619813174961861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133374201260413208783307907 200061301890619813174961861)
          ·
            refine ⟨37511494104491214970305349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 200061301890619813174961861 37511494104491214970305349)
            ·
              refine ⟨7033405144592102806932253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37511494104491214970305349 7033405144592102806932253)
              ·
                refine ⟨2637526929222038552599595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7033405144592102806932253 2637526929222038552599595)
                ·
                  refine ⟨3956290393833057828899393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2637526929222038552599595 3956290393833057828899393)
                  ·
                    refine ⟨2967217795374793371674545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3956290393833057828899393 2967217795374793371674545)
                    ·
                      refine ⟨2225413346531095028755909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2967217795374793371674545 2225413346531095028755909)
                      ·
                        rfl

theorem cell23_4333977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 1, 2, 2].length) (baseStart_4333977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4333977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4333977 prefixEnd_4333977 := by exact prefixLift 4333977
  have htrace : WordTrace (prefixWord ++ tailWord_4333977) baseStart_4333977 baseEnd_4333977 := by
    simpa [prefixWord, tailWord_4333977, baseEnd_4333977] using wordTrace_append hprefix tailTrace_4333977
  have hstable : (prefixWord ++ tailWord_4333977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4333977).length < 2 ^ (prefixWord ++ tailWord_4333977).sum := by decide
  have hdescent : baseEnd_4333977 < baseStart_4333977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4333977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334004 : List Nat := [2, 5, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_4334004 : Nat := 118140960795 + 4334004 * 2 ^ 59
def prefixEnd_4334004 : Nat := 4983230072969 + 3 ^ 40 * 4334004 * 2
def baseEnd_4334004 : Nat := 741809070169588807706095

theorem tailTrace_4334004 : CollatzResearch.WordTrace tailWord_4334004 prefixEnd_4334004 741809070169588807706095 := by
  unfold tailWord_4334004
  simp only [CollatzResearch.WordTrace]
  refine ⟨79037056095325585899428533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105382741460434114532571377 79037056095325585899428533)
  ·
    refine ⟨7409724008936773678071425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79037056095325585899428533 7409724008936773678071425)
    ·
      refine ⟨5557293006702580258553569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7409724008936773678071425 5557293006702580258553569)
      ·
        refine ⟨4167969755026935193915177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5557293006702580258553569 4167969755026935193915177)
        ·
          refine ⟨3125977316270201395436383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4167969755026935193915177 3125977316270201395436383)
          ·
            refine ⟨4688965974405302093154575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3125977316270201395436383 4688965974405302093154575)
            ·
              refine ⟨7033448961607953139731863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4688965974405302093154575 7033448961607953139731863)
              ·
                refine ⟨10550173442411929709597795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7033448961607953139731863 10550173442411929709597795)
                ·
                  refine ⟨15825260163617894564396693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10550173442411929709597795 15825260163617894564396693)
                  ·
                    refine ⟨741809070169588807706095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15825260163617894564396693 741809070169588807706095)
                    ·
                      rfl

theorem cell23_4334004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_4334004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334004 prefixEnd_4334004 := by exact prefixLift 4334004
  have htrace : WordTrace (prefixWord ++ tailWord_4334004) baseStart_4334004 baseEnd_4334004 := by
    simpa [prefixWord, tailWord_4334004, baseEnd_4334004] using wordTrace_append hprefix tailTrace_4334004
  have hstable : (prefixWord ++ tailWord_4334004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334004).length < 2 ^ (prefixWord ++ tailWord_4334004).sum := by decide
  have hdescent : baseEnd_4334004 < baseStart_4334004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334033 : List Nat := [1, 2, 2, 1, 2, 1, 1, 6, 1, 4, 2]
def baseStart_4334033 : Nat := 118140960795 + 4334033 * 2 ^ 59
def prefixEnd_4334033 : Nat := 4983230072969 + 3 ^ 40 * 4334033 * 2
def baseEnd_4334033 : Nat := 2225442101447746809655651

theorem tailTrace_4334033 : CollatzResearch.WordTrace tailWord_4334033 prefixEnd_4334033 2225442101447746809655651 := by
  unfold tailWord_4334033
  simp only [CollatzResearch.WordTrace]
  refine ⟨158075169907546109751662753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105383446605030739834441835 158075169907546109751662753)
  ·
    refine ⟨118556377430659582313747065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158075169907546109751662753 118556377430659582313747065)
    ·
      refine ⟨88917283072994686735310299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118556377430659582313747065 88917283072994686735310299)
      ·
        refine ⟨133375924609492030102965449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88917283072994686735310299 133375924609492030102965449)
        ·
          refine ⟨100031943457119022577224087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133375924609492030102965449 100031943457119022577224087)
          ·
            refine ⟨150047915185678533865836131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100031943457119022577224087 150047915185678533865836131)
            ·
              refine ⟨225071872778517800798754197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150047915185678533865836131 225071872778517800798754197)
              ·
                refine ⟨10550244036493021912441603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 225071872778517800798754197 10550244036493021912441603)
                ·
                  refine ⟨15825366054739532868662405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10550244036493021912441603 15825366054739532868662405)
                  ·
                    refine ⟨2967256135263662412874201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15825366054739532868662405 2967256135263662412874201)
                    ·
                      refine ⟨2225442101447746809655651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2967256135263662412874201 2225442101447746809655651)
                      ·
                        rfl

theorem cell23_4334033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 4, 2].length) (baseStart_4334033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334033 prefixEnd_4334033 := by exact prefixLift 4334033
  have htrace : WordTrace (prefixWord ++ tailWord_4334033) baseStart_4334033 baseEnd_4334033 := by
    simpa [prefixWord, tailWord_4334033, baseEnd_4334033] using wordTrace_append hprefix tailTrace_4334033
  have hstable : (prefixWord ++ tailWord_4334033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334033).length < 2 ^ (prefixWord ++ tailWord_4334033).sum := by decide
  have hdescent : baseEnd_4334033 < baseStart_4334033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334140 : List Nat := [2, 2, 2, 2, 3, 1, 3, 1, 2, 1, 4]
def baseStart_4334140 : Nat := 118140960795 + 4334140 * 2 ^ 59
def prefixEnd_4334140 : Nat := 4983230072969 + 3 ^ 40 * 4334140 * 2
def baseEnd_4334140 : Nat := 2225497043877777891017659

theorem tailTrace_4334140 : CollatzResearch.WordTrace tailWord_4334140 prefixEnd_4334140 2225497043877777891017659 := by
  unfold tailWord_4334140
  simp only [CollatzResearch.WordTrace]
  refine ⟨79039536259079233512903937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105386048345438978017205249 79039536259079233512903937)
  ·
    refine ⟨59279652194309425134677953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79039536259079233512903937 59279652194309425134677953)
    ·
      refine ⟨44459739145732068851008465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59279652194309425134677953 44459739145732068851008465)
      ·
        refine ⟨33344804359299051638256349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44459739145732068851008465 33344804359299051638256349)
        ·
          refine ⟨12504301634737144364346131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33344804359299051638256349 12504301634737144364346131)
          ·
            refine ⟨18756452452105716546519197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12504301634737144364346131 18756452452105716546519197)
            ·
              refine ⟨7033669669539643704944699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18756452452105716546519197 7033669669539643704944699)
              ·
                refine ⟨10550504504309465557417049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7033669669539643704944699 10550504504309465557417049)
                ·
                  refine ⟨7912878378232099168062787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10550504504309465557417049 7912878378232099168062787)
                  ·
                    refine ⟨11869317567348148752094181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7912878378232099168062787 11869317567348148752094181)
                    ·
                      refine ⟨2225497043877777891017659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11869317567348148752094181 2225497043877777891017659)
                      ·
                        rfl

theorem cell23_4334140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_4334140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334140 prefixEnd_4334140 := by exact prefixLift 4334140
  have htrace : WordTrace (prefixWord ++ tailWord_4334140) baseStart_4334140 baseEnd_4334140 := by
    simpa [prefixWord, tailWord_4334140, baseEnd_4334140] using wordTrace_append hprefix tailTrace_4334140
  have hstable : (prefixWord ++ tailWord_4334140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334140).length < 2 ^ (prefixWord ++ tailWord_4334140).sum := by decide
  have hdescent : baseEnd_4334140 < baseStart_4334140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334143 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 3]
def baseStart_4334143 : Nat := 118140960795 + 4334143 * 2 ^ 59
def prefixEnd_4334143 : Nat := 4983230072969 + 3 ^ 40 * 4334143 * 2
def baseEnd_4334143 : Nat := 2225498584319741379280145

theorem tailTrace_4334143 : CollatzResearch.WordTrace tailWord_4334143 prefixEnd_4334143 2225498584319741379280145 := by
  unfold tailWord_4334143
  simp only [CollatzResearch.WordTrace]
  refine ⟨158079181937147598538167083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105386121291431732358778055 158079181937147598538167083)
  ·
    refine ⟨237118772905721397807250625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158079181937147598538167083 237118772905721397807250625)
    ·
      refine ⟨177839079679291048355437969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237118772905721397807250625 177839079679291048355437969)
      ·
        refine ⟨133379309759468286266578477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177839079679291048355437969 133379309759468286266578477)
        ·
          refine ⟨50017241159800607349966929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133379309759468286266578477 50017241159800607349966929)
          ·
            refine ⟨37512930869850455512475197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50017241159800607349966929 37512930869850455512475197)
            ·
              refine ⟨14067349076193920817178199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37512930869850455512475197 14067349076193920817178199)
              ·
                refine ⟨21101023614290881225767299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14067349076193920817178199 21101023614290881225767299)
                ·
                  refine ⟨31651535421436321838650949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21101023614290881225767299 31651535421436321838650949)
                  ·
                    refine ⟨5934662891519310344747053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31651535421436321838650949 5934662891519310344747053)
                    ·
                      refine ⟨2225498584319741379280145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5934662891519310344747053 2225498584319741379280145)
                      ·
                        rfl

theorem cell23_4334143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_4334143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334143 prefixEnd_4334143 := by exact prefixLift 4334143
  have htrace : WordTrace (prefixWord ++ tailWord_4334143) baseStart_4334143 baseEnd_4334143 := by
    simpa [prefixWord, tailWord_4334143, baseEnd_4334143] using wordTrace_append hprefix tailTrace_4334143
  have hstable : (prefixWord ++ tailWord_4334143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334143).length < 2 ^ (prefixWord ++ tailWord_4334143).sum := by decide
  have hdescent : baseEnd_4334143 < baseStart_4334143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334157 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_4334157 : Nat := 118140960795 + 4334157 * 2 ^ 59
def prefixEnd_4334157 : Nat := 4983230072969 + 3 ^ 40 * 4334157 * 2
def baseEnd_4334157 : Nat := 2225505773048904324505081

theorem tailTrace_4334157 : CollatzResearch.WordTrace tailWord_4334157 prefixEnd_4334157 2225505773048904324505081 := by
  unfold tailWord_4334157
  simp only [CollatzResearch.WordTrace]
  refine ⟨158079692559096878929176725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105386461706064585952784483 158079692559096878929176725)
  ·
    refine ⟨7409985588707666199805159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 158079692559096878929176725 7409985588707666199805159)
    ·
      refine ⟨11114978383061499299707739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7409985588707666199805159 11114978383061499299707739)
      ·
        refine ⟨16672467574592248949561609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11114978383061499299707739 16672467574592248949561609)
        ·
          refine ⟨12504350680944186712171207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16672467574592248949561609 12504350680944186712171207)
          ·
            refine ⟨18756526021416280068256811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12504350680944186712171207 18756526021416280068256811)
            ·
              refine ⟨28134789032124420102385217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18756526021416280068256811 28134789032124420102385217)
              ·
                refine ⟨21101091774093315076788913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28134789032124420102385217 21101091774093315076788913)
                ·
                  refine ⟨15825818830569986307591685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21101091774093315076788913 15825818830569986307591685)
                  ·
                    refine ⟨2967341030731872432673441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15825818830569986307591685 2967341030731872432673441)
                    ·
                      refine ⟨2225505773048904324505081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2967341030731872432673441 2225505773048904324505081)
                      ·
                        rfl

theorem cell23_4334157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_4334157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334157 prefixEnd_4334157 := by exact prefixLift 4334157
  have htrace : WordTrace (prefixWord ++ tailWord_4334157) baseStart_4334157 baseEnd_4334157 := by
    simpa [prefixWord, tailWord_4334157, baseEnd_4334157] using wordTrace_append hprefix tailTrace_4334157
  have hstable : (prefixWord ++ tailWord_4334157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334157).length < 2 ^ (prefixWord ++ tailWord_4334157).sum := by decide
  have hdescent : baseEnd_4334157 < baseStart_4334157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334180 : List Nat := [2, 3, 1, 1, 2, 2, 5, 1, 6]
def baseStart_4334180 : Nat := 118140960795 + 4334180 * 2 ^ 59
def prefixEnd_4334180 : Nat := 4983230072969 + 3 ^ 40 * 4334180 * 2
def baseEnd_4334180 : Nat := 247279731455995303835275

theorem tailTrace_4334180 : CollatzResearch.WordTrace tailWord_4334180 prefixEnd_4334180 247279731455995303835275 := by
  unfold tailWord_4334180
  simp only [CollatzResearch.WordTrace]
  refine ⟨79040265719006776928631997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105387020958675702571509329 79040265719006776928631997)
  ·
    refine ⟨29640099644627541348236999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79040265719006776928631997 29640099644627541348236999)
    ·
      refine ⟨44460149466941312022355499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29640099644627541348236999 44460149466941312022355499)
      ·
        refine ⟨66690224200411968033533249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44460149466941312022355499 66690224200411968033533249)
        ·
          refine ⟨50017668150308976025149937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66690224200411968033533249 50017668150308976025149937)
          ·
            refine ⟨37513251112731732018862453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50017668150308976025149937 37513251112731732018862453)
            ·
              refine ⟨3516867291818599876768355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37513251112731732018862453 3516867291818599876768355)
              ·
                refine ⟨5275300937727899815152533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3516867291818599876768355 5275300937727899815152533)
                ·
                  refine ⟨247279731455995303835275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5275300937727899815152533 247279731455995303835275)
                  ·
                    rfl

theorem cell23_4334180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_4334180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334180 prefixEnd_4334180 := by exact prefixLift 4334180
  have htrace : WordTrace (prefixWord ++ tailWord_4334180) baseStart_4334180 baseEnd_4334180 := by
    simpa [prefixWord, tailWord_4334180, baseEnd_4334180] using wordTrace_append hprefix tailTrace_4334180
  have hstable : (prefixWord ++ tailWord_4334180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334180).length < 2 ^ (prefixWord ++ tailWord_4334180).sum := by decide
  have hdescent : baseEnd_4334180 < baseStart_4334180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334207 : List Nat := [1, 1, 2, 2, 1, 1, 1, 9, 1, 1, 3]
def baseStart_4334207 : Nat := 118140960795 + 4334207 * 2 ^ 59
def prefixEnd_4334207 : Nat := 4983230072969 + 3 ^ 40 * 4334207 * 2
def baseEnd_4334207 : Nat := 2225531447081629128879851

theorem tailTrace_4334207 : CollatzResearch.WordTrace tailWord_4334207 prefixEnd_4334207 2225531447081629128879851 := by
  unfold tailWord_4334207
  simp only [CollatzResearch.WordTrace]
  refine ⟨158081516208915737468496875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105387677472610491645664583 158081516208915737468496875)
  ·
    refine ⟨237122274313373606202745313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158081516208915737468496875 237122274313373606202745313)
    ·
      refine ⟨177841705735030204652058985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237122274313373606202745313 177841705735030204652058985)
      ·
        refine ⟨133381279301272653489044239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177841705735030204652058985 133381279301272653489044239)
        ·
          refine ⟨200071918951908980233566359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133381279301272653489044239 200071918951908980233566359)
          ·
            refine ⟨300107878427863470350349539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200071918951908980233566359 300107878427863470350349539)
            ·
              refine ⟨450161817641795205525524309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300107878427863470350349539 450161817641795205525524309)
              ·
                refine ⟨2637666900244893782376119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 450161817641795205525524309 2637666900244893782376119)
                ·
                  refine ⟨3956500350367340673564179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2637666900244893782376119 3956500350367340673564179)
                  ·
                    refine ⟨5934750525551011010346269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3956500350367340673564179 5934750525551011010346269)
                    ·
                      refine ⟨2225531447081629128879851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5934750525551011010346269 2225531447081629128879851)
                      ·
                        rfl

theorem cell23_4334207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 1, 1, 3].length) (baseStart_4334207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334207 prefixEnd_4334207 := by exact prefixLift 4334207
  have htrace : WordTrace (prefixWord ++ tailWord_4334207) baseStart_4334207 baseEnd_4334207 := by
    simpa [prefixWord, tailWord_4334207, baseEnd_4334207] using wordTrace_append hprefix tailTrace_4334207
  have hstable : (prefixWord ++ tailWord_4334207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334207).length < 2 ^ (prefixWord ++ tailWord_4334207).sum := by decide
  have hdescent : baseEnd_4334207 < baseStart_4334207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334233 : List Nat := [1, 2, 1, 2, 1, 2, 3, 4, 1, 1, 5]
def baseStart_4334233 : Nat := 118140960795 + 4334233 * 2 ^ 59
def prefixEnd_4334233 : Nat := 4983230072969 + 3 ^ 40 * 4334233 * 2
def baseEnd_4334233 : Nat := 2225544797578646027154731

theorem tailTrace_4334233 : CollatzResearch.WordTrace tailWord_4334233 prefixEnd_4334233 2225544797578646027154731 := by
  unfold tailWord_4334233
  simp only [CollatzResearch.WordTrace]
  refine ⟨158082464506821543908943353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105388309671214362605962235 158082464506821543908943353)
  ·
    refine ⟨118561848380116157931707515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158082464506821543908943353 118561848380116157931707515)
    ·
      refine ⟨177842772570174236897561273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118561848380116157931707515 177842772570174236897561273)
      ·
        refine ⟨133382079427630677673170955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177842772570174236897561273 133382079427630677673170955)
        ·
          refine ⟨200073119141446016509756433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133382079427630677673170955 200073119141446016509756433)
          ·
            refine ⟨150054839356084512382317325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200073119141446016509756433 150054839356084512382317325)
            ·
              refine ⟨56270564758531692143368997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150054839356084512382317325 56270564758531692143368997)
              ·
                refine ⟨10550730892224692276881687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56270564758531692143368997 10550730892224692276881687)
                ·
                  refine ⟨15826096338337038415322531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10550730892224692276881687 15826096338337038415322531)
                  ·
                    refine ⟨23739144507505557622983797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15826096338337038415322531 23739144507505557622983797)
                    ·
                      refine ⟨2225544797578646027154731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23739144507505557622983797 2225544797578646027154731)
                      ·
                        rfl

theorem cell23_4334233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_4334233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334233 prefixEnd_4334233 := by exact prefixLift 4334233
  have htrace : WordTrace (prefixWord ++ tailWord_4334233) baseStart_4334233 baseEnd_4334233 := by
    simpa [prefixWord, tailWord_4334233, baseEnd_4334233] using wordTrace_append hprefix tailTrace_4334233
  have hstable : (prefixWord ++ tailWord_4334233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334233).length < 2 ^ (prefixWord ++ tailWord_4334233).sum := by decide
  have hdescent : baseEnd_4334233 < baseStart_4334233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334257 : List Nat := [1, 2, 2, 6, 1, 1, 1, 2, 1, 6]
def baseStart_4334257 : Nat := 118140960795 + 4334257 * 2 ^ 59
def prefixEnd_4334257 : Nat := 4983230072969 + 3 ^ 40 * 4334257 * 2
def baseEnd_4334257 : Nat := 741852373704784644418207

theorem tailTrace_4334257 : CollatzResearch.WordTrace tailWord_4334257 prefixEnd_4334257 741852373704784644418207 := by
  unfold tailWord_4334257
  simp only [CollatzResearch.WordTrace]
  refine ⟨158083339858734596007817025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105388893239156397338544683 158083339858734596007817025)
  ·
    refine ⟨118562504894050947005862769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158083339858734596007817025 118562504894050947005862769)
    ·
      refine ⟨88921878670538210254397077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118562504894050947005862769 88921878670538210254397077)
      ·
        refine ⟨4168213062681478605674863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88921878670538210254397077 4168213062681478605674863)
        ·
          refine ⟨6252319594022217908512295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4168213062681478605674863 6252319594022217908512295)
          ·
            refine ⟨9378479391033326862768443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6252319594022217908512295 9378479391033326862768443)
            ·
              refine ⟨14067719086549990294152665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9378479391033326862768443 14067719086549990294152665)
              ·
                refine ⟨10550789314912492720614499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14067719086549990294152665 10550789314912492720614499)
                ·
                  refine ⟨15826183972368739080921749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10550789314912492720614499 15826183972368739080921749)
                  ·
                    refine ⟨741852373704784644418207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15826183972368739080921749 741852373704784644418207)
                    ·
                      rfl

theorem cell23_4334257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_4334257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334257 prefixEnd_4334257 := by exact prefixLift 4334257
  have htrace : WordTrace (prefixWord ++ tailWord_4334257) baseStart_4334257 baseEnd_4334257 := by
    simpa [prefixWord, tailWord_4334257, baseEnd_4334257] using wordTrace_append hprefix tailTrace_4334257
  have hstable : (prefixWord ++ tailWord_4334257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334257).length < 2 ^ (prefixWord ++ tailWord_4334257).sum := by decide
  have hdescent : baseEnd_4334257 < baseStart_4334257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334297 : List Nat := [1, 2, 1, 2, 3, 2, 1, 5, 2, 1, 3]
def baseStart_4334297 : Nat := 118140960795 + 4334297 * 2 ^ 59
def prefixEnd_4334297 : Nat := 4983230072969 + 3 ^ 40 * 4334297 * 2
def baseEnd_4334297 : Nat := 2225577660340533776754437

theorem tailTrace_4334297 : CollatzResearch.WordTrace tailWord_4334297 prefixEnd_4334297 2225577660340533776754437 := by
  unfold tailWord_4334297
  simp only [CollatzResearch.WordTrace]
  refine ⟨158084798778589682839273145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105389865852393121892848763 158084798778589682839273145)
  ·
    refine ⟨118563599083942262129454859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158084798778589682839273145 118563599083942262129454859)
    ·
      refine ⟨177845398625913393194182289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118563599083942262129454859 177845398625913393194182289)
      ·
        refine ⟨133384048969435044895636717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177845398625913393194182289 133384048969435044895636717)
        ·
          refine ⟨50019018363538141835863769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133384048969435044895636717 50019018363538141835863769)
          ·
            refine ⟨37514263772653606376897827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50019018363538141835863769 37514263772653606376897827)
            ·
              refine ⟨56271395658980409565346741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37514263772653606376897827 56271395658980409565346741)
              ·
                refine ⟨5275443343029413396751257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56271395658980409565346741 5275443343029413396751257)
                ·
                  refine ⟨3956582507272060047563443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5275443343029413396751257 3956582507272060047563443)
                  ·
                    refine ⟨5934873760908090071345165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3956582507272060047563443 5934873760908090071345165)
                    ·
                      refine ⟨2225577660340533776754437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5934873760908090071345165 2225577660340533776754437)
                      ·
                        rfl

theorem cell23_4334297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 1, 3].length) (baseStart_4334297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334297 prefixEnd_4334297 := by exact prefixLift 4334297
  have htrace : WordTrace (prefixWord ++ tailWord_4334297) baseStart_4334297 baseEnd_4334297 := by
    simpa [prefixWord, tailWord_4334297, baseEnd_4334297] using wordTrace_append hprefix tailTrace_4334297
  have hstable : (prefixWord ++ tailWord_4334297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334297).length < 2 ^ (prefixWord ++ tailWord_4334297).sum := by decide
  have hdescent : baseEnd_4334297 < baseStart_4334297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334323 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 5]
def baseStart_4334323 : Nat := 118140960795 + 4334323 * 2 ^ 59
def prefixEnd_4334323 : Nat := 4983230072969 + 3 ^ 40 * 4334323 * 2
def baseEnd_4334323 : Nat := 2225591010837550675029317

theorem tailTrace_4334323 : CollatzResearch.WordTrace tailWord_4334323 prefixEnd_4334323 2225591010837550675029317 := by
  unfold tailWord_4334323
  simp only [CollatzResearch.WordTrace]
  refine ⟨158085747076495489279719623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105390498050996992853146415 158085747076495489279719623)
  ·
    refine ⟨237128620614743233919579435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158085747076495489279719623 237128620614743233919579435)
    ·
      refine ⟨355692930922114850879369153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237128620614743233919579435 355692930922114850879369153)
      ·
        refine ⟨266769698191586138159526865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 355692930922114850879369153 266769698191586138159526865)
        ·
          refine ⟨200077273643689603619645149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266769698191586138159526865 200077273643689603619645149)
          ·
            refine ⟨75028977616383601357366931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 200077273643689603619645149 75028977616383601357366931)
            ·
              refine ⟨112543466424575402036050397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75028977616383601357366931 112543466424575402036050397)
              ·
                refine ⟨42203799909215775763518899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112543466424575402036050397 42203799909215775763518899)
                ·
                  refine ⟨63305699863823663645278349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42203799909215775763518899 63305699863823663645278349)
                  ·
                    refine ⟨23739637448933873866979381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63305699863823663645278349 23739637448933873866979381)
                    ·
                      refine ⟨2225591010837550675029317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23739637448933873866979381 2225591010837550675029317)
                      ·
                        rfl

theorem cell23_4334323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_4334323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334323 prefixEnd_4334323 := by exact prefixLift 4334323
  have htrace : WordTrace (prefixWord ++ tailWord_4334323) baseStart_4334323 baseEnd_4334323 := by
    simpa [prefixWord, tailWord_4334323, baseEnd_4334323] using wordTrace_append hprefix tailTrace_4334323
  have hstable : (prefixWord ++ tailWord_4334323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334323).length < 2 ^ (prefixWord ++ tailWord_4334323).sum := by decide
  have hdescent : baseEnd_4334323 < baseStart_4334323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334325 : List Nat := [1, 3, 6, 1, 2, 1, 1, 2, 2, 4]
def baseStart_4334325 : Nat := 118140960795 + 4334325 * 2 ^ 59
def prefixEnd_4334325 : Nat := 4983230072969 + 3 ^ 40 * 4334325 * 2
def baseEnd_4334325 : Nat := 741864012599619889068103

theorem tailTrace_4334325 : CollatzResearch.WordTrace tailWord_4334325 prefixEnd_4334325 741864012599619889068103 := by
  unfold tailWord_4334325
  simp only [CollatzResearch.WordTrace]
  refine ⟨158085820022488243621292429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105390546681658829080861619 158085820022488243621292429)
  ·
    refine ⟨59282182508433091357984661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158085820022488243621292429 59282182508433091357984661)
    ·
      refine ⟨2778852305082801157405531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59282182508433091357984661 2778852305082801157405531)
      ·
        refine ⟨4168278457624201736108297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2778852305082801157405531 4168278457624201736108297)
        ·
          refine ⟨3126208843218151302081223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4168278457624201736108297 3126208843218151302081223)
          ·
            refine ⟨4689313264827226953121835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3126208843218151302081223 4689313264827226953121835)
            ·
              refine ⟨7033969897240840429682753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4689313264827226953121835 7033969897240840429682753)
              ·
                refine ⟨5275477422930630322262065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7033969897240840429682753 5275477422930630322262065)
                ·
                  refine ⟨3956608067197972741696549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5275477422930630322262065 3956608067197972741696549)
                  ·
                    refine ⟨741864012599619889068103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3956608067197972741696549 741864012599619889068103)
                    ·
                      rfl

theorem cell23_4334325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_4334325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334325 prefixEnd_4334325 := by exact prefixLift 4334325
  have htrace : WordTrace (prefixWord ++ tailWord_4334325) baseStart_4334325 baseEnd_4334325 := by
    simpa [prefixWord, tailWord_4334325, baseEnd_4334325] using wordTrace_append hprefix tailTrace_4334325
  have hstable : (prefixWord ++ tailWord_4334325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334325).length < 2 ^ (prefixWord ++ tailWord_4334325).sum := by decide
  have hdescent : baseEnd_4334325 < baseStart_4334325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334394 : List Nat := [3, 1, 1, 1, 7, 1, 1, 1, 7]
def baseStart_4334394 : Nat := 118140960795 + 4334394 * 2 ^ 59
def prefixEnd_4334394 : Nat := 4983230072969 + 3 ^ 40 * 4334394 * 2
def baseEnd_4334394 : Nat := 247291940884891099693499

theorem tailTrace_4334394 : CollatzResearch.WordTrace tailWord_4334394 prefixEnd_4334394 247291940884891099693499 := by
  unfold tailWord_4334394
  simp only [CollatzResearch.WordTrace]
  refine ⟨39522084164809567101388559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105392224439492178937036157 39522084164809567101388559)
  ·
    refine ⟨59283126247214350652082839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39522084164809567101388559 59283126247214350652082839)
    ·
      refine ⟨88924689370821525978124259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59283126247214350652082839 88924689370821525978124259)
      ·
        refine ⟨133387034056232288967186389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88924689370821525978124259 133387034056232288967186389)
        ·
          refine ⟨3126258610692944272668431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 133387034056232288967186389 3126258610692944272668431)
          ·
            refine ⟨4689387916039416409002647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3126258610692944272668431 4689387916039416409002647)
            ·
              refine ⟨7034081874059124613503971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4689387916039416409002647 7034081874059124613503971)
              ·
                refine ⟨10551122811088686920255957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7034081874059124613503971 10551122811088686920255957)
                ·
                  refine ⟨247291940884891099693499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10551122811088686920255957 247291940884891099693499)
                  ·
                    rfl

theorem cell23_4334394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 7].length) (baseStart_4334394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334394 prefixEnd_4334394 := by exact prefixLift 4334394
  have htrace : WordTrace (prefixWord ++ tailWord_4334394) baseStart_4334394 baseEnd_4334394 := by
    simpa [prefixWord, tailWord_4334394, baseEnd_4334394] using wordTrace_append hprefix tailTrace_4334394
  have hstable : (prefixWord ++ tailWord_4334394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334394).length < 2 ^ (prefixWord ++ tailWord_4334394).sum := by decide
  have hdescent : baseEnd_4334394 < baseStart_4334394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334410 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_4334410 : Nat := 118140960795 + 4334410 * 2 ^ 59
def prefixEnd_4334410 : Nat := 4983230072969 + 3 ^ 40 * 4334410 * 2
def baseEnd_4334410 : Nat := 2225635683654491834641417

theorem tailTrace_4334410 : CollatzResearch.WordTrace tailWord_4334410 prefixEnd_4334410 2225635683654491834641417 := by
  unfold tailWord_4334410
  simp only [CollatzResearch.WordTrace]
  refine ⟨39522230056795075784534171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105392613484786868758757789 39522230056795075784534171)
  ·
    refine ⟨59283345085192613676801257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39522230056795075784534171 59283345085192613676801257)
    ·
      refine ⟨44462508813894460257600943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59283345085192613676801257 44462508813894460257600943)
      ·
        refine ⟨66693763220841690386401415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44462508813894460257600943 66693763220841690386401415)
        ·
          refine ⟨100040644831262535579602123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66693763220841690386401415 100040644831262535579602123)
          ·
            refine ⟨150060967246893803369403185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100040644831262535579602123 150060967246893803369403185)
            ·
              refine ⟨112545725435170352527052389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150060967246893803369403185 112545725435170352527052389)
              ·
                refine ⟨21102323519094441098822323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112545725435170352527052389 21102323519094441098822323)
                ·
                  refine ⟨31653485278641661648233485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21102323519094441098822323 31653485278641661648233485)
                  ·
                    refine ⟨11870056979490623118087557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31653485278641661648233485 11870056979490623118087557)
                    ·
                      refine ⟨2225635683654491834641417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11870056979490623118087557 2225635683654491834641417)
                      ·
                        rfl

theorem cell23_4334410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_4334410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334410 prefixEnd_4334410 := by exact prefixLift 4334410
  have htrace : WordTrace (prefixWord ++ tailWord_4334410) baseStart_4334410 baseEnd_4334410 := by
    simpa [prefixWord, tailWord_4334410, baseEnd_4334410] using wordTrace_append hprefix tailTrace_4334410
  have hstable : (prefixWord ++ tailWord_4334410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334410).length < 2 ^ (prefixWord ++ tailWord_4334410).sum := by decide
  have hdescent : baseEnd_4334410 < baseStart_4334410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334450 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 8]
def baseStart_4334450 : Nat := 118140960795 + 4334450 * 2 ^ 59
def prefixEnd_4334450 : Nat := 4983230072969 + 3 ^ 40 * 4334450 * 2
def baseEnd_4334450 : Nat := 247295135875630186460137

theorem tailTrace_4334450 : CollatzResearch.WordTrace tailWord_4334450 prefixEnd_4334450 247295135875630186460137 := by
  unfold tailWord_4334450
  simp only [CollatzResearch.WordTrace]
  refine ⟨39522594786758847492398201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105393586098023593313061869 39522594786758847492398201)
  ·
    refine ⟨29641946090069135619298651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39522594786758847492398201 29641946090069135619298651)
    ·
      refine ⟨44462919135103703428947977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29641946090069135619298651 44462919135103703428947977)
      ·
        refine ⟨33347189351327777571710983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44462919135103703428947977 33347189351327777571710983)
        ·
          refine ⟨50020784026991666357566475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33347189351327777571710983 50020784026991666357566475)
          ·
            refine ⟨75031176040487499536349713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50020784026991666357566475 75031176040487499536349713)
            ·
              refine ⟨56273382030365624652262285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75031176040487499536349713 56273382030365624652262285)
              ·
                refine ⟨21102518261387109244598357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56273382030365624652262285 21102518261387109244598357)
                ·
                  refine ⟨247295135875630186460137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21102518261387109244598357 247295135875630186460137)
                  ·
                    rfl

theorem cell23_4334450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_4334450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334450 prefixEnd_4334450 := by exact prefixLift 4334450
  have htrace : WordTrace (prefixWord ++ tailWord_4334450) baseStart_4334450 baseEnd_4334450 := by
    simpa [prefixWord, tailWord_4334450, baseEnd_4334450] using wordTrace_append hprefix tailTrace_4334450
  have hstable : (prefixWord ++ tailWord_4334450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334450).length < 2 ^ (prefixWord ++ tailWord_4334450).sum := by decide
  have hdescent : baseEnd_4334450 < baseStart_4334450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334480 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 7, 5]
def baseStart_4334480 : Nat := 118140960795 + 4334480 * 2 ^ 59
def prefixEnd_4334480 : Nat := 4983230072969 + 3 ^ 40 * 4334480 * 2
def baseEnd_4334480 : Nat := 741890542433435520255365

theorem tailTrace_4334480 : CollatzResearch.WordTrace tailWord_4334480 prefixEnd_4334480 741890542433435520255365 := by
  unfold tailWord_4334480
  simp only [CollatzResearch.WordTrace]
  refine ⟨79045736668463352546592447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105394315557951136728789929 79045736668463352546592447)
  ·
    refine ⟨118568605002695028819888671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79045736668463352546592447 118568605002695028819888671)
    ·
      refine ⟨177852907504042543229833007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118568605002695028819888671 177852907504042543229833007)
      ·
        refine ⟨266779361256063814844749511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177852907504042543229833007 266779361256063814844749511)
        ·
          refine ⟨400169041884095722267124267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266779361256063814844749511 400169041884095722267124267)
          ·
            refine ⟨600253562826143583400686401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400169041884095722267124267 600253562826143583400686401)
            ·
              refine ⟨450190172119607687550514801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 600253562826143583400686401 450190172119607687550514801)
              ·
                refine ⟨337642629089705765662886101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 450190172119607687550514801 337642629089705765662886101)
                ·
                  refine ⟨7913499119289978882723893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 337642629089705765662886101 7913499119289978882723893)
                  ·
                    refine ⟨741890542433435520255365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7913499119289978882723893 741890542433435520255365)
                    ·
                      rfl

theorem cell23_4334480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 7, 5].length) (baseStart_4334480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334480 prefixEnd_4334480 := by exact prefixLift 4334480
  have htrace : WordTrace (prefixWord ++ tailWord_4334480) baseStart_4334480 baseEnd_4334480 := by
    simpa [prefixWord, tailWord_4334480, baseEnd_4334480] using wordTrace_append hprefix tailTrace_4334480
  have hstable : (prefixWord ++ tailWord_4334480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334480).length < 2 ^ (prefixWord ++ tailWord_4334480).sum := by decide
  have hdescent : baseEnd_4334480 < baseStart_4334480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334554 : List Nat := [3, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5]
def baseStart_4334554 : Nat := 118140960795 + 4334554 * 2 ^ 59
def prefixEnd_4334554 : Nat := 4983230072969 + 3 ^ 40 * 4334554 * 2
def baseEnd_4334554 : Nat := 2225709624868739271240755

theorem tailTrace_4334554 : CollatzResearch.WordTrace tailWord_4334554 prefixEnd_4334554 2225709624868739271240755 := by
  unfold tailWord_4334554
  simp only [CollatzResearch.WordTrace]
  refine ⟨39523543084664653932844679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105396114892439077154252477 39523543084664653932844679)
  ·
    refine ⟨59285314626996980899267019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39523543084664653932844679 59285314626996980899267019)
    ·
      refine ⟨88927971940495471348900529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59285314626996980899267019 88927971940495471348900529)
      ·
        refine ⟨66695978955371603511675397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88927971940495471348900529 66695978955371603511675397)
        ·
          refine ⟨12505496054132175658439137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66695978955371603511675397 12505496054132175658439137)
          ·
            refine ⟨9379122040599131743829353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12505496054132175658439137 9379122040599131743829353)
            ·
              refine ⟨7034341530449348807872015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9379122040599131743829353 7034341530449348807872015)
              ·
                refine ⟨10551512295674023211808023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7034341530449348807872015 10551512295674023211808023)
                ·
                  refine ⟨15827268443511034817712035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10551512295674023211808023 15827268443511034817712035)
                  ·
                    refine ⟨23740902665266552226568053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15827268443511034817712035 23740902665266552226568053)
                    ·
                      refine ⟨2225709624868739271240755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23740902665266552226568053 2225709624868739271240755)
                      ·
                        rfl

theorem cell23_4334554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_4334554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334554 prefixEnd_4334554 := by exact prefixLift 4334554
  have htrace : WordTrace (prefixWord ++ tailWord_4334554) baseStart_4334554 baseEnd_4334554 := by
    simpa [prefixWord, tailWord_4334554, baseEnd_4334554] using wordTrace_append hprefix tailTrace_4334554
  have hstable : (prefixWord ++ tailWord_4334554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334554).length < 2 ^ (prefixWord ++ tailWord_4334554).sum := by decide
  have hdescent : baseEnd_4334554 < baseStart_4334554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334557 : List Nat := [1, 4, 3, 1, 2, 1, 11]
def baseStart_4334557 : Nat := 118140960795 + 4334557 * 2 ^ 59
def prefixEnd_4334557 : Nat := 4983230072969 + 3 ^ 40 * 4334557 * 2
def baseEnd_4334557 : Nat := 27477915621119787154361

theorem tailTrace_4334557 : CollatzResearch.WordTrace tailWord_4334557 prefixEnd_4334557 27477915621119787154361 := by
  unfold tailWord_4334557
  simp only [CollatzResearch.WordTrace]
  refine ⟨158094281757647747243737925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105396187838431831495825283 158094281757647747243737925)
  ·
    refine ⟨29642677829558952608200861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158094281757647747243737925 29642677829558952608200861)
    ·
      refine ⟨11116004186084607228075323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29642677829558952608200861 11116004186084607228075323)
      ·
        refine ⟨16674006279126910842112985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11116004186084607228075323 16674006279126910842112985)
        ·
          refine ⟨12505504709345183131584739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16674006279126910842112985 12505504709345183131584739)
          ·
            refine ⟨18758257064017774697377109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12505504709345183131584739 18758257064017774697377109)
            ·
              refine ⟨27477915621119787154361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18758257064017774697377109 27477915621119787154361)
              ·
                rfl

theorem cell23_4334557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 11].length) (baseStart_4334557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334557 prefixEnd_4334557 := by exact prefixLift 4334557
  have htrace : WordTrace (prefixWord ++ tailWord_4334557) baseStart_4334557 baseEnd_4334557 := by
    simpa [prefixWord, tailWord_4334557, baseEnd_4334557] using wordTrace_append hprefix tailTrace_4334557
  have hstable : (prefixWord ++ tailWord_4334557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334557).length < 2 ^ (prefixWord ++ tailWord_4334557).sum := by decide
  have hdescent : baseEnd_4334557 < baseStart_4334557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334562 : List Nat := [3, 3, 3, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_4334562 : Nat := 118140960795 + 4334562 * 2 ^ 59
def prefixEnd_4334562 : Nat := 4983230072969 + 3 ^ 40 * 4334562 * 2
def baseEnd_4334562 : Nat := 2225713732713975239940719

theorem tailTrace_4334562 : CollatzResearch.WordTrace tailWord_4334562 prefixEnd_4334562 2225713732713975239940719 := by
  unfold tailWord_4334562
  simp only [CollatzResearch.WordTrace]
  refine ⟨39523616030657408274417485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105396309415086422065113293 39523616030657408274417485)
  ·
    refine ⟨14821356011496528102906557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39523616030657408274417485 14821356011496528102906557)
    ·
      refine ⟨5558008504311198038589959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14821356011496528102906557 5558008504311198038589959)
      ·
        refine ⟨8337012756466797057884939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5558008504311198038589959 8337012756466797057884939)
        ·
          refine ⟨12505519134700195586827409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8337012756466797057884939 12505519134700195586827409)
          ·
            refine ⟨9379139351025146690120557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12505519134700195586827409 9379139351025146690120557)
            ·
              refine ⟨3517177256634430008795209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9379139351025146690120557 3517177256634430008795209)
              ·
                refine ⟨2637882942475822506596407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3517177256634430008795209 2637882942475822506596407)
                ·
                  refine ⟨3956824413713733759894611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2637882942475822506596407 3956824413713733759894611)
                  ·
                    refine ⟨5935236620570600639841917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3956824413713733759894611 5935236620570600639841917)
                    ·
                      refine ⟨2225713732713975239940719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5935236620570600639841917 2225713732713975239940719)
                      ·
                        rfl

theorem cell23_4334562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_4334562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334562 prefixEnd_4334562 := by exact prefixLift 4334562
  have htrace : WordTrace (prefixWord ++ tailWord_4334562) baseStart_4334562 baseEnd_4334562 := by
    simpa [prefixWord, tailWord_4334562, baseEnd_4334562] using wordTrace_append hprefix tailTrace_4334562
  have hstable : (prefixWord ++ tailWord_4334562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334562).length < 2 ^ (prefixWord ++ tailWord_4334562).sum := by decide
  have hdescent : baseEnd_4334562 < baseStart_4334562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334568 : List Nat := [2, 1, 4, 1, 1, 1, 2, 6, 1, 2, 2]
def baseStart_4334568 : Nat := 118140960795 + 4334568 * 2 ^ 59
def prefixEnd_4334568 : Nat := 4983230072969 + 3 ^ 40 * 4334568 * 2
def baseEnd_4334568 : Nat := 2225716813597902216465691

theorem tailTrace_4334568 : CollatzResearch.WordTrace tailWord_4334568 prefixEnd_4334568 2225716813597902216465691 := by
  unfold tailWord_4334568
  simp only [CollatzResearch.WordTrace]
  refine ⟨79047341480303948061194179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105396455307071930748258905 79047341480303948061194179)
  ·
    refine ⟨118571012220455922091791269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79047341480303948061194179 118571012220455922091791269)
    ·
      refine ⟨22232064791335485392210863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118571012220455922091791269 22232064791335485392210863)
      ·
        refine ⟨33348097187003228088316295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22232064791335485392210863 33348097187003228088316295)
        ·
          refine ⟨50022145780504842132474443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33348097187003228088316295 50022145780504842132474443)
          ·
            refine ⟨75033218670757263198711665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50022145780504842132474443 75033218670757263198711665)
            ·
              refine ⟨56274914003067947399033749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75033218670757263198711665 56274914003067947399033749)
              ·
                refine ⟨2637886593893810034329707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56274914003067947399033749 2637886593893810034329707)
                ·
                  refine ⟨3956829890840715051494561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2637886593893810034329707 3956829890840715051494561)
                  ·
                    refine ⟨2967622418130536288620921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3956829890840715051494561 2967622418130536288620921)
                    ·
                      refine ⟨2225716813597902216465691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2967622418130536288620921 2225716813597902216465691)
                      ·
                        rfl

theorem cell23_4334568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_4334568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334568 prefixEnd_4334568 := by exact prefixLift 4334568
  have htrace : WordTrace (prefixWord ++ tailWord_4334568) baseStart_4334568 baseEnd_4334568 := by
    simpa [prefixWord, tailWord_4334568, baseEnd_4334568] using wordTrace_append hprefix tailTrace_4334568
  have hstable : (prefixWord ++ tailWord_4334568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334568).length < 2 ^ (prefixWord ++ tailWord_4334568).sum := by decide
  have hdescent : baseEnd_4334568 < baseStart_4334568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334574 : List Nat := [4, 1, 2, 1, 4, 1, 2, 8]
def baseStart_4334574 : Nat := 118140960795 + 4334574 * 2 ^ 59
def prefixEnd_4334574 : Nat := 4983230072969 + 3 ^ 40 * 4334574 * 2
def baseEnd_4334574 : Nat := 82434070165993673814469

theorem tailTrace_4334574 : CollatzResearch.WordTrace tailWord_4334574 prefixEnd_4334574 82434070165993673814469 := by
  unfold tailWord_4334574
  simp only [CollatzResearch.WordTrace]
  refine ⟨19761862724823269893388347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105396601199057439431404517 19761862724823269893388347)
  ·
    refine ⟨29642794087234904840082521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19761862724823269893388347 29642794087234904840082521)
    ·
      refine ⟨22232095565426178630061891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29642794087234904840082521 22232095565426178630061891)
      ·
        refine ⟨33348143348139267945092837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22232095565426178630061891 33348143348139267945092837)
        ·
          refine ⟨6252776877776112739704907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33348143348139267945092837 6252776877776112739704907)
          ·
            refine ⟨9379165316664169109557361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6252776877776112739704907 9379165316664169109557361)
            ·
              refine ⟨7034373987498126832168021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9379165316664169109557361 7034373987498126832168021)
              ·
                refine ⟨82434070165993673814469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7034373987498126832168021 82434070165993673814469)
                ·
                  rfl

theorem cell23_4334574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 8].length) (baseStart_4334574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334574 prefixEnd_4334574 := by exact prefixLift 4334574
  have htrace : WordTrace (prefixWord ++ tailWord_4334574) baseStart_4334574 baseEnd_4334574 := by
    simpa [prefixWord, tailWord_4334574, baseEnd_4334574] using wordTrace_append hprefix tailTrace_4334574
  have hstable : (prefixWord ++ tailWord_4334574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334574).length < 2 ^ (prefixWord ++ tailWord_4334574).sum := by decide
  have hdescent : baseEnd_4334574 < baseStart_4334574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334578 : List Nat := [3, 2, 1, 5, 1, 1, 1, 3, 2, 4]
def baseStart_4334578 : Nat := 118140960795 + 4334578 * 2 ^ 59
def prefixEnd_4334578 : Nat := 4983230072969 + 3 ^ 40 * 4334578 * 2
def baseEnd_4334578 : Nat := 741907316134815725780215

theorem tailTrace_4334578 : CollatzResearch.WordTrace tailWord_4334578 prefixEnd_4334578 741907316134815725780215 := by
  unfold tailWord_4334578
  simp only [CollatzResearch.WordTrace]
  refine ⟨39523761922642916957563097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105396698460381111886834925 39523761922642916957563097)
  ·
    refine ⟨29642821441982187718172323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39523761922642916957563097 29642821441982187718172323)
    ·
      refine ⟨44464232162973281577258485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29642821441982187718172323 44464232162973281577258485)
      ·
        refine ⟨4168521765278745147867983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44464232162973281577258485 4168521765278745147867983)
        ·
          refine ⟨6252782647918117721801975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4168521765278745147867983 6252782647918117721801975)
          ·
            refine ⟨9379173971877176582702963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6252782647918117721801975 9379173971877176582702963)
            ·
              refine ⟨14068760957815764874054445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9379173971877176582702963 14068760957815764874054445)
              ·
                refine ⟨5275785359180911827770417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14068760957815764874054445 5275785359180911827770417)
                ·
                  refine ⟨3956839019385683870827813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5275785359180911827770417 3956839019385683870827813)
                  ·
                    refine ⟨741907316134815725780215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3956839019385683870827813 741907316134815725780215)
                    ·
                      rfl

theorem cell23_4334578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_4334578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334578 prefixEnd_4334578 := by exact prefixLift 4334578
  have htrace : WordTrace (prefixWord ++ tailWord_4334578) baseStart_4334578 baseEnd_4334578 := by
    simpa [prefixWord, tailWord_4334578, baseEnd_4334578] using wordTrace_append hprefix tailTrace_4334578
  have hstable : (prefixWord ++ tailWord_4334578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334578).length < 2 ^ (prefixWord ++ tailWord_4334578).sum := by decide
  have hdescent : baseEnd_4334578 < baseStart_4334578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334641 : List Nat := [1, 2, 2, 3, 1, 2, 4, 1, 1, 4, 2]
def baseStart_4334641 : Nat := 118140960795 + 4334641 * 2 ^ 59
def prefixEnd_4334641 : Nat := 4983230072969 + 3 ^ 40 * 4334641 * 2
def baseEnd_4334641 : Nat := 2225754297685680430852855

theorem tailTrace_4334641 : CollatzResearch.WordTrace tailWord_4334641 prefixEnd_4334641 2225754297685680430852855 := by
  unfold tailWord_4334641
  simp only [CollatzResearch.WordTrace]
  refine ⟨158097345489343429589795777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105398230326228953059863851 158097345489343429589795777)
  ·
    refine ⟨118573009117007572192346833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158097345489343429589795777 118573009117007572192346833)
    ·
      refine ⟨88929756837755679144260125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118573009117007572192346833 88929756837755679144260125)
      ·
        refine ⟨33348658814158379679097547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88929756837755679144260125 33348658814158379679097547)
        ·
          refine ⟨50022988221237569518646321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33348658814158379679097547 50022988221237569518646321)
          ·
            refine ⟨37517241165928177138984741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50022988221237569518646321 37517241165928177138984741)
            ·
              refine ⟨7034482718611533213559639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37517241165928177138984741 7034482718611533213559639)
              ·
                refine ⟨10551724077917299820339459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7034482718611533213559639 10551724077917299820339459)
                ·
                  refine ⟨15827586116875949730509189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10551724077917299820339459 15827586116875949730509189)
                  ·
                    refine ⟨2967672396914240574470473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15827586116875949730509189 2967672396914240574470473)
                    ·
                      refine ⟨2225754297685680430852855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2967672396914240574470473 2225754297685680430852855)
                      ·
                        rfl

theorem cell23_4334641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_4334641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334641 prefixEnd_4334641 := by exact prefixLift 4334641
  have htrace : WordTrace (prefixWord ++ tailWord_4334641) baseStart_4334641 baseEnd_4334641 := by
    simpa [prefixWord, tailWord_4334641, baseEnd_4334641] using wordTrace_append hprefix tailTrace_4334641
  have hstable : (prefixWord ++ tailWord_4334641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334641).length < 2 ^ (prefixWord ++ tailWord_4334641).sum := by decide
  have hdescent : baseEnd_4334641 < baseStart_4334641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334662 : List Nat := [6, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_4334662 : Nat := 118140960795 + 4334662 * 2 ^ 59
def prefixEnd_4334662 : Nat := 4983230072969 + 3 ^ 40 * 4334662 * 2
def baseEnd_4334662 : Nat := 2225765080779424848690259

theorem tailTrace_4334662 : CollatzResearch.WordTrace tailWord_4334662 prefixEnd_4334662 2225765080779424848690259 := by
  unfold tailWord_4334662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4940565981945854693009695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 105398740948178233450873493 4940565981945854693009695)
  ·
    refine ⟨7410848972918782039514543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4940565981945854693009695 7410848972918782039514543)
    ·
      refine ⟨11116273459378173059271815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7410848972918782039514543 11116273459378173059271815)
      ·
        refine ⟨16674410189067259588907723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11116273459378173059271815 16674410189067259588907723)
        ·
          refine ⟨25011615283600889383361585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16674410189067259588907723 25011615283600889383361585)
          ·
            refine ⟨18758711462700667037521189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25011615283600889383361585 18758711462700667037521189)
            ·
              refine ⟨3517258399256375069535223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18758711462700667037521189 3517258399256375069535223)
              ·
                refine ⟨5275887598884562604302835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3517258399256375069535223 5275887598884562604302835)
                ·
                  refine ⟨7913831398326843906454253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5275887598884562604302835 7913831398326843906454253)
                  ·
                    refine ⟨2967686774372566464920345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7913831398326843906454253 2967686774372566464920345)
                    ·
                      refine ⟨2225765080779424848690259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2967686774372566464920345 2225765080779424848690259)
                      ·
                        rfl

theorem cell23_4334662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_4334662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334662 prefixEnd_4334662 := by exact prefixLift 4334662
  have htrace : WordTrace (prefixWord ++ tailWord_4334662) baseStart_4334662 baseEnd_4334662 := by
    simpa [prefixWord, tailWord_4334662, baseEnd_4334662] using wordTrace_append hprefix tailTrace_4334662
  have hstable : (prefixWord ++ tailWord_4334662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334662).length < 2 ^ (prefixWord ++ tailWord_4334662).sum := by decide
  have hdescent : baseEnd_4334662 < baseStart_4334662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334687 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 7]
def baseStart_4334687 : Nat := 118140960795 + 4334687 * 2 ^ 59
def prefixEnd_4334687 : Nat := 4983230072969 + 3 ^ 40 * 4334687 * 2
def baseEnd_4334687 : Nat := 2225777917795787250877643

theorem tailTrace_4334687 : CollatzResearch.WordTrace tailWord_4334687 prefixEnd_4334687 2225777917795787250877643 := by
  unfold tailWord_4334687
  simp only [CollatzResearch.WordTrace]
  refine ⟨158099023247176779445970315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105399348831451186297313543 158099023247176779445970315)
  ·
    refine ⟨237148534870765169168955473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158099023247176779445970315 237148534870765169168955473)
    ·
      refine ⟨177861401153073876876716605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237148534870765169168955473 177861401153073876876716605)
      ·
        refine ⟨66698025432402703828768727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177861401153073876876716605 66698025432402703828768727)
        ·
          refine ⟨100047038148604055743153091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66698025432402703828768727 100047038148604055743153091)
          ·
            refine ⟨150070557222906083614729637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100047038148604055743153091 150070557222906083614729637)
            ·
              refine ⟨28138229479294890677761807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 150070557222906083614729637 28138229479294890677761807)
              ·
                refine ⟨42207344218942336016642711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28138229479294890677761807 42207344218942336016642711)
                ·
                  refine ⟨63311016328413504024964067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42207344218942336016642711 63311016328413504024964067)
                  ·
                    refine ⟨94966524492620256037446101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63311016328413504024964067 94966524492620256037446101)
                    ·
                      refine ⟨2225777917795787250877643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94966524492620256037446101 2225777917795787250877643)
                      ·
                        rfl

theorem cell23_4334687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_4334687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334687 prefixEnd_4334687 := by exact prefixLift 4334687
  have htrace : WordTrace (prefixWord ++ tailWord_4334687) baseStart_4334687 baseEnd_4334687 := by
    simpa [prefixWord, tailWord_4334687, baseEnd_4334687] using wordTrace_append hprefix tailTrace_4334687
  have hstable : (prefixWord ++ tailWord_4334687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334687).length < 2 ^ (prefixWord ++ tailWord_4334687).sum := by decide
  have hdescent : baseEnd_4334687 < baseStart_4334687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334788 : List Nat := [2, 3, 3, 1, 3, 1, 2, 2, 6]
def baseStart_4334788 : Nat := 118140960795 + 4334788 * 2 ^ 59
def prefixEnd_4334788 : Nat := 4983230072969 + 3 ^ 40 * 4334788 * 2
def baseEnd_4334788 : Nat := 247314419926876817301631

theorem tailTrace_4334788 : CollatzResearch.WordTrace tailWord_4334788 prefixEnd_4334788 247314419926876817301631 := by
  unfold tailWord_4334788
  simp only [CollatzResearch.WordTrace]
  refine ⟨79051353509905436847698509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105401804679873915796931345 79051353509905436847698509)
  ·
    refine ⟨29644257566214538817886941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79051353509905436847698509 29644257566214538817886941)
    ·
      refine ⟨11116596587330452056707603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29644257566214538817886941 11116596587330452056707603)
      ·
        refine ⟨16674894880995678085061405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11116596587330452056707603 16674894880995678085061405)
        ·
          refine ⟨6253085580373379281898027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16674894880995678085061405 6253085580373379281898027)
          ·
            refine ⟨9379628370560068922847041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6253085580373379281898027 9379628370560068922847041)
            ·
              refine ⟨7034721277920051692135281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9379628370560068922847041 7034721277920051692135281)
              ·
                refine ⟨5276040958440038769101461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7034721277920051692135281 5276040958440038769101461)
                ·
                  refine ⟨247314419926876817301631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5276040958440038769101461 247314419926876817301631)
                  ·
                    rfl

theorem cell23_4334788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_4334788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334788 prefixEnd_4334788 := by exact prefixLift 4334788
  have htrace : WordTrace (prefixWord ++ tailWord_4334788) baseStart_4334788 baseEnd_4334788 := by
    simpa [prefixWord, tailWord_4334788, baseEnd_4334788] using wordTrace_append hprefix tailTrace_4334788
  have hstable : (prefixWord ++ tailWord_4334788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334788).length < 2 ^ (prefixWord ++ tailWord_4334788).sum := by decide
  have hdescent : baseEnd_4334788 < baseStart_4334788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
