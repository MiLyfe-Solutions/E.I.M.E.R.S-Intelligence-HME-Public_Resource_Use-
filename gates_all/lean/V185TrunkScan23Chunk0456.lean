import V185TrunkScan23Chunk0455

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2698111 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 3, 7]
def baseStart_2698111 : Nat := 118140960795 + 2698111 * 2 ^ 59
def prefixEnd_2698111 : Nat := 4983230072969 + 3 ^ 40 * 2698111 * 2
def baseEnd_2698111 : Nat := 461809267394399454001373

theorem tailTrace_2698111 : CollatzResearch.WordTrace tailWord_2698111 prefixEnd_2698111 461809267394399454001373 := by
  unfold tailWord_2698111
  simp only [CollatzResearch.WordTrace]
  refine ⟨98408192728212122517694187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65605461818808081678462791 98408192728212122517694187)
  ·
    refine ⟨147612289092318183776541281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98408192728212122517694187 147612289092318183776541281)
    ·
      refine ⟨110709216819238637832405961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147612289092318183776541281 110709216819238637832405961)
      ·
        refine ⟨83031912614428978374304471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110709216819238637832405961 83031912614428978374304471)
        ·
          refine ⟨124547868921643467561456707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83031912614428978374304471 124547868921643467561456707)
          ·
            refine ⟨186821803382465201342185061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124547868921643467561456707 186821803382465201342185061)
            ·
              refine ⟨35029088134212225251659699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186821803382465201342185061 35029088134212225251659699)
              ·
                refine ⟨52543632201318337877489549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35029088134212225251659699 52543632201318337877489549)
                ·
                  refine ⟨19703862075494376704058581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52543632201318337877489549 19703862075494376704058581)
                  ·
                    refine ⟨461809267394399454001373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19703862075494376704058581 461809267394399454001373)
                    ·
                      rfl

theorem cell23_2698111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 7].length) (baseStart_2698111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698111 prefixEnd_2698111 := by exact prefixLift 2698111
  have htrace : WordTrace (prefixWord ++ tailWord_2698111) baseStart_2698111 baseEnd_2698111 := by
    simpa [prefixWord, tailWord_2698111, baseEnd_2698111] using wordTrace_append hprefix tailTrace_2698111
  have hstable : (prefixWord ++ tailWord_2698111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698111).length < 2 ^ (prefixWord ++ tailWord_2698111).sum := by decide
  have hdescent : baseEnd_2698111 < baseStart_2698111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698145 : List Nat := [1, 2, 3, 4, 1, 1, 2, 2, 2, 5]
def baseStart_2698145 : Nat := 118140960795 + 2698145 * 2 ^ 59
def prefixEnd_2698145 : Nat := 4983230072969 + 3 ^ 40 * 2698145 * 2
def baseEnd_2698145 : Nat := 461815086841817076326321

theorem tailTrace_2698145 : CollatzResearch.WordTrace tailWord_2698145 prefixEnd_2698145 461815086841817076326321 := by
  unfold tailWord_2698145
  simp only [CollatzResearch.WordTrace]
  refine ⟨98409432810088946324431889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65606288540059297549621259 98409432810088946324431889)
  ·
    refine ⟨73807074607566709743323917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98409432810088946324431889 73807074607566709743323917)
    ·
      refine ⟨27677652977837516153746469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73807074607566709743323917 27677652977837516153746469)
      ·
        refine ⟨5189559933344534278827463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27677652977837516153746469 5189559933344534278827463)
        ·
          refine ⟨7784339900016801418241195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5189559933344534278827463 7784339900016801418241195)
          ·
            refine ⟨11676509850025202127361793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7784339900016801418241195 11676509850025202127361793)
            ·
              refine ⟨8757382387518901595521345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11676509850025202127361793 8757382387518901595521345)
              ·
                refine ⟨6568036790639176196641009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8757382387518901595521345 6568036790639176196641009)
                ·
                  refine ⟨4926027592979382147480757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6568036790639176196641009 4926027592979382147480757)
                  ·
                    refine ⟨461815086841817076326321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4926027592979382147480757 461815086841817076326321)
                    ·
                      rfl

theorem cell23_2698145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_2698145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698145 prefixEnd_2698145 := by exact prefixLift 2698145
  have htrace : WordTrace (prefixWord ++ tailWord_2698145) baseStart_2698145 baseEnd_2698145 := by
    simpa [prefixWord, tailWord_2698145, baseEnd_2698145] using wordTrace_append hprefix tailTrace_2698145
  have hstable : (prefixWord ++ tailWord_2698145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698145).length < 2 ^ (prefixWord ++ tailWord_2698145).sum := by decide
  have hdescent : baseEnd_2698145 < baseStart_2698145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698188 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 8]
def baseStart_2698188 : Nat := 118140960795 + 2698188 * 2 ^ 59
def prefixEnd_2698188 : Nat := 4983230072969 + 3 ^ 40 * 2698188 * 2
def baseEnd_2698188 : Nat := 153940815577066062304585

theorem tailTrace_2698188 : CollatzResearch.WordTrace tailWord_2698188 prefixEnd_2698188 153940815577066062304585 := by
  unfold tailWord_2698188
  simp only [CollatzResearch.WordTrace]
  refine ⟨49205500574466582334123609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65607334099288776445498145 49205500574466582334123609)
  ·
    refine ⟨36904125430849936750592707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49205500574466582334123609 36904125430849936750592707)
    ·
      refine ⟨55356188146274905125889061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36904125430849936750592707 55356188146274905125889061)
      ·
        refine ⟨10379285277426544711104199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55356188146274905125889061 10379285277426544711104199)
        ·
          refine ⟨15568927916139817066656299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10379285277426544711104199 15568927916139817066656299)
          ·
            refine ⟨23353391874209725599984449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15568927916139817066656299 23353391874209725599984449)
            ·
              refine ⟨17515043905657294199988337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23353391874209725599984449 17515043905657294199988337)
              ·
                refine ⟨13136282929242970649991253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17515043905657294199988337 13136282929242970649991253)
                ·
                  refine ⟨153940815577066062304585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13136282929242970649991253 153940815577066062304585)
                  ·
                    rfl

theorem cell23_2698188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 8].length) (baseStart_2698188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698188 prefixEnd_2698188 := by exact prefixLift 2698188
  have htrace : WordTrace (prefixWord ++ tailWord_2698188) baseStart_2698188 baseEnd_2698188 := by
    simpa [prefixWord, tailWord_2698188, baseEnd_2698188] using wordTrace_append hprefix tailTrace_2698188
  have hstable : (prefixWord ++ tailWord_2698188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698188).length < 2 ^ (prefixWord ++ tailWord_2698188).sum := by decide
  have hdescent : baseEnd_2698188 < baseStart_2698188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698205 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 8]
def baseStart_2698205 : Nat := 118140960795 + 2698205 * 2 ^ 59
def prefixEnd_2698205 : Nat := 4983230072969 + 3 ^ 40 * 2698205 * 2
def baseEnd_2698205 : Nat := 153941785484968999358743

theorem tailTrace_2698205 : CollatzResearch.WordTrace tailWord_2698205 prefixEnd_2698205 153941785484968999358743 := by
  unfold tailWord_2698205
  simp only [CollatzResearch.WordTrace]
  refine ⟨98411621189871576571616069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65607747459914384381077379 98411621189871576571616069)
  ·
    refine ⟨18452178973100920607178013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98411621189871576571616069 18452178973100920607178013)
    ·
      refine ⟨6919567114912845227691755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18452178973100920607178013 6919567114912845227691755)
      ·
        refine ⟨10379350672369267841537633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6919567114912845227691755 10379350672369267841537633)
        ·
          refine ⟨7784513004276950881153225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10379350672369267841537633 7784513004276950881153225)
          ·
            refine ⟨5838384753207713160864919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7784513004276950881153225 5838384753207713160864919)
            ·
              refine ⟨8757577129811569741297379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5838384753207713160864919 8757577129811569741297379)
              ·
                refine ⟨13136365694717354611946069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8757577129811569741297379 13136365694717354611946069)
                ·
                  refine ⟨153941785484968999358743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13136365694717354611946069 153941785484968999358743)
                  ·
                    rfl

theorem cell23_2698205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_2698205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698205 prefixEnd_2698205 := by exact prefixLift 2698205
  have htrace : WordTrace (prefixWord ++ tailWord_2698205) baseStart_2698205 baseEnd_2698205 := by
    simpa [prefixWord, tailWord_2698205, baseEnd_2698205] using wordTrace_append hprefix tailTrace_2698205
  have hstable : (prefixWord ++ tailWord_2698205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698205).length < 2 ^ (prefixWord ++ tailWord_2698205).sum := by decide
  have hdescent : baseEnd_2698205 < baseStart_2698205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698265 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 4, 4]
def baseStart_2698265 : Nat := 118140960795 + 2698265 * 2 ^ 59
def prefixEnd_2698265 : Nat := 4983230072969 + 3 ^ 40 * 2698265 * 2
def baseEnd_2698265 : Nat := 461835626067996919826137

theorem tailTrace_2698265 : CollatzResearch.WordTrace tailWord_2698265 prefixEnd_2698265 461835626067996919826137 := by
  unfold tailWord_2698265
  simp only [CollatzResearch.WordTrace]
  refine ⟨98413809569654206818800249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65609206379769471212533499 98413809569654206818800249)
  ·
    refine ⟨73810357177240655114100187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98413809569654206818800249 73810357177240655114100187)
    ·
      refine ⟨110715535765860982671150281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73810357177240655114100187 110715535765860982671150281)
      ·
        refine ⟨83036651824395737003362711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110715535765860982671150281 83036651824395737003362711)
        ·
          refine ⟨124554977736593605505044067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83036651824395737003362711 124554977736593605505044067)
          ·
            refine ⟨186832466604890408257566101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124554977736593605505044067 186832466604890408257566101)
            ·
              refine ⟨8757771872104237887073411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 186832466604890408257566101 8757771872104237887073411)
              ·
                refine ⟨13136657808156356830610117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8757771872104237887073411 13136657808156356830610117)
                ·
                  refine ⟨2463123339029316905739397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13136657808156356830610117 2463123339029316905739397)
                  ·
                    refine ⟨461835626067996919826137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2463123339029316905739397 461835626067996919826137)
                    ·
                      rfl

theorem cell23_2698265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 4].length) (baseStart_2698265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698265 prefixEnd_2698265 := by exact prefixLift 2698265
  have htrace : WordTrace (prefixWord ++ tailWord_2698265) baseStart_2698265 baseEnd_2698265 := by
    simpa [prefixWord, tailWord_2698265, baseEnd_2698265] using wordTrace_append hprefix tailTrace_2698265
  have hstable : (prefixWord ++ tailWord_2698265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698265).length < 2 ^ (prefixWord ++ tailWord_2698265).sum := by decide
  have hdescent : baseEnd_2698265 < baseStart_2698265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698266 : List Nat := [3, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3]
def baseStart_2698266 : Nat := 118140960795 + 2698266 * 2 ^ 59
def prefixEnd_2698266 : Nat := 4983230072969 + 3 ^ 40 * 2698266 * 2
def baseEnd_2698266 : Nat := 1385507391684645255565907

theorem tailTrace_2698266 : CollatzResearch.WordTrace tailWord_2698266 prefixEnd_2698266 1385507391684645255565907 := by
  unfold tailWord_2698266
  simp only [CollatzResearch.WordTrace]
  refine ⟨24603461510662645997396663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65609230695100389326391101 24603461510662645997396663)
  ·
    refine ⟨36905192265993968996094995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24603461510662645997396663 36905192265993968996094995)
    ·
      refine ⟨55357788398990953494142493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36905192265993968996094995 55357788398990953494142493)
      ·
        refine ⟨20759170649621607560303435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55357788398990953494142493 20759170649621607560303435)
        ·
          refine ⟨31138755974432411340455153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20759170649621607560303435 31138755974432411340455153)
          ·
            refine ⟨23354066980824308505341365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31138755974432411340455153 23354066980824308505341365)
            ·
              refine ⟨2189443779452278922375753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23354066980824308505341365 2189443779452278922375753)
              ·
                refine ⟨1642082834589209191781815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2189443779452278922375753 1642082834589209191781815)
                ·
                  refine ⟨2463124251883813787672723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1642082834589209191781815 2463124251883813787672723)
                  ·
                    refine ⟨3694686377825720681509085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2463124251883813787672723 3694686377825720681509085)
                    ·
                      refine ⟨1385507391684645255565907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3694686377825720681509085 1385507391684645255565907)
                      ·
                        rfl

theorem cell23_2698266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_2698266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698266 prefixEnd_2698266 := by exact prefixLift 2698266
  have htrace : WordTrace (prefixWord ++ tailWord_2698266) baseStart_2698266 baseEnd_2698266 := by
    simpa [prefixWord, tailWord_2698266, baseEnd_2698266] using wordTrace_append hprefix tailTrace_2698266
  have hstable : (prefixWord ++ tailWord_2698266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698266).length < 2 ^ (prefixWord ++ tailWord_2698266).sum := by decide
  have hdescent : baseEnd_2698266 < baseStart_2698266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698275 : List Nat := [1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 5]
def baseStart_2698275 : Nat := 118140960795 + 2698275 * 2 ^ 59
def prefixEnd_2698275 : Nat := 4983230072969 + 3 ^ 40 * 2698275 * 2
def baseEnd_2698275 : Nat := 1385512013010535720353365

theorem tailTrace_2698275 : CollatzResearch.WordTrace tailWord_2698275 prefixEnd_2698275 1385512013010535720353365 := by
  unfold tailWord_2698275
  simp only [CollatzResearch.WordTrace]
  refine ⟨98414174299617978526664279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65609449533078652351109519 98414174299617978526664279)
  ·
    refine ⟨147621261449426967789996419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98414174299617978526664279 147621261449426967789996419)
    ·
      refine ⟨221431892174140451684994629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147621261449426967789996419 221431892174140451684994629)
      ·
        refine ⟨41518479782651334690936493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221431892174140451684994629 41518479782651334690936493)
        ·
          refine ⟨15569429918494250509101185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41518479782651334690936493 15569429918494250509101185)
          ·
            refine ⟨11677072438870687881825889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15569429918494250509101185 11677072438870687881825889)
            ·
              refine ⟨8757804329153015911369417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11677072438870687881825889 8757804329153015911369417)
              ·
                refine ⟨6568353246864761933527063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8757804329153015911369417 6568353246864761933527063)
                ·
                  refine ⟨9852529870297142900290595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6568353246864761933527063 9852529870297142900290595)
                  ·
                    refine ⟨14778794805445714350435893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9852529870297142900290595 14778794805445714350435893)
                    ·
                      refine ⟨1385512013010535720353365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14778794805445714350435893 1385512013010535720353365)
                      ·
                        rfl

theorem cell23_2698275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_2698275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698275 prefixEnd_2698275 := by exact prefixLift 2698275
  have htrace : WordTrace (prefixWord ++ tailWord_2698275) baseStart_2698275 baseEnd_2698275 := by
    simpa [prefixWord, tailWord_2698275, baseEnd_2698275] using wordTrace_append hprefix tailTrace_2698275
  have hstable : (prefixWord ++ tailWord_2698275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698275).length < 2 ^ (prefixWord ++ tailWord_2698275).sum := by decide
  have hdescent : baseEnd_2698275 < baseStart_2698275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698302 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_2698302 : Nat := 118140960795 + 2698302 * 2 ^ 59
def prefixEnd_2698302 : Nat := 4983230072969 + 3 ^ 40 * 2698302 * 2
def baseEnd_2698302 : Nat := 1385525876988207114715741

theorem tailTrace_2698302 : CollatzResearch.WordTrace tailWord_2698302 prefixEnd_2698302 1385525876988207114715741 := by
  unfold tailWord_2698302
  simp only [CollatzResearch.WordTrace]
  refine ⟨12301894883815020267237145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65610106047013441425264773 12301894883815020267237145)
  ·
    refine ⟨9226421162861265200427859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12301894883815020267237145 9226421162861265200427859)
    ·
      refine ⟨13839631744291897800641789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9226421162861265200427859 13839631744291897800641789)
      ·
        refine ⟨5189861904109461675240671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13839631744291897800641789 5189861904109461675240671)
        ·
          refine ⟨7784792856164192512861007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5189861904109461675240671 7784792856164192512861007)
          ·
            refine ⟨11677189284246288769291511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7784792856164192512861007 11677189284246288769291511)
            ·
              refine ⟨17515783926369433153937267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11677189284246288769291511 17515783926369433153937267)
              ·
                refine ⟨26273675889554149730905901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17515783926369433153937267 26273675889554149730905901)
                ·
                  refine ⟨9852628458582806149089713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26273675889554149730905901 9852628458582806149089713)
                  ·
                    refine ⟨7389471343937104611817285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9852628458582806149089713 7389471343937104611817285)
                    ·
                      refine ⟨1385525876988207114715741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7389471343937104611817285 1385525876988207114715741)
                      ·
                        rfl

theorem cell23_2698302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_2698302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698302 prefixEnd_2698302 := by exact prefixLift 2698302
  have htrace : WordTrace (prefixWord ++ tailWord_2698302) baseStart_2698302 baseEnd_2698302 := by
    simpa [prefixWord, tailWord_2698302, baseEnd_2698302] using wordTrace_append hprefix tailTrace_2698302
  have hstable : (prefixWord ++ tailWord_2698302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698302).length < 2 ^ (prefixWord ++ tailWord_2698302).sum := by decide
  have hdescent : baseEnd_2698302 < baseStart_2698302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698349 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 3, 3, 2]
def baseStart_2698349 : Nat := 118140960795 + 2698349 * 2 ^ 59
def prefixEnd_2698349 : Nat := 4983230072969 + 3 ^ 40 * 2698349 * 2
def baseEnd_2698349 : Nat := 1385550010578968430828025

theorem tailTrace_2698349 : CollatzResearch.WordTrace tailWord_2698349 prefixEnd_2698349 1385550010578968430828025 := by
  unfold tailWord_2698349
  simp only [CollatzResearch.WordTrace]
  refine ⟨98416873301349889164858101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65611248867566592776572067 98416873301349889164858101)
  ·
    refine ⟨9226581872001552109205447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98416873301349889164858101 9226581872001552109205447)
    ·
      refine ⟨13839872808002328163808171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9226581872001552109205447 13839872808002328163808171)
      ·
        refine ⟨20759809212003492245712257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13839872808002328163808171 20759809212003492245712257)
        ·
          refine ⟨15569856909002619184284193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20759809212003492245712257 15569856909002619184284193)
          ·
            refine ⟨11677392681751964388213145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15569856909002619184284193 11677392681751964388213145)
            ·
              refine ⟨8758044511313973291159859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11677392681751964388213145 8758044511313973291159859)
              ·
                refine ⟨13137066766970959936739789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8758044511313973291159859 13137066766970959936739789)
                ·
                  refine ⟨4926400037614109976277421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13137066766970959936739789 4926400037614109976277421)
                  ·
                    refine ⟨1847400014105291241104033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4926400037614109976277421 1847400014105291241104033)
                    ·
                      refine ⟨1385550010578968430828025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1847400014105291241104033 1385550010578968430828025)
                      ·
                        rfl

theorem cell23_2698349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_2698349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698349 prefixEnd_2698349 := by exact prefixLift 2698349
  have htrace : WordTrace (prefixWord ++ tailWord_2698349) baseStart_2698349 baseEnd_2698349 := by
    simpa [prefixWord, tailWord_2698349, baseEnd_2698349] using wordTrace_append hprefix tailTrace_2698349
  have hstable : (prefixWord ++ tailWord_2698349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698349).length < 2 ^ (prefixWord ++ tailWord_2698349).sum := by decide
  have hdescent : baseEnd_2698349 < baseStart_2698349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698365 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_2698365 : Nat := 118140960795 + 2698365 * 2 ^ 59
def prefixEnd_2698365 : Nat := 4983230072969 + 3 ^ 40 * 2698365 * 2
def baseEnd_2698365 : Nat := 1385558226269440368227951

theorem tailTrace_2698365 : CollatzResearch.WordTrace tailWord_2698365 prefixEnd_2698365 1385558226269440368227951 := by
  unfold tailWord_2698365
  simp only [CollatzResearch.WordTrace]
  refine ⟨98417456869291923897440549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65611637912861282598293699 98417456869291923897440549)
  ·
    refine ⟨18453273162992235730770103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98417456869291923897440549 18453273162992235730770103)
    ·
      refine ⟨27679909744488353596155155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18453273162992235730770103 27679909744488353596155155)
      ·
        refine ⟨41519864616732530394232733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27679909744488353596155155 41519864616732530394232733)
        ·
          refine ⟨15569949231274698897837275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41519864616732530394232733 15569949231274698897837275)
          ·
            refine ⟨23354923846912048346755913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15569949231274698897837275 23354923846912048346755913)
            ·
              refine ⟨17516192885184036260066935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23354923846912048346755913 17516192885184036260066935)
              ·
                refine ⟨26274289327776054390100403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17516192885184036260066935 26274289327776054390100403)
                ·
                  refine ⟨39411433991664081585150605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26274289327776054390100403 39411433991664081585150605)
                  ·
                    refine ⟨14779287746874030594431477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39411433991664081585150605 14779287746874030594431477)
                    ·
                      refine ⟨1385558226269440368227951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14779287746874030594431477 1385558226269440368227951)
                      ·
                        rfl

theorem cell23_2698365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_2698365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698365 prefixEnd_2698365 := by exact prefixLift 2698365
  have htrace : WordTrace (prefixWord ++ tailWord_2698365) baseStart_2698365 baseEnd_2698365 := by
    simpa [prefixWord, tailWord_2698365, baseEnd_2698365] using wordTrace_append hprefix tailTrace_2698365
  have hstable : (prefixWord ++ tailWord_2698365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698365).length < 2 ^ (prefixWord ++ tailWord_2698365).sum := by decide
  have hdescent : baseEnd_2698365 < baseStart_2698365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698373 : List Nat := [1, 3, 1, 1, 7, 1, 1, 2, 2, 1, 3]
def baseStart_2698373 : Nat := 118140960795 + 2698373 * 2 ^ 59
def prefixEnd_2698373 : Nat := 4983230072969 + 3 ^ 40 * 2698373 * 2
def baseEnd_2698373 : Nat := 1385562334114676336927915

theorem tailTrace_2698373 : CollatzResearch.WordTrace tailWord_2698373 prefixEnd_2698373 1385562334114676336927915 := by
  unfold tailWord_2698373
  simp only [CollatzResearch.WordTrace]
  refine ⟨98417748653262941263731773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65611832435508627509154515 98417748653262941263731773)
  ·
    refine ⟨36906655744973602973899415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98417748653262941263731773 36906655744973602973899415)
    ·
      refine ⟨55359983617460404460849123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36906655744973602973899415 55359983617460404460849123)
      ·
        refine ⟨83039975426190606691273685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55359983617460404460849123 83039975426190606691273685)
        ·
          refine ⟨1946249424051342344326727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 83039975426190606691273685 1946249424051342344326727)
          ·
            refine ⟨2919374136077013516490091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1946249424051342344326727 2919374136077013516490091)
            ·
              refine ⟨4379061204115520274735137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2919374136077013516490091 4379061204115520274735137)
              ·
                refine ⟨3284295903086640206051353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4379061204115520274735137 3284295903086640206051353)
                ·
                  refine ⟨2463221927314980154538515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3284295903086640206051353 2463221927314980154538515)
                  ·
                    refine ⟨3694832890972470231807773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2463221927314980154538515 3694832890972470231807773)
                    ·
                      refine ⟨1385562334114676336927915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3694832890972470231807773 1385562334114676336927915)
                      ·
                        rfl

theorem cell23_2698373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 2, 1, 3].length) (baseStart_2698373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698373 prefixEnd_2698373 := by exact prefixLift 2698373
  have htrace : WordTrace (prefixWord ++ tailWord_2698373) baseStart_2698373 baseEnd_2698373 := by
    simpa [prefixWord, tailWord_2698373, baseEnd_2698373] using wordTrace_append hprefix tailTrace_2698373
  have hstable : (prefixWord ++ tailWord_2698373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698373).length < 2 ^ (prefixWord ++ tailWord_2698373).sum := by decide
  have hdescent : baseEnd_2698373 < baseStart_2698373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698392 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 2, 2, 4]
def baseStart_2698392 : Nat := 118140960795 + 2698392 * 2 ^ 59
def prefixEnd_2698392 : Nat := 4983230072969 + 3 ^ 40 * 2698392 * 2
def baseEnd_2698392 : Nat := 1385572090247111762590327

theorem tailTrace_2698392 : CollatzResearch.WordTrace tailWord_2698392 prefixEnd_2698392 1385572090247111762590327 := by
  unfold tailWord_2698392
  simp only [CollatzResearch.WordTrace]
  refine ⟨49209220820097053754336715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65612294426796071672448953 49209220820097053754336715)
  ·
    refine ⟨73813831230145580631505073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49209220820097053754336715 73813831230145580631505073)
    ·
      refine ⟨55360373422609185473628805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73813831230145580631505073 55360373422609185473628805)
      ·
        refine ⟨10380070016739222276305401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55360373422609185473628805 10380070016739222276305401)
        ·
          refine ⟨7785052512554416707229051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10380070016739222276305401 7785052512554416707229051)
          ·
            refine ⟨11677578768831625060843577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7785052512554416707229051 11677578768831625060843577)
            ·
              refine ⟨8758184076623718795632683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11677578768831625060843577 8758184076623718795632683)
              ·
                refine ⟨13137276114935578193449025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8758184076623718795632683 13137276114935578193449025)
                ·
                  refine ⟨9852957086201683645086769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13137276114935578193449025 9852957086201683645086769)
                  ·
                    refine ⟨7389717814651262733815077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9852957086201683645086769 7389717814651262733815077)
                    ·
                      refine ⟨1385572090247111762590327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7389717814651262733815077 1385572090247111762590327)
                      ·
                        rfl

theorem cell23_2698392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_2698392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698392 prefixEnd_2698392 := by exact prefixLift 2698392
  have htrace : WordTrace (prefixWord ++ tailWord_2698392) baseStart_2698392 baseEnd_2698392 := by
    simpa [prefixWord, tailWord_2698392, baseEnd_2698392] using wordTrace_append hprefix tailTrace_2698392
  have hstable : (prefixWord ++ tailWord_2698392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698392).length < 2 ^ (prefixWord ++ tailWord_2698392).sum := by decide
  have hdescent : baseEnd_2698392 < baseStart_2698392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698396 : List Nat := [2, 2, 3, 2, 1, 4, 1, 1, 1, 4, 2]
def baseStart_2698396 : Nat := 118140960795 + 2698396 * 2 ^ 59
def prefixEnd_2698396 : Nat := 4983230072969 + 3 ^ 40 * 2698396 * 2
def baseEnd_2698396 : Nat := 1385574144169729746940309

theorem tailTrace_2698396 : CollatzResearch.WordTrace tailWord_2698396 prefixEnd_2698396 1385574144169729746940309 := by
  unfold tailWord_2698396
  simp only [CollatzResearch.WordTrace]
  refine ⟨49209293766089808095909521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65612391688119744127879361 49209293766089808095909521)
  ·
    refine ⟨36906970324567356071932141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49209293766089808095909521 36906970324567356071932141)
    ·
      refine ⟨13840113871712758526974553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36906970324567356071932141 13840113871712758526974553)
      ·
        refine ⟨10380085403784568895230915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13840113871712758526974553 10380085403784568895230915)
        ·
          refine ⟨15570128105676853342846373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10380085403784568895230915 15570128105676853342846373)
          ·
            refine ⟨2919399019814410001783695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15570128105676853342846373 2919399019814410001783695)
            ·
              refine ⟨4379098529721615002675543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2919399019814410001783695 4379098529721615002675543)
              ·
                refine ⟨6568647794582422504013315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4379098529721615002675543 6568647794582422504013315)
                ·
                  refine ⟨9852971691873633756019973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6568647794582422504013315 9852971691873633756019973)
                  ·
                    refine ⟨1847432192226306329253745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9852971691873633756019973 1847432192226306329253745)
                    ·
                      refine ⟨1385574144169729746940309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1847432192226306329253745 1385574144169729746940309)
                      ·
                        rfl

theorem cell23_2698396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_2698396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698396 prefixEnd_2698396 := by exact prefixLift 2698396
  have htrace : WordTrace (prefixWord ++ tailWord_2698396) baseStart_2698396 baseEnd_2698396 := by
    simpa [prefixWord, tailWord_2698396, baseEnd_2698396] using wordTrace_append hprefix tailTrace_2698396
  have hstable : (prefixWord ++ tailWord_2698396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698396).length < 2 ^ (prefixWord ++ tailWord_2698396).sum := by decide
  have hdescent : baseEnd_2698396 < baseStart_2698396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698415 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 1, 7]
def baseStart_2698415 : Nat := 118140960795 + 2698415 * 2 ^ 59
def prefixEnd_2698415 : Nat := 4983230072969 + 3 ^ 40 * 2698415 * 2
def baseEnd_2698415 : Nat := 461861300100721724200907

theorem tailTrace_2698415 : CollatzResearch.WordTrace tailWord_2698415 prefixEnd_2698415 461861300100721724200907 := by
  unfold tailWord_2698415
  simp only [CollatzResearch.WordTrace]
  refine ⟨98419280519110782436760699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65612853679407188291173799 98419280519110782436760699)
  ·
    refine ⟨147628920778666173655141049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98419280519110782436760699 147628920778666173655141049)
    ·
      refine ⟨110721690583999630241355787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147628920778666173655141049 110721690583999630241355787)
      ·
        refine ⟨166082535875999445362033681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110721690583999630241355787 166082535875999445362033681)
        ·
          refine ⟨124561901906999584021525261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166082535875999445362033681 124561901906999584021525261)
          ·
            refine ⟨46710713215124844008071973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124561901906999584021525261 46710713215124844008071973)
            ·
              refine ⟨8758258727835908251513495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46710713215124844008071973 8758258727835908251513495)
              ·
                refine ⟨13137388091753862377270243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8758258727835908251513495 13137388091753862377270243)
                ·
                  refine ⟨19706082137630793565905365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13137388091753862377270243 19706082137630793565905365)
                  ·
                    refine ⟨461861300100721724200907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19706082137630793565905365 461861300100721724200907)
                    ·
                      rfl

theorem cell23_2698415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 7].length) (baseStart_2698415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698415 prefixEnd_2698415 := by exact prefixLift 2698415
  have htrace : WordTrace (prefixWord ++ tailWord_2698415) baseStart_2698415 baseEnd_2698415 := by
    simpa [prefixWord, tailWord_2698415, baseEnd_2698415] using wordTrace_append hprefix tailTrace_2698415
  have hstable : (prefixWord ++ tailWord_2698415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698415).length < 2 ^ (prefixWord ++ tailWord_2698415).sum := by decide
  have hdescent : baseEnd_2698415 < baseStart_2698415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698435 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 4]
def baseStart_2698435 : Nat := 118140960795 + 2698435 * 2 ^ 59
def prefixEnd_2698435 : Nat := 4983230072969 + 3 ^ 40 * 2698435 * 2
def baseEnd_2698435 : Nat := 1385594169915255094352629

theorem tailTrace_2698435 : CollatzResearch.WordTrace tailWord_2698435 prefixEnd_2698435 1385594169915255094352629 := by
  unfold tailWord_2698435
  simp only [CollatzResearch.WordTrace]
  refine ⟨98420009979038325852488759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65613339986025550568325839 98420009979038325852488759)
  ·
    refine ⟨147630014968557488778733139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98420009979038325852488759 147630014968557488778733139)
    ·
      refine ⟨221445022452836233168099709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147630014968557488778733139 221445022452836233168099709)
      ·
        refine ⟨83041883419813587438037391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221445022452836233168099709 83041883419813587438037391)
        ·
          refine ⟨124562825129720381157056087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83041883419813587438037391 124562825129720381157056087)
          ·
            refine ⟨186844237694580571735584131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124562825129720381157056087 186844237694580571735584131)
            ·
              refine ⟨280266356541870857603376197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186844237694580571735584131 280266356541870857603376197)
              ·
                refine ⟨52549941851600785800633037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 280266356541870857603376197 52549941851600785800633037)
                ·
                  refine ⟨19706228194350294675237389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52549941851600785800633037 19706228194350294675237389)
                  ·
                    refine ⟨7389835572881360503214021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19706228194350294675237389 7389835572881360503214021)
                    ·
                      refine ⟨1385594169915255094352629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7389835572881360503214021 1385594169915255094352629)
                      ·
                        rfl

theorem cell23_2698435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_2698435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698435 prefixEnd_2698435 := by exact prefixLift 2698435
  have htrace : WordTrace (prefixWord ++ tailWord_2698435) baseStart_2698435 baseEnd_2698435 := by
    simpa [prefixWord, tailWord_2698435, baseEnd_2698435] using wordTrace_append hprefix tailTrace_2698435
  have hstable : (prefixWord ++ tailWord_2698435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698435).length < 2 ^ (prefixWord ++ tailWord_2698435).sum := by decide
  have hdescent : baseEnd_2698435 < baseStart_2698435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698436 : List Nat := [2, 3, 3, 1, 4, 1, 1, 1, 7]
def baseStart_2698436 : Nat := 118140960795 + 2698436 * 2 ^ 59
def prefixEnd_2698436 : Nat := 4983230072969 + 3 ^ 40 * 2698436 * 2
def baseEnd_2698436 : Nat := 153954964821767732271125

theorem tailTrace_2698436 : CollatzResearch.WordTrace tailWord_2698436 prefixEnd_2698436 153954964821767732271125 := by
  unfold tailWord_2698436
  simp only [CollatzResearch.WordTrace]
  refine ⟨49210023226017351511637581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65613364301356468682183441 49210023226017351511637581)
  ·
    refine ⟨18453758709756506816864093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49210023226017351511637581 18453758709756506816864093)
    ·
      refine ⟨6920159516158690056324035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18453758709756506816864093 6920159516158690056324035)
      ·
        refine ⟨10380239274238035084486053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6920159516158690056324035 10380239274238035084486053)
        ·
          refine ⟨1946294863919631578341135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10380239274238035084486053 1946294863919631578341135)
          ·
            refine ⟨2919442295879447367511703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1946294863919631578341135 2919442295879447367511703)
            ·
              refine ⟨4379163443819171051267555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2919442295879447367511703 4379163443819171051267555)
              ·
                refine ⟨6568745165728756576901333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4379163443819171051267555 6568745165728756576901333)
                ·
                  refine ⟨153954964821767732271125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6568745165728756576901333 153954964821767732271125)
                  ·
                    rfl

theorem cell23_2698436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_2698436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698436 prefixEnd_2698436 := by exact prefixLift 2698436
  have htrace : WordTrace (prefixWord ++ tailWord_2698436) baseStart_2698436 baseEnd_2698436 := by
    simpa [prefixWord, tailWord_2698436, baseEnd_2698436] using wordTrace_append hprefix tailTrace_2698436
  have hstable : (prefixWord ++ tailWord_2698436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698436).length < 2 ^ (prefixWord ++ tailWord_2698436).sum := by decide
  have hdescent : baseEnd_2698436 < baseStart_2698436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698442 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_2698442 : Nat := 118140960795 + 2698442 * 2 ^ 59
def prefixEnd_2698442 : Nat := 4983230072969 + 3 ^ 40 * 2698442 * 2
def baseEnd_2698442 : Nat := 1385597764279836566965097

theorem tailTrace_2698442 : CollatzResearch.WordTrace tailWord_2698442 prefixEnd_2698442 1385597764279836566965097 := by
  unfold tailWord_2698442
  simp only [CollatzResearch.WordTrace]
  refine ⟨24605066322503241511998395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65613510193341977365329053 24605066322503241511998395)
  ·
    refine ⟨36907599483754862267997593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24605066322503241511998395 36907599483754862267997593)
    ·
      refine ⟨27680699612816146700998195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36907599483754862267997593 27680699612816146700998195)
      ·
        refine ⟨41521049419224220051497293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27680699612816146700998195 41521049419224220051497293)
        ·
          refine ⟨15570393532209082519311485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41521049419224220051497293 15570393532209082519311485)
          ·
            refine ⟨5838897574578405944741807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15570393532209082519311485 5838897574578405944741807)
            ·
              refine ⟨8758346361867608917112711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5838897574578405944741807 8758346361867608917112711)
              ·
                refine ⟨13137519542801413375669067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8758346361867608917112711 13137519542801413375669067)
                ·
                  refine ⟨19706279314202120063503601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13137519542801413375669067 19706279314202120063503601)
                  ·
                    refine ⟨14779709485651590047627701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19706279314202120063503601 14779709485651590047627701)
                    ·
                      refine ⟨1385597764279836566965097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14779709485651590047627701 1385597764279836566965097)
                      ·
                        rfl

theorem cell23_2698442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_2698442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698442 prefixEnd_2698442 := by exact prefixLift 2698442
  have htrace : WordTrace (prefixWord ++ tailWord_2698442) baseStart_2698442 baseEnd_2698442 := by
    simpa [prefixWord, tailWord_2698442, baseEnd_2698442] using wordTrace_append hprefix tailTrace_2698442
  have hstable : (prefixWord ++ tailWord_2698442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698442).length < 2 ^ (prefixWord ++ tailWord_2698442).sum := by decide
  have hdescent : baseEnd_2698442 < baseStart_2698442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698553 : List Nat := [1, 2, 1, 6, 2, 1, 2, 1, 3, 1, 3]
def baseStart_2698553 : Nat := 118140960795 + 2698553 * 2 ^ 59
def prefixEnd_2698553 : Nat := 4983230072969 + 3 ^ 40 * 2698553 * 2
def baseEnd_2698553 : Nat := 1385654760632485632677087

theorem tailTrace_2698553 : CollatzResearch.WordTrace tailWord_2698553 prefixEnd_2698553 1385654760632485632677087 := by
  unfold tailWord_2698553
  simp only [CollatzResearch.WordTrace]
  refine ⟨98424313792610832005284313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65616209195073888003522875 98424313792610832005284313)
  ·
    refine ⟨73818235344458124003963235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98424313792610832005284313 73818235344458124003963235)
    ·
      refine ⟨110727353016687186005944853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73818235344458124003963235 110727353016687186005944853)
      ·
        refine ⟨5190344672657211844028665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 110727353016687186005944853 5190344672657211844028665)
        ·
          refine ⟨3892758504492908883021499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5190344672657211844028665 3892758504492908883021499)
          ·
            refine ⟨5839137756739363324532249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3892758504492908883021499 5839137756739363324532249)
            ·
              refine ⟨4379353317554522493399187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5839137756739363324532249 4379353317554522493399187)
              ·
                refine ⟨6569029976331783740098781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4379353317554522493399187 6569029976331783740098781)
                ·
                  refine ⟨2463386241124418902537043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6569029976331783740098781 2463386241124418902537043)
                  ·
                    refine ⟨3695079361686628353805565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2463386241124418902537043 3695079361686628353805565)
                    ·
                      refine ⟨1385654760632485632677087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3695079361686628353805565 1385654760632485632677087)
                      ·
                        rfl

theorem cell23_2698553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_2698553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698553 prefixEnd_2698553 := by exact prefixLift 2698553
  have htrace : WordTrace (prefixWord ++ tailWord_2698553) baseStart_2698553 baseEnd_2698553 := by
    simpa [prefixWord, tailWord_2698553, baseEnd_2698553] using wordTrace_append hprefix tailTrace_2698553
  have hstable : (prefixWord ++ tailWord_2698553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698553).length < 2 ^ (prefixWord ++ tailWord_2698553).sum := by decide
  have hdescent : baseEnd_2698553 < baseStart_2698553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698569 : List Nat := [1, 2, 1, 1, 2, 3, 2, 5, 2, 4]
def baseStart_2698569 : Nat := 118140960795 + 2698569 * 2 ^ 59
def prefixEnd_2698569 : Nat := 4983230072969 + 3 ^ 40 * 2698569 * 2
def baseEnd_2698569 : Nat := 461887658774319190025671

theorem tailTrace_2698569 : CollatzResearch.WordTrace tailWord_2698569 prefixEnd_2698569 461887658774319190025671 := by
  unfold tailWord_2698569
  simp only [CollatzResearch.WordTrace]
  refine ⟨98424897360552866737866761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65616598240368577825244507 98424897360552866737866761)
  ·
    refine ⟨73818673020414650053400071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98424897360552866737866761 73818673020414650053400071)
    ·
      refine ⟨110728009530621975080100107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73818673020414650053400071 110728009530621975080100107)
      ·
        refine ⟨166092014295932962620150161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110728009530621975080100107 166092014295932962620150161)
        ·
          refine ⟨124569010721949721965112621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166092014295932962620150161 124569010721949721965112621)
          ·
            refine ⟨46713379020731145736917233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124569010721949721965112621 46713379020731145736917233)
            ·
              refine ⟨35035034265548359302687925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46713379020731145736917233 35035034265548359302687925)
              ·
                refine ⟨3284534462395158684626993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35035034265548359302687925 3284534462395158684626993)
                ·
                  refine ⟨2463400846796369013470245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3284534462395158684626993 2463400846796369013470245)
                  ·
                    refine ⟨461887658774319190025671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2463400846796369013470245 461887658774319190025671)
                    ·
                      rfl

theorem cell23_2698569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 4].length) (baseStart_2698569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698569 prefixEnd_2698569 := by exact prefixLift 2698569
  have htrace : WordTrace (prefixWord ++ tailWord_2698569) baseStart_2698569 baseEnd_2698569 := by
    simpa [prefixWord, tailWord_2698569, baseEnd_2698569] using wordTrace_append hprefix tailTrace_2698569
  have hstable : (prefixWord ++ tailWord_2698569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698569).length < 2 ^ (prefixWord ++ tailWord_2698569).sum := by decide
  have hdescent : baseEnd_2698569 < baseStart_2698569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698576 : List Nat := [2, 1, 1, 1, 1, 5, 1, 4, 3, 2, 2]
def baseStart_2698576 : Nat := 118140960795 + 2698576 * 2 ^ 59
def prefixEnd_2698576 : Nat := 4983230072969 + 3 ^ 40 * 2698576 * 2
def baseEnd_2698576 : Nat := 1385666570687539042689481

theorem tailTrace_2698576 : CollatzResearch.WordTrace tailWord_2698576 prefixEnd_2698576 1385666570687539042689481 := by
  unfold tailWord_2698576
  simp only [CollatzResearch.WordTrace]
  refine ⟨49212576335763753466685791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65616768447685004622247721 49212576335763753466685791)
  ·
    refine ⟨73818864503645630200028687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49212576335763753466685791 73818864503645630200028687)
    ·
      refine ⟨110728296755468445300043031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73818864503645630200028687 110728296755468445300043031)
      ·
        refine ⟨166092445133202667950064547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110728296755468445300043031 166092445133202667950064547)
        ·
          refine ⟨249138667699804001925096821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166092445133202667950064547 249138667699804001925096821)
          ·
            refine ⟨23356750096856625180477827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 249138667699804001925096821 23356750096856625180477827)
            ·
              refine ⟨35035125145284937770716741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23356750096856625180477827 35035125145284937770716741)
              ·
                refine ⟨6569085964740925832009389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35035125145284937770716741 6569085964740925832009389)
                ·
                  refine ⟨2463407236777847187003521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6569085964740925832009389 2463407236777847187003521)
                  ·
                    refine ⟨1847555427583385390252641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2463407236777847187003521 1847555427583385390252641)
                    ·
                      refine ⟨1385666570687539042689481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1847555427583385390252641 1385666570687539042689481)
                      ·
                        rfl

theorem cell23_2698576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 3, 2, 2].length) (baseStart_2698576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698576 prefixEnd_2698576 := by exact prefixLift 2698576
  have htrace : WordTrace (prefixWord ++ tailWord_2698576) baseStart_2698576 baseEnd_2698576 := by
    simpa [prefixWord, tailWord_2698576, baseEnd_2698576] using wordTrace_append hprefix tailTrace_2698576
  have hstable : (prefixWord ++ tailWord_2698576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698576).length < 2 ^ (prefixWord ++ tailWord_2698576).sum := by decide
  have hdescent : baseEnd_2698576 < baseStart_2698576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698596 : List Nat := [2, 3, 1, 1, 3, 2, 2, 3, 1, 2, 3]
def baseStart_2698596 : Nat := 118140960795 + 2698596 * 2 ^ 59
def prefixEnd_2698596 : Nat := 4983230072969 + 3 ^ 40 * 2698596 * 2
def baseEnd_2698596 : Nat := 1385676840300628964439389

theorem tailTrace_2698596 : CollatzResearch.WordTrace tailWord_2698596 prefixEnd_2698596 1385676840300628964439389 := by
  unfold tailWord_2698596
  simp only [CollatzResearch.WordTrace]
  refine ⟨49212941065727525174549821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65617254754303366899399761 49212941065727525174549821)
  ·
    refine ⟨18454852899647821940456183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49212941065727525174549821 18454852899647821940456183)
    ·
      refine ⟨27682279349471732910684275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18454852899647821940456183 27682279349471732910684275)
      ·
        refine ⟨41523419024207599366026413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27682279349471732910684275 41523419024207599366026413)
        ·
          refine ⟨15571282134077849762259905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41523419024207599366026413 15571282134077849762259905)
          ·
            refine ⟨11678461600558387321694929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15571282134077849762259905 11678461600558387321694929)
            ·
              refine ⟨8758846200418790491271197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11678461600558387321694929 8758846200418790491271197)
              ·
                refine ⟨3284567325157046434226699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8758846200418790491271197 3284567325157046434226699)
                ·
                  refine ⟨4926850987735569651340049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3284567325157046434226699 4926850987735569651340049)
                  ·
                    refine ⟨3695138240801677238505037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4926850987735569651340049 3695138240801677238505037)
                    ·
                      refine ⟨1385676840300628964439389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3695138240801677238505037 1385676840300628964439389)
                      ·
                        rfl

theorem cell23_2698596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_2698596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698596 prefixEnd_2698596 := by exact prefixLift 2698596
  have htrace : WordTrace (prefixWord ++ tailWord_2698596) baseStart_2698596 baseEnd_2698596 := by
    simpa [prefixWord, tailWord_2698596, baseEnd_2698596] using wordTrace_append hprefix tailTrace_2698596
  have hstable : (prefixWord ++ tailWord_2698596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698596).length < 2 ^ (prefixWord ++ tailWord_2698596).sum := by decide
  have hdescent : baseEnd_2698596 < baseStart_2698596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698599 : List Nat := [1, 1, 5, 1, 4, 2, 9]
def baseStart_2698599 : Nat := 118140960795 + 2698599 * 2 ^ 59
def prefixEnd_2698599 : Nat := 4983230072969 + 3 ^ 40 * 2698599 * 2
def baseEnd_2698599 : Nat := 17107140502994968551875

theorem tailTrace_2698599 : CollatzResearch.WordTrace tailWord_2698599 prefixEnd_2698599 17107140502994968551875 := by
  unfold tailWord_2698599
  simp only [CollatzResearch.WordTrace]
  refine ⟨98425991550444181861458851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65617327700296121240972567 98425991550444181861458851)
  ·
    refine ⟨147638987325666272792188277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98425991550444181861458851 147638987325666272792188277)
    ·
      refine ⟨13841155061781213074267651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147638987325666272792188277 13841155061781213074267651)
      ·
        refine ⟨20761732592671819611401477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13841155061781213074267651 20761732592671819611401477)
        ·
          refine ⟨3892824861125966177137777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20761732592671819611401477 3892824861125966177137777)
          ·
            refine ⟨2919618645844474632853333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3892824861125966177137777 2919618645844474632853333)
            ·
              refine ⟨17107140502994968551875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2919618645844474632853333 17107140502994968551875)
              ·
                rfl

theorem cell23_2698599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 9].length) (baseStart_2698599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698599 prefixEnd_2698599 := by exact prefixLift 2698599
  have htrace : WordTrace (prefixWord ++ tailWord_2698599) baseStart_2698599 baseEnd_2698599 := by
    simpa [prefixWord, tailWord_2698599, baseEnd_2698599] using wordTrace_append hprefix tailTrace_2698599
  have hstable : (prefixWord ++ tailWord_2698599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698599).length < 2 ^ (prefixWord ++ tailWord_2698599).sum := by decide
  have hdescent : baseEnd_2698599 < baseStart_2698599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698636 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 3, 3, 2]
def baseStart_2698636 : Nat := 118140960795 + 2698636 * 2 ^ 59
def prefixEnd_2698636 : Nat := 4983230072969 + 3 ^ 40 * 2698636 * 2
def baseEnd_2698636 : Nat := 1385697379526808807939205

theorem tailTrace_2698636 : CollatzResearch.WordTrace tailWord_2698636 prefixEnd_2698636 1385697379526808807939205 := by
  unfold tailWord_2698636
  simp only [CollatzResearch.WordTrace]
  refine ⟨49213670525655068590277881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65618227367540091453703841 49213670525655068590277881)
  ·
    refine ⟨36910252894241301442708411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49213670525655068590277881 36910252894241301442708411)
    ·
      refine ⟨55365379341361952164062617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36910252894241301442708411 55365379341361952164062617)
      ·
        refine ⟨41524034506021464123046963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55365379341361952164062617 41524034506021464123046963)
        ·
          refine ⟨62286051759032196184570445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41524034506021464123046963 62286051759032196184570445)
          ·
            refine ⟨23357269409637073569213917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62286051759032196184570445 23357269409637073569213917)
            ·
              refine ⟨8758976028613902588455219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23357269409637073569213917 8758976028613902588455219)
              ·
                refine ⟨13138464042920853882682829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8758976028613902588455219 13138464042920853882682829)
                ·
                  refine ⟨4926924016095320206006061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13138464042920853882682829 4926924016095320206006061)
                  ·
                    refine ⟨1847596506035745077252273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4926924016095320206006061 1847596506035745077252273)
                    ·
                      refine ⟨1385697379526808807939205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1847596506035745077252273 1385697379526808807939205)
                      ·
                        rfl

theorem cell23_2698636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_2698636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698636 prefixEnd_2698636 := by exact prefixLift 2698636
  have htrace : WordTrace (prefixWord ++ tailWord_2698636) baseStart_2698636 baseEnd_2698636 := by
    simpa [prefixWord, tailWord_2698636, baseEnd_2698636] using wordTrace_append hprefix tailTrace_2698636
  have hstable : (prefixWord ++ tailWord_2698636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698636).length < 2 ^ (prefixWord ++ tailWord_2698636).sum := by decide
  have hdescent : baseEnd_2698636 < baseStart_2698636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698679 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 4]
def baseStart_2698679 : Nat := 118140960795 + 2698679 * 2 ^ 59
def prefixEnd_2698679 : Nat := 4983230072969 + 3 ^ 40 * 2698679 * 2
def baseEnd_2698679 : Nat := 1385719459194952139701507

theorem tailTrace_2698679 : CollatzResearch.WordTrace tailWord_2698679 prefixEnd_2698679 1385719459194952139701507 := by
  unfold tailWord_2698679
  simp only [CollatzResearch.WordTrace]
  refine ⟨98428909390154355524371091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65619272926769570349580727 98428909390154355524371091)
  ·
    refine ⟨147643364085231533286556637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98428909390154355524371091 147643364085231533286556637)
    ·
      refine ⟨55366261531961824982458739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147643364085231533286556637 55366261531961824982458739)
      ·
        refine ⟨83049392297942737473688109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55366261531961824982458739 83049392297942737473688109)
        ·
          refine ⟨31143522111728526552633041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83049392297942737473688109 31143522111728526552633041)
          ·
            refine ⟨23357641583796394914474781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31143522111728526552633041 23357641583796394914474781)
            ·
              refine ⟨8759115593923648092928043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23357641583796394914474781 8759115593923648092928043)
              ·
                refine ⟨13138673390885472139392065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8759115593923648092928043 13138673390885472139392065)
                ·
                  refine ⟨9854005043164104104544049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13138673390885472139392065 9854005043164104104544049)
                  ·
                    refine ⟨7390503782373078078408037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9854005043164104104544049 7390503782373078078408037)
                    ·
                      refine ⟨1385719459194952139701507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7390503782373078078408037 1385719459194952139701507)
                      ·
                        rfl

theorem cell23_2698679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_2698679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698679 prefixEnd_2698679 := by exact prefixLift 2698679
  have htrace : WordTrace (prefixWord ++ tailWord_2698679) baseStart_2698679 baseEnd_2698679 := by
    simpa [prefixWord, tailWord_2698679, baseEnd_2698679] using wordTrace_append hprefix tailTrace_2698679
  have hstable : (prefixWord ++ tailWord_2698679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698679).length < 2 ^ (prefixWord ++ tailWord_2698679).sum := by decide
  have hdescent : baseEnd_2698679 < baseStart_2698679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698717 : List Nat := [1, 4, 3, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_2698717 : Nat := 118140960795 + 2698717 * 2 ^ 59
def prefixEnd_2698717 : Nat := 4983230072969 + 3 ^ 40 * 2698717 * 2
def baseEnd_2698717 : Nat := 1385738971459822991026333

theorem tailTrace_2698717 : CollatzResearch.WordTrace tailWord_2698717 prefixEnd_2698717 1385738971459822991026333 := by
  unfold tailWord_2698717
  simp only [CollatzResearch.WordTrace]
  refine ⟨98430295364016688014254405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65620196909344458676169603 98430295364016688014254405)
  ·
    refine ⟨18455680380753129002672701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98430295364016688014254405 18455680380753129002672701)
    ·
      refine ⟨6920880142782423376002263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18455680380753129002672701 6920880142782423376002263)
      ·
        refine ⟨10381320214173635064003395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6920880142782423376002263 10381320214173635064003395)
        ·
          refine ⟨15571980321260452596005093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10381320214173635064003395 15571980321260452596005093)
          ·
            refine ⟨2919746310236334861750955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15571980321260452596005093 2919746310236334861750955)
            ·
              refine ⟨4379619465354502292626433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2919746310236334861750955 4379619465354502292626433)
              ·
                refine ⟨3284714599015876719469825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4379619465354502292626433 3284714599015876719469825)
                ·
                  refine ⟨2463535949261907539602369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3284714599015876719469825 2463535949261907539602369)
                  ·
                    refine ⟨1847651961946430654701777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2463535949261907539602369 1847651961946430654701777)
                    ·
                      refine ⟨1385738971459822991026333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1847651961946430654701777 1385738971459822991026333)
                      ·
                        rfl

theorem cell23_2698717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_2698717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698717 prefixEnd_2698717 := by exact prefixLift 2698717
  have htrace : WordTrace (prefixWord ++ tailWord_2698717) baseStart_2698717 baseEnd_2698717 := by
    simpa [prefixWord, tailWord_2698717, baseEnd_2698717] using wordTrace_append hprefix tailTrace_2698717
  have hstable : (prefixWord ++ tailWord_2698717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698717).length < 2 ^ (prefixWord ++ tailWord_2698717).sum := by decide
  have hdescent : baseEnd_2698717 < baseStart_2698717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698719 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 4, 5]
def baseStart_2698719 : Nat := 118140960795 + 2698719 * 2 ^ 59
def prefixEnd_2698719 : Nat := 4983230072969 + 3 ^ 40 * 2698719 * 2
def baseEnd_2698719 : Nat := 461913332807043994400441

theorem tailTrace_2698719 : CollatzResearch.WordTrace tailWord_2698719 prefixEnd_2698719 461913332807043994400441 := by
  unfold tailWord_2698719
  simp only [CollatzResearch.WordTrace]
  refine ⟨98430368310009442355827211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65620245540006294903884807 98430368310009442355827211)
  ·
    refine ⟨147645552465014163533740817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98430368310009442355827211 147645552465014163533740817)
    ·
      refine ⟨110734164348760622650305613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147645552465014163533740817 110734164348760622650305613)
      ·
        refine ⟨41525311630785233493864605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110734164348760622650305613 41525311630785233493864605)
        ·
          refine ⟨15571991861544462560199227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41525311630785233493864605 15571991861544462560199227)
          ·
            refine ⟨23357987792316693840298841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15571991861544462560199227 23357987792316693840298841)
            ·
              refine ⟨17518490844237520380224131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23357987792316693840298841 17518490844237520380224131)
              ·
                refine ⟨26277736266356280570336197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17518490844237520380224131 26277736266356280570336197)
                ·
                  refine ⟨4927075549941802606938037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26277736266356280570336197 4927075549941802606938037)
                  ·
                    refine ⟨461913332807043994400441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4927075549941802606938037 461913332807043994400441)
                    ·
                      rfl

theorem cell23_2698719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 5].length) (baseStart_2698719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698719 prefixEnd_2698719 := by exact prefixLift 2698719
  have htrace : WordTrace (prefixWord ++ tailWord_2698719) baseStart_2698719 baseEnd_2698719 := by
    simpa [prefixWord, tailWord_2698719, baseEnd_2698719] using wordTrace_append hprefix tailTrace_2698719
  have hstable : (prefixWord ++ tailWord_2698719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698719).length < 2 ^ (prefixWord ++ tailWord_2698719).sum := by decide
  have hdescent : baseEnd_2698719 < baseStart_2698719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698739 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 4]
def baseStart_2698739 : Nat := 118140960795 + 2698739 * 2 ^ 59
def prefixEnd_2698739 : Nat := 4983230072969 + 3 ^ 40 * 2698739 * 2
def baseEnd_2698739 : Nat := 1385750268034221904951231

theorem tailTrace_2698739 : CollatzResearch.WordTrace tailWord_2698739 prefixEnd_2698739 1385750268034221904951231 := by
  unfold tailWord_2698739
  simp only [CollatzResearch.WordTrace]
  refine ⟨98431097769936985771555271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65620731846624657181036847 98431097769936985771555271)
  ·
    refine ⟨147646646654905478657332907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98431097769936985771555271 147646646654905478657332907)
    ·
      refine ⟨221469969982358217985999361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147646646654905478657332907 221469969982358217985999361)
      ·
        refine ⟨166102477486768663489499521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221469969982358217985999361 166102477486768663489499521)
        ·
          refine ⟨124576858115076497617124641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166102477486768663489499521 124576858115076497617124641)
          ·
            refine ⟨93432643586307373212843481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124576858115076497617124641 93432643586307373212843481)
            ·
              refine ⟨70074482689730529909632611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93432643586307373212843481 70074482689730529909632611)
              ·
                refine ⟨105111724034595794864448917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70074482689730529909632611 105111724034595794864448917)
                ·
                  refine ⟨4927112064121677884271043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105111724034595794864448917 4927112064121677884271043)
                  ·
                    refine ⟨7390668096182516826406565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4927112064121677884271043 7390668096182516826406565)
                    ·
                      refine ⟨1385750268034221904951231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7390668096182516826406565 1385750268034221904951231)
                      ·
                        rfl

theorem cell23_2698739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 4].length) (baseStart_2698739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698739 prefixEnd_2698739 := by exact prefixLift 2698739
  have htrace : WordTrace (prefixWord ++ tailWord_2698739) baseStart_2698739 baseEnd_2698739 := by
    simpa [prefixWord, tailWord_2698739, baseEnd_2698739] using wordTrace_append hprefix tailTrace_2698739
  have hstable : (prefixWord ++ tailWord_2698739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698739).length < 2 ^ (prefixWord ++ tailWord_2698739).sum := by decide
  have hdescent : baseEnd_2698739 < baseStart_2698739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698783 : List Nat := [1, 1, 2, 4, 1, 1, 2, 6, 1, 4]
def baseStart_2698783 : Nat := 118140960795 + 2698783 * 2 ^ 59
def prefixEnd_2698783 : Nat := 4983230072969 + 3 ^ 40 * 2698783 * 2
def baseEnd_2698783 : Nat := 461924287061006577600343

theorem tailTrace_2698783 : CollatzResearch.WordTrace tailWord_2698783 prefixEnd_2698783 461924287061006577600343 := by
  unfold tailWord_2698783
  simp only [CollatzResearch.WordTrace]
  refine ⟨98432702581777581286157003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65621801721185054190771335 98432702581777581286157003)
  ·
    refine ⟨147649053872666371929235505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98432702581777581286157003 147649053872666371929235505)
    ·
      refine ⟨110736790404499778946926629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147649053872666371929235505 110736790404499778946926629)
      ·
        refine ⟨20763148200843708552548743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110736790404499778946926629 20763148200843708552548743)
        ·
          refine ⟨31144722301265562828823115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20763148200843708552548743 31144722301265562828823115)
          ·
            refine ⟨46717083451898344243234673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31144722301265562828823115 46717083451898344243234673)
            ·
              refine ⟨35037812588923758182426005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46717083451898344243234673 35037812588923758182426005)
              ·
                refine ⟨1642397465105801164801219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35037812588923758182426005 1642397465105801164801219)
                ·
                  refine ⟨2463596197658701747201829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1642397465105801164801219 2463596197658701747201829)
                  ·
                    refine ⟨461924287061006577600343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2463596197658701747201829 461924287061006577600343)
                    ·
                      rfl

theorem cell23_2698783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 1, 4].length) (baseStart_2698783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698783 prefixEnd_2698783 := by exact prefixLift 2698783
  have htrace : WordTrace (prefixWord ++ tailWord_2698783) baseStart_2698783 baseEnd_2698783 := by
    simpa [prefixWord, tailWord_2698783, baseEnd_2698783] using wordTrace_append hprefix tailTrace_2698783
  have hstable : (prefixWord ++ tailWord_2698783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698783).length < 2 ^ (prefixWord ++ tailWord_2698783).sum := by decide
  have hdescent : baseEnd_2698783 < baseStart_2698783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698833 : List Nat := [1, 2, 2, 1, 3, 2, 1, 4, 2, 3, 2]
def baseStart_2698833 : Nat := 118140960795 + 2698833 * 2 ^ 59
def prefixEnd_2698833 : Nat := 4983230072969 + 3 ^ 40 * 2698833 * 2
def baseEnd_2698833 : Nat := 1385798535215744537175799

theorem tailTrace_2698833 : CollatzResearch.WordTrace tailWord_2698833 prefixEnd_2698833 1385798535215744537175799 := by
  unfold tailWord_2698833
  simp only [CollatzResearch.WordTrace]
  refine ⟨98434526231596439825477153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65623017487730959883651435 98434526231596439825477153)
  ·
    refine ⟨73825894673697329869107865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98434526231596439825477153 73825894673697329869107865)
    ·
      refine ⟨55369421005272997401830899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73825894673697329869107865 55369421005272997401830899)
      ·
        refine ⟨83054131507909496102746349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55369421005272997401830899 83054131507909496102746349)
        ·
          refine ⟨31145299315466061038529881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83054131507909496102746349 31145299315466061038529881)
          ·
            refine ⟨23358974486599545778897411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31145299315466061038529881 23358974486599545778897411)
            ·
              refine ⟨35038461729899318668346117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23358974486599545778897411 35038461729899318668346117)
              ·
                refine ⟨6569711574356122250314897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35038461729899318668346117 6569711574356122250314897)
                ·
                  refine ⟨4927283680767091687736173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6569711574356122250314897 4927283680767091687736173)
                  ·
                    refine ⟨1847731380287659382901065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4927283680767091687736173 1847731380287659382901065)
                    ·
                      refine ⟨1385798535215744537175799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1847731380287659382901065 1385798535215744537175799)
                      ·
                        rfl

theorem cell23_2698833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 3, 2].length) (baseStart_2698833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698833 prefixEnd_2698833 := by exact prefixLift 2698833
  have htrace : WordTrace (prefixWord ++ tailWord_2698833) baseStart_2698833 baseEnd_2698833 := by
    simpa [prefixWord, tailWord_2698833, baseEnd_2698833] using wordTrace_append hprefix tailTrace_2698833
  have hstable : (prefixWord ++ tailWord_2698833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698833).length < 2 ^ (prefixWord ++ tailWord_2698833).sum := by decide
  have hdescent : baseEnd_2698833 < baseStart_2698833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698859 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 6]
def baseStart_2698859 : Nat := 118140960795 + 2698859 * 2 ^ 59
def prefixEnd_2698859 : Nat := 4983230072969 + 3 ^ 40 * 2698859 * 2
def baseEnd_2698859 : Nat := 1385811885712761435450679

theorem tailTrace_2698859 : CollatzResearch.WordTrace tailWord_2698859 prefixEnd_2698859 1385811885712761435450679 := by
  unfold tailWord_2698859
  simp only [CollatzResearch.WordTrace]
  refine ⟨98435474529502246265923631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65623649686334830843949087 98435474529502246265923631)
  ·
    refine ⟨147653211794253369398885447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98435474529502246265923631 147653211794253369398885447)
    ·
      refine ⟨221479817691380054098328171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147653211794253369398885447 221479817691380054098328171)
      ·
        refine ⟨332219726537070081147492257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221479817691380054098328171 332219726537070081147492257)
        ·
          refine ⟨249164794902802560860619193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332219726537070081147492257 249164794902802560860619193)
          ·
            refine ⟨186873596177101920645464395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249164794902802560860619193 186873596177101920645464395)
            ·
              refine ⟨280310394265652880968196593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186873596177101920645464395 280310394265652880968196593)
              ·
                refine ⟨210232795699239660726147445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280310394265652880968196593 210232795699239660726147445)
                ·
                  refine ⟨19709324596803718193076323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 210232795699239660726147445 19709324596803718193076323)
                  ·
                    refine ⟨29563986895205577289614485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19709324596803718193076323 29563986895205577289614485)
                    ·
                      refine ⟨1385811885712761435450679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29563986895205577289614485 1385811885712761435450679)
                      ·
                        rfl

theorem cell23_2698859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 6].length) (baseStart_2698859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698859 prefixEnd_2698859 := by exact prefixLift 2698859
  have htrace : WordTrace (prefixWord ++ tailWord_2698859) baseStart_2698859 baseEnd_2698859 := by
    simpa [prefixWord, tailWord_2698859, baseEnd_2698859] using wordTrace_append hprefix tailTrace_2698859
  have hstable : (prefixWord ++ tailWord_2698859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698859).length < 2 ^ (prefixWord ++ tailWord_2698859).sum := by decide
  have hdescent : baseEnd_2698859 < baseStart_2698859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698879 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 7]
def baseStart_2698879 : Nat := 118140960795 + 2698879 * 2 ^ 59
def prefixEnd_2698879 : Nat := 4983230072969 + 3 ^ 40 * 2698879 * 2
def baseEnd_2698879 : Nat := 1385822155325851357200587

theorem tailTrace_2698879 : CollatzResearch.WordTrace tailWord_2698879 prefixEnd_2698879 1385822155325851357200587 := by
  unfold tailWord_2698879
  simp only [CollatzResearch.WordTrace]
  refine ⟨98436203989429789681651691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65624135992953193121101127 98436203989429789681651691)
  ·
    refine ⟨147654305984144684522477537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98436203989429789681651691 147654305984144684522477537)
    ·
      refine ⟨110740729488108513391858153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147654305984144684522477537 110740729488108513391858153)
      ·
        refine ⟨83055547116081385043893615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110740729488108513391858153 83055547116081385043893615)
        ·
          refine ⟨124583320674122077565840423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83055547116081385043893615 124583320674122077565840423)
          ·
            refine ⟨186874981011183116348760635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124583320674122077565840423 186874981011183116348760635)
            ·
              refine ⟨280312471516774674523140953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186874981011183116348760635 280312471516774674523140953)
              ·
                refine ⟨210234353637581005892355715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280312471516774674523140953 210234353637581005892355715)
                ·
                  refine ⟨315351530456371508838533573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210234353637581005892355715 315351530456371508838533573)
                  ·
                    refine ⟨59128411960569657907225045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 315351530456371508838533573 59128411960569657907225045)
                    ·
                      refine ⟨1385822155325851357200587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59128411960569657907225045 1385822155325851357200587)
                      ·
                        rfl

theorem cell23_2698879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_2698879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698879 prefixEnd_2698879 := by exact prefixLift 2698879
  have htrace : WordTrace (prefixWord ++ tailWord_2698879) baseStart_2698879 baseEnd_2698879 := by
    simpa [prefixWord, tailWord_2698879, baseEnd_2698879] using wordTrace_append hprefix tailTrace_2698879
  have hstable : (prefixWord ++ tailWord_2698879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698879).length < 2 ^ (prefixWord ++ tailWord_2698879).sum := by decide
  have hdescent : baseEnd_2698879 < baseStart_2698879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698890 : List Nat := [3, 1, 2, 3, 2, 1, 3, 2, 2, 4]
def baseStart_2698890 : Nat := 118140960795 + 2698890 * 2 ^ 59
def prefixEnd_2698890 : Nat := 4983230072969 + 3 ^ 40 * 2698890 * 2
def baseEnd_2698890 : Nat := 461942601204350271387679

theorem tailTrace_2698890 : CollatzResearch.WordTrace tailWord_2698890 prefixEnd_2698890 461942601204350271387679 := by
  unfold tailWord_2698890
  simp only [CollatzResearch.WordTrace]
  refine ⟨24609151298097484640075531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65624403461593292373534749 24609151298097484640075531)
  ·
    refine ⟨36913726947146226960113297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24609151298097484640075531 36913726947146226960113297)
    ·
      refine ⟨27685295210359670220084973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36913726947146226960113297 27685295210359670220084973)
      ·
        refine ⟨10381985703884876332531865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27685295210359670220084973 10381985703884876332531865)
        ·
          refine ⟨7786489277913657249398899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10381985703884876332531865 7786489277913657249398899)
          ·
            refine ⟨11679733916870485874098349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7786489277913657249398899 11679733916870485874098349)
            ·
              refine ⟨4379900218826432202786881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11679733916870485874098349 4379900218826432202786881)
              ·
                refine ⟨3284925164119824152090161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4379900218826432202786881 3284925164119824152090161)
                ·
                  refine ⟨2463693873089868114067621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3284925164119824152090161 2463693873089868114067621)
                  ·
                    refine ⟨461942601204350271387679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2463693873089868114067621 461942601204350271387679)
                    ·
                      rfl

theorem cell23_2698890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_2698890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698890 prefixEnd_2698890 := by exact prefixLift 2698890
  have htrace : WordTrace (prefixWord ++ tailWord_2698890) baseStart_2698890 baseEnd_2698890 := by
    simpa [prefixWord, tailWord_2698890, baseEnd_2698890] using wordTrace_append hprefix tailTrace_2698890
  have hstable : (prefixWord ++ tailWord_2698890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698890).length < 2 ^ (prefixWord ++ tailWord_2698890).sum := by decide
  have hdescent : baseEnd_2698890 < baseStart_2698890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698896 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 3]
def baseStart_2698896 : Nat := 118140960795 + 2698896 * 2 ^ 59
def prefixEnd_2698896 : Nat := 4983230072969 + 3 ^ 40 * 2698896 * 2
def baseEnd_2698896 : Nat := 1385830884496977790688009

theorem tailTrace_2698896 : CollatzResearch.WordTrace tailWord_2698896 prefixEnd_2698896 1385830884496977790688009 := by
  unfold tailWord_2698896
  simp only [CollatzResearch.WordTrace]
  refine ⟨49218412015184100792510271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65624549353578801056680361 49218412015184100792510271)
  ·
    refine ⟨73827618022776151188765407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49218412015184100792510271 73827618022776151188765407)
    ·
      refine ⟨110741427034164226783148111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73827618022776151188765407 110741427034164226783148111)
      ·
        refine ⟨166112140551246340174722167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110741427034164226783148111 166112140551246340174722167)
        ·
          refine ⟨249168210826869510262083251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166112140551246340174722167 249168210826869510262083251)
          ·
            refine ⟨373752316240304265393124877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249168210826869510262083251 373752316240304265393124877)
            ·
              refine ⟨140157118590114099522421829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 373752316240304265393124877 140157118590114099522421829)
              ·
                refine ⟨26279459735646393660454093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140157118590114099522421829 26279459735646393660454093)
                ·
                  refine ⟨9854797400867397622670285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26279459735646393660454093 9854797400867397622670285)
                  ·
                    refine ⟨3695549025325274108501357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9854797400867397622670285 3695549025325274108501357)
                    ·
                      refine ⟨1385830884496977790688009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3695549025325274108501357 1385830884496977790688009)
                      ·
                        rfl

theorem cell23_2698896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 3].length) (baseStart_2698896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698896 prefixEnd_2698896 := by exact prefixLift 2698896
  have htrace : WordTrace (prefixWord ++ tailWord_2698896) baseStart_2698896 baseEnd_2698896 := by
    simpa [prefixWord, tailWord_2698896, baseEnd_2698896] using wordTrace_append hprefix tailTrace_2698896
  have hstable : (prefixWord ++ tailWord_2698896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698896).length < 2 ^ (prefixWord ++ tailWord_2698896).sum := by decide
  have hdescent : baseEnd_2698896 < baseStart_2698896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698900 : List Nat := [2, 4, 2, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_2698900 : Nat := 118140960795 + 2698900 * 2 ^ 59
def prefixEnd_2698900 : Nat := 4983230072969 + 3 ^ 40 * 2698900 * 2
def baseEnd_2698900 : Nat := 1385832938419595775037991

theorem tailTrace_2698900 : CollatzResearch.WordTrace tailWord_2698900 prefixEnd_2698900 1385832938419595775037991 := by
  unfold tailWord_2698900
  simp only [CollatzResearch.WordTrace]
  refine ⟨49218484961176855134083077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65624646614902473512110769 49218484961176855134083077)
  ·
    refine ⟨9228465930220660337640577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49218484961176855134083077 9228465930220660337640577)
    ·
      refine ⟨6921349447665495253230433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9228465930220660337640577 6921349447665495253230433)
      ·
        refine ⟨5191012085749121439922825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6921349447665495253230433 5191012085749121439922825)
        ·
          refine ⟨3893259064311841079942119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5191012085749121439922825 3893259064311841079942119)
          ·
            refine ⟨5839888596467761619913179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3893259064311841079942119 5839888596467761619913179)
            ·
              refine ⟨8759832894701642429869769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5839888596467761619913179 8759832894701642429869769)
              ·
                refine ⟨6569874671026231822402327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8759832894701642429869769 6569874671026231822402327)
                ·
                  refine ⟨9854812006539347733603491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6569874671026231822402327 9854812006539347733603491)
                  ·
                    refine ⟨14782218009809021600405237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9854812006539347733603491 14782218009809021600405237)
                    ·
                      refine ⟨1385832938419595775037991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14782218009809021600405237 1385832938419595775037991)
                      ·
                        rfl

theorem cell23_2698900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_2698900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698900 prefixEnd_2698900 := by exact prefixLift 2698900
  have htrace : WordTrace (prefixWord ++ tailWord_2698900) baseStart_2698900 baseEnd_2698900 := by
    simpa [prefixWord, tailWord_2698900, baseEnd_2698900] using wordTrace_append hprefix tailTrace_2698900
  have hstable : (prefixWord ++ tailWord_2698900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698900).length < 2 ^ (prefixWord ++ tailWord_2698900).sum := by decide
  have hdescent : baseEnd_2698900 < baseStart_2698900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698910 : List Nat := [4, 3, 1, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_2698910 : Nat := 118140960795 + 2698910 * 2 ^ 59
def prefixEnd_2698910 : Nat := 4983230072969 + 3 ^ 40 * 2698910 * 2
def baseEnd_2698910 : Nat := 1385838073226140735912945

theorem tailTrace_2698910 : CollatzResearch.WordTrace tailWord_2698910 prefixEnd_2698910 1385838073226140735912945 := by
  unfold tailWord_2698910
  simp only [CollatzResearch.WordTrace]
  refine ⟨12304666831539685247003773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65624889768211654650686789 12304666831539685247003773)
  ·
    refine ⟨4614250061827381967626415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12304666831539685247003773 4614250061827381967626415)
    ·
      refine ⟨6921375092741072951439623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4614250061827381967626415 6921375092741072951439623)
      ·
        refine ⟨10382062639111609427159435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6921375092741072951439623 10382062639111609427159435)
        ·
          refine ⟨15573093958667414140739153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10382062639111609427159435 15573093958667414140739153)
          ·
            refine ⟨11679820469000560605554365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15573093958667414140739153 11679820469000560605554365)
            ·
              refine ⟨4379932675875210227082887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11679820469000560605554365 4379932675875210227082887)
              ·
                refine ⟨6569899013812815340624331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4379932675875210227082887 6569899013812815340624331)
                ·
                  refine ⟨9854848520719223010936497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6569899013812815340624331 9854848520719223010936497)
                  ·
                    refine ⟨7391136390539417258202373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9854848520719223010936497 7391136390539417258202373)
                    ·
                      refine ⟨1385838073226140735912945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7391136390539417258202373 1385838073226140735912945)
                      ·
                        rfl

theorem cell23_2698910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_2698910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698910 prefixEnd_2698910 := by exact prefixLift 2698910
  have htrace : WordTrace (prefixWord ++ tailWord_2698910) baseStart_2698910 baseEnd_2698910 := by
    simpa [prefixWord, tailWord_2698910, baseEnd_2698910] using wordTrace_append hprefix tailTrace_2698910
  have hstable : (prefixWord ++ tailWord_2698910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698910).length < 2 ^ (prefixWord ++ tailWord_2698910).sum := by decide
  have hdescent : baseEnd_2698910 < baseStart_2698910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698964 : List Nat := [2, 4, 1, 3, 1, 1, 4, 1, 2, 1, 3]
def baseStart_2698964 : Nat := 118140960795 + 2698964 * 2 ^ 59
def prefixEnd_2698964 : Nat := 4983230072969 + 3 ^ 40 * 2698964 * 2
def baseEnd_2698964 : Nat := 1385865801181483524637697

theorem tailTrace_2698964 : CollatzResearch.WordTrace tailWord_2698964 prefixEnd_2698964 1385865801181483524637697 := by
  unfold tailWord_2698964
  simp only [CollatzResearch.WordTrace]
  refine ⟨49219652097060924599247973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65626202796081232798997297 49219652097060924599247973)
  ·
    refine ⟨9228684768198923362358995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49219652097060924599247973 9228684768198923362358995)
    ·
      refine ⟨13843027152298385043538493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9228684768198923362358995 13843027152298385043538493)
      ·
        refine ⟨5191135182111894391326935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13843027152298385043538493 5191135182111894391326935)
        ·
          refine ⟨7786702773167841586990403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5191135182111894391326935 7786702773167841586990403)
          ·
            refine ⟨11680054159751762380485605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7786702773167841586990403 11680054159751762380485605)
            ·
              refine ⟨2190010154953455446341051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11680054159751762380485605 2190010154953455446341051)
              ·
                refine ⟨3285015232430183169511577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190010154953455446341051 3285015232430183169511577)
                ·
                  refine ⟨2463761424322637377133683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3285015232430183169511577 2463761424322637377133683)
                  ·
                    refine ⟨3695642136483956065700525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2463761424322637377133683 3695642136483956065700525)
                    ·
                      refine ⟨1385865801181483524637697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3695642136483956065700525 1385865801181483524637697)
                      ·
                        rfl

theorem cell23_2698964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_2698964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698964 prefixEnd_2698964 := by exact prefixLift 2698964
  have htrace : WordTrace (prefixWord ++ tailWord_2698964) baseStart_2698964 baseEnd_2698964 := by
    simpa [prefixWord, tailWord_2698964, baseEnd_2698964] using wordTrace_append hprefix tailTrace_2698964
  have hstable : (prefixWord ++ tailWord_2698964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698964).length < 2 ^ (prefixWord ++ tailWord_2698964).sum := by decide
  have hdescent : baseEnd_2698964 < baseStart_2698964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698976 : List Nat := [2, 1, 1, 3, 1, 2, 2, 4, 7]
def baseStart_2698976 : Nat := 118140960795 + 2698976 * 2 ^ 59
def prefixEnd_2698976 : Nat := 4983230072969 + 3 ^ 40 * 2698976 * 2
def baseEnd_2698976 : Nat := 153985773661037497520849

theorem tailTrace_2698976 : CollatzResearch.WordTrace tailWord_2698976 prefixEnd_2698976 153985773661037497520849 := by
  unfold tailWord_2698976
  simp only [CollatzResearch.WordTrace]
  refine ⟨49219870935039187623966391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65626494580052250165288521 49219870935039187623966391)
  ·
    refine ⟨73829806402558781435949587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49219870935039187623966391 73829806402558781435949587)
    ·
      refine ⟨110744709603838172153924381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73829806402558781435949587 110744709603838172153924381)
      ·
        refine ⟨41529266101439314557721643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110744709603838172153924381 41529266101439314557721643)
        ·
          refine ⟨62293899152158971836582465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41529266101439314557721643 62293899152158971836582465)
          ·
            refine ⟨46720424364119228877436849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62293899152158971836582465 46720424364119228877436849)
            ·
              refine ⟨35040318273089421658077637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46720424364119228877436849 35040318273089421658077637)
              ·
                refine ⟨6570059676204266560889557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35040318273089421658077637 6570059676204266560889557)
                ·
                  refine ⟨153985773661037497520849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6570059676204266560889557 153985773661037497520849)
                  ·
                    rfl

theorem cell23_2698976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 7].length) (baseStart_2698976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698976 prefixEnd_2698976 := by exact prefixLift 2698976
  have htrace : WordTrace (prefixWord ++ tailWord_2698976) baseStart_2698976 baseEnd_2698976 := by
    simpa [prefixWord, tailWord_2698976, baseEnd_2698976] using wordTrace_append hprefix tailTrace_2698976
  have hstable : (prefixWord ++ tailWord_2698976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698976).length < 2 ^ (prefixWord ++ tailWord_2698976).sum := by decide
  have hdescent : baseEnd_2698976 < baseStart_2698976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699104 : List Nat := [2, 1, 1, 3, 3, 4, 1, 3, 1, 4]
def baseStart_2699104 : Nat := 118140960795 + 2699104 * 2 ^ 59
def prefixEnd_2699104 : Nat := 4983230072969 + 3 ^ 40 * 2699104 * 2
def baseEnd_2699104 : Nat := 461979229491037658962351

theorem tailTrace_2699104 : CollatzResearch.WordTrace tailWord_2699104 prefixEnd_2699104 461979229491037658962351 := by
  unfold tailWord_2699104
  simp only [CollatzResearch.WordTrace]
  refine ⟨49222205206807326554296183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65629606942409768739061577 49222205206807326554296183)
  ·
    refine ⟨73833307810210989831444275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49222205206807326554296183 73833307810210989831444275)
    ·
      refine ⟨110749961715316484747166413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73833307810210989831444275 110749961715316484747166413)
      ·
        refine ⟨41531235643243681780187405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110749961715316484747166413 41531235643243681780187405)
        ·
          refine ⟨15574213366216380667570277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41531235643243681780187405 15574213366216380667570277)
          ·
            refine ⟨2920165006165571375169427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15574213366216380667570277 2920165006165571375169427)
            ·
              refine ⟨4380247509248357062754141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2920165006165571375169427 4380247509248357062754141)
              ·
                refine ⟨1642592815968133898532803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4380247509248357062754141 1642592815968133898532803)
                ·
                  refine ⟨2463889223952200847799205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1642592815968133898532803 2463889223952200847799205)
                  ·
                    refine ⟨461979229491037658962351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2463889223952200847799205 461979229491037658962351)
                    ·
                      rfl

theorem cell23_2699104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 1, 4].length) (baseStart_2699104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699104 prefixEnd_2699104 := by exact prefixLift 2699104
  have htrace : WordTrace (prefixWord ++ tailWord_2699104) baseStart_2699104 baseEnd_2699104 := by
    simpa [prefixWord, tailWord_2699104, baseEnd_2699104] using wordTrace_append hprefix tailTrace_2699104
  have hstable : (prefixWord ++ tailWord_2699104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699104).length < 2 ^ (prefixWord ++ tailWord_2699104).sum := by decide
  have hdescent : baseEnd_2699104 < baseStart_2699104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699114 : List Nat := [3, 1, 3, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_2699114 : Nat := 118140960795 + 2699114 * 2 ^ 59
def prefixEnd_2699114 : Nat := 4983230072969 + 3 ^ 40 * 2699114 * 2
def baseEnd_2699114 : Nat := 1385942823279657937762007

theorem tailTrace_2699114 : CollatzResearch.WordTrace tailWord_2699114 prefixEnd_2699114 1385942823279657937762007 := by
  unfold tailWord_2699114
  simp only [CollatzResearch.WordTrace]
  refine ⟨24611193785894606204114099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65629850095718949877637597 24611193785894606204114099)
  ·
    refine ⟨36916790678841909306171149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24611193785894606204114099 36916790678841909306171149)
    ·
      refine ⟨13843796504565715989814181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36916790678841909306171149 13843796504565715989814181)
      ·
        refine ⟨2595711844606071748090159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13843796504565715989814181 2595711844606071748090159)
        ·
          refine ⟨3893567766909107622135239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2595711844606071748090159 3893567766909107622135239)
          ·
            refine ⟨5840351650363661433202859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3893567766909107622135239 5840351650363661433202859)
            ·
              refine ⟨8760527475545492149804289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5840351650363661433202859 8760527475545492149804289)
              ·
                refine ⟨6570395606659119112353217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8760527475545492149804289 6570395606659119112353217)
                ·
                  refine ⟨4927796704994339334264913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6570395606659119112353217 4927796704994339334264913)
                  ·
                    refine ⟨3695847528745754500698685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4927796704994339334264913 3695847528745754500698685)
                    ·
                      refine ⟨1385942823279657937762007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3695847528745754500698685 1385942823279657937762007)
                      ·
                        rfl

theorem cell23_2699114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_2699114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699114 prefixEnd_2699114 := by exact prefixLift 2699114
  have htrace : WordTrace (prefixWord ++ tailWord_2699114) baseStart_2699114 baseEnd_2699114 := by
    simpa [prefixWord, tailWord_2699114, baseEnd_2699114] using wordTrace_append hprefix tailTrace_2699114
  have hstable : (prefixWord ++ tailWord_2699114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699114).length < 2 ^ (prefixWord ++ tailWord_2699114).sum := by decide
  have hdescent : baseEnd_2699114 < baseStart_2699114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699133 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_2699133 : Nat := 118140960795 + 2699133 * 2 ^ 59
def prefixEnd_2699133 : Nat := 4983230072969 + 3 ^ 40 * 2699133 * 2
def baseEnd_2699133 : Nat := 1385952579412093363424419

theorem tailTrace_2699133 : CollatzResearch.WordTrace tailWord_2699133 prefixEnd_2699133 1385952579412093363424419 := by
  unfold tailWord_2699133
  simp only [CollatzResearch.WordTrace]
  refine ⟨98445468130509591061398053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65630312087006394040932035 98445468130509591061398053)
  ·
    refine ⟨18458525274470548324012135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98445468130509591061398053 18458525274470548324012135)
    ·
      refine ⟨27687787911705822486018203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18458525274470548324012135 27687787911705822486018203)
      ·
        refine ⟨41531681867558733729027305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27687787911705822486018203 41531681867558733729027305)
        ·
          refine ⟨31148761400669050296770479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41531681867558733729027305 31148761400669050296770479)
          ·
            refine ⟨46723142101003575445155719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31148761400669050296770479 46723142101003575445155719)
            ·
              refine ⟨70084713151505363167733579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46723142101003575445155719 70084713151505363167733579)
              ·
                refine ⟨105127069727258044751600369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70084713151505363167733579 105127069727258044751600369)
                ·
                  refine ⟨78845302295443533563700277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105127069727258044751600369 78845302295443533563700277)
                  ·
                    refine ⟨7391747090197831271596901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78845302295443533563700277 7391747090197831271596901)
                    ·
                      refine ⟨1385952579412093363424419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7391747090197831271596901 1385952579412093363424419)
                      ·
                        rfl

theorem cell23_2699133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_2699133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699133 prefixEnd_2699133 := by exact prefixLift 2699133
  have htrace : WordTrace (prefixWord ++ tailWord_2699133) baseStart_2699133 baseEnd_2699133 := by
    simpa [prefixWord, tailWord_2699133, baseEnd_2699133] using wordTrace_append hprefix tailTrace_2699133
  have hstable : (prefixWord ++ tailWord_2699133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699133).length < 2 ^ (prefixWord ++ tailWord_2699133).sum := by decide
  have hdescent : baseEnd_2699133 < baseStart_2699133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699134 : List Nat := [4, 2, 3, 1, 1, 1, 4, 1, 6]
def baseStart_2699134 : Nat := 118140960795 + 2699134 * 2 ^ 59
def prefixEnd_2699134 : Nat := 4983230072969 + 3 ^ 40 * 2699134 * 2
def baseEnd_2699134 : Nat := 153994788099194206612435

theorem tailTrace_2699134 : CollatzResearch.WordTrace tailWord_2699134 prefixEnd_2699134 153994788099194206612435 := by
  unfold tailWord_2699134
  simp only [CollatzResearch.WordTrace]
  refine ⟨12305688075438246029023057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65630336402337312154789637 12305688075438246029023057)
  ·
    refine ⟨9229266056578684521767293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12305688075438246029023057 9229266056578684521767293)
    ·
      refine ⟨3460974771217006695662735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9229266056578684521767293 3460974771217006695662735)
      ·
        refine ⟨5191462156825510043494103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3460974771217006695662735 5191462156825510043494103)
        ·
          refine ⟨7787193235238265065241155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5191462156825510043494103 7787193235238265065241155)
          ·
            refine ⟨11680789852857397597861733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7787193235238265065241155 11680789852857397597861733)
            ·
              refine ⟨2190148097410762049599075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11680789852857397597861733 2190148097410762049599075)
              ·
                refine ⟨3285222146116143074398613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190148097410762049599075 3285222146116143074398613)
                ·
                  refine ⟨153994788099194206612435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3285222146116143074398613 153994788099194206612435)
                  ·
                    rfl

theorem cell23_2699134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_2699134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699134 prefixEnd_2699134 := by exact prefixLift 2699134
  have htrace : WordTrace (prefixWord ++ tailWord_2699134) baseStart_2699134 baseEnd_2699134 := by
    simpa [prefixWord, tailWord_2699134, baseEnd_2699134] using wordTrace_append hprefix tailTrace_2699134
  have hstable : (prefixWord ++ tailWord_2699134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699134).length < 2 ^ (prefixWord ++ tailWord_2699134).sum := by decide
  have hdescent : baseEnd_2699134 < baseStart_2699134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699153 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 5]
def baseStart_2699153 : Nat := 118140960795 + 2699153 * 2 ^ 59
def prefixEnd_2699153 : Nat := 4983230072969 + 3 ^ 40 * 2699153 * 2
def baseEnd_2699153 : Nat := 1385962849025183285174327

theorem tailTrace_2699153 : CollatzResearch.WordTrace tailWord_2699153 prefixEnd_2699153 1385962849025183285174327 := by
  unfold tailWord_2699153
  simp only [CollatzResearch.WordTrace]
  refine ⟨98446197590437134477126113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65630798393624756318084075 98446197590437134477126113)
  ·
    refine ⟨73834648192827850857844585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98446197590437134477126113 73834648192827850857844585)
    ·
      refine ⟨55375986144620888143383439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73834648192827850857844585 55375986144620888143383439)
      ·
        refine ⟨83063979216931332215075159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55375986144620888143383439 83063979216931332215075159)
        ·
          refine ⟨124595968825396998322612739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83063979216931332215075159 124595968825396998322612739)
          ·
            refine ⟨186893953238095497483919109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124595968825396998322612739 186893953238095497483919109)
            ·
              refine ⟨35042616232142905778234833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186893953238095497483919109 35042616232142905778234833)
              ·
                refine ⟨26281962174107179333676125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35042616232142905778234833 26281962174107179333676125)
                ·
                  refine ⟨9855735815290192250128547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26281962174107179333676125 9855735815290192250128547)
                  ·
                    refine ⟨14783603722935288375192821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9855735815290192250128547 14783603722935288375192821)
                    ·
                      refine ⟨1385962849025183285174327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14783603722935288375192821 1385962849025183285174327)
                      ·
                        rfl

theorem cell23_2699153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_2699153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699153 prefixEnd_2699153 := by exact prefixLift 2699153
  have htrace : WordTrace (prefixWord ++ tailWord_2699153) baseStart_2699153 baseEnd_2699153 := by
    simpa [prefixWord, tailWord_2699153, baseEnd_2699153] using wordTrace_append hprefix tailTrace_2699153
  have hstable : (prefixWord ++ tailWord_2699153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699153).length < 2 ^ (prefixWord ++ tailWord_2699153).sum := by decide
  have hdescent : baseEnd_2699153 < baseStart_2699153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699154 : List Nat := [3, 2, 3, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_2699154 : Nat := 118140960795 + 2699154 * 2 ^ 59
def prefixEnd_2699154 : Nat := 4983230072969 + 3 ^ 40 * 2699154 * 2
def baseEnd_2699154 : Nat := 1385963362505837781261823

theorem tailTrace_2699154 : CollatzResearch.WordTrace tailWord_2699154 prefixEnd_2699154 1385963362505837781261823 := by
  unfold tailWord_2699154
  simp only [CollatzResearch.WordTrace]
  refine ⟨24611558515858377911978129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65630822708955674431941677 24611558515858377911978129)
  ·
    refine ⟨18458668886893783433983597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24611558515858377911978129 18458668886893783433983597)
    ·
      refine ⟨6922000832585168787743849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18458668886893783433983597 6922000832585168787743849)
      ·
        refine ⟨5191500624438876590807887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6922000832585168787743849 5191500624438876590807887)
        ·
          refine ⟨7787250936658314886211831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5191500624438876590807887 7787250936658314886211831)
          ·
            refine ⟨11680876404987472329317747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7787250936658314886211831 11680876404987472329317747)
            ·
              refine ⟨17521314607481208493976621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11680876404987472329317747 17521314607481208493976621)
              ·
                refine ⟨6570492977805453185241233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17521314607481208493976621 6570492977805453185241233)
                ·
                  refine ⟨4927869733354089888930925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6570492977805453185241233 4927869733354089888930925)
                  ·
                    refine ⟨1847951150007783708349097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4927869733354089888930925 1847951150007783708349097)
                    ·
                      refine ⟨1385963362505837781261823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1847951150007783708349097 1385963362505837781261823)
                      ·
                        rfl

theorem cell23_2699154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_2699154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699154 prefixEnd_2699154 := by exact prefixLift 2699154
  have htrace : WordTrace (prefixWord ++ tailWord_2699154) baseStart_2699154 baseEnd_2699154 := by
    simpa [prefixWord, tailWord_2699154, baseEnd_2699154] using wordTrace_append hprefix tailTrace_2699154
  have hstable : (prefixWord ++ tailWord_2699154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699154).length < 2 ^ (prefixWord ++ tailWord_2699154).sum := by decide
  have hdescent : baseEnd_2699154 < baseStart_2699154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699164 : List Nat := [2, 2, 3, 3, 1, 2, 3, 1, 1, 5]
def baseStart_2699164 : Nat := 118140960795 + 2699164 * 2 ^ 59
def prefixEnd_2699164 : Nat := 4983230072969 + 3 ^ 40 * 2699164 * 2
def baseEnd_2699164 : Nat := 461989499104127580712259

theorem tailTrace_2699164 : CollatzResearch.WordTrace tailWord_2699164 prefixEnd_2699164 461989499104127580712259 := by
  unfold tailWord_2699164
  simp only [CollatzResearch.WordTrace]
  refine ⟨49223299396698641677888273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65631065862264855570517697 49223299396698641677888273)
  ·
    refine ⟨36917474547523981258416205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49223299396698641677888273 36917474547523981258416205)
    ·
      refine ⟨13844052955321492971906077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36917474547523981258416205 13844052955321492971906077)
      ·
        refine ⟨5191519858245559864464779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13844052955321492971906077 5191519858245559864464779)
        ·
          refine ⟨7787279787368339796697169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5191519858245559864464779 7787279787368339796697169)
          ·
            refine ⟨5840459840526254847522877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7787279787368339796697169 5840459840526254847522877)
            ·
              refine ⟨2190172440197345567821079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5840459840526254847522877 2190172440197345567821079)
              ·
                refine ⟨3285258660296018351731619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190172440197345567821079 3285258660296018351731619)
                ·
                  refine ⟨4927887990444027527597429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3285258660296018351731619 4927887990444027527597429)
                  ·
                    refine ⟨461989499104127580712259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4927887990444027527597429 461989499104127580712259)
                    ·
                      rfl

theorem cell23_2699164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_2699164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699164 prefixEnd_2699164 := by exact prefixLift 2699164
  have htrace : WordTrace (prefixWord ++ tailWord_2699164) baseStart_2699164 baseEnd_2699164 := by
    simpa [prefixWord, tailWord_2699164, baseEnd_2699164] using wordTrace_append hprefix tailTrace_2699164
  have hstable : (prefixWord ++ tailWord_2699164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699164).length < 2 ^ (prefixWord ++ tailWord_2699164).sum := by decide
  have hdescent : baseEnd_2699164 < baseStart_2699164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699197 : List Nat := [1, 4, 1, 2, 3, 2, 2, 1, 1, 2, 4]
def baseStart_2699197 : Nat := 118140960795 + 2699197 * 2 ^ 59
def prefixEnd_2699197 : Nat := 4983230072969 + 3 ^ 40 * 2699197 * 2
def baseEnd_2699197 : Nat := 1385985442173981113024125

theorem tailTrace_2699197 : CollatzResearch.WordTrace tailWord_2699197 prefixEnd_2699197 1385985442173981113024125 := by
  unfold tailWord_2699197
  simp only [CollatzResearch.WordTrace]
  refine ⟨98447802402277729991727845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65631868268185153327818563 98447802402277729991727845)
  ·
    refine ⟨18458962950427074373448971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98447802402277729991727845 18458962950427074373448971)
    ·
      refine ⟨27688444425640611560173457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18458962950427074373448971 27688444425640611560173457)
      ·
        refine ⟨20766333319230458670130093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27688444425640611560173457 20766333319230458670130093)
        ·
          refine ⟨7787374994711422001298785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20766333319230458670130093 7787374994711422001298785)
          ·
            refine ⟨5840531246033566500974089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7787374994711422001298785 5840531246033566500974089)
            ·
              refine ⟨4380398434525174875730567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5840531246033566500974089 4380398434525174875730567)
              ·
                refine ⟨6570597651787762313595851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4380398434525174875730567 6570597651787762313595851)
                ·
                  refine ⟨9855896477681643470393777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6570597651787762313595851 9855896477681643470393777)
                  ·
                    refine ⟨7391922358261232602795333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9855896477681643470393777 7391922358261232602795333)
                    ·
                      refine ⟨1385985442173981113024125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7391922358261232602795333 1385985442173981113024125)
                      ·
                        rfl

theorem cell23_2699197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_2699197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699197 prefixEnd_2699197 := by exact prefixLift 2699197
  have htrace : WordTrace (prefixWord ++ tailWord_2699197) baseStart_2699197 baseEnd_2699197 := by
    simpa [prefixWord, tailWord_2699197, baseEnd_2699197] using wordTrace_append hprefix tailTrace_2699197
  have hstable : (prefixWord ++ tailWord_2699197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699197).length < 2 ^ (prefixWord ++ tailWord_2699197).sum := by decide
  have hdescent : baseEnd_2699197 < baseStart_2699197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699218 : List Nat := [3, 2, 2, 3, 3, 1, 2, 1, 1, 1, 4]
def baseStart_2699218 : Nat := 118140960795 + 2699218 * 2 ^ 59
def prefixEnd_2699218 : Nat := 4983230072969 + 3 ^ 40 * 2699218 * 2
def baseEnd_2699218 : Nat := 1385996225267725530861529

theorem tailTrace_2699218 : CollatzResearch.WordTrace tailWord_2699218 prefixEnd_2699218 1385996225267725530861529 := by
  unfold tailWord_2699218
  simp only [CollatzResearch.WordTrace]
  refine ⟨24612142083800412644560577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65632378890134433718828205 24612142083800412644560577)
  ·
    refine ⟨18459106562850309483420433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24612142083800412644560577 18459106562850309483420433)
    ·
      refine ⟨13844329922137732112565325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18459106562850309483420433 13844329922137732112565325)
      ·
        refine ⟨5191623720801649542211997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13844329922137732112565325 5191623720801649542211997)
        ·
          refine ⟨1946858895300618578329499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5191623720801649542211997 1946858895300618578329499)
          ·
            refine ⟨2920288342950927867494249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1946858895300618578329499 2920288342950927867494249)
            ·
              refine ⟨2190216257213195900620687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2920288342950927867494249 2190216257213195900620687)
              ·
                refine ⟨3285324385819793850931031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190216257213195900620687 3285324385819793850931031)
                ·
                  refine ⟨4927986578729690776396547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3285324385819793850931031 4927986578729690776396547)
                  ·
                    refine ⟨7391979868094536164594821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4927986578729690776396547 7391979868094536164594821)
                    ·
                      refine ⟨1385996225267725530861529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7391979868094536164594821 1385996225267725530861529)
                      ·
                        rfl

theorem cell23_2699218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_2699218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699218 prefixEnd_2699218 := by exact prefixLift 2699218
  have htrace : WordTrace (prefixWord ++ tailWord_2699218) baseStart_2699218 baseEnd_2699218 := by
    simpa [prefixWord, tailWord_2699218, baseEnd_2699218] using wordTrace_append hprefix tailTrace_2699218
  have hstable : (prefixWord ++ tailWord_2699218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699218).length < 2 ^ (prefixWord ++ tailWord_2699218).sum := by decide
  have hdescent : baseEnd_2699218 < baseStart_2699218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699221 : List Nat := [1, 3, 2, 3, 2, 3, 2, 1, 1, 2, 3]
def baseStart_2699221 : Nat := 118140960795 + 2699221 * 2 ^ 59
def prefixEnd_2699221 : Nat := 4983230072969 + 3 ^ 40 * 2699221 * 2
def baseEnd_2699221 : Nat := 1385997765709689019124015

theorem tailTrace_2699221 : CollatzResearch.WordTrace tailWord_2699221 prefixEnd_2699221 1385997765709689019124015 := by
  unfold tailWord_2699221
  simp only [CollatzResearch.WordTrace]
  refine ⟨98448677754190782090601517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65632451836127188060401011 98448677754190782090601517)
  ·
    refine ⟨36918254157821543283975569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98448677754190782090601517 36918254157821543283975569)
    ·
      refine ⟨27688690618366157462981677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36918254157821543283975569 27688690618366157462981677)
      ·
        refine ⟨10383258981887309048618129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27688690618366157462981677 10383258981887309048618129)
        ·
          refine ⟨7787444236415481786463597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10383258981887309048618129 7787444236415481786463597)
          ·
            refine ⟨2920291588655805669923849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7787444236415481786463597 2920291588655805669923849)
            ·
              refine ⟨2190218691491854252442887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2920291588655805669923849 2190218691491854252442887)
              ·
                refine ⟨3285328037237781378664331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190218691491854252442887 3285328037237781378664331)
                ·
                  refine ⟨4927992055856672067996497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3285328037237781378664331 4927992055856672067996497)
                  ·
                    refine ⟨3695994041892504050997373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4927992055856672067996497 3695994041892504050997373)
                    ·
                      refine ⟨1385997765709689019124015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3695994041892504050997373 1385997765709689019124015)
                      ·
                        rfl

theorem cell23_2699221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_2699221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699221 prefixEnd_2699221 := by exact prefixLift 2699221
  have htrace : WordTrace (prefixWord ++ tailWord_2699221) baseStart_2699221 baseEnd_2699221 := by
    simpa [prefixWord, tailWord_2699221, baseEnd_2699221] using wordTrace_append hprefix tailTrace_2699221
  have hstable : (prefixWord ++ tailWord_2699221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699221).length < 2 ^ (prefixWord ++ tailWord_2699221).sum := by decide
  have hdescent : baseEnd_2699221 < baseStart_2699221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699260 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_2699260 : Nat := 118140960795 + 2699260 * 2 ^ 59
def prefixEnd_2699260 : Nat := 4983230072969 + 3 ^ 40 * 2699260 * 2
def baseEnd_2699260 : Nat := 1386017791455214366536335

theorem tailTrace_2699260 : CollatzResearch.WordTrace tailWord_2699260 prefixEnd_2699260 1386017791455214366536335 := by
  unfold tailWord_2699260
  simp only [CollatzResearch.WordTrace]
  refine ⟨49225050100524745875635617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65633400134032994500847489 49225050100524745875635617)
  ·
    refine ⟨36918787575393559406726713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49225050100524745875635617 36918787575393559406726713)
    ·
      refine ⟨27689090681545169555045035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36918787575393559406726713 27689090681545169555045035)
      ·
        refine ⟨41533636022317754332567553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27689090681545169555045035 41533636022317754332567553)
        ·
          refine ⟨31150227016738315749425665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41533636022317754332567553 31150227016738315749425665)
          ·
            refine ⟨23362670262553736812069249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31150227016738315749425665 23362670262553736812069249)
            ·
              refine ⟨17522002696915302609051937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23362670262553736812069249 17522002696915302609051937)
              ·
                refine ⟨13141502022686476956788953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17522002696915302609051937 13141502022686476956788953)
                ·
                  refine ⟨9856126517014857717591715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13141502022686476956788953 9856126517014857717591715)
                  ·
                    refine ⟨14784189775522286576387573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9856126517014857717591715 14784189775522286576387573)
                    ·
                      refine ⟨1386017791455214366536335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14784189775522286576387573 1386017791455214366536335)
                      ·
                        rfl

theorem cell23_2699260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_2699260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699260 prefixEnd_2699260 := by exact prefixLift 2699260
  have htrace : WordTrace (prefixWord ++ tailWord_2699260) baseStart_2699260 baseEnd_2699260 := by
    simpa [prefixWord, tailWord_2699260, baseEnd_2699260] using wordTrace_append hprefix tailTrace_2699260
  have hstable : (prefixWord ++ tailWord_2699260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699260).length < 2 ^ (prefixWord ++ tailWord_2699260).sum := by decide
  have hdescent : baseEnd_2699260 < baseStart_2699260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699358 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_2699358 : Nat := 118140960795 + 2699358 * 2 ^ 59
def prefixEnd_2699358 : Nat := 4983230072969 + 3 ^ 40 * 2699358 * 2
def baseEnd_2699358 : Nat := 1386068112559354983110885

theorem tailTrace_2699358 : CollatzResearch.WordTrace tailWord_2699358 prefixEnd_2699358 1386068112559354983110885 := by
  unfold tailWord_2699358
  simp only [CollatzResearch.WordTrace]
  refine ⟨12306709319336806811042341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65635783036462969658892485 12306709319336806811042341)
  ·
    refine ⟨2307507997375651277070439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12306709319336806811042341 2307507997375651277070439)
    ·
      refine ⟨3461261996063476915605659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2307507997375651277070439 3461261996063476915605659)
      ·
        refine ⟨5191892994095215373408489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3461261996063476915605659 5191892994095215373408489)
        ·
          refine ⟨3893919745571411530056367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5191892994095215373408489 3893919745571411530056367)
          ·
            refine ⟨5840879618357117295084551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3893919745571411530056367 5840879618357117295084551)
            ·
              refine ⟨8761319427535675942626827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5840879618357117295084551 8761319427535675942626827)
              ·
                refine ⟨13141979141303513913940241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8761319427535675942626827 13141979141303513913940241)
                ·
                  refine ⟨9856484355977635435455181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13141979141303513913940241 9856484355977635435455181)
                  ·
                    refine ⟨3696181633491613288295693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9856484355977635435455181 3696181633491613288295693)
                    ·
                      refine ⟨1386068112559354983110885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3696181633491613288295693 1386068112559354983110885)
                      ·
                        rfl

theorem cell23_2699358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_2699358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699358 prefixEnd_2699358 := by exact prefixLift 2699358
  have htrace : WordTrace (prefixWord ++ tailWord_2699358) baseStart_2699358 baseEnd_2699358 := by
    simpa [prefixWord, tailWord_2699358, baseEnd_2699358] using wordTrace_append hprefix tailTrace_2699358
  have hstable : (prefixWord ++ tailWord_2699358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699358).length < 2 ^ (prefixWord ++ tailWord_2699358).sum := by decide
  have hdescent : baseEnd_2699358 < baseStart_2699358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699367 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_2699367 : Nat := 118140960795 + 2699367 * 2 ^ 59
def prefixEnd_2699367 : Nat := 4983230072969 + 3 ^ 40 * 2699367 * 2
def baseEnd_2699367 : Nat := 1386072733885245447898343

theorem tailTrace_2699367 : CollatzResearch.WordTrace tailWord_2699367 prefixEnd_2699367 1386072733885245447898343 := by
  unfold tailWord_2699367
  simp only [CollatzResearch.WordTrace]
  refine ⟨98454002811661849025416355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65636001874441232683610903 98454002811661849025416355)
  ·
    refine ⟨147681004217492773538124533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98454002811661849025416355 147681004217492773538124533)
    ·
      refine ⟨13845094145389947519199175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147681004217492773538124533 13845094145389947519199175)
      ·
        refine ⟨20767641218084921278798763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13845094145389947519199175 20767641218084921278798763)
        ·
          refine ⟨31151461827127381918198145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20767641218084921278798763 31151461827127381918198145)
          ·
            refine ⟨23363596370345536438648609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31151461827127381918198145 23363596370345536438648609)
            ·
              refine ⟨17522697277759152328986457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23363596370345536438648609 17522697277759152328986457)
              ·
                refine ⟨13142022958319364246739843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17522697277759152328986457 13142022958319364246739843)
                ·
                  refine ⟨19713034437479046370109765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13142022958319364246739843 19713034437479046370109765)
                  ·
                    refine ⟨3696193957027321194395581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19713034437479046370109765 3696193957027321194395581)
                    ·
                      refine ⟨1386072733885245447898343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3696193957027321194395581 1386072733885245447898343)
                      ·
                        rfl

theorem cell23_2699367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_2699367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699367 prefixEnd_2699367 := by exact prefixLift 2699367
  have htrace : WordTrace (prefixWord ++ tailWord_2699367) baseStart_2699367 baseEnd_2699367 := by
    simpa [prefixWord, tailWord_2699367, baseEnd_2699367] using wordTrace_append hprefix tailTrace_2699367
  have hstable : (prefixWord ++ tailWord_2699367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699367).length < 2 ^ (prefixWord ++ tailWord_2699367).sum := by decide
  have hdescent : baseEnd_2699367 < baseStart_2699367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699374 : List Nat := [4, 1, 2, 2, 1, 1, 3, 2, 3, 4]
def baseStart_2699374 : Nat := 118140960795 + 2699374 * 2 ^ 59
def prefixEnd_2699374 : Nat := 4983230072969 + 3 ^ 40 * 2699374 * 2
def baseEnd_2699374 : Nat := 462025442749942306836937

theorem tailTrace_2699374 : CollatzResearch.WordTrace tailWord_2699374 prefixEnd_2699374 462025442749942306836937 := by
  unfold tailWord_2699374
  simp only [CollatzResearch.WordTrace]
  refine ⟨12306782265329561152615147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65636172081757659480614117 12306782265329561152615147)
  ·
    refine ⟨18460173397994341728922721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12306782265329561152615147 18460173397994341728922721)
    ·
      refine ⟨13845130048495756296692041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18460173397994341728922721 13845130048495756296692041)
      ·
        refine ⟨10383847536371817222519031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13845130048495756296692041 10383847536371817222519031)
        ·
          refine ⟨15575771304557725833778547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10383847536371817222519031 15575771304557725833778547)
          ·
            refine ⟨23363656956836588750667821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15575771304557725833778547 23363656956836588750667821)
            ·
              refine ⟨8761371358813720781500433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23363656956836588750667821 8761371358813720781500433)
              ·
                refine ⟨6571028519110290586125325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8761371358813720781500433 6571028519110290586125325)
                ·
                  refine ⟨2464135694666358969796997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6571028519110290586125325 2464135694666358969796997)
                  ·
                    refine ⟨462025442749942306836937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2464135694666358969796997 462025442749942306836937)
                    ·
                      rfl

theorem cell23_2699374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_2699374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699374 prefixEnd_2699374 := by exact prefixLift 2699374
  have htrace : WordTrace (prefixWord ++ tailWord_2699374) baseStart_2699374 baseEnd_2699374 := by
    simpa [prefixWord, tailWord_2699374, baseEnd_2699374] using wordTrace_append hprefix tailTrace_2699374
  have hstable : (prefixWord ++ tailWord_2699374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699374).length < 2 ^ (prefixWord ++ tailWord_2699374).sum := by decide
  have hdescent : baseEnd_2699374 < baseStart_2699374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699424 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 1, 5, 2]
def baseStart_2699424 : Nat := 118140960795 + 2699424 * 2 ^ 59
def prefixEnd_2699424 : Nat := 4983230072969 + 3 ^ 40 * 2699424 * 2
def baseEnd_2699424 : Nat := 1386102002282551724885581

theorem tailTrace_2699424 : CollatzResearch.WordTrace tailWord_2699424 prefixEnd_2699424 1386102002282551724885581 := by
  unfold tailWord_2699424
  simp only [CollatzResearch.WordTrace]
  refine ⟨49228040886227673880120663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65637387848303565173494217 49228040886227673880120663)
  ·
    refine ⟨73842061329341510820180995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49228040886227673880120663 73842061329341510820180995)
    ·
      refine ⟨110763091994012266230271493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73842061329341510820180995 110763091994012266230271493)
      ·
        refine ⟨20768079748877299918175905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110763091994012266230271493 20768079748877299918175905)
        ·
          refine ⟨15576059811657974938631929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20768079748877299918175905 15576059811657974938631929)
          ·
            refine ⟨11682044858743481203973947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15576059811657974938631929 11682044858743481203973947)
            ·
              refine ⟨17523067288115221805960921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11682044858743481203973947 17523067288115221805960921)
              ·
                refine ⟨13142300466086416354470691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17523067288115221805960921 13142300466086416354470691)
                ·
                  refine ⟨19713450699129624531706037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13142300466086416354470691 19713450699129624531706037)
                  ·
                    refine ⟨1848136003043402299847441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19713450699129624531706037 1848136003043402299847441)
                    ·
                      refine ⟨1386102002282551724885581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1848136003043402299847441 1386102002282551724885581)
                      ·
                        rfl

theorem cell23_2699424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_2699424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699424 prefixEnd_2699424 := by exact prefixLift 2699424
  have htrace : WordTrace (prefixWord ++ tailWord_2699424) baseStart_2699424 baseEnd_2699424 := by
    simpa [prefixWord, tailWord_2699424, baseEnd_2699424] using wordTrace_append hprefix tailTrace_2699424
  have hstable : (prefixWord ++ tailWord_2699424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699424).length < 2 ^ (prefixWord ++ tailWord_2699424).sum := by decide
  have hdescent : baseEnd_2699424 < baseStart_2699424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699464 : List Nat := [2, 1, 3, 1, 2, 1, 1, 6, 2, 4]
def baseStart_2699464 : Nat := 118140960795 + 2699464 * 2 ^ 59
def prefixEnd_2699464 : Nat := 4983230072969 + 3 ^ 40 * 2699464 * 2
def baseEnd_2699464 : Nat := 462040847169577189461799

theorem tailTrace_2699464 : CollatzResearch.WordTrace tailWord_2699464 prefixEnd_2699464 462040847169577189461799 := by
  unfold tailWord_2699464
  simp only [CollatzResearch.WordTrace]
  refine ⟨49228770346155217295848723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65638360461540289727798297 49228770346155217295848723)
  ·
    refine ⟨73843155519232825943773085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49228770346155217295848723 73843155519232825943773085)
    ·
      refine ⟨27691183319712309728914907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73843155519232825943773085 27691183319712309728914907)
      ·
        refine ⟨41536774979568464593372361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27691183319712309728914907 41536774979568464593372361)
        ·
          refine ⟨31152581234676348445029271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41536774979568464593372361 31152581234676348445029271)
          ·
            refine ⟨46728871852014522667543907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31152581234676348445029271 46728871852014522667543907)
            ·
              refine ⟨70093307778021784001315861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46728871852014522667543907 70093307778021784001315861)
              ·
                refine ⟨3285623802094771125061681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70093307778021784001315861 3285623802094771125061681)
                ·
                  refine ⟨2464217851571078343796261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3285623802094771125061681 2464217851571078343796261)
                  ·
                    refine ⟨462040847169577189461799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2464217851571078343796261 462040847169577189461799)
                    ·
                      rfl

theorem cell23_2699464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_2699464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699464 prefixEnd_2699464 := by exact prefixLift 2699464
  have htrace : WordTrace (prefixWord ++ tailWord_2699464) baseStart_2699464 baseEnd_2699464 := by
    simpa [prefixWord, tailWord_2699464, baseEnd_2699464] using wordTrace_append hprefix tailTrace_2699464
  have hstable : (prefixWord ++ tailWord_2699464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699464).length < 2 ^ (prefixWord ++ tailWord_2699464).sum := by decide
  have hdescent : baseEnd_2699464 < baseStart_2699464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699474 : List Nat := [3, 2, 2, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_2699474 : Nat := 118140960795 + 2699474 * 2 ^ 59
def prefixEnd_2699474 : Nat := 4983230072969 + 3 ^ 40 * 2699474 * 2
def baseEnd_2699474 : Nat := 1386127676315276529260351

theorem tailTrace_2699474 : CollatzResearch.WordTrace tailWord_2699474 prefixEnd_2699474 1386127676315276529260351 := by
  unfold tailWord_2699474
  simp only [CollatzResearch.WordTrace]
  refine ⟨24614476355568551574890369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65638603614849470866374317 24614476355568551574890369)
  ·
    refine ⟨18460857266676413681167777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24614476355568551574890369 18460857266676413681167777)
    ·
      refine ⟨13845642950007310260875833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18460857266676413681167777 13845642950007310260875833)
      ·
        refine ⟨10384232212505482695656875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13845642950007310260875833 10384232212505482695656875)
        ·
          refine ⟨15576348318758224043485313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10384232212505482695656875 15576348318758224043485313)
          ·
            refine ⟨11682261239068668032613985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15576348318758224043485313 11682261239068668032613985)
            ·
              refine ⟨8761695929301501024460489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11682261239068668032613985 8761695929301501024460489)
              ·
                refine ⟨6571271946976125768345367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8761695929301501024460489 6571271946976125768345367)
                ·
                  refine ⟨9856907920464188652518051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6571271946976125768345367 9856907920464188652518051)
                  ·
                    refine ⟨14785361880696282978777077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9856907920464188652518051 14785361880696282978777077)
                    ·
                      refine ⟨1386127676315276529260351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14785361880696282978777077 1386127676315276529260351)
                      ·
                        rfl

theorem cell23_2699474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_2699474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699474 prefixEnd_2699474 := by exact prefixLift 2699474
  have htrace : WordTrace (prefixWord ++ tailWord_2699474) baseStart_2699474 baseEnd_2699474 := by
    simpa [prefixWord, tailWord_2699474, baseEnd_2699474] using wordTrace_append hprefix tailTrace_2699474
  have hstable : (prefixWord ++ tailWord_2699474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699474).length < 2 ^ (prefixWord ++ tailWord_2699474).sum := by decide
  have hdescent : baseEnd_2699474 < baseStart_2699474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699481 : List Nat := [1, 2, 1, 2, 3, 1, 6, 1, 2, 4]
def baseStart_2699481 : Nat := 118140960795 + 2699481 * 2 ^ 59
def prefixEnd_2699481 : Nat := 4983230072969 + 3 ^ 40 * 2699481 * 2
def baseEnd_2699481 : Nat := 462043756893286000624273

theorem tailTrace_2699481 : CollatzResearch.WordTrace tailWord_2699481 prefixEnd_2699481 462043756893286000624273 := by
  unfold tailWord_2699481
  simp only [CollatzResearch.WordTrace]
  refine ⟨98458160733248846495066297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65638773822165897663377531 98458160733248846495066297)
  ·
    refine ⟨73843620549936634871299723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98458160733248846495066297 73843620549936634871299723)
    ·
      refine ⟨110765430824904952306949585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73843620549936634871299723 110765430824904952306949585)
      ·
        refine ⟨83074073118678714230212189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110765430824904952306949585 83074073118678714230212189)
        ·
          refine ⟨31152777419504517836329571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83074073118678714230212189 31152777419504517836329571)
          ·
            refine ⟨46729166129256776754494357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31152777419504517836329571 46729166129256776754494357)
            ·
              refine ⟨2190429662308911410366923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46729166129256776754494357 2190429662308911410366923)
              ·
                refine ⟨3285644493463367115550385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190429662308911410366923 3285644493463367115550385)
                ·
                  refine ⟨2464233370097525336662789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3285644493463367115550385 2464233370097525336662789)
                  ·
                    refine ⟨462043756893286000624273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2464233370097525336662789 462043756893286000624273)
                    ·
                      rfl

theorem cell23_2699481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 2, 4].length) (baseStart_2699481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699481 prefixEnd_2699481 := by exact prefixLift 2699481
  have htrace : WordTrace (prefixWord ++ tailWord_2699481) baseStart_2699481 baseEnd_2699481 := by
    simpa [prefixWord, tailWord_2699481, baseEnd_2699481] using wordTrace_append hprefix tailTrace_2699481
  have hstable : (prefixWord ++ tailWord_2699481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699481).length < 2 ^ (prefixWord ++ tailWord_2699481).sum := by decide
  have hdescent : baseEnd_2699481 < baseStart_2699481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699501 : List Nat := [1, 5, 1, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_2699501 : Nat := 118140960795 + 2699501 * 2 ^ 59
def prefixEnd_2699501 : Nat := 4983230072969 + 3 ^ 40 * 2699501 * 2
def baseEnd_2699501 : Nat := 1386141540292947923622727

theorem tailTrace_2699501 : CollatzResearch.WordTrace tailWord_2699501 prefixEnd_2699501 1386141540292947923622727 := by
  unfold tailWord_2699501
  simp only [CollatzResearch.WordTrace]
  refine ⟨98458890193176389910794357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65639260128784259940529571 98458890193176389910794357)
  ·
    refine ⟨9230520955610286554136971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98458890193176389910794357 9230520955610286554136971)
    ·
      refine ⟨13845781433415429831205457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9230520955610286554136971 13845781433415429831205457)
      ·
        refine ⟨10384336075061572373404093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13845781433415429831205457 10384336075061572373404093)
        ·
          refine ⟨3894126028148089640026535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10384336075061572373404093 3894126028148089640026535)
          ·
            refine ⟨5841189042222134460039803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3894126028148089640026535 5841189042222134460039803)
            ·
              refine ⟨8761783563333201690059705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5841189042222134460039803 8761783563333201690059705)
              ·
                refine ⟨6571337672499901267544779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8761783563333201690059705 6571337672499901267544779)
                ·
                  refine ⟨9857006508749851901317169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6571337672499901267544779 9857006508749851901317169)
                  ·
                    refine ⟨7392754881562388925987877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9857006508749851901317169 7392754881562388925987877)
                    ·
                      refine ⟨1386141540292947923622727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7392754881562388925987877 1386141540292947923622727)
                      ·
                        rfl

theorem cell23_2699501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_2699501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699501 prefixEnd_2699501 := by exact prefixLift 2699501
  have htrace : WordTrace (prefixWord ++ tailWord_2699501) baseStart_2699501 baseEnd_2699501 := by
    simpa [prefixWord, tailWord_2699501, baseEnd_2699501] using wordTrace_append hprefix tailTrace_2699501
  have hstable : (prefixWord ++ tailWord_2699501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699501).length < 2 ^ (prefixWord ++ tailWord_2699501).sum := by decide
  have hdescent : baseEnd_2699501 < baseStart_2699501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699504 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 6, 1, 3]
def baseStart_2699504 : Nat := 118140960795 + 2699504 * 2 ^ 59
def prefixEnd_2699504 : Nat := 4983230072969 + 3 ^ 40 * 2699504 * 2
def baseEnd_2699504 : Nat := 1386143080734911411885213

theorem tailTrace_2699504 : CollatzResearch.WordTrace tailWord_2699504 prefixEnd_2699504 1386143080734911411885213 := by
  unfold tailWord_2699504
  simp only [CollatzResearch.WordTrace]
  refine ⟨49229499806082760711576783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65639333074777014282102377 49229499806082760711576783)
  ·
    refine ⟨73844249709124141067365175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49229499806082760711576783 73844249709124141067365175)
    ·
      refine ⟨110766374563686211601047763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73844249709124141067365175 110766374563686211601047763)
      ·
        refine ⟨166149561845529317401571645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110766374563686211601047763 166149561845529317401571645)
        ·
          refine ⟨62306085692073494025589367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166149561845529317401571645 62306085692073494025589367)
          ·
            refine ⟨93459128538110241038384051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62306085692073494025589367 93459128538110241038384051)
            ·
              refine ⟨140188692807165361557576077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93459128538110241038384051 140188692807165361557576077)
              ·
                refine ⟨52570759802687010584091029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140188692807165361557576077 52570759802687010584091029)
                ·
                  refine ⟨2464254365750953621129267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52570759802687010584091029 2464254365750953621129267)
                  ·
                    refine ⟨3696381548626430431693901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2464254365750953621129267 3696381548626430431693901)
                    ·
                      refine ⟨1386143080734911411885213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3696381548626430431693901 1386143080734911411885213)
                      ·
                        rfl

theorem cell23_2699504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 6, 1, 3].length) (baseStart_2699504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699504 prefixEnd_2699504 := by exact prefixLift 2699504
  have htrace : WordTrace (prefixWord ++ tailWord_2699504) baseStart_2699504 baseEnd_2699504 := by
    simpa [prefixWord, tailWord_2699504, baseEnd_2699504] using wordTrace_append hprefix tailTrace_2699504
  have hstable : (prefixWord ++ tailWord_2699504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699504).length < 2 ^ (prefixWord ++ tailWord_2699504).sum := by decide
  have hdescent : baseEnd_2699504 < baseStart_2699504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699517 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_2699517 : Nat := 118140960795 + 2699517 * 2 ^ 59
def prefixEnd_2699517 : Nat := 4983230072969 + 3 ^ 40 * 2699517 * 2
def baseEnd_2699517 : Nat := 1386149755983419861022653

theorem tailTrace_2699517 : CollatzResearch.WordTrace tailWord_2699517 prefixEnd_2699517 1386149755983419861022653 := by
  unfold tailWord_2699517
  simp only [CollatzResearch.WordTrace]
  refine ⟨98459473761118424643376805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65639649174078949762251203 98459473761118424643376805)
  ·
    refine ⟨18461151330209704620633151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98459473761118424643376805 18461151330209704620633151)
    ·
      refine ⟨27691726995314556930949727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18461151330209704620633151 27691726995314556930949727)
      ·
        refine ⟨41537590492971835396424591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27691726995314556930949727 41537590492971835396424591)
        ·
          refine ⟨62306385739457753094636887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41537590492971835396424591 62306385739457753094636887)
          ·
            refine ⟨93459578609186629641955331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62306385739457753094636887 93459578609186629641955331)
            ·
              refine ⟨140189367913779944462932997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93459578609186629641955331 140189367913779944462932997)
              ·
                refine ⟨26285506483833739586799937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140189367913779944462932997 26285506483833739586799937)
                ·
                  refine ⟨19714129862875304690099953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26285506483833739586799937 19714129862875304690099953)
                  ·
                    refine ⟨14785597397156478517574965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19714129862875304690099953 14785597397156478517574965)
                    ·
                      refine ⟨1386149755983419861022653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14785597397156478517574965 1386149755983419861022653)
                      ·
                        rfl

theorem cell23_2699517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_2699517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699517 prefixEnd_2699517 := by exact prefixLift 2699517
  have htrace : WordTrace (prefixWord ++ tailWord_2699517) baseStart_2699517 baseEnd_2699517 := by
    simpa [prefixWord, tailWord_2699517, baseEnd_2699517] using wordTrace_append hprefix tailTrace_2699517
  have hstable : (prefixWord ++ tailWord_2699517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699517).length < 2 ^ (prefixWord ++ tailWord_2699517).sum := by decide
  have hdescent : baseEnd_2699517 < baseStart_2699517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699522 : List Nat := [3, 4, 1, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_2699522 : Nat := 118140960795 + 2699522 * 2 ^ 59
def prefixEnd_2699522 : Nat := 4983230072969 + 3 ^ 40 * 2699522 * 2
def baseEnd_2699522 : Nat := 1386152323386692341460131

theorem tailTrace_2699522 : CollatzResearch.WordTrace tailWord_2699522 prefixEnd_2699522 1386152323386692341460131 := by
  unfold tailWord_2699522
  simp only [CollatzResearch.WordTrace]
  refine ⟨24614914031525077624327205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65639770750733540331539213 24614914031525077624327205)
  ·
    refine ⟨4615296380910952054561351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24614914031525077624327205 4615296380910952054561351)
    ·
      refine ⟨6922944571366428081842027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4615296380910952054561351 6922944571366428081842027)
      ·
        refine ⟨10384416857049642122763041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6922944571366428081842027 10384416857049642122763041)
        ·
          refine ⟨7788312642787231592072281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10384416857049642122763041 7788312642787231592072281)
          ·
            refine ⟨5841234482090423694054211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7788312642787231592072281 5841234482090423694054211)
            ·
              refine ⟨8761851723135635541081317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5841234482090423694054211 8761851723135635541081317)
              ·
                refine ⟨1642847198087931663952747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8761851723135635541081317 1642847198087931663952747)
                ·
                  refine ⟨2464270797131897495929121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1642847198087931663952747 2464270797131897495929121)
                  ·
                    refine ⟨1848203097848923121946841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2464270797131897495929121 1848203097848923121946841)
                    ·
                      refine ⟨1386152323386692341460131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1848203097848923121946841 1386152323386692341460131)
                      ·
                        rfl

theorem cell23_2699522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_2699522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699522 prefixEnd_2699522 := by exact prefixLift 2699522
  have htrace : WordTrace (prefixWord ++ tailWord_2699522) baseStart_2699522 baseEnd_2699522 := by
    simpa [prefixWord, tailWord_2699522, baseEnd_2699522] using wordTrace_append hprefix tailTrace_2699522
  have hstable : (prefixWord ++ tailWord_2699522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699522).length < 2 ^ (prefixWord ++ tailWord_2699522).sum := by decide
  have hdescent : baseEnd_2699522 < baseStart_2699522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699537 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 1, 8]
def baseStart_2699537 : Nat := 118140960795 + 2699537 * 2 ^ 59
def prefixEnd_2699537 : Nat := 4983230072969 + 3 ^ 40 * 2699537 * 2
def baseEnd_2699537 : Nat := 462053341865503260924187

theorem tailTrace_2699537 : CollatzResearch.WordTrace tailWord_2699537 prefixEnd_2699537 462053341865503260924187 := by
  unfold tailWord_2699537
  simp only [CollatzResearch.WordTrace]
  refine ⟨98460203221045968059104865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65640135480697312039403243 98460203221045968059104865)
  ·
    refine ⟨73845152415784476044328649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98460203221045968059104865 73845152415784476044328649)
    ·
      refine ⟨55383864311838357033246487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73845152415784476044328649 55383864311838357033246487)
      ·
        refine ⟨83075796467757535549869731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55383864311838357033246487 83075796467757535549869731)
        ·
          refine ⟨124613694701636303324804597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83075796467757535549869731 124613694701636303324804597)
          ·
            refine ⟨11682533878278403436700431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124613694701636303324804597 11682533878278403436700431)
            ·
              refine ⟨17523800817417605155050647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11682533878278403436700431 17523800817417605155050647)
              ·
                refine ⟨26285701226126407732575971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17523800817417605155050647 26285701226126407732575971)
                ·
                  refine ⟨39428551839189611598863957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26285701226126407732575971 39428551839189611598863957)
                  ·
                    refine ⟨462053341865503260924187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39428551839189611598863957 462053341865503260924187)
                    ·
                      rfl

theorem cell23_2699537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_2699537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699537 prefixEnd_2699537 := by exact prefixLift 2699537
  have htrace : WordTrace (prefixWord ++ tailWord_2699537) baseStart_2699537 baseEnd_2699537 := by
    simpa [prefixWord, tailWord_2699537, baseEnd_2699537] using wordTrace_append hprefix tailTrace_2699537
  have hstable : (prefixWord ++ tailWord_2699537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699537).length < 2 ^ (prefixWord ++ tailWord_2699537).sum := by decide
  have hdescent : baseEnd_2699537 < baseStart_2699537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699547 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 5]
def baseStart_2699547 : Nat := 118140960795 + 2699547 * 2 ^ 59
def prefixEnd_2699547 : Nat := 4983230072969 + 3 ^ 40 * 2699547 * 2
def baseEnd_2699547 : Nat := 1386165160403054743647515

theorem tailTrace_2699547 : CollatzResearch.WordTrace tailWord_2699547 prefixEnd_2699547 1386165160403054743647515 := by
  unfold tailWord_2699547
  simp only [CollatzResearch.WordTrace]
  refine ⟨98460567951009739766968895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65640378634006493177979263 98460567951009739766968895)
  ·
    refine ⟨147690851926514609650453343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98460567951009739766968895 147690851926514609650453343)
    ·
      refine ⟨221536277889771914475680015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147690851926514609650453343 221536277889771914475680015)
      ·
        refine ⟨332304416834657871713520023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221536277889771914475680015 332304416834657871713520023)
        ·
          refine ⟨498456625251986807570280035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332304416834657871713520023 498456625251986807570280035)
          ·
            refine ⟨747684937877980211355420053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498456625251986807570280035 747684937877980211355420053)
            ·
              refine ⟨35047731463030322407285315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 747684937877980211355420053 35047731463030322407285315)
              ·
                refine ⟨52571597194545483610927973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35047731463030322407285315 52571597194545483610927973)
                ·
                  refine ⟨9857174473977278177048995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52571597194545483610927973 9857174473977278177048995)
                  ·
                    refine ⟨14785761710965917265573493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9857174473977278177048995 14785761710965917265573493)
                    ·
                      refine ⟨1386165160403054743647515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14785761710965917265573493 1386165160403054743647515)
                      ·
                        rfl

theorem cell23_2699547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 5].length) (baseStart_2699547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699547 prefixEnd_2699547 := by exact prefixLift 2699547
  have htrace : WordTrace (prefixWord ++ tailWord_2699547) baseStart_2699547 baseEnd_2699547 := by
    simpa [prefixWord, tailWord_2699547, baseEnd_2699547] using wordTrace_append hprefix tailTrace_2699547
  have hstable : (prefixWord ++ tailWord_2699547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699547).length < 2 ^ (prefixWord ++ tailWord_2699547).sum := by decide
  have hdescent : baseEnd_2699547 < baseStart_2699547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699559 : List Nat := [1, 1, 8, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_2699559 : Nat := 118140960795 + 2699559 * 2 ^ 59
def prefixEnd_2699559 : Nat := 4983230072969 + 3 ^ 40 * 2699559 * 2
def baseEnd_2699559 : Nat := 1386171322170908696697461

theorem tailTrace_2699559 : CollatzResearch.WordTrace tailWord_2699559 prefixEnd_2699559 1386171322170908696697461 := by
  unfold tailWord_2699559
  simp only [CollatzResearch.WordTrace]
  refine ⟨98461005626966265816405731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65640670417977510544270487 98461005626966265816405731)
  ·
    refine ⟨147691508440449398724608597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98461005626966265816405731 147691508440449398724608597)
    ·
      refine ⟨1730759864536516391304007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 147691508440449398724608597 1730759864536516391304007)
      ·
        refine ⟨2596139796804774586956011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1730759864536516391304007 2596139796804774586956011)
        ·
          refine ⟨3894209695207161880434017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2596139796804774586956011 3894209695207161880434017)
          ·
            refine ⟨2920657271405371410325513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3894209695207161880434017 2920657271405371410325513)
            ·
              refine ⟨2190492953554028557744135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2920657271405371410325513 2190492953554028557744135)
              ·
                refine ⟨3285739430331042836616203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190492953554028557744135 3285739430331042836616203)
                ·
                  refine ⟨4928609145496564254924305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3285739430331042836616203 4928609145496564254924305)
                  ·
                    refine ⟨3696456859122423191193229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4928609145496564254924305 3696456859122423191193229)
                    ·
                      refine ⟨1386171322170908696697461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3696456859122423191193229 1386171322170908696697461)
                      ·
                        rfl

theorem cell23_2699559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_2699559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699559 prefixEnd_2699559 := by exact prefixLift 2699559
  have htrace : WordTrace (prefixWord ++ tailWord_2699559) baseStart_2699559 baseEnd_2699559 := by
    simpa [prefixWord, tailWord_2699559, baseEnd_2699559] using wordTrace_append hprefix tailTrace_2699559
  have hstable : (prefixWord ++ tailWord_2699559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699559).length < 2 ^ (prefixWord ++ tailWord_2699559).sum := by decide
  have hdescent : baseEnd_2699559 < baseStart_2699559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699578 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2]
def baseStart_2699578 : Nat := 118140960795 + 2699578 * 2 ^ 59
def prefixEnd_2699578 : Nat := 4983230072969 + 3 ^ 40 * 2699578 * 2
def baseEnd_2699578 : Nat := 1386181078303344122359873

theorem tailTrace_2699578 : CollatzResearch.WordTrace tailWord_2699578 prefixEnd_2699578 1386181078303344122359873 := by
  unfold tailWord_2699578
  simp only [CollatzResearch.WordTrace]
  refine ⟨24615424653474358015336847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65641132409264954707564925 24615424653474358015336847)
  ·
    refine ⟨36923136980211537023005271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24615424653474358015336847 36923136980211537023005271)
    ·
      refine ⟨55384705470317305534507907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36923136980211537023005271 55384705470317305534507907)
      ·
        refine ⟨83077058205475958301761861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55384705470317305534507907 83077058205475958301761861)
        ·
          refine ⟨15576948413526742181580349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83077058205475958301761861 15576948413526742181580349)
          ·
            refine ⟨5841355655072528318092631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15576948413526742181580349 5841355655072528318092631)
            ·
              refine ⟨8762033482608792477138947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5841355655072528318092631 8762033482608792477138947)
              ·
                refine ⟨13143050223913188715708421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8762033482608792477138947 13143050223913188715708421)
                ·
                  refine ⟨2464321916983722884195329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13143050223913188715708421 2464321916983722884195329)
                  ·
                    refine ⟨1848241437737792163146497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2464321916983722884195329 1848241437737792163146497)
                    ·
                      refine ⟨1386181078303344122359873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1848241437737792163146497 1386181078303344122359873)
                      ·
                        rfl

theorem cell23_2699578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2].length) (baseStart_2699578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699578 prefixEnd_2699578 := by exact prefixLift 2699578
  have htrace : WordTrace (prefixWord ++ tailWord_2699578) baseStart_2699578 baseEnd_2699578 := by
    simpa [prefixWord, tailWord_2699578, baseEnd_2699578] using wordTrace_append hprefix tailTrace_2699578
  have hstable : (prefixWord ++ tailWord_2699578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699578).length < 2 ^ (prefixWord ++ tailWord_2699578).sum := by decide
  have hdescent : baseEnd_2699578 < baseStart_2699578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699618 : List Nat := [3, 3, 2, 1, 1, 2, 3, 3, 5]
def baseStart_2699618 : Nat := 118140960795 + 2699618 * 2 ^ 59
def prefixEnd_2699618 : Nat := 4983230072969 + 3 ^ 40 * 2699618 * 2
def baseEnd_2699618 : Nat := 154022401947724885095521

theorem tailTrace_2699618 : CollatzResearch.WordTrace tailWord_2699618 prefixEnd_2699618 154022401947724885095521 := by
  unfold tailWord_2699618
  simp only [CollatzResearch.WordTrace]
  refine ⟨24615789383438129723200877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65642105022501679261869005 24615789383438129723200877)
  ·
    refine ⟨9230921018789298646200329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24615789383438129723200877 9230921018789298646200329)
    ·
      refine ⟨6923190764091973984650247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9230921018789298646200329 6923190764091973984650247)
      ·
        refine ⟨10384786146137960976975371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6923190764091973984650247 10384786146137960976975371)
        ·
          refine ⟨15577179219206941465463057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10384786146137960976975371 15577179219206941465463057)
          ·
            refine ⟨11682884414405206099097293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15577179219206941465463057 11682884414405206099097293)
            ·
              refine ⟨4381081655401952287161485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11682884414405206099097293 4381081655401952287161485)
              ·
                refine ⟨1642905620775732107685557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4381081655401952287161485 1642905620775732107685557)
                ·
                  refine ⟨154022401947724885095521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1642905620775732107685557 154022401947724885095521)
                  ·
                    rfl

theorem cell23_2699618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_2699618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699618 prefixEnd_2699618 := by exact prefixLift 2699618
  have htrace : WordTrace (prefixWord ++ tailWord_2699618) baseStart_2699618 baseEnd_2699618 := by
    simpa [prefixWord, tailWord_2699618, baseEnd_2699618] using wordTrace_append hprefix tailTrace_2699618
  have hstable : (prefixWord ++ tailWord_2699618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699618).length < 2 ^ (prefixWord ++ tailWord_2699618).sum := by decide
  have hdescent : baseEnd_2699618 < baseStart_2699618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699627 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 1, 10]
def baseStart_2699627 : Nat := 118140960795 + 2699627 * 2 ^ 59
def prefixEnd_2699627 : Nat := 4983230072969 + 3 ^ 40 * 2699627 * 2
def baseEnd_2699627 : Nat := 462068746285138143549049

theorem tailTrace_2699627 : CollatzResearch.WordTrace tailWord_2699627 prefixEnd_2699627 462068746285138143549049 := by
  unfold tailWord_2699627
  simp only [CollatzResearch.WordTrace]
  refine ⟨98463485790719913429881135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65642323860479942286587423 98463485790719913429881135)
  ·
    refine ⟨147695228686079870144821703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98463485790719913429881135 147695228686079870144821703)
    ·
      refine ⟨221542843029119805217232555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147695228686079870144821703 221542843029119805217232555)
      ·
        refine ⟨332314264543679707825848833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221542843029119805217232555 332314264543679707825848833)
        ·
          refine ⟨249235698407759780869386625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332314264543679707825848833 249235698407759780869386625)
          ·
            refine ⟨186926773805819835652039969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249235698407759780869386625 186926773805819835652039969)
            ·
              refine ⟨140195080354364876739029977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186926773805819835652039969 140195080354364876739029977)
              ·
                refine ⟨105146310265773657554272483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140195080354364876739029977 105146310265773657554272483)
                ·
                  refine ⟨157719465398660486331408725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105146310265773657554272483 157719465398660486331408725)
                  ·
                    refine ⟨462068746285138143549049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 157719465398660486331408725 462068746285138143549049)
                    ·
                      rfl

theorem cell23_2699627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 10].length) (baseStart_2699627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699627 prefixEnd_2699627 := by exact prefixLift 2699627
  have htrace : WordTrace (prefixWord ++ tailWord_2699627) baseStart_2699627 baseEnd_2699627 := by
    simpa [prefixWord, tailWord_2699627, baseEnd_2699627] using wordTrace_append hprefix tailTrace_2699627
  have hstable : (prefixWord ++ tailWord_2699627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699627).length < 2 ^ (prefixWord ++ tailWord_2699627).sum := by decide
  have hdescent : baseEnd_2699627 < baseStart_2699627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699671 : List Nat := [1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 3]
def baseStart_2699671 : Nat := 118140960795 + 2699671 * 2 ^ 59
def prefixEnd_2699671 : Nat := 4983230072969 + 3 ^ 40 * 2699671 * 2
def baseEnd_2699671 : Nat := 1386228832004212258496945

theorem tailTrace_2699671 : CollatzResearch.WordTrace tailWord_2699671 prefixEnd_2699671 1386228832004212258496945 := by
  unfold tailWord_2699671
  simp only [CollatzResearch.WordTrace]
  refine ⟨98465090602560508944482867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65643393735040339296321911 98465090602560508944482867)
  ·
    refine ⟨147697635903840763416724301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98465090602560508944482867 147697635903840763416724301)
    ·
      refine ⟨55386613463940286281271613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147697635903840763416724301 55386613463940286281271613)
      ·
        refine ⟨20769980048977607355476855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55386613463940286281271613 20769980048977607355476855)
        ·
          refine ⟨31154970073466411033215283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20769980048977607355476855 31154970073466411033215283)
          ·
            refine ⟨46732455110199616549822925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31154970073466411033215283 46732455110199616549822925)
            ·
              refine ⟨17524670666324856206183597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46732455110199616549822925 17524670666324856206183597)
              ·
                refine ⟨6571751499871821077318849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17524670666324856206183597 6571751499871821077318849)
                ·
                  refine ⟨4928813624903865807989137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6571751499871821077318849 4928813624903865807989137)
                  ·
                    refine ⟨3696610218677899355991853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4928813624903865807989137 3696610218677899355991853)
                    ·
                      refine ⟨1386228832004212258496945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3696610218677899355991853 1386228832004212258496945)
                      ·
                        rfl

theorem cell23_2699671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_2699671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699671 prefixEnd_2699671 := by exact prefixLift 2699671
  have htrace : WordTrace (prefixWord ++ tailWord_2699671) baseStart_2699671 baseEnd_2699671 := by
    simpa [prefixWord, tailWord_2699671, baseEnd_2699671] using wordTrace_append hprefix tailTrace_2699671
  have hstable : (prefixWord ++ tailWord_2699671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699671).length < 2 ^ (prefixWord ++ tailWord_2699671).sum := by decide
  have hdescent : baseEnd_2699671 < baseStart_2699671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699761 : List Nat := [1, 2, 2, 2, 3, 1, 3, 2, 1, 1, 5]
def baseStart_2699761 : Nat := 118140960795 + 2699761 * 2 ^ 59
def prefixEnd_2699761 : Nat := 4983230072969 + 3 ^ 40 * 2699761 * 2
def baseEnd_2699761 : Nat := 1386275045263116906371531

theorem tailTrace_2699761 : CollatzResearch.WordTrace tailWord_2699761 prefixEnd_2699761 1386275045263116906371531 := by
  unfold tailWord_2699761
  simp only [CollatzResearch.WordTrace]
  refine ⟨98468373172234454315259137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65645582114822969543506091 98468373172234454315259137)
  ·
    refine ⟨73851279879175840736444353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98468373172234454315259137 73851279879175840736444353)
    ·
      refine ⟨55388459909381880552333265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73851279879175840736444353 55388459909381880552333265)
      ·
        refine ⟨41541344932036410414249949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55388459909381880552333265 41541344932036410414249949)
        ·
          refine ⟨15578004349513653905343731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41541344932036410414249949 15578004349513653905343731)
          ·
            refine ⟨23367006524270480858015597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15578004349513653905343731 23367006524270480858015597)
            ·
              refine ⟨8762627446601430321755849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23367006524270480858015597 8762627446601430321755849)
              ·
                refine ⟨6571970584951072741316887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8762627446601430321755849 6571970584951072741316887)
                ·
                  refine ⟨9857955877426609111975331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6571970584951072741316887 9857955877426609111975331)
                  ·
                    refine ⟨14786933816139913667962997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9857955877426609111975331 14786933816139913667962997)
                    ·
                      refine ⟨1386275045263116906371531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14786933816139913667962997 1386275045263116906371531)
                      ·
                        rfl

theorem cell23_2699761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_2699761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699761 prefixEnd_2699761 := by exact prefixLift 2699761
  have htrace : WordTrace (prefixWord ++ tailWord_2699761) baseStart_2699761 baseEnd_2699761 := by
    simpa [prefixWord, tailWord_2699761, baseEnd_2699761] using wordTrace_append hprefix tailTrace_2699761
  have hstable : (prefixWord ++ tailWord_2699761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699761).length < 2 ^ (prefixWord ++ tailWord_2699761).sum := by decide
  have hdescent : baseEnd_2699761 < baseStart_2699761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699781 : List Nat := [1, 3, 1, 1, 2, 2, 6, 7]
def baseStart_2699781 : Nat := 118140960795 + 2699781 * 2 ^ 59
def prefixEnd_2699781 : Nat := 4983230072969 + 3 ^ 40 * 2699781 * 2
def baseEnd_2699781 : Nat := 51343900550970623263757

theorem tailTrace_2699781 : CollatzResearch.WordTrace tailWord_2699781 prefixEnd_2699781 51343900550970623263757 := by
  unfold tailWord_2699781
  simp only [CollatzResearch.WordTrace]
  refine ⟨98469102632161997730987197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65646068421441331820658131 98469102632161997730987197)
  ·
    refine ⟨36925913487060749149120199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98469102632161997730987197 36925913487060749149120199)
    ·
      refine ⟨55388870230591123723680299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36925913487060749149120199 55388870230591123723680299)
      ·
        refine ⟨83083305345886685585520449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55388870230591123723680299 83083305345886685585520449)
        ·
          refine ⟨62312479009415014189140337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83083305345886685585520449 62312479009415014189140337)
          ·
            refine ⟨46734359257061260641855253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62312479009415014189140337 46734359257061260641855253)
            ·
              refine ⟨2190673090174746592586965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46734359257061260641855253 2190673090174746592586965)
              ·
                refine ⟨51343900550970623263757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2190673090174746592586965 51343900550970623263757)
                ·
                  rfl

theorem cell23_2699781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 7].length) (baseStart_2699781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699781 prefixEnd_2699781 := by exact prefixLift 2699781
  have htrace : WordTrace (prefixWord ++ tailWord_2699781) baseStart_2699781 baseEnd_2699781 := by
    simpa [prefixWord, tailWord_2699781, baseEnd_2699781] using wordTrace_append hprefix tailTrace_2699781
  have hstable : (prefixWord ++ tailWord_2699781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699781).length < 2 ^ (prefixWord ++ tailWord_2699781).sum := by decide
  have hdescent : baseEnd_2699781 < baseStart_2699781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699809 : List Nat := [1, 2, 3, 2, 2, 1, 5, 2, 1, 2, 2]
def baseStart_2699809 : Nat := 118140960795 + 2699809 * 2 ^ 59
def prefixEnd_2699809 : Nat := 4983230072969 + 3 ^ 40 * 2699809 * 2
def baseEnd_2699809 : Nat := 1386299692334532718571311

theorem tailTrace_2699809 : CollatzResearch.WordTrace tailWord_2699809 prefixEnd_2699809 1386299692334532718571311 := by
  unfold tailWord_2699809
  simp only [CollatzResearch.WordTrace]
  refine ⟨98470123876060558513006481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65646749250707039008670987 98470123876060558513006481)
  ·
    refine ⟨73852592907045418884754861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98470123876060558513006481 73852592907045418884754861)
    ·
      refine ⟨27694722340142032081783073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73852592907045418884754861 27694722340142032081783073)
      ·
        refine ⟨20771041755106524061337305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27694722340142032081783073 20771041755106524061337305)
        ·
          refine ⟨15578281316329893046002979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20771041755106524061337305 15578281316329893046002979)
          ·
            refine ⟨23367421974494839569004469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15578281316329893046002979 23367421974494839569004469)
            ·
              refine ⟨2190695810108891209594169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23367421974494839569004469 2190695810108891209594169)
              ·
                refine ⟨1643021857581668407195627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2190695810108891209594169 1643021857581668407195627)
                ·
                  refine ⟨2464532786372502610793441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1643021857581668407195627 2464532786372502610793441)
                  ·
                    refine ⟨1848399589779376958095081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2464532786372502610793441 1848399589779376958095081)
                    ·
                      refine ⟨1386299692334532718571311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1848399589779376958095081 1386299692334532718571311)
                      ·
                        rfl

theorem cell23_2699809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_2699809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699809 prefixEnd_2699809 := by exact prefixLift 2699809
  have htrace : WordTrace (prefixWord ++ tailWord_2699809) baseStart_2699809 baseEnd_2699809 := by
    simpa [prefixWord, tailWord_2699809, baseEnd_2699809] using wordTrace_append hprefix tailTrace_2699809
  have hstable : (prefixWord ++ tailWord_2699809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699809).length < 2 ^ (prefixWord ++ tailWord_2699809).sum := by decide
  have hdescent : baseEnd_2699809 < baseStart_2699809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699815 : List Nat := [1, 1, 7, 2, 1, 1, 2, 8]
def baseStart_2699815 : Nat := 118140960795 + 2699815 * 2 ^ 59
def prefixEnd_2699815 : Nat := 4983230072969 + 3 ^ 40 * 2699815 * 2
def baseEnd_2699815 : Nat := 51344547156239247966529

theorem tailTrace_2699815 : CollatzResearch.WordTrace tailWord_2699815 prefixEnd_2699815 51344547156239247966529 := by
  unfold tailWord_2699815
  simp only [CollatzResearch.WordTrace]
  refine ⟨98470342714038821537724899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65646895142692547691816599 98470342714038821537724899)
  ·
    refine ⟨147705514071058232306587349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98470342714038821537724899 147705514071058232306587349)
    ·
      refine ⟨3461847986040427319685641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 147705514071058232306587349 3461847986040427319685641)
      ·
        refine ⟨2596385989530320489764231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3461847986040427319685641 2596385989530320489764231)
        ·
          refine ⟨3894578984295480734646347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2596385989530320489764231 3894578984295480734646347)
          ·
            refine ⟨5841868476443221101969521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3894578984295480734646347 5841868476443221101969521)
            ·
              refine ⟨4381401357332415826477141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5841868476443221101969521 4381401357332415826477141)
              ·
                refine ⟨51344547156239247966529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4381401357332415826477141 51344547156239247966529)
                ·
                  rfl

theorem cell23_2699815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 8].length) (baseStart_2699815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699815 prefixEnd_2699815 := by exact prefixLift 2699815
  have htrace : WordTrace (prefixWord ++ tailWord_2699815) baseStart_2699815 baseEnd_2699815 := by
    simpa [prefixWord, tailWord_2699815, baseEnd_2699815] using wordTrace_append hprefix tailTrace_2699815
  have hstable : (prefixWord ++ tailWord_2699815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699815).length < 2 ^ (prefixWord ++ tailWord_2699815).sum := by decide
  have hdescent : baseEnd_2699815 < baseStart_2699815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699851 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 5]
def baseStart_2699851 : Nat := 118140960795 + 2699851 * 2 ^ 59
def prefixEnd_2699851 : Nat := 4983230072969 + 3 ^ 40 * 2699851 * 2
def baseEnd_2699851 : Nat := 1386321258522021554246117

theorem tailTrace_2699851 : CollatzResearch.WordTrace tailWord_2699851 prefixEnd_2699851 1386321258522021554246117 := by
  unfold tailWord_2699851
  simp only [CollatzResearch.WordTrace]
  refine ⟨98471655741908399686035407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65647770494605599790690271 98471655741908399686035407)
  ·
    refine ⟨147707483612862599529053111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98471655741908399686035407 147707483612862599529053111)
    ·
      refine ⟨221561225419293899293579667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147707483612862599529053111 221561225419293899293579667)
      ·
        refine ⟨332341838128940848940369501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221561225419293899293579667 332341838128940848940369501)
        ·
          refine ⟨124628189298352818352638563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332341838128940848940369501 124628189298352818352638563)
          ·
            refine ⟨186942283947529227528957845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124628189298352818352638563 186942283947529227528957845)
            ·
              refine ⟨8762919560040432540419899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 186942283947529227528957845 8762919560040432540419899)
              ·
                refine ⟨13144379340060648810629849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8762919560040432540419899 13144379340060648810629849)
                ·
                  refine ⟨9858284505045486607972387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13144379340060648810629849 9858284505045486607972387)
                  ·
                    refine ⟨14787426757568229911958581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9858284505045486607972387 14787426757568229911958581)
                    ·
                      refine ⟨1386321258522021554246117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14787426757568229911958581 1386321258522021554246117)
                      ·
                        rfl

theorem cell23_2699851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 5].length) (baseStart_2699851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699851 prefixEnd_2699851 := by exact prefixLift 2699851
  have htrace : WordTrace (prefixWord ++ tailWord_2699851) baseStart_2699851 baseEnd_2699851 := by
    simpa [prefixWord, tailWord_2699851, baseEnd_2699851] using wordTrace_append hprefix tailTrace_2699851
  have hstable : (prefixWord ++ tailWord_2699851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699851).length < 2 ^ (prefixWord ++ tailWord_2699851).sum := by decide
  have hdescent : baseEnd_2699851 < baseStart_2699851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699852 : List Nat := [2, 2, 1, 3, 1, 2, 5, 1, 1, 3, 2]
def baseStart_2699852 : Nat := 118140960795 + 2699852 * 2 ^ 59
def prefixEnd_2699852 : Nat := 4983230072969 + 3 ^ 40 * 2699852 * 2
def baseEnd_2699852 : Nat := 1386321772002676050333613

theorem tailTrace_2699852 : CollatzResearch.WordTrace tailWord_2699852 prefixEnd_2699852 1386321772002676050333613 := by
  unfold tailWord_2699852
  simp only [CollatzResearch.WordTrace]
  refine ⟨49235846107452388428410905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65647794809936517904547873 49235846107452388428410905)
  ·
    refine ⟨36926884580589291321308179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49235846107452388428410905 36926884580589291321308179)
    ·
      refine ⟨55390326870883936981962269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36926884580589291321308179 55390326870883936981962269)
      ·
        refine ⟨20771372576581476368235851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55390326870883936981962269 20771372576581476368235851)
        ·
          refine ⟨31157058864872214552353777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20771372576581476368235851 31157058864872214552353777)
          ·
            refine ⟨23367794148654160914265333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31157058864872214552353777 23367794148654160914265333)
            ·
              refine ⟨2190730701436327585712375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23367794148654160914265333 2190730701436327585712375)
              ·
                refine ⟨3286096052154491378568563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190730701436327585712375 3286096052154491378568563)
                ·
                  refine ⟨4929144078231737067852845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3286096052154491378568563 4929144078231737067852845)
                  ·
                    refine ⟨1848429029336901400444817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4929144078231737067852845 1848429029336901400444817)
                    ·
                      refine ⟨1386321772002676050333613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1848429029336901400444817 1386321772002676050333613)
                      ·
                        rfl

theorem cell23_2699852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_2699852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699852 prefixEnd_2699852 := by exact prefixLift 2699852
  have htrace : WordTrace (prefixWord ++ tailWord_2699852) baseStart_2699852 baseEnd_2699852 := by
    simpa [prefixWord, tailWord_2699852, baseEnd_2699852] using wordTrace_append hprefix tailTrace_2699852
  have hstable : (prefixWord ++ tailWord_2699852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699852).length < 2 ^ (prefixWord ++ tailWord_2699852).sum := by decide
  have hdescent : baseEnd_2699852 < baseStart_2699852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699882 : List Nat := [3, 1, 3, 2, 1, 1, 1, 5, 2, 2, 2]
def baseStart_2699882 : Nat := 118140960795 + 2699882 * 2 ^ 59
def prefixEnd_2699882 : Nat := 4983230072969 + 3 ^ 40 * 2699882 * 2
def baseEnd_2699882 : Nat := 1386337176422310932958475

theorem tailTrace_2699882 : CollatzResearch.WordTrace tailWord_2699882 prefixEnd_2699882 1386337176422310932958475 := by
  unfold tailWord_2699882
  simp only [CollatzResearch.WordTrace]
  refine ⟨24618196601199022995103475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65648524269864061320275933 24618196601199022995103475)
  ·
    refine ⟨36927294901798534492655213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24618196601199022995103475 36927294901798534492655213)
    ·
      refine ⟨13847735588174450434745705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36927294901798534492655213 13847735588174450434745705)
      ·
        refine ⟨10385801691130837826059279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13847735588174450434745705 10385801691130837826059279)
        ·
          refine ⟨15578702536696256739088919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10385801691130837826059279 15578702536696256739088919)
          ·
            refine ⟨23368053805044385108633379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15578702536696256739088919 23368053805044385108633379)
            ·
              refine ⟨35052080707566577662950069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23368053805044385108633379 35052080707566577662950069)
              ·
                refine ⟨3286132566334366655901569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35052080707566577662950069 3286132566334366655901569)
                ·
                  refine ⟨2464599424750774991926177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3286132566334366655901569 2464599424750774991926177)
                  ·
                    refine ⟨1848449568563081243944633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2464599424750774991926177 1848449568563081243944633)
                    ·
                      refine ⟨1386337176422310932958475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1848449568563081243944633 1386337176422310932958475)
                      ·
                        rfl

theorem cell23_2699882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_2699882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699882 prefixEnd_2699882 := by exact prefixLift 2699882
  have htrace : WordTrace (prefixWord ++ tailWord_2699882) baseStart_2699882 baseEnd_2699882 := by
    simpa [prefixWord, tailWord_2699882, baseEnd_2699882] using wordTrace_append hprefix tailTrace_2699882
  have hstable : (prefixWord ++ tailWord_2699882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699882).length < 2 ^ (prefixWord ++ tailWord_2699882).sum := by decide
  have hdescent : baseEnd_2699882 < baseStart_2699882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699888 : List Nat := [2, 1, 1, 1, 7, 1, 1, 2, 7]
def baseStart_2699888 : Nat := 118140960795 + 2699888 * 2 ^ 59
def prefixEnd_2699888 : Nat := 4983230072969 + 3 ^ 40 * 2699888 * 2
def baseEnd_2699888 : Nat := 154037806367359767720383

theorem tailTrace_2699888 : CollatzResearch.WordTrace tailWord_2699888 prefixEnd_2699888 154037806367359767720383 := by
  unfold tailWord_2699888
  simp only [CollatzResearch.WordTrace]
  refine ⟨49236502621387177502566159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65648670161849570003421545 49236502621387177502566159)
  ·
    refine ⟨73854753932080766253849239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49236502621387177502566159 73854753932080766253849239)
    ·
      refine ⟨110782130898121149380773859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73854753932080766253849239 110782130898121149380773859)
      ·
        refine ⟨166173196347181724071160789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110782130898121149380773859 166173196347181724071160789)
        ·
          refine ⟨3894684289387071657917831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 166173196347181724071160789 3894684289387071657917831)
          ·
            refine ⟨5842026434080607486876747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3894684289387071657917831 5842026434080607486876747)
            ·
              refine ⟨8763039651120911230315121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5842026434080607486876747 8763039651120911230315121)
              ·
                refine ⟨6572279738340683422736341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8763039651120911230315121 6572279738340683422736341)
                ·
                  refine ⟨154037806367359767720383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6572279738340683422736341 154037806367359767720383)
                  ·
                    rfl

theorem cell23_2699888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 7].length) (baseStart_2699888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699888 prefixEnd_2699888 := by exact prefixLift 2699888
  have htrace : WordTrace (prefixWord ++ tailWord_2699888) baseStart_2699888 baseEnd_2699888 := by
    simpa [prefixWord, tailWord_2699888, baseEnd_2699888] using wordTrace_append hprefix tailTrace_2699888
  have hstable : (prefixWord ++ tailWord_2699888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699888).length < 2 ^ (prefixWord ++ tailWord_2699888).sum := by decide
  have hdescent : baseEnd_2699888 < baseStart_2699888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699905 : List Nat := [1, 2, 4, 2, 1, 1, 4, 3, 5]
def baseStart_2699905 : Nat := 118140960795 + 2699905 * 2 ^ 59
def prefixEnd_2699905 : Nat := 4983230072969 + 3 ^ 40 * 2699905 * 2
def baseEnd_2699905 : Nat := 154038776275262704774541

theorem tailTrace_2699905 : CollatzResearch.WordTrace tailWord_2699905 prefixEnd_2699905 154038776275262704774541 := by
  unfold tailWord_2699905
  simp only [CollatzResearch.WordTrace]
  refine ⟨98473625283712766908501169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65649083522475177939000779 98473625283712766908501169)
  ·
    refine ⟨73855218962784575181375877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98473625283712766908501169 73855218962784575181375877)
    ·
      refine ⟨13847853555522107846507977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73855218962784575181375877 13847853555522107846507977)
      ·
        refine ⟨10385890166641580884880983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13847853555522107846507977 10385890166641580884880983)
        ·
          refine ⟨15578835249962371327321475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10385890166641580884880983 15578835249962371327321475)
          ·
            refine ⟨23368252874943556990982213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15578835249962371327321475 23368252874943556990982213)
            ·
              refine ⟨4381547414051916935809165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23368252874943556990982213 4381547414051916935809165)
              ·
                refine ⟨1643080280269468850928437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4381547414051916935809165 1643080280269468850928437)
                ·
                  refine ⟨154038776275262704774541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1643080280269468850928437 154038776275262704774541)
                  ·
                    rfl

theorem cell23_2699905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 5].length) (baseStart_2699905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699905 prefixEnd_2699905 := by exact prefixLift 2699905
  have htrace : WordTrace (prefixWord ++ tailWord_2699905) baseStart_2699905 baseEnd_2699905 := by
    simpa [prefixWord, tailWord_2699905, baseEnd_2699905] using wordTrace_append hprefix tailTrace_2699905
  have hstable : (prefixWord ++ tailWord_2699905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699905).length < 2 ^ (prefixWord ++ tailWord_2699905).sum := by decide
  have hdescent : baseEnd_2699905 < baseStart_2699905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699918 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 4, 5]
def baseStart_2699918 : Nat := 118140960795 + 2699918 * 2 ^ 59
def prefixEnd_2699918 : Nat := 4983230072969 + 3 ^ 40 * 2699918 * 2
def baseEnd_2699918 : Nat := 462118553908624264036103

theorem tailTrace_2699918 : CollatzResearch.WordTrace tailWord_2699918 prefixEnd_2699918 462118553908624264036103 := by
  unfold tailWord_2699918
  simp only [CollatzResearch.WordTrace]
  refine ⟨12309262429083208766090551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65649399621777113419149605 12309262429083208766090551)
  ·
    refine ⟨18463893643624813149135827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12309262429083208766090551 18463893643624813149135827)
    ·
      refine ⟨27695840465437219723703741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18463893643624813149135827 27695840465437219723703741)
      ·
        refine ⟨10385940174538957396388903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27695840465437219723703741 10385940174538957396388903)
        ·
          refine ⟨15578910261808436094583355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10385940174538957396388903 15578910261808436094583355)
          ·
            refine ⟨23368365392712654141875033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15578910261808436094583355 23368365392712654141875033)
            ·
              refine ⟨17526274044534490606406275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23368365392712654141875033 17526274044534490606406275)
              ·
                refine ⟨26289411066801735909609413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17526274044534490606406275 26289411066801735909609413)
                ·
                  refine ⟨4929264575025325483051765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26289411066801735909609413 4929264575025325483051765)
                  ·
                    refine ⟨462118553908624264036103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4929264575025325483051765 462118553908624264036103)
                    ·
                      rfl

theorem cell23_2699918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_2699918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699918 prefixEnd_2699918 := by exact prefixLift 2699918
  have htrace : WordTrace (prefixWord ++ tailWord_2699918) baseStart_2699918 baseEnd_2699918 := by
    simpa [prefixWord, tailWord_2699918, baseEnd_2699918] using wordTrace_append hprefix tailTrace_2699918
  have hstable : (prefixWord ++ tailWord_2699918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699918).length < 2 ^ (prefixWord ++ tailWord_2699918).sum := by decide
  have hdescent : baseEnd_2699918 < baseStart_2699918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699978 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 8]
def baseStart_2699978 : Nat := 118140960795 + 2699978 * 2 ^ 59
def prefixEnd_2699978 : Nat := 4983230072969 + 3 ^ 40 * 2699978 * 2
def baseEnd_2699978 : Nat := 154042941173904728595337

theorem tailTrace_2699978 : CollatzResearch.WordTrace tailWord_2699978 prefixEnd_2699978 154042941173904728595337 := by
  unfold tailWord_2699978
  simp only [CollatzResearch.WordTrace]
  refine ⟨24619071953112075093977147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65650858541632200250605725 24619071953112075093977147)
  ·
    refine ⟨36928607929668112640965721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24619071953112075093977147 36928607929668112640965721)
    ·
      refine ⟨27696455947251084480724291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36928607929668112640965721 27696455947251084480724291)
      ·
        refine ⟨41544683920876626721086437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27696455947251084480724291 41544683920876626721086437)
        ·
          refine ⟨7789628235164367510203707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41544683920876626721086437 7789628235164367510203707)
          ·
            refine ⟨11684442352746551265305561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7789628235164367510203707 11684442352746551265305561)
            ·
              refine ⟨8763331764559913448979171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11684442352746551265305561 8763331764559913448979171)
              ·
                refine ⟨13144997646839870173468757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8763331764559913448979171 13144997646839870173468757)
                ·
                  refine ⟨154042941173904728595337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13144997646839870173468757 154042941173904728595337)
                  ·
                    rfl

theorem cell23_2699978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 8].length) (baseStart_2699978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699978 prefixEnd_2699978 := by exact prefixLift 2699978
  have htrace : WordTrace (prefixWord ++ tailWord_2699978) baseStart_2699978 baseEnd_2699978 := by
    simpa [prefixWord, tailWord_2699978, baseEnd_2699978] using wordTrace_append hprefix tailTrace_2699978
  have hstable : (prefixWord ++ tailWord_2699978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699978).length < 2 ^ (prefixWord ++ tailWord_2699978).sum := by decide
  have hdescent : baseEnd_2699978 < baseStart_2699978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699982 : List Nat := [4, 1, 1, 1, 3, 4, 1, 1, 3, 4]
def baseStart_2699982 : Nat := 118140960795 + 2699982 * 2 ^ 59
def prefixEnd_2699982 : Nat := 4983230072969 + 3 ^ 40 * 2699982 * 2
def baseEnd_2699982 : Nat := 462129508162586847236005

theorem tailTrace_2699982 : CollatzResearch.WordTrace tailWord_2699982 prefixEnd_2699982 462129508162586847236005 := by
  unfold tailWord_2699982
  simp only [CollatzResearch.WordTrace]
  refine ⟨12309554213054226132381775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65650955802955872706036133 12309554213054226132381775)
  ·
    refine ⟨18464331319581339198572663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12309554213054226132381775 18464331319581339198572663)
    ·
      refine ⟨27696496979372008797858995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18464331319581339198572663 27696496979372008797858995)
      ·
        refine ⟨41544745469058013196788493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27696496979372008797858995 41544745469058013196788493)
        ·
          refine ⟨15579279550896754948795685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41544745469058013196788493 15579279550896754948795685)
          ·
            refine ⟨2921114915793141552899191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15579279550896754948795685 2921114915793141552899191)
            ·
              refine ⟨4381672373689712329348787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2921114915793141552899191 4381672373689712329348787)
              ·
                refine ⟨6572508560534568494023181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4381672373689712329348787 6572508560534568494023181)
                ·
                  refine ⟨2464690710200463185258693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6572508560534568494023181 2464690710200463185258693)
                  ·
                    refine ⟨462129508162586847236005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2464690710200463185258693 462129508162586847236005)
                    ·
                      rfl

theorem cell23_2699982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_2699982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2699982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2699982 prefixEnd_2699982 := by exact prefixLift 2699982
  have htrace : WordTrace (prefixWord ++ tailWord_2699982) baseStart_2699982 baseEnd_2699982 := by
    simpa [prefixWord, tailWord_2699982, baseEnd_2699982] using wordTrace_append hprefix tailTrace_2699982
  have hstable : (prefixWord ++ tailWord_2699982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699982).length < 2 ^ (prefixWord ++ tailWord_2699982).sum := by decide
  have hdescent : baseEnd_2699982 < baseStart_2699982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700065 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 3, 2, 3]
def baseStart_2700065 : Nat := 118140960795 + 2700065 * 2 ^ 59
def prefixEnd_2700065 : Nat := 4983230072969 + 3 ^ 40 * 2700065 * 2
def baseEnd_2700065 : Nat := 1386431143382083716970133

theorem tailTrace_2700065 : CollatzResearch.WordTrace tailWord_2700065 prefixEnd_2700065 1386431143382083716970133 := by
  unfold tailWord_2700065
  simp only [CollatzResearch.WordTrace]
  refine ⟨98479460963133114234325649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65652973975422076156217099 98479460963133114234325649)
  ·
    refine ⟨73859595722349835675744237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98479460963133114234325649 73859595722349835675744237)
    ·
      refine ⟨27697348395881188378404089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73859595722349835675744237 27697348395881188378404089)
      ·
        refine ⟨20773011296910891283803067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27697348395881188378404089 20773011296910891283803067)
        ·
          refine ⟨31159516945366336925704601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20773011296910891283803067 31159516945366336925704601)
          ·
            refine ⟨23369637709024752694278451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31159516945366336925704601 23369637709024752694278451)
            ·
              refine ⟨35054456563537129041417677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23369637709024752694278451 35054456563537129041417677)
              ·
                refine ⟨13145421211326423390531629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35054456563537129041417677 13145421211326423390531629)
                ·
                  refine ⟨4929532954247408771449361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13145421211326423390531629 4929532954247408771449361)
                  ·
                    refine ⟨3697149715685556578587021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4929532954247408771449361 3697149715685556578587021)
                    ·
                      refine ⟨1386431143382083716970133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3697149715685556578587021 1386431143382083716970133)
                      ·
                        rfl

theorem cell23_2700065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_2700065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700065 prefixEnd_2700065 := by exact prefixLift 2700065
  have htrace : WordTrace (prefixWord ++ tailWord_2700065) baseStart_2700065 baseEnd_2700065 := by
    simpa [prefixWord, tailWord_2700065, baseEnd_2700065] using wordTrace_append hprefix tailTrace_2700065
  have hstable : (prefixWord ++ tailWord_2700065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700065).length < 2 ^ (prefixWord ++ tailWord_2700065).sum := by decide
  have hdescent : baseEnd_2700065 < baseStart_2700065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700082 : List Nat := [3, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3]
def baseStart_2700082 : Nat := 118140960795 + 2700082 * 2 ^ 59
def prefixEnd_2700082 : Nat := 4983230072969 + 3 ^ 40 * 2700082 * 2
def baseEnd_2700082 : Nat := 1386439872553210150457555

theorem tailTrace_2700082 : CollatzResearch.WordTrace tailWord_2700082 prefixEnd_2700082 1386439872553210150457555 := by
  unfold tailWord_2700082
  simp only [CollatzResearch.WordTrace]
  refine ⟨24620020251017881534423625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65653387336047684091796333 24620020251017881534423625)
  ·
    refine ⟨18465015188263411150817719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24620020251017881534423625 18465015188263411150817719)
    ·
      refine ⟨27697522782395116726226579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18465015188263411150817719 27697522782395116726226579)
      ·
        refine ⟨41546284173592675089339869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27697522782395116726226579 41546284173592675089339869)
        ·
          refine ⟨15579856565097253158502451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41546284173592675089339869 15579856565097253158502451)
          ·
            refine ⟨23369784847645879737753677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15579856565097253158502451 23369784847645879737753677)
            ·
              refine ⟨8763669317867204901657629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23369784847645879737753677 8763669317867204901657629)
              ·
                refine ⟨3286375994200201838121611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8763669317867204901657629 3286375994200201838121611)
                ·
                  refine ⟨4929563991300302757182417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3286375994200201838121611 4929563991300302757182417)
                  ·
                    refine ⟨3697172993475227067886813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4929563991300302757182417 3697172993475227067886813)
                    ·
                      refine ⟨1386439872553210150457555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3697172993475227067886813 1386439872553210150457555)
                      ·
                        rfl

theorem cell23_2700082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_2700082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700082 prefixEnd_2700082 := by exact prefixLift 2700082
  have htrace : WordTrace (prefixWord ++ tailWord_2700082) baseStart_2700082 baseEnd_2700082 := by
    simpa [prefixWord, tailWord_2700082, baseEnd_2700082] using wordTrace_append hprefix tailTrace_2700082
  have hstable : (prefixWord ++ tailWord_2700082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700082).length < 2 ^ (prefixWord ++ tailWord_2700082).sum := by decide
  have hdescent : baseEnd_2700082 < baseStart_2700082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700112 : List Nat := [2, 1, 1, 1, 1, 4, 2, 5, 2, 1, 3]
def baseStart_2700112 : Nat := 118140960795 + 2700112 * 2 ^ 59
def prefixEnd_2700112 : Nat := 4983230072969 + 3 ^ 40 * 2700112 * 2
def baseEnd_2700112 : Nat := 1386455276972845033082417

theorem tailTrace_2700112 : CollatzResearch.WordTrace tailWord_2700112 prefixEnd_2700112 1386455276972845033082417 := by
  unfold tailWord_2700112
  simp only [CollatzResearch.WordTrace]
  refine ⟨49240587596981420630643295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65654116795975227507524393 49240587596981420630643295)
  ·
    refine ⟨73860881395472130945964943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49240587596981420630643295 73860881395472130945964943)
    ·
      refine ⟨110791322093208196418947415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73860881395472130945964943 110791322093208196418947415)
      ·
        refine ⟨166186983139812294628421123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110791322093208196418947415 166186983139812294628421123)
        ·
          refine ⟨249280474709718441942631685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166186983139812294628421123 249280474709718441942631685)
          ·
            refine ⟨46740089008072207864243441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 249280474709718441942631685 46740089008072207864243441)
            ·
              refine ⟨35055066756054155898182581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46740089008072207864243441 35055066756054155898182581)
              ·
                refine ⟨3286412508380077115454617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35055066756054155898182581 3286412508380077115454617)
                ·
                  refine ⟨2464809381285057836590963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3286412508380077115454617 2464809381285057836590963)
                  ·
                    refine ⟨3697214071927586754886445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2464809381285057836590963 3697214071927586754886445)
                    ·
                      refine ⟨1386455276972845033082417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3697214071927586754886445 1386455276972845033082417)
                      ·
                        rfl

theorem cell23_2700112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 2, 1, 3].length) (baseStart_2700112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700112 prefixEnd_2700112 := by exact prefixLift 2700112
  have htrace : WordTrace (prefixWord ++ tailWord_2700112) baseStart_2700112 baseEnd_2700112 := by
    simpa [prefixWord, tailWord_2700112, baseEnd_2700112] using wordTrace_append hprefix tailTrace_2700112
  have hstable : (prefixWord ++ tailWord_2700112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700112).length < 2 ^ (prefixWord ++ tailWord_2700112).sum := by decide
  have hdescent : baseEnd_2700112 < baseStart_2700112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700130 : List Nat := [3, 3, 2, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_2700130 : Nat := 118140960795 + 2700130 * 2 ^ 59
def prefixEnd_2700130 : Nat := 4983230072969 + 3 ^ 40 * 2700130 * 2
def baseEnd_2700130 : Nat := 1386464519624625962657335

theorem tailTrace_2700130 : CollatzResearch.WordTrace tailWord_2700130 prefixEnd_2700130 1386464519624625962657335 := by
  unfold tailWord_2700130
  simp only [CollatzResearch.WordTrace]
  refine ⟨24620457926974407583860461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65654554471931753556961229 24620457926974407583860461)
  ·
    refine ⟨9232671722615402843947673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24620457926974407583860461 9232671722615402843947673)
    ·
      refine ⟨6924503791961552132960755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9232671722615402843947673 6924503791961552132960755)
      ·
        refine ⟨10386755687942328199441133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6924503791961552132960755 10386755687942328199441133)
        ·
          refine ⟨3895033382978373074790425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10386755687942328199441133 3895033382978373074790425)
          ·
            refine ⟨2921275037233779806092819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3895033382978373074790425 2921275037233779806092819)
            ·
              refine ⟨4381912555850669709139229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2921275037233779806092819 4381912555850669709139229)
              ·
                refine ⟨1643217208444001140927211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4381912555850669709139229 1643217208444001140927211)
                ·
                  refine ⟨2464825812666001711390817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1643217208444001140927211 2464825812666001711390817)
                  ·
                    refine ⟨1848619359499501283543113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2464825812666001711390817 1848619359499501283543113)
                    ·
                      refine ⟨1386464519624625962657335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1848619359499501283543113 1386464519624625962657335)
                      ·
                        rfl

theorem cell23_2700130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_2700130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700130 prefixEnd_2700130 := by exact prefixLift 2700130
  have htrace : WordTrace (prefixWord ++ tailWord_2700130) baseStart_2700130 baseEnd_2700130 := by
    simpa [prefixWord, tailWord_2700130, baseEnd_2700130] using wordTrace_append hprefix tailTrace_2700130
  have hstable : (prefixWord ++ tailWord_2700130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700130).length < 2 ^ (prefixWord ++ tailWord_2700130).sum := by decide
  have hdescent : baseEnd_2700130 < baseStart_2700130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700185 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 4, 3, 3]
def baseStart_2700185 : Nat := 118140960795 + 2700185 * 2 ^ 59
def prefixEnd_2700185 : Nat := 4983230072969 + 3 ^ 40 * 2700185 * 2
def baseEnd_2700185 : Nat := 1386492761060623247469581

theorem tailTrace_2700185 : CollatzResearch.WordTrace tailWord_2700185 prefixEnd_2700185 1386492761060623247469581 := by
  unfold tailWord_2700185
  simp only [CollatzResearch.WordTrace]
  refine ⟨98483837722698374728694009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65655891815132249819129339 98483837722698374728694009)
  ·
    refine ⟨73862878292023781046520507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98483837722698374728694009 73862878292023781046520507)
    ·
      refine ⟨110794317438035671569780761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73862878292023781046520507 110794317438035671569780761)
      ·
        refine ⟨83095738078526753677335571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110794317438035671569780761 83095738078526753677335571)
        ·
          refine ⟨124643607117790130516003357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83095738078526753677335571 124643607117790130516003357)
          ·
            refine ⟨46741352669171298943501259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124643607117790130516003357 46741352669171298943501259)
            ·
              refine ⟨70112029003756948415251889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46741352669171298943501259 70112029003756948415251889)
              ·
                refine ⟨52584021752817711311438917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70112029003756948415251889 52584021752817711311438917)
                ·
                  refine ⟨9859504078653320870894797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52584021752817711311438917 9859504078653320870894797)
                  ·
                    refine ⟨3697314029494995326585549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9859504078653320870894797 3697314029494995326585549)
                    ·
                      refine ⟨1386492761060623247469581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3697314029494995326585549 1386492761060623247469581)
                      ·
                        rfl

theorem cell23_2700185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_2700185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700185 prefixEnd_2700185 := by exact prefixLift 2700185
  have htrace : WordTrace (prefixWord ++ tailWord_2700185) baseStart_2700185 baseEnd_2700185 := by
    simpa [prefixWord, tailWord_2700185, baseEnd_2700185] using wordTrace_append hprefix tailTrace_2700185
  have hstable : (prefixWord ++ tailWord_2700185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700185).length < 2 ^ (prefixWord ++ tailWord_2700185).sum := by decide
  have hdescent : baseEnd_2700185 < baseStart_2700185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700209 : List Nat := [1, 2, 2, 4, 3, 1, 1, 4, 5]
def baseStart_2700209 : Nat := 118140960795 + 2700209 * 2 ^ 59
def prefixEnd_2700209 : Nat := 4983230072969 + 3 ^ 40 * 2700209 * 2
def baseEnd_2700209 : Nat := 154056120510703461507719

theorem tailTrace_2700209 : CollatzResearch.WordTrace tailWord_2700209 prefixEnd_2700209 154056120510703461507719 := by
  unfold tailWord_2700209
  simp only [CollatzResearch.WordTrace]
  refine ⟨98484713074611426827567681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65656475383074284551711787 98484713074611426827567681)
  ·
    refine ⟨73863534805958570120675761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98484713074611426827567681 73863534805958570120675761)
    ·
      refine ⟨55397651104468927590506821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73863534805958570120675761 55397651104468927590506821)
      ·
        refine ⟨10387059582087923923220029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55397651104468927590506821 10387059582087923923220029)
        ·
          refine ⟨3895147343282971471207511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10387059582087923923220029 3895147343282971471207511)
          ·
            refine ⟨5842721014924457206811267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3895147343282971471207511 5842721014924457206811267)
            ·
              refine ⟨8764081522386685810216901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5842721014924457206811267 8764081522386685810216901)
              ·
                refine ⟨1643265285447503589415669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8764081522386685810216901 1643265285447503589415669)
                ·
                  refine ⟨154056120510703461507719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1643265285447503589415669 154056120510703461507719)
                  ·
                    rfl

theorem cell23_2700209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 5].length) (baseStart_2700209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700209 prefixEnd_2700209 := by exact prefixLift 2700209
  have htrace : WordTrace (prefixWord ++ tailWord_2700209) baseStart_2700209 baseEnd_2700209 := by
    simpa [prefixWord, tailWord_2700209, baseEnd_2700209] using wordTrace_append hprefix tailTrace_2700209
  have hstable : (prefixWord ++ tailWord_2700209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700209).length < 2 ^ (prefixWord ++ tailWord_2700209).sum := by decide
  have hdescent : baseEnd_2700209 < baseStart_2700209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700215 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 5]
def baseStart_2700215 : Nat := 118140960795 + 2700215 * 2 ^ 59
def prefixEnd_2700215 : Nat := 4983230072969 + 3 ^ 40 * 2700215 * 2
def baseEnd_2700215 : Nat := 1386508165480258130094443

theorem tailTrace_2700215 : CollatzResearch.WordTrace tailWord_2700215 prefixEnd_2700215 1386508165480258130094443 := by
  unfold tailWord_2700215
  simp only [CollatzResearch.WordTrace]
  refine ⟨98484931912589689852286099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65656621275059793234857399 98484931912589689852286099)
  ·
    refine ⟨147727397868884534778429149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98484931912589689852286099 147727397868884534778429149)
    ·
      refine ⟨55397774200831700541910931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147727397868884534778429149 55397774200831700541910931)
      ·
        refine ⟨83096661301247550812866397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55397774200831700541910931 83096661301247550812866397)
        ·
          refine ⟨31161247987967831554824899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83096661301247550812866397 31161247987967831554824899)
          ·
            refine ⟨46741871981951747332237349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31161247987967831554824899 46741871981951747332237349)
            ·
              refine ⟨8764100996615952624794503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46741871981951747332237349 8764100996615952624794503)
              ·
                refine ⟨13146151494923928937191755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8764100996615952624794503 13146151494923928937191755)
                ·
                  refine ⟨19719227242385893405787633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13146151494923928937191755 19719227242385893405787633)
                  ·
                    refine ⟨14789420431789420054340725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19719227242385893405787633 14789420431789420054340725)
                    ·
                      refine ⟨1386508165480258130094443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14789420431789420054340725 1386508165480258130094443)
                      ·
                        rfl

theorem cell23_2700215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_2700215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700215 prefixEnd_2700215 := by exact prefixLift 2700215
  have htrace : WordTrace (prefixWord ++ tailWord_2700215) baseStart_2700215 baseEnd_2700215 := by
    simpa [prefixWord, tailWord_2700215, baseEnd_2700215] using wordTrace_append hprefix tailTrace_2700215
  have hstable : (prefixWord ++ tailWord_2700215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700215).length < 2 ^ (prefixWord ++ tailWord_2700215).sum := by decide
  have hdescent : baseEnd_2700215 < baseStart_2700215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700285 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_2700285 : Nat := 118140960795 + 2700285 * 2 ^ 59
def prefixEnd_2700285 : Nat := 4983230072969 + 3 ^ 40 * 2700285 * 2
def baseEnd_2700285 : Nat := 1386544109126072856219121

theorem tailTrace_2700285 : CollatzResearch.WordTrace tailWord_2700285 prefixEnd_2700285 1386544109126072856219121 := by
  unfold tailWord_2700285
  simp only [CollatzResearch.WordTrace]
  refine ⟨98487485022336091807334309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65658323348224061204889539 98487485022336091807334309)
  ·
    refine ⟨18466403441688017213875183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98487485022336091807334309 18466403441688017213875183)
    ·
      refine ⟨27699605162532025820812775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18466403441688017213875183 27699605162532025820812775)
      ·
        refine ⟨41549407743798038731219163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27699605162532025820812775 41549407743798038731219163)
        ·
          refine ⟨62324111615697058096828745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41549407743798038731219163 62324111615697058096828745)
          ·
            refine ⟨46743083711772793572621559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62324111615697058096828745 46743083711772793572621559)
            ·
              refine ⟨70114625567659190358932339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46743083711772793572621559 70114625567659190358932339)
              ·
                refine ⟨105171938351488785538398509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70114625567659190358932339 105171938351488785538398509)
                ·
                  refine ⟨39439476881808294576899441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105171938351488785538398509 39439476881808294576899441)
                  ·
                    refine ⟨29579607661356220932674581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39439476881808294576899441 29579607661356220932674581)
                    ·
                      refine ⟨1386544109126072856219121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29579607661356220932674581 1386544109126072856219121)
                      ·
                        rfl

theorem cell23_2700285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_2700285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700285 prefixEnd_2700285 := by exact prefixLift 2700285
  have htrace : WordTrace (prefixWord ++ tailWord_2700285) baseStart_2700285 baseEnd_2700285 := by
    simpa [prefixWord, tailWord_2700285, baseEnd_2700285] using wordTrace_append hprefix tailTrace_2700285
  have hstable : (prefixWord ++ tailWord_2700285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700285).length < 2 ^ (prefixWord ++ tailWord_2700285).sum := by decide
  have hdescent : baseEnd_2700285 < baseStart_2700285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700315 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 4]
def baseStart_2700315 : Nat := 118140960795 + 2700315 * 2 ^ 59
def prefixEnd_2700315 : Nat := 4983230072969 + 3 ^ 40 * 2700315 * 2
def baseEnd_2700315 : Nat := 1386559513545707738843983

theorem tailTrace_2700315 : CollatzResearch.WordTrace tailWord_2700315 prefixEnd_2700315 1386559513545707738843983 := by
  unfold tailWord_2700315
  simp only [CollatzResearch.WordTrace]
  refine ⟨98488579212227406930926399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65659052808151604620617599 98488579212227406930926399)
  ·
    refine ⟨147732868818341110396389599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98488579212227406930926399 147732868818341110396389599)
    ·
      refine ⟨221599303227511665594584399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147732868818341110396389599 221599303227511665594584399)
      ·
        refine ⟨332398954841267498391876599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221599303227511665594584399 332398954841267498391876599)
        ·
          refine ⟨498598432261901247587814899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332398954841267498391876599 498598432261901247587814899)
          ·
            refine ⟨747897648392851871381722349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498598432261901247587814899 747897648392851871381722349)
            ·
              refine ⟨280461618147319451768145881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 747897648392851871381722349 280461618147319451768145881)
              ·
                refine ⟨210346213610489588826109411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280461618147319451768145881 210346213610489588826109411)
                ·
                  refine ⟨315519320415734383239164117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210346213610489588826109411 315519320415734383239164117)
                  ·
                    refine ⟨7394984072243774607167909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 315519320415734383239164117 7394984072243774607167909)
                    ·
                      refine ⟨1386559513545707738843983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7394984072243774607167909 1386559513545707738843983)
                      ·
                        rfl

theorem cell23_2700315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 4].length) (baseStart_2700315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700315 prefixEnd_2700315 := by exact prefixLift 2700315
  have htrace : WordTrace (prefixWord ++ tailWord_2700315) baseStart_2700315 baseEnd_2700315 := by
    simpa [prefixWord, tailWord_2700315, baseEnd_2700315] using wordTrace_append hprefix tailTrace_2700315
  have hstable : (prefixWord ++ tailWord_2700315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700315).length < 2 ^ (prefixWord ++ tailWord_2700315).sum := by decide
  have hdescent : baseEnd_2700315 < baseStart_2700315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700319 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 4, 3, 2]
def baseStart_2700319 : Nat := 118140960795 + 2700319 * 2 ^ 59
def prefixEnd_2700319 : Nat := 4983230072969 + 3 ^ 40 * 2700319 * 2
def baseEnd_2700319 : Nat := 1386561567468325723193965

theorem tailTrace_2700319 : CollatzResearch.WordTrace tailWord_2700319 prefixEnd_2700319 1386561567468325723193965 := by
  unfold tailWord_2700319
  simp only [CollatzResearch.WordTrace]
  refine ⟨98488725104212915614072011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65659150069475277076048007 98488725104212915614072011)
  ·
    refine ⟨147733087656319373421108017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98488725104212915614072011 147733087656319373421108017)
    ·
      refine ⟨110799815742239530065831013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147733087656319373421108017 110799815742239530065831013)
      ·
        refine ⟨20774965451669911887343315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110799815742239530065831013 20774965451669911887343315)
        ·
          refine ⟨31162448177504867831014973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20774965451669911887343315 31162448177504867831014973)
          ·
            refine ⟨11685918066564325436630615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31162448177504867831014973 11685918066564325436630615)
            ·
              refine ⟨17528877099846488154945923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11685918066564325436630615 17528877099846488154945923)
              ·
                refine ⟨26293315649769732232418885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17528877099846488154945923 26293315649769732232418885)
                ·
                  refine ⟨4929996684331824793578541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26293315649769732232418885 4929996684331824793578541)
                  ·
                    refine ⟨1848748756624434297591953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4929996684331824793578541 1848748756624434297591953)
                    ·
                      refine ⟨1386561567468325723193965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1848748756624434297591953 1386561567468325723193965)
                      ·
                        rfl

theorem cell23_2700319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_2700319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700319 prefixEnd_2700319 := by exact prefixLift 2700319
  have htrace : WordTrace (prefixWord ++ tailWord_2700319) baseStart_2700319 baseEnd_2700319 := by
    simpa [prefixWord, tailWord_2700319, baseEnd_2700319] using wordTrace_append hprefix tailTrace_2700319
  have hstable : (prefixWord ++ tailWord_2700319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700319).length < 2 ^ (prefixWord ++ tailWord_2700319).sum := by decide
  have hdescent : baseEnd_2700319 < baseStart_2700319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700320 : List Nat := [2, 1, 1, 7, 1, 1, 3, 2, 1, 4]
def baseStart_2700320 : Nat := 118140960795 + 2700320 * 2 ^ 59
def prefixEnd_2700320 : Nat := 4983230072969 + 3 ^ 40 * 2700320 * 2
def baseEnd_2700320 : Nat := 462187360316326739760487

theorem tailTrace_2700320 : CollatzResearch.WordTrace tailWord_2700320 prefixEnd_2700320 462187360316326739760487 := by
  unfold tailWord_2700320
  simp only [CollatzResearch.WordTrace]
  refine ⟨49244380788604646392429207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65659174384806195189905609 49244380788604646392429207)
  ·
    refine ⟨73866571182906969588643811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49244380788604646392429207 73866571182906969588643811)
    ·
      refine ⟨110799856774360454382965717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73866571182906969588643811 110799856774360454382965717)
      ·
        refine ⟨2596871643149073149600759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 110799856774360454382965717 2596871643149073149600759)
        ·
          refine ⟨3895307464723609724401139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2596871643149073149600759 3895307464723609724401139)
          ·
            refine ⟨5842961197085414586601709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3895307464723609724401139 5842961197085414586601709)
            ·
              refine ⟨2191110448907030469975641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5842961197085414586601709 2191110448907030469975641)
              ·
                refine ⟨1643332836680272852481731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2191110448907030469975641 1643332836680272852481731)
                ·
                  refine ⟨2464999255020409278722597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1643332836680272852481731 2464999255020409278722597)
                  ·
                    refine ⟨462187360316326739760487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2464999255020409278722597 462187360316326739760487)
                    ·
                      rfl

theorem cell23_2700320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 1, 4].length) (baseStart_2700320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700320 prefixEnd_2700320 := by exact prefixLift 2700320
  have htrace : WordTrace (prefixWord ++ tailWord_2700320) baseStart_2700320 baseEnd_2700320 := by
    simpa [prefixWord, tailWord_2700320, baseEnd_2700320] using wordTrace_append hprefix tailTrace_2700320
  have hstable : (prefixWord ++ tailWord_2700320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700320).length < 2 ^ (prefixWord ++ tailWord_2700320).sum := by decide
  have hdescent : baseEnd_2700320 < baseStart_2700320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700332 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 4]
def baseStart_2700332 : Nat := 118140960795 + 2700332 * 2 ^ 59
def prefixEnd_2700332 : Nat := 4983230072969 + 3 ^ 40 * 2700332 * 2
def baseEnd_2700332 : Nat := 1386568242716834172331405

theorem tailTrace_2700332 : CollatzResearch.WordTrace tailWord_2700332 prefixEnd_2700332 1386568242716834172331405 := by
  unfold tailWord_2700332
  simp only [CollatzResearch.WordTrace]
  refine ⟨49244599626582909417147625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65659466168777212556196833 49244599626582909417147625)
  ·
    refine ⟨36933449719937182062860719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49244599626582909417147625 36933449719937182062860719)
    ·
      refine ⟨55400174579905773094291079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36933449719937182062860719 55400174579905773094291079)
      ·
        refine ⟨83100261869858659641436619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55400174579905773094291079 83100261869858659641436619)
        ·
          refine ⟨124650392804787989462154929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83100261869858659641436619 124650392804787989462154929)
          ·
            refine ⟨93487794603590992096616197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124650392804787989462154929 93487794603590992096616197)
            ·
              refine ⟨17528961488173311018115537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93487794603590992096616197 17528961488173311018115537)
              ·
                refine ⟨13146721116129983263586653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17528961488173311018115537 13146721116129983263586653)
                ·
                  refine ⟨4930020418548743723844995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13146721116129983263586653 4930020418548743723844995)
                  ·
                    refine ⟨7395030627823115585767493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4930020418548743723844995 7395030627823115585767493)
                    ·
                      refine ⟨1386568242716834172331405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7395030627823115585767493 1386568242716834172331405)
                      ·
                        rfl

theorem cell23_2700332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_2700332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700332 prefixEnd_2700332 := by exact prefixLift 2700332
  have htrace : WordTrace (prefixWord ++ tailWord_2700332) baseStart_2700332 baseEnd_2700332 := by
    simpa [prefixWord, tailWord_2700332, baseEnd_2700332] using wordTrace_append hprefix tailTrace_2700332
  have hstable : (prefixWord ++ tailWord_2700332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700332).length < 2 ^ (prefixWord ++ tailWord_2700332).sum := by decide
  have hdescent : baseEnd_2700332 < baseStart_2700332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700335 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 5]
def baseStart_2700335 : Nat := 118140960795 + 2700335 * 2 ^ 59
def prefixEnd_2700335 : Nat := 4983230072969 + 3 ^ 40 * 2700335 * 2
def baseEnd_2700335 : Nat := 1386569783158797660593891

theorem tailTrace_2700335 : CollatzResearch.WordTrace tailWord_2700335 prefixEnd_2700335 1386569783158797660593891 := by
  unfold tailWord_2700335
  simp only [CollatzResearch.WordTrace]
  refine ⟨98489308672154950346654459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65659539114769966897769639 98489308672154950346654459)
  ·
    refine ⟨147733963008232425519981689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98489308672154950346654459 147733963008232425519981689)
    ·
      refine ⟨110800472256174319139986267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147733963008232425519981689 110800472256174319139986267)
      ·
        refine ⟨166200708384261478709979401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110800472256174319139986267 166200708384261478709979401)
        ·
          refine ⟨124650531288196109032484551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166200708384261478709979401 124650531288196109032484551)
          ·
            refine ⟨186975796932294163548726827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124650531288196109032484551 186975796932294163548726827)
            ·
              refine ⟨280463695398441245323090241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186975796932294163548726827 280463695398441245323090241)
              ·
                refine ⟨210347771548830933992317681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280463695398441245323090241 210347771548830933992317681)
                ·
                  refine ⟨157760828661623200494238261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210347771548830933992317681 157760828661623200494238261)
                  ·
                    refine ⟨14790077687027175046334837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 157760828661623200494238261 14790077687027175046334837)
                    ·
                      refine ⟨1386569783158797660593891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14790077687027175046334837 1386569783158797660593891)
                      ·
                        rfl

theorem cell23_2700335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_2700335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700335 prefixEnd_2700335 := by exact prefixLift 2700335
  have htrace : WordTrace (prefixWord ++ tailWord_2700335) baseStart_2700335 baseEnd_2700335 := by
    simpa [prefixWord, tailWord_2700335, baseEnd_2700335] using wordTrace_append hprefix tailTrace_2700335
  have hstable : (prefixWord ++ tailWord_2700335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700335).length < 2 ^ (prefixWord ++ tailWord_2700335).sum := by decide
  have hdescent : baseEnd_2700335 < baseStart_2700335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700349 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_2700349 : Nat := 118140960795 + 2700349 * 2 ^ 59
def prefixEnd_2700349 : Nat := 4983230072969 + 3 ^ 40 * 2700349 * 2
def baseEnd_2700349 : Nat := 1386576971887960605818827

theorem tailTrace_2700349 : CollatzResearch.WordTrace tailWord_2700349 prefixEnd_2700349 1386576971887960605818827 := by
  unfold tailWord_2700349
  simp only [CollatzResearch.WordTrace]
  refine ⟨98489819294104230737664101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65659879529402820491776067 98489819294104230737664101)
  ·
    refine ⟨18466841117644543263312019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98489819294104230737664101 18466841117644543263312019)
    ·
      refine ⟨27700261676466814894968029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18466841117644543263312019 27700261676466814894968029)
      ·
        refine ⟨10387598128675055585613011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27700261676466814894968029 10387598128675055585613011)
        ·
          refine ⟨15581397193012583378419517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10387598128675055585613011 15581397193012583378419517)
          ·
            refine ⟨5843023947379718766907319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15581397193012583378419517 5843023947379718766907319)
            ·
              refine ⟨8764535921069578150360979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5843023947379718766907319 8764535921069578150360979)
              ·
                refine ⟨13146803881604367225541469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8764535921069578150360979 13146803881604367225541469)
                ·
                  refine ⟨4930051455601637709578051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13146803881604367225541469 4930051455601637709578051)
                  ·
                    refine ⟨7395077183402456564367077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4930051455601637709578051 7395077183402456564367077)
                    ·
                      refine ⟨1386576971887960605818827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7395077183402456564367077 1386576971887960605818827)
                      ·
                        rfl

theorem cell23_2700349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_2700349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700349 prefixEnd_2700349 := by exact prefixLift 2700349
  have htrace : WordTrace (prefixWord ++ tailWord_2700349) baseStart_2700349 baseEnd_2700349 := by
    simpa [prefixWord, tailWord_2700349, baseEnd_2700349] using wordTrace_append hprefix tailTrace_2700349
  have hstable : (prefixWord ++ tailWord_2700349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700349).length < 2 ^ (prefixWord ++ tailWord_2700349).sum := by decide
  have hdescent : baseEnd_2700349 < baseStart_2700349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700353 : List Nat := [1, 2, 5, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_2700353 : Nat := 118140960795 + 2700353 * 2 ^ 59
def prefixEnd_2700353 : Nat := 4983230072969 + 3 ^ 40 * 2700353 * 2
def baseEnd_2700353 : Nat := 1386579025810578590168809

theorem tailTrace_2700353 : CollatzResearch.WordTrace tailWord_2700353 prefixEnd_2700353 1386579025810578590168809 := by
  unfold tailWord_2700353
  simp only [CollatzResearch.WordTrace]
  refine ⟨98489965186089739420809713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65659976790726492947206475 98489965186089739420809713)
  ·
    refine ⟨73867473889567304565607285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98489965186089739420809713 73867473889567304565607285)
    ·
      refine ⟨6925075677146934803025683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73867473889567304565607285 6925075677146934803025683)
      ·
        refine ⟨10387613515720402204538525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6925075677146934803025683 10387613515720402204538525)
        ·
          refine ⟨3895355068395150826701947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10387613515720402204538525 3895355068395150826701947)
          ·
            refine ⟨5843032602592726240052921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3895355068395150826701947 5843032602592726240052921)
            ·
              refine ⟨4382274451944544680039691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5843032602592726240052921 4382274451944544680039691)
              ·
                refine ⟨6573411677916817020059537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4382274451944544680039691 6573411677916817020059537)
                ·
                  refine ⟨4930058758437612765044653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6573411677916817020059537 4930058758437612765044653)
                  ·
                    refine ⟨1848772034414104786891745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4930058758437612765044653 1848772034414104786891745)
                    ·
                      refine ⟨1386579025810578590168809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1848772034414104786891745 1386579025810578590168809)
                      ·
                        rfl

theorem cell23_2700353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_2700353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700353 prefixEnd_2700353 := by exact prefixLift 2700353
  have htrace : WordTrace (prefixWord ++ tailWord_2700353) baseStart_2700353 baseEnd_2700353 := by
    simpa [prefixWord, tailWord_2700353, baseEnd_2700353] using wordTrace_append hprefix tailTrace_2700353
  have hstable : (prefixWord ++ tailWord_2700353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700353).length < 2 ^ (prefixWord ++ tailWord_2700353).sum := by decide
  have hdescent : baseEnd_2700353 < baseStart_2700353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700355 : List Nat := [1, 1, 1, 3, 1, 2, 3, 11]
def baseStart_2700355 : Nat := 118140960795 + 2700355 * 2 ^ 59
def prefixEnd_2700355 : Nat := 4983230072969 + 3 ^ 40 * 2700355 * 2
def baseEnd_2700355 : Nat := 51354816769329169716437

theorem tailTrace_2700355 : CollatzResearch.WordTrace tailWord_2700355 prefixEnd_2700355 51354816769329169716437 := by
  unfold tailWord_2700355
  simp only [CollatzResearch.WordTrace]
  refine ⟨98490038132082493762382519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65660025421388329174921679 98490038132082493762382519)
  ·
    refine ⟨147735057198123740643573779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98490038132082493762382519 147735057198123740643573779)
    ·
      refine ⟨221602585797185610965360669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147735057198123740643573779 221602585797185610965360669)
      ·
        refine ⟨83100969673944604112010251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221602585797185610965360669 83100969673944604112010251)
        ·
          refine ⟨124651454510916906168015377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83100969673944604112010251 124651454510916906168015377)
          ·
            refine ⟨93488590883187679626011533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124651454510916906168015377 93488590883187679626011533)
            ·
              refine ⟨35058221581195379859754325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93488590883187679626011533 35058221581195379859754325)
              ·
                refine ⟨51354816769329169716437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 35058221581195379859754325 51354816769329169716437)
                ·
                  rfl

theorem cell23_2700355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 11].length) (baseStart_2700355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700355 prefixEnd_2700355 := by exact prefixLift 2700355
  have htrace : WordTrace (prefixWord ++ tailWord_2700355) baseStart_2700355 baseEnd_2700355 := by
    simpa [prefixWord, tailWord_2700355, baseEnd_2700355] using wordTrace_append hprefix tailTrace_2700355
  have hstable : (prefixWord ++ tailWord_2700355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700355).length < 2 ^ (prefixWord ++ tailWord_2700355).sum := by decide
  have hdescent : baseEnd_2700355 < baseStart_2700355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700362 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_2700362 : Nat := 118140960795 + 2700362 * 2 ^ 59
def prefixEnd_2700362 : Nat := 4983230072969 + 3 ^ 40 * 2700362 * 2
def baseEnd_2700362 : Nat := 1386583647136469054956267

theorem tailTrace_2700362 : CollatzResearch.WordTrace tailWord_2700362 prefixEnd_2700362 1386583647136469054956267 := by
  unfold tailWord_2700362
  simp only [CollatzResearch.WordTrace]
  refine ⟨24622573360764283489471835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65660195628704755971924893 24622573360764283489471835)
  ·
    refine ⟨36933860041146425234207753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24622573360764283489471835 36933860041146425234207753)
    ·
      refine ⟨27700395030859818925655815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36933860041146425234207753 27700395030859818925655815)
      ·
        refine ⟨41550592546289728388483723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27700395030859818925655815 41550592546289728388483723)
        ·
          refine ⟨62325888819434592582725585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41550592546289728388483723 62325888819434592582725585)
          ·
            refine ⟨46744416614575944437044189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62325888819434592582725585 46744416614575944437044189)
            ·
              refine ⟨17529156230465979163891571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46744416614575944437044189 17529156230465979163891571)
              ·
                refine ⟨26293734345698968745837357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17529156230465979163891571 26293734345698968745837357)
                ·
                  refine ⟨9860150379637113279689009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26293734345698968745837357 9860150379637113279689009)
                  ·
                    refine ⟨7395112784727834959766757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9860150379637113279689009 7395112784727834959766757)
                    ·
                      refine ⟨1386583647136469054956267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7395112784727834959766757 1386583647136469054956267)
                      ·
                        rfl

theorem cell23_2700362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_2700362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700362 prefixEnd_2700362 := by exact prefixLift 2700362
  have htrace : WordTrace (prefixWord ++ tailWord_2700362) baseStart_2700362 baseEnd_2700362 := by
    simpa [prefixWord, tailWord_2700362, baseEnd_2700362] using wordTrace_append hprefix tailTrace_2700362
  have hstable : (prefixWord ++ tailWord_2700362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700362).length < 2 ^ (prefixWord ++ tailWord_2700362).sum := by decide
  have hdescent : baseEnd_2700362 < baseStart_2700362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700366 : List Nat := [4, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4]
def baseStart_2700366 : Nat := 118140960795 + 2700366 * 2 ^ 59
def prefixEnd_2700366 : Nat := 4983230072969 + 3 ^ 40 * 2700366 * 2
def baseEnd_2700366 : Nat := 1386585701059087039306249

theorem tailTrace_2700366 : CollatzResearch.WordTrace tailWord_2700366 prefixEnd_2700366 1386585701059087039306249 := by
  unfold tailWord_2700366
  simp only [CollatzResearch.WordTrace]
  refine ⟨12311304916880330330129119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65660292890028428427355301 12311304916880330330129119)
  ·
    refine ⟨18466957375320495495193679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12311304916880330330129119 18466957375320495495193679)
    ·
      refine ⟨27700436062980743242790519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18466957375320495495193679 27700436062980743242790519)
      ·
        refine ⟨41550654094471114864185779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27700436062980743242790519 41550654094471114864185779)
        ·
          refine ⟨62325981141706672296278669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41550654094471114864185779 62325981141706672296278669)
          ·
            refine ⟨23372242928140002111104501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62325981141706672296278669 23372242928140002111104501)
            ·
              refine ⟨2191147774513125197916047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23372242928140002111104501 2191147774513125197916047)
              ·
                refine ⟨3286721661769687796874071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2191147774513125197916047 3286721661769687796874071)
                ·
                  refine ⟨4930082492654531695311107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3286721661769687796874071 4930082492654531695311107)
                  ·
                    refine ⟨7395123738981797542966661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4930082492654531695311107 7395123738981797542966661)
                    ·
                      refine ⟨1386585701059087039306249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7395123738981797542966661 1386585701059087039306249)
                      ·
                        rfl

theorem cell23_2700366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_2700366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700366 prefixEnd_2700366 := by exact prefixLift 2700366
  have htrace : WordTrace (prefixWord ++ tailWord_2700366) baseStart_2700366 baseEnd_2700366 := by
    simpa [prefixWord, tailWord_2700366, baseEnd_2700366] using wordTrace_append hprefix tailTrace_2700366
  have hstable : (prefixWord ++ tailWord_2700366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700366).length < 2 ^ (prefixWord ++ tailWord_2700366).sum := by decide
  have hdescent : baseEnd_2700366 < baseStart_2700366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700369 : List Nat := [1, 2, 2, 1, 3, 1, 2, 5, 1, 2, 3]
def baseStart_2700369 : Nat := 118140960795 + 2700369 * 2 ^ 59
def prefixEnd_2700369 : Nat := 4983230072969 + 3 ^ 40 * 2700369 * 2
def baseEnd_2700369 : Nat := 1386587241501050527568735

theorem tailTrace_2700369 : CollatzResearch.WordTrace tailWord_2700369 prefixEnd_2700369 1386587241501050527568735 := by
  unfold tailWord_2700369
  simp only [CollatzResearch.WordTrace]
  refine ⟨98490548754031774153392161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65660365836021182768928107 98490548754031774153392161)
  ·
    refine ⟨73867911565523830615044121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98490548754031774153392161 73867911565523830615044121)
    ·
      refine ⟨55400933674142872961283091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73867911565523830615044121 55400933674142872961283091)
      ·
        refine ⟨83101400511214309441924637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55400933674142872961283091 83101400511214309441924637)
        ·
          refine ⟨31163025191705366040721739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83101400511214309441924637 31163025191705366040721739)
          ·
            refine ⟨46744537787558049061082609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31163025191705366040721739 46744537787558049061082609)
            ·
              refine ⟨35058403340668536795811957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46744537787558049061082609 35058403340668536795811957)
              ·
                refine ⟨3286725313187675324607371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35058403340668536795811957 3286725313187675324607371)
                ·
                  refine ⟨4930087969781512986911057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3286725313187675324607371 4930087969781512986911057)
                  ·
                    refine ⟨3697565977336134740183293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4930087969781512986911057 3697565977336134740183293)
                    ·
                      refine ⟨1386587241501050527568735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3697565977336134740183293 1386587241501050527568735)
                      ·
                        rfl

theorem cell23_2700369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 2, 3].length) (baseStart_2700369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700369 prefixEnd_2700369 := by exact prefixLift 2700369
  have htrace : WordTrace (prefixWord ++ tailWord_2700369) baseStart_2700369 baseEnd_2700369 := by
    simpa [prefixWord, tailWord_2700369, baseEnd_2700369] using wordTrace_append hprefix tailTrace_2700369
  have hstable : (prefixWord ++ tailWord_2700369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700369).length < 2 ^ (prefixWord ++ tailWord_2700369).sum := by decide
  have hdescent : baseEnd_2700369 < baseStart_2700369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700383 : List Nat := [1, 1, 2, 3, 1, 1, 5, 4, 1, 2, 2]
def baseStart_2700383 : Nat := 118140960795 + 2700383 * 2 ^ 59
def prefixEnd_2700383 : Nat := 4983230072969 + 3 ^ 40 * 2700383 * 2
def baseEnd_2700383 : Nat := 1386594430230213472793671

theorem tailTrace_2700383 : CollatzResearch.WordTrace tailWord_2700383 prefixEnd_2700383 1386594430230213472793671 := by
  unfold tailWord_2700383
  simp only [CollatzResearch.WordTrace]
  refine ⟨98491059375981054544401803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65660706250654036362934535 98491059375981054544401803)
  ·
    refine ⟨147736589063971581816602705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98491059375981054544401803 147736589063971581816602705)
    ·
      refine ⟨110802441797978686362452029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147736589063971581816602705 110802441797978686362452029)
      ·
        refine ⟨41550915674242007385919511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110802441797978686362452029 41550915674242007385919511)
        ·
          refine ⟨62326373511363011078879267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41550915674242007385919511 62326373511363011078879267)
          ·
            refine ⟨93489560267044516618318901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62326373511363011078879267 93489560267044516618318901)
            ·
              refine ⟨8764646275035423432967397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93489560267044516618318901 8764646275035423432967397)
              ·
                refine ⟨1643371176569141893681387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8764646275035423432967397 1643371176569141893681387)
                ·
                  refine ⟨2465056764853712840522081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1643371176569141893681387 2465056764853712840522081)
                  ·
                    refine ⟨1848792573640284630391561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2465056764853712840522081 1848792573640284630391561)
                    ·
                      refine ⟨1386594430230213472793671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1848792573640284630391561 1386594430230213472793671)
                      ·
                        rfl

theorem cell23_2700383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 1, 2, 2].length) (baseStart_2700383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700383 prefixEnd_2700383 := by exact prefixLift 2700383
  have htrace : WordTrace (prefixWord ++ tailWord_2700383) baseStart_2700383 baseEnd_2700383 := by
    simpa [prefixWord, tailWord_2700383, baseEnd_2700383] using wordTrace_append hprefix tailTrace_2700383
  have hstable : (prefixWord ++ tailWord_2700383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700383).length < 2 ^ (prefixWord ++ tailWord_2700383).sum := by decide
  have hdescent : baseEnd_2700383 < baseStart_2700383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700386 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_2700386 : Nat := 118140960795 + 2700386 * 2 ^ 59
def prefixEnd_2700386 : Nat := 4983230072969 + 3 ^ 40 * 2700386 * 2
def baseEnd_2700386 : Nat := 1386595970672176961056157

theorem tailTrace_2700386 : CollatzResearch.WordTrace tailWord_2700386 prefixEnd_2700386 1386595970672176961056157 := by
  unfold tailWord_2700386
  simp only [CollatzResearch.WordTrace]
  refine ⟨24622792198742546514190253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65660779196646790704507341 24622792198742546514190253)
  ·
    refine ⟨9233547074528454942821345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24622792198742546514190253 9233547074528454942821345)
    ·
      refine ⟨6925160305896341207116009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9233547074528454942821345 6925160305896341207116009)
      ·
        refine ⟨5193870229422255905337007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6925160305896341207116009 5193870229422255905337007)
        ·
          refine ⟨7790805344133383858005511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5193870229422255905337007 7790805344133383858005511)
          ·
            refine ⟨11686208016200075787008267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7790805344133383858005511 11686208016200075787008267)
            ·
              refine ⟨17529312024300113680512401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11686208016200075787008267 17529312024300113680512401)
              ·
                refine ⟨13146984018225085260384301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17529312024300113680512401 13146984018225085260384301)
                ·
                  refine ⟨4930119006834406972644113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13146984018225085260384301 4930119006834406972644113)
                  ·
                    refine ⟨3697589255125805229483085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4930119006834406972644113 3697589255125805229483085)
                    ·
                      refine ⟨1386595970672176961056157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3697589255125805229483085 1386595970672176961056157)
                      ·
                        rfl

theorem cell23_2700386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_2700386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700386 prefixEnd_2700386 := by exact prefixLift 2700386
  have htrace : WordTrace (prefixWord ++ tailWord_2700386) baseStart_2700386 baseEnd_2700386 := by
    simpa [prefixWord, tailWord_2700386, baseEnd_2700386] using wordTrace_append hprefix tailTrace_2700386
  have hstable : (prefixWord ++ tailWord_2700386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700386).length < 2 ^ (prefixWord ++ tailWord_2700386).sum := by decide
  have hdescent : baseEnd_2700386 < baseStart_2700386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700399 : List Nat := [1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 3]
def baseStart_2700399 : Nat := 118140960795 + 2700399 * 2 ^ 59
def prefixEnd_2700399 : Nat := 4983230072969 + 3 ^ 40 * 2700399 * 2
def baseEnd_2700399 : Nat := 1386602645920685410193597

theorem tailTrace_2700399 : CollatzResearch.WordTrace tailWord_2700399 prefixEnd_2700399 1386602645920685410193597 := by
  unfold tailWord_2700399
  simp only [CollatzResearch.WordTrace]
  refine ⟨98491642943923089276984251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65661095295948726184656167 98491642943923089276984251)
  ·
    refine ⟨147737464415884633915476377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98491642943923089276984251 147737464415884633915476377)
    ·
      refine ⟨110803098311913475436607283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147737464415884633915476377 110803098311913475436607283)
      ·
        refine ⟨166204647467870213154910925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110803098311913475436607283 166204647467870213154910925)
        ·
          refine ⟨62326742800451329933091597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166204647467870213154910925 62326742800451329933091597)
          ·
            refine ⟨23372528550169248724909349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62326742800451329933091597 23372528550169248724909349)
            ·
              refine ⟨4382349103156734135920503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23372528550169248724909349 4382349103156734135920503)
              ·
                refine ⟨6573523654735101203880755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4382349103156734135920503 6573523654735101203880755)
                ·
                  refine ⟨9860285482102651805821133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6573523654735101203880755 9860285482102651805821133)
                  ·
                    refine ⟨3697607055788494427182925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9860285482102651805821133 3697607055788494427182925)
                    ·
                      refine ⟨1386602645920685410193597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3697607055788494427182925 1386602645920685410193597)
                      ·
                        rfl

theorem cell23_2700399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 3].length) (baseStart_2700399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700399 prefixEnd_2700399 := by exact prefixLift 2700399
  have htrace : WordTrace (prefixWord ++ tailWord_2700399) baseStart_2700399 baseEnd_2700399 := by
    simpa [prefixWord, tailWord_2700399, baseEnd_2700399] using wordTrace_append hprefix tailTrace_2700399
  have hstable : (prefixWord ++ tailWord_2700399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700399).length < 2 ^ (prefixWord ++ tailWord_2700399).sum := by decide
  have hdescent : baseEnd_2700399 < baseStart_2700399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700402 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 2, 7]
def baseStart_2700402 : Nat := 118140960795 + 2700402 * 2 ^ 59
def prefixEnd_2700402 : Nat := 4983230072969 + 3 ^ 40 * 2700402 * 2
def baseEnd_2700402 : Nat := 462201395454216299485361

theorem tailTrace_2700402 : CollatzResearch.WordTrace tailWord_2700402 prefixEnd_2700402 462201395454216299485361 := by
  unfold tailWord_2700402
  simp only [CollatzResearch.WordTrace]
  refine ⟨24622938090728055197335865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65661168241941480526228973 24622938090728055197335865)
  ·
    refine ⟨18467203568046041398001899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24622938090728055197335865 18467203568046041398001899)
    ·
      refine ⟨27700805352069062097002849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18467203568046041398001899 27700805352069062097002849)
      ·
        refine ⟨20775604014051796572752137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27700805352069062097002849 20775604014051796572752137)
        ·
          refine ⟨15581703010538847429564103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20775604014051796572752137 15581703010538847429564103)
          ·
            refine ⟨23372554515808271144346155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15581703010538847429564103 23372554515808271144346155)
            ·
              refine ⟨35058831773712406716519233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23372554515808271144346155 35058831773712406716519233)
              ·
                refine ⟨26294123830284305037389425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35058831773712406716519233 26294123830284305037389425)
                ·
                  refine ⟨19720592872713228778042069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26294123830284305037389425 19720592872713228778042069)
                  ·
                    refine ⟨462201395454216299485361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19720592872713228778042069 462201395454216299485361)
                    ·
                      rfl

theorem cell23_2700402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_2700402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700402 prefixEnd_2700402 := by exact prefixLift 2700402
  have htrace : WordTrace (prefixWord ++ tailWord_2700402) baseStart_2700402 baseEnd_2700402 := by
    simpa [prefixWord, tailWord_2700402, baseEnd_2700402] using wordTrace_append hprefix tailTrace_2700402
  have hstable : (prefixWord ++ tailWord_2700402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700402).length < 2 ^ (prefixWord ++ tailWord_2700402).sum := by decide
  have hdescent : baseEnd_2700402 < baseStart_2700402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700412 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_2700412 : Nat := 118140960795 + 2700412 * 2 ^ 59
def prefixEnd_2700412 : Nat := 4983230072969 + 3 ^ 40 * 2700412 * 2
def baseEnd_2700412 : Nat := 1386609321169193859331037

theorem tailTrace_2700412 : CollatzResearch.WordTrace tailWord_2700412 prefixEnd_2700412 1386609321169193859331037 := by
  unfold tailWord_2700412
  simp only [CollatzResearch.WordTrace]
  refine ⟨49246058546437996248603745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65661411395250661664804993 49246058546437996248603745)
  ·
    refine ⟨36934543909828497186452809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49246058546437996248603745 36934543909828497186452809)
    ·
      refine ⟨27700907932371372889839607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36934543909828497186452809 27700907932371372889839607)
      ·
        refine ⟨41551361898557059334759411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27700907932371372889839607 41551361898557059334759411)
        ·
          refine ⟨62327042847835589002139117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41551361898557059334759411 62327042847835589002139117)
          ·
            refine ⟨23372641067938345875802169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62327042847835589002139117 23372641067938345875802169)
            ·
              refine ⟨17529480800953759406851627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23372641067938345875802169 17529480800953759406851627)
              ·
                refine ⟨26294221201430639110277441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17529480800953759406851627 26294221201430639110277441)
                ·
                  refine ⟨19720665901072979332708081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26294221201430639110277441 19720665901072979332708081)
                  ·
                    refine ⟨14790499425804734499531061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19720665901072979332708081 14790499425804734499531061)
                    ·
                      refine ⟨1386609321169193859331037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14790499425804734499531061 1386609321169193859331037)
                      ·
                        rfl

theorem cell23_2700412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_2700412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700412 prefixEnd_2700412 := by exact prefixLift 2700412
  have htrace : WordTrace (prefixWord ++ tailWord_2700412) baseStart_2700412 baseEnd_2700412 := by
    simpa [prefixWord, tailWord_2700412, baseEnd_2700412] using wordTrace_append hprefix tailTrace_2700412
  have hstable : (prefixWord ++ tailWord_2700412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700412).length < 2 ^ (prefixWord ++ tailWord_2700412).sum := by decide
  have hdescent : baseEnd_2700412 < baseStart_2700412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700414 : List Nat := [4, 2, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2700414 : Nat := 118140960795 + 2700414 * 2 ^ 59
def prefixEnd_2700414 : Nat := 4983230072969 + 3 ^ 40 * 2700414 * 2
def baseEnd_2700414 : Nat := 462203449376834283835343

theorem tailTrace_2700414 : CollatzResearch.WordTrace tailWord_2700414 prefixEnd_2700414 462203449376834283835343 := by
  unfold tailWord_2700414
  simp only [CollatzResearch.WordTrace]
  refine ⟨12311523754858593354847537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65661460025912497892520197 12311523754858593354847537)
  ·
    refine ⟨9233642816143945016135653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12311523754858593354847537 9233642816143945016135653)
    ·
      refine ⟨1731308028026989690525435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9233642816143945016135653 1731308028026989690525435)
      ·
        refine ⟨2596962042040484535788153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1731308028026989690525435 2596962042040484535788153)
        ·
          refine ⟨1947721531530363401841115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2596962042040484535788153 1947721531530363401841115)
          ·
            refine ⟨2921582297295545102761673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1947721531530363401841115 2921582297295545102761673)
            ·
              refine ⟨2191186722971658827071255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2921582297295545102761673 2191186722971658827071255)
              ·
                refine ⟨3286780084457488240606883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2191186722971658827071255 3286780084457488240606883)
                ·
                  refine ⟨4930170126686232360910325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3286780084457488240606883 4930170126686232360910325)
                  ·
                    refine ⟨462203449376834283835343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4930170126686232360910325 462203449376834283835343)
                    ·
                      rfl

theorem cell23_2700414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2700414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700414 prefixEnd_2700414 := by exact prefixLift 2700414
  have htrace : WordTrace (prefixWord ++ tailWord_2700414) baseStart_2700414 baseEnd_2700414 := by
    simpa [prefixWord, tailWord_2700414, baseEnd_2700414] using wordTrace_append hprefix tailTrace_2700414
  have hstable : (prefixWord ++ tailWord_2700414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700414).length < 2 ^ (prefixWord ++ tailWord_2700414).sum := by decide
  have hdescent : baseEnd_2700414 < baseStart_2700414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700450 : List Nat := [3, 3, 1, 3, 3, 1, 1, 1, 1, 3, 3]
def baseStart_2700450 : Nat := 118140960795 + 2700450 * 2 ^ 59
def prefixEnd_2700450 : Nat := 4983230072969 + 3 ^ 40 * 2700450 * 2
def baseEnd_2700450 : Nat := 1386628833434064710655863

theorem tailTrace_2700450 : CollatzResearch.WordTrace tailWord_2700450 prefixEnd_2700450 1386628833434064710655863 := by
  unfold tailWord_2700450
  simp only [CollatzResearch.WordTrace]
  refine ⟨24623375766684581246772701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65662335377825549991393869 24623375766684581246772701)
  ·
    refine ⟨9233765912506717967539763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24623375766684581246772701 9233765912506717967539763)
    ·
      refine ⟨13850648868760076951309645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9233765912506717967539763 13850648868760076951309645)
      ·
        refine ⟨5193993325785028856741117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13850648868760076951309645 5193993325785028856741117)
        ·
          refine ⟨1947747497169385821277919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5193993325785028856741117 1947747497169385821277919)
          ·
            refine ⟨2921621245754078731916879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1947747497169385821277919 2921621245754078731916879)
            ·
              refine ⟨4382431868631118097875319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2921621245754078731916879 4382431868631118097875319)
              ·
                refine ⟨6573647802946677146812979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4382431868631118097875319 6573647802946677146812979)
                ·
                  refine ⟨9860471704420015720219469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6573647802946677146812979 9860471704420015720219469)
                  ·
                    refine ⟨3697676889157505895082301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9860471704420015720219469 3697676889157505895082301)
                    ·
                      refine ⟨1386628833434064710655863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3697676889157505895082301 1386628833434064710655863)
                      ·
                        rfl

theorem cell23_2700450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_2700450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700450 prefixEnd_2700450 := by exact prefixLift 2700450
  have htrace : WordTrace (prefixWord ++ tailWord_2700450) baseStart_2700450 baseEnd_2700450 := by
    simpa [prefixWord, tailWord_2700450, baseEnd_2700450] using wordTrace_append hprefix tailTrace_2700450
  have hstable : (prefixWord ++ tailWord_2700450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700450).length < 2 ^ (prefixWord ++ tailWord_2700450).sum := by decide
  have hdescent : baseEnd_2700450 < baseStart_2700450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700499 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 1, 7, 2]
def baseStart_2700499 : Nat := 118140960795 + 2700499 * 2 ^ 59
def prefixEnd_2700499 : Nat := 4983230072969 + 3 ^ 40 * 2700499 * 2
def baseEnd_2700499 : Nat := 1386653993986135018943137

theorem tailTrace_2700499 : CollatzResearch.WordTrace tailWord_2700499 prefixEnd_2700499 1386653993986135018943137 := by
  unfold tailWord_2700499
  simp only [CollatzResearch.WordTrace]
  refine ⟨98495290243560806355624551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65663526829040537570416367 98495290243560806355624551)
  ·
    refine ⟨147742935365341209533436827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98495290243560806355624551 147742935365341209533436827)
    ·
      refine ⟨221614403048011814300155241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147742935365341209533436827 221614403048011814300155241)
      ·
        refine ⟨166210802286008860725116431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221614403048011814300155241 166210802286008860725116431)
        ·
          refine ⟨249316203429013291087674647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166210802286008860725116431 249316203429013291087674647)
          ·
            refine ⟨373974305143519936631511971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249316203429013291087674647 373974305143519936631511971)
            ·
              refine ⟨560961457715279904947267957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373974305143519936631511971 560961457715279904947267957)
              ·
                refine ⟨52590136660807491088806371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 560961457715279904947267957 52590136660807491088806371)
                ·
                  refine ⟨78885204991211236633209557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52590136660807491088806371 78885204991211236633209557)
                  ·
                    refine ⟨1848871991981513358590849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 78885204991211236633209557 1848871991981513358590849)
                    ·
                      refine ⟨1386653993986135018943137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1848871991981513358590849 1386653993986135018943137)
                      ·
                        rfl

theorem cell23_2700499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 7, 2].length) (baseStart_2700499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700499 prefixEnd_2700499 := by exact prefixLift 2700499
  have htrace : WordTrace (prefixWord ++ tailWord_2700499) baseStart_2700499 baseEnd_2700499 := by
    simpa [prefixWord, tailWord_2700499, baseEnd_2700499] using wordTrace_append hprefix tailTrace_2700499
  have hstable : (prefixWord ++ tailWord_2700499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700499).length < 2 ^ (prefixWord ++ tailWord_2700499).sum := by decide
  have hdescent : baseEnd_2700499 < baseStart_2700499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700573 : List Nat := [1, 4, 2, 3, 1, 2, 1, 2, 3, 4]
def baseStart_2700573 : Nat := 118140960795 + 2700573 * 2 ^ 59
def prefixEnd_2700573 : Nat := 4983230072969 + 3 ^ 40 * 2700573 * 2
def baseEnd_2700573 : Nat := 462230663851522576472599

theorem tailTrace_2700573 : CollatzResearch.WordTrace tailWord_2700573 prefixEnd_2700573 462230663851522576472599 := by
  unfold tailWord_2700573
  simp only [CollatzResearch.WordTrace]
  refine ⟨98497989245292716993818373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65665326163528477995878915 98497989245292716993818373)
  ·
    refine ⟨18468372983492384436340945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98497989245292716993818373 18468372983492384436340945)
    ·
      refine ⟨13851279737619288327255709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18468372983492384436340945 13851279737619288327255709)
      ·
        refine ⟨5194229901607233122720891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13851279737619288327255709 5194229901607233122720891)
        ·
          refine ⟨7791344852410849684081337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5194229901607233122720891 7791344852410849684081337)
          ·
            refine ⟨5843508639308137263061003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7791344852410849684081337 5843508639308137263061003)
            ·
              refine ⟨8765262958962205894591505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5843508639308137263061003 8765262958962205894591505)
              ·
                refine ⟨6573947219221654420943629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8765262958962205894591505 6573947219221654420943629)
                ·
                  refine ⟨2465230207208120407853861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6573947219221654420943629 2465230207208120407853861)
                  ·
                    refine ⟨462230663851522576472599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2465230207208120407853861 462230663851522576472599)
                    ·
                      rfl

theorem cell23_2700573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_2700573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700573 prefixEnd_2700573 := by exact prefixLift 2700573
  have htrace : WordTrace (prefixWord ++ tailWord_2700573) baseStart_2700573 baseEnd_2700573 := by
    simpa [prefixWord, tailWord_2700573, baseEnd_2700573] using wordTrace_append hprefix tailTrace_2700573
  have hstable : (prefixWord ++ tailWord_2700573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700573).length < 2 ^ (prefixWord ++ tailWord_2700573).sum := by decide
  have hdescent : baseEnd_2700573 < baseStart_2700573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700639 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 5]
def baseStart_2700639 : Nat := 118140960795 + 2700639 * 2 ^ 59
def prefixEnd_2700639 : Nat := 4983230072969 + 3 ^ 40 * 2700639 * 2
def baseEnd_2700639 : Nat := 1386725881277764471192493

theorem tailTrace_2700639 : CollatzResearch.WordTrace tailWord_2700639 prefixEnd_2700639 1386725881277764471192493 := by
  unfold tailWord_2700639
  simp only [CollatzResearch.WordTrace]
  refine ⟨98500396463053610265720971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65666930975369073510480647 98500396463053610265720971)
  ·
    refine ⟨147750594694580415398581457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98500396463053610265720971 147750594694580415398581457)
    ·
      refine ⟨110812946020935311548936093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147750594694580415398581457 110812946020935311548936093)
      ·
        refine ⟨41554854757850741830851035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110812946020935311548936093 41554854757850741830851035)
        ·
          refine ⟨62332282136776112746276553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41554854757850741830851035 62332282136776112746276553)
          ·
            refine ⟨46749211602582084559707415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62332282136776112746276553 46749211602582084559707415)
            ·
              refine ⟨70123817403873126839561123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46749211602582084559707415 70123817403873126839561123)
              ·
                refine ⟨105185726105809690259341685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70123817403873126839561123 105185726105809690259341685)
                ·
                  refine ⟨9861161822419658461813283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105185726105809690259341685 9861161822419658461813283)
                  ·
                    refine ⟨14791742733629487692719925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9861161822419658461813283 14791742733629487692719925)
                    ·
                      refine ⟨1386725881277764471192493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14791742733629487692719925 1386725881277764471192493)
                      ·
                        rfl

theorem cell23_2700639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_2700639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700639 prefixEnd_2700639 := by exact prefixLift 2700639
  have htrace : WordTrace (prefixWord ++ tailWord_2700639) baseStart_2700639 baseEnd_2700639 := by
    simpa [prefixWord, tailWord_2700639, baseEnd_2700639] using wordTrace_append hprefix tailTrace_2700639
  have hstable : (prefixWord ++ tailWord_2700639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700639).length < 2 ^ (prefixWord ++ tailWord_2700639).sum := by decide
  have hdescent : baseEnd_2700639 < baseStart_2700639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700653 : List Nat := [1, 5, 1, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_2700653 : Nat := 118140960795 + 2700653 * 2 ^ 59
def prefixEnd_2700653 : Nat := 4983230072969 + 3 ^ 40 * 2700653 * 2
def baseEnd_2700653 : Nat := 1386733070006927416417429

theorem tailTrace_2700653 : CollatzResearch.WordTrace tailWord_2700653 prefixEnd_2700653 1386733070006927416417429 := by
  unfold tailWord_2700653
  simp only [CollatzResearch.WordTrace]
  refine ⟨98500907085002890656730613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65667271390001927104487075 98500907085002890656730613)
  ·
    refine ⟨9234460039219020999068495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98500907085002890656730613 9234460039219020999068495)
    ·
      refine ⟨13851690058828531498602743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9234460039219020999068495 13851690058828531498602743)
      ·
        refine ⟨20777535088242797247904115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13851690058828531498602743 20777535088242797247904115)
        ·
          refine ⟨31166302632364195871856173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20777535088242797247904115 31166302632364195871856173)
          ·
            refine ⟨11687363487136573451946065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31166302632364195871856173 11687363487136573451946065)
            ·
              refine ⟨8765522615352430088959549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11687363487136573451946065 8765522615352430088959549)
              ·
                refine ⟨3287070980757161283359831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8765522615352430088959549 3287070980757161283359831)
                ·
                  refine ⟨4930606471135741925039747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3287070980757161283359831 4930606471135741925039747)
                  ·
                    refine ⟨7395909706703612887559621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4930606471135741925039747 7395909706703612887559621)
                    ·
                      refine ⟨1386733070006927416417429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7395909706703612887559621 1386733070006927416417429)
                      ·
                        rfl

theorem cell23_2700653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_2700653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700653 prefixEnd_2700653 := by exact prefixLift 2700653
  have htrace : WordTrace (prefixWord ++ tailWord_2700653) baseStart_2700653 baseEnd_2700653 := by
    simpa [prefixWord, tailWord_2700653, baseEnd_2700653] using wordTrace_append hprefix tailTrace_2700653
  have hstable : (prefixWord ++ tailWord_2700653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700653).length < 2 ^ (prefixWord ++ tailWord_2700653).sum := by decide
  have hdescent : baseEnd_2700653 < baseStart_2700653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700656 : List Nat := [2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 5]
def baseStart_2700656 : Nat := 118140960795 + 2700656 * 2 ^ 59
def prefixEnd_2700656 : Nat := 4983230072969 + 3 ^ 40 * 2700656 * 2
def baseEnd_2700656 : Nat := 1386734610448890904679915

theorem tailTrace_2700656 : CollatzResearch.WordTrace tailWord_2700656 prefixEnd_2700656 1386734610448890904679915 := by
  unfold tailWord_2700656
  simp only [CollatzResearch.WordTrace]
  refine ⟨49250508251996011084544911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65667344335994681446059881 49250508251996011084544911)
  ·
    refine ⟨73875762377994016626817367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49250508251996011084544911 73875762377994016626817367)
    ·
      refine ⟨110813643566991024940226051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73875762377994016626817367 110813643566991024940226051)
      ·
        refine ⟨166220465350486537410339077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110813643566991024940226051 166220465350486537410339077)
        ·
          refine ⟨31166337253216225764438577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166220465350486537410339077 31166337253216225764438577)
          ·
            refine ⟨23374752939912169323328933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31166337253216225764438577 23374752939912169323328933)
            ·
              refine ⟨4382766176233531748124175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23374752939912169323328933 4382766176233531748124175)
              ·
                refine ⟨6574149264350297622186263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4382766176233531748124175 6574149264350297622186263)
                ·
                  refine ⟨9861223896525446433279395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6574149264350297622186263 9861223896525446433279395)
                  ·
                    refine ⟨14791835844788169649919093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9861223896525446433279395 14791835844788169649919093)
                    ·
                      refine ⟨1386734610448890904679915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14791835844788169649919093 1386734610448890904679915)
                      ·
                        rfl

theorem cell23_2700656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 5].length) (baseStart_2700656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700656 prefixEnd_2700656 := by exact prefixLift 2700656
  have htrace : WordTrace (prefixWord ++ tailWord_2700656) baseStart_2700656 baseEnd_2700656 := by
    simpa [prefixWord, tailWord_2700656, baseEnd_2700656] using wordTrace_append hprefix tailTrace_2700656
  have hstable : (prefixWord ++ tailWord_2700656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700656).length < 2 ^ (prefixWord ++ tailWord_2700656).sum := by decide
  have hdescent : baseEnd_2700656 < baseStart_2700656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700676 : List Nat := [2, 3, 2, 1, 1, 4, 2, 8]
def baseStart_2700676 : Nat := 118140960795 + 2700676 * 2 ^ 59
def prefixEnd_2700676 : Nat := 4983230072969 + 3 ^ 40 * 2700676 * 2
def baseEnd_2700676 : Nat := 51360921483777067645549

theorem tailTrace_2700676 : CollatzResearch.WordTrace tailWord_2700676 prefixEnd_2700676 51360921483777067645549 := by
  unfold tailWord_2700676
  simp only [CollatzResearch.WordTrace]
  refine ⟨49250872981959782792408941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65667830642613043723211921 49250872981959782792408941)
  ·
    refine ⟨18469077368234918547153353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49250872981959782792408941 18469077368234918547153353)
    ·
      refine ⟨13851808026176188910365015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18469077368234918547153353 13851808026176188910365015)
      ·
        refine ⟨20777712039264283365547523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13851808026176188910365015 20777712039264283365547523)
        ·
          refine ⟨31166568058896425048321285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20777712039264283365547523 31166568058896425048321285)
          ·
            refine ⟨5843731511043079696560241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31166568058896425048321285 5843731511043079696560241)
            ·
              refine ⟨4382798633282309772420181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5843731511043079696560241 4382798633282309772420181)
              ·
                refine ⟨51360921483777067645549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4382798633282309772420181 51360921483777067645549)
                ·
                  rfl

theorem cell23_2700676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 8].length) (baseStart_2700676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700676 prefixEnd_2700676 := by exact prefixLift 2700676
  have htrace : WordTrace (prefixWord ++ tailWord_2700676) baseStart_2700676 baseEnd_2700676 := by
    simpa [prefixWord, tailWord_2700676, baseEnd_2700676] using wordTrace_append hprefix tailTrace_2700676
  have hstable : (prefixWord ++ tailWord_2700676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700676).length < 2 ^ (prefixWord ++ tailWord_2700676).sum := by decide
  have hdescent : baseEnd_2700676 < baseStart_2700676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700680 : List Nat := [2, 1, 3, 3, 1, 2, 4, 1, 2, 4]
def baseStart_2700680 : Nat := 118140960795 + 2700680 * 2 ^ 59
def prefixEnd_2700680 : Nat := 4983230072969 + 3 ^ 40 * 2700680 * 2
def baseEnd_2700680 : Nat := 462248977994866270259935

theorem tailTrace_2700680 : CollatzResearch.WordTrace tailWord_2700680 prefixEnd_2700680 462248977994866270259935 := by
  unfold tailWord_2700680
  simp only [CollatzResearch.WordTrace]
  refine ⟨49250945927952537133981747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65667927903936716178642329 49250945927952537133981747)
  ·
    refine ⟨73876418891928805700972621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49250945927952537133981747 73876418891928805700972621)
    ·
      refine ⟨27703657084473302137864733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73876418891928805700972621 27703657084473302137864733)
      ·
        refine ⟨10388871406677488301699275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27703657084473302137864733 10388871406677488301699275)
        ·
          refine ⟨15583307110016232452548913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10388871406677488301699275 15583307110016232452548913)
          ·
            refine ⟨11687480332512174339411685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15583307110016232452548913 11687480332512174339411685)
            ·
              refine ⟨2191402562346032688639691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11687480332512174339411685 2191402562346032688639691)
              ·
                refine ⟨3287103843519049032959537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2191402562346032688639691 3287103843519049032959537)
                ·
                  refine ⟨2465327882639286774719653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3287103843519049032959537 2465327882639286774719653)
                  ·
                    refine ⟨462248977994866270259935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2465327882639286774719653 462248977994866270259935)
                    ·
                      rfl

theorem cell23_2700680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_2700680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700680 prefixEnd_2700680 := by exact prefixLift 2700680
  have htrace : WordTrace (prefixWord ++ tailWord_2700680) baseStart_2700680 baseEnd_2700680 := by
    simpa [prefixWord, tailWord_2700680, baseEnd_2700680] using wordTrace_append hprefix tailTrace_2700680
  have hstable : (prefixWord ++ tailWord_2700680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700680).length < 2 ^ (prefixWord ++ tailWord_2700680).sum := by decide
  have hdescent : baseEnd_2700680 < baseStart_2700680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700689 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 2, 7]
def baseStart_2700689 : Nat := 118140960795 + 2700689 * 2 ^ 59
def prefixEnd_2700689 : Nat := 4983230072969 + 3 ^ 40 * 2700689 * 2
def baseEnd_2700689 : Nat := 462250518436829758522421

theorem tailTrace_2700689 : CollatzResearch.WordTrace tailWord_2700689 prefixEnd_2700689 462250518436829758522421 := by
  unfold tailWord_2700689
  simp only [CollatzResearch.WordTrace]
  refine ⟨98502220112872468805041121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65668146741914979203360747 98502220112872468805041121)
  ·
    refine ⟨73876665084654351603780841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98502220112872468805041121 73876665084654351603780841)
    ·
      refine ⟨55407498813490763702835631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73876665084654351603780841 55407498813490763702835631)
      ·
        refine ⟨83111248220236145554253447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55407498813490763702835631 83111248220236145554253447)
        ·
          refine ⟨124666872330354218331380171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83111248220236145554253447 124666872330354218331380171)
          ·
            refine ⟨187000308495531327497070257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124666872330354218331380171 187000308495531327497070257)
            ·
              refine ⟨140250231371648495622802693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187000308495531327497070257 140250231371648495622802693)
              ·
                refine ⟨26296918382184092929275505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140250231371648495622802693 26296918382184092929275505)
                ·
                  refine ⟨19722688786638069696956629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26296918382184092929275505 19722688786638069696956629)
                  ·
                    refine ⟨462250518436829758522421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19722688786638069696956629 462250518436829758522421)
                    ·
                      rfl

theorem cell23_2700689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_2700689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700689 prefixEnd_2700689 := by exact prefixLift 2700689
  have htrace : WordTrace (prefixWord ++ tailWord_2700689) baseStart_2700689 baseEnd_2700689 := by
    simpa [prefixWord, tailWord_2700689, baseEnd_2700689] using wordTrace_append hprefix tailTrace_2700689
  have hstable : (prefixWord ++ tailWord_2700689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700689).length < 2 ^ (prefixWord ++ tailWord_2700689).sum := by decide
  have hdescent : baseEnd_2700689 < baseStart_2700689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700700 : List Nat := [2, 2, 3, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2700700 : Nat := 118140960795 + 2700700 * 2 ^ 59
def prefixEnd_2700700 : Nat := 4983230072969 + 3 ^ 40 * 2700700 * 2
def baseEnd_2700700 : Nat := 1386757203597688732529713

theorem tailTrace_2700700 : CollatzResearch.WordTrace tailWord_2700700 prefixEnd_2700700 1386757203597688732529713 := by
  unfold tailWord_2700700
  simp only [CollatzResearch.WordTrace]
  refine ⟨49251310657916308841845777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65668414210555078455794369 49251310657916308841845777)
  ·
    refine ⟨36938482993437231631384333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49251310657916308841845777 36938482993437231631384333)
    ·
      refine ⟨13851931122538961861769125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36938482993437231631384333 13851931122538961861769125)
      ·
        refine ⟨2597237085476055349081711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13851931122538961861769125 2597237085476055349081711)
        ·
          refine ⟨3895855628214083023622567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2597237085476055349081711 3895855628214083023622567)
          ·
            refine ⟨5843783442321124535433851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3895855628214083023622567 5843783442321124535433851)
            ·
              refine ⟨8765675163481686803150777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5843783442321124535433851 8765675163481686803150777)
              ·
                refine ⟨6574256372611265102363083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8765675163481686803150777 6574256372611265102363083)
                ·
                  refine ⟨9861384558916897653544625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6574256372611265102363083 9861384558916897653544625)
                  ·
                    refine ⟨7396038419187673240158469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9861384558916897653544625 7396038419187673240158469)
                    ·
                      refine ⟨1386757203597688732529713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7396038419187673240158469 1386757203597688732529713)
                      ·
                        rfl

theorem cell23_2700700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2700700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700700 prefixEnd_2700700 := by exact prefixLift 2700700
  have htrace : WordTrace (prefixWord ++ tailWord_2700700) baseStart_2700700 baseEnd_2700700 := by
    simpa [prefixWord, tailWord_2700700, baseEnd_2700700] using wordTrace_append hprefix tailTrace_2700700
  have hstable : (prefixWord ++ tailWord_2700700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700700).length < 2 ^ (prefixWord ++ tailWord_2700700).sum := by decide
  have hdescent : baseEnd_2700700 < baseStart_2700700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700703 : List Nat := [1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 3]
def baseStart_2700703 : Nat := 118140960795 + 2700703 * 2 ^ 59
def prefixEnd_2700703 : Nat := 4983230072969 + 3 ^ 40 * 2700703 * 2
def baseEnd_2700703 : Nat := 1386758744039652220792199

theorem tailTrace_2700703 : CollatzResearch.WordTrace tailWord_2700703 prefixEnd_2700703 1386758744039652220792199 := by
  unfold tailWord_2700703
  simp only [CollatzResearch.WordTrace]
  refine ⟨98502730734821749196050763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65668487156547832797367175 98502730734821749196050763)
  ·
    refine ⟨147754096102232623794076145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98502730734821749196050763 147754096102232623794076145)
    ·
      refine ⟨110815572076674467845557109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147754096102232623794076145 110815572076674467845557109)
      ·
        refine ⟨10388959882188231360520979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110815572076674467845557109 10388959882188231360520979)
        ·
          refine ⟨15583439823282347040781469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10388959882188231360520979 15583439823282347040781469)
          ·
            refine ⟨5843789933730880140293051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15583439823282347040781469 5843789933730880140293051)
            ·
              refine ⟨8765684900596320210439577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5843789933730880140293051 8765684900596320210439577)
              ·
                refine ⟨6574263675447240157829683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8765684900596320210439577 6574263675447240157829683)
                ·
                  refine ⟨9861395513170860236744525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6574263675447240157829683 9861395513170860236744525)
                  ·
                    refine ⟨3698023317439072588779197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9861395513170860236744525 3698023317439072588779197)
                    ·
                      refine ⟨1386758744039652220792199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3698023317439072588779197 1386758744039652220792199)
                      ·
                        rfl

theorem cell23_2700703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_2700703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700703 prefixEnd_2700703 := by exact prefixLift 2700703
  have htrace : WordTrace (prefixWord ++ tailWord_2700703) baseStart_2700703 baseEnd_2700703 := by
    simpa [prefixWord, tailWord_2700703, baseEnd_2700703] using wordTrace_append hprefix tailTrace_2700703
  have hstable : (prefixWord ++ tailWord_2700703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700703).length < 2 ^ (prefixWord ++ tailWord_2700703).sum := by decide
  have hdescent : baseEnd_2700703 < baseStart_2700703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700719 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 3, 8]
def baseStart_2700719 : Nat := 118140960795 + 2700719 * 2 ^ 59
def prefixEnd_2700719 : Nat := 4983230072969 + 3 ^ 40 * 2700719 * 2
def baseEnd_2700719 : Nat := 462255653243374719397375

theorem tailTrace_2700719 : CollatzResearch.WordTrace tailWord_2700719 prefixEnd_2700719 462255653243374719397375 := by
  unfold tailWord_2700719
  simp only [CollatzResearch.WordTrace]
  refine ⟨98503314302763783928633211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65668876201842522619088807 98503314302763783928633211)
  ·
    refine ⟨147754971454145675892949817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98503314302763783928633211 147754971454145675892949817)
    ·
      refine ⟨110816228590609256919712363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147754971454145675892949817 110816228590609256919712363)
      ·
        refine ⟨166224342885913885379568545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110816228590609256919712363 166224342885913885379568545)
        ·
          refine ⟨124668257164435414034676409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166224342885913885379568545 124668257164435414034676409)
          ·
            refine ⟨93501192873326560526007307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124668257164435414034676409 93501192873326560526007307)
            ·
              refine ⟨140251789309989840789010961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93501192873326560526007307 140251789309989840789010961)
              ·
                refine ⟨105188841982492380591758221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140251789309989840789010961 105188841982492380591758221)
                ·
                  refine ⟨39445815743434642721909333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105188841982492380591758221 39445815743434642721909333)
                  ·
                    refine ⟨462255653243374719397375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39445815743434642721909333 462255653243374719397375)
                    ·
                      rfl

theorem cell23_2700719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 8].length) (baseStart_2700719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700719 prefixEnd_2700719 := by exact prefixLift 2700719
  have htrace : WordTrace (prefixWord ++ tailWord_2700719) baseStart_2700719 baseEnd_2700719 := by
    simpa [prefixWord, tailWord_2700719, baseEnd_2700719] using wordTrace_append hprefix tailTrace_2700719
  have hstable : (prefixWord ++ tailWord_2700719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700719).length < 2 ^ (prefixWord ++ tailWord_2700719).sum := by decide
  have hdescent : baseEnd_2700719 < baseStart_2700719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700738 : List Nat := [3, 5, 2, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_2700738 : Nat := 118140960795 + 2700738 * 2 ^ 59
def prefixEnd_2700738 : Nat := 4983230072969 + 3 ^ 40 * 2700738 * 2
def baseEnd_2700738 : Nat := 1386776715862559583854539

theorem tailTrace_2700738 : CollatzResearch.WordTrace tailWord_2700738 prefixEnd_2700738 1386776715862559583854539 := by
  unfold tailWord_2700738
  simp only [CollatzResearch.WordTrace]
  refine ⟨24626001822423737543393717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65669338193129966782383245 24626001822423737543393717)
  ·
    refine ⟨2308687670852225394693161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24626001822423737543393717 2308687670852225394693161)
    ·
      refine ⟨1731515753139169046019871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2308687670852225394693161 1731515753139169046019871)
      ·
        refine ⟨2597273629708753569029807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1731515753139169046019871 2597273629708753569029807)
        ·
          refine ⟨3895910444563130353544711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2597273629708753569029807 3895910444563130353544711)
          ·
            refine ⟨5843865666844695530317067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3895910444563130353544711 5843865666844695530317067)
            ·
              refine ⟨8765798500267043295475601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5843865666844695530317067 8765798500267043295475601)
              ·
                refine ⟨6574348875200282471606701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8765798500267043295475601 6574348875200282471606701)
                ·
                  refine ⟨2465380828200105926852513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6574348875200282471606701 2465380828200105926852513)
                  ·
                    refine ⟨1849035621150079445139385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2465380828200105926852513 1849035621150079445139385)
                    ·
                      refine ⟨1386776715862559583854539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1849035621150079445139385 1386776715862559583854539)
                      ·
                        rfl

theorem cell23_2700738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_2700738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700738 prefixEnd_2700738 := by exact prefixLift 2700738
  have htrace : WordTrace (prefixWord ++ tailWord_2700738) baseStart_2700738 baseEnd_2700738 := by
    simpa [prefixWord, tailWord_2700738, baseEnd_2700738] using wordTrace_append hprefix tailTrace_2700738
  have hstable : (prefixWord ++ tailWord_2700738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700738).length < 2 ^ (prefixWord ++ tailWord_2700738).sum := by decide
  have hdescent : baseEnd_2700738 < baseStart_2700738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700773 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 2, 2, 4]
def baseStart_2700773 : Nat := 118140960795 + 2700773 * 2 ^ 59
def prefixEnd_2700773 : Nat := 4983230072969 + 3 ^ 40 * 2700773 * 2
def baseEnd_2700773 : Nat := 1386794687685466946916877

theorem tailTrace_2700773 : CollatzResearch.WordTrace tailWord_2700773 prefixEnd_2700773 1386794687685466946916877 := by
  unfold tailWord_2700773
  simp only [CollatzResearch.WordTrace]
  refine ⟨98505283844568151151098973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65670189229712100767399315 98505283844568151151098973)
  ·
    refine ⟨36939481441713056681662115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98505283844568151151098973 36939481441713056681662115)
    ·
      refine ⟨55409222162569585022493173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36939481441713056681662115 55409222162569585022493173)
      ·
        refine ⟨5194614577740898595858735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55409222162569585022493173 5194614577740898595858735)
        ·
          refine ⟨7791921866611347893788103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5194614577740898595858735 7791921866611347893788103)
          ·
            refine ⟨11687882799917021840682155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7791921866611347893788103 11687882799917021840682155)
            ·
              refine ⟨17531824199875532761023233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11687882799917021840682155 17531824199875532761023233)
              ·
                refine ⟨13148868149906649570767425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17531824199875532761023233 13148868149906649570767425)
                ·
                  refine ⟨9861651112429987178075569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13148868149906649570767425 9861651112429987178075569)
                  ·
                    refine ⟨7396238334322490383556677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9861651112429987178075569 7396238334322490383556677)
                    ·
                      refine ⟨1386794687685466946916877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7396238334322490383556677 1386794687685466946916877)
                      ·
                        rfl

theorem cell23_2700773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_2700773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700773 prefixEnd_2700773 := by exact prefixLift 2700773
  have htrace : WordTrace (prefixWord ++ tailWord_2700773) baseStart_2700773 baseEnd_2700773 := by
    simpa [prefixWord, tailWord_2700773, baseEnd_2700773] using wordTrace_append hprefix tailTrace_2700773
  have hstable : (prefixWord ++ tailWord_2700773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700773).length < 2 ^ (prefixWord ++ tailWord_2700773).sum := by decide
  have hdescent : baseEnd_2700773 < baseStart_2700773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700783 : List Nat := [1, 1, 2, 1, 4, 1, 4, 4, 5]
def baseStart_2700783 : Nat := 118140960795 + 2700783 * 2 ^ 59
def prefixEnd_2700783 : Nat := 4983230072969 + 3 ^ 40 * 2700783 * 2
def baseEnd_2700783 : Nat := 154088869165779100865759

theorem tailTrace_2700783 : CollatzResearch.WordTrace tailWord_2700783 prefixEnd_2700783 154088869165779100865759 := by
  unfold tailWord_2700783
  simp only [CollatzResearch.WordTrace]
  refine ⟨98505648574531922858963003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65670432383021281905975335 98505648574531922858963003)
  ·
    refine ⟨147758472861797884288444505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98505648574531922858963003 147758472861797884288444505)
    ·
      refine ⟨110818854646348413216333379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147758472861797884288444505 110818854646348413216333379)
      ·
        refine ⟨166228281969522619824500069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110818854646348413216333379 166228281969522619824500069)
        ·
          refine ⟨31167802869285491217093763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166228281969522619824500069 31167802869285491217093763)
          ·
            refine ⟨46751704303928236825640645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31167802869285491217093763 46751704303928236825640645)
            ·
              refine ⟨8765944556986544404807621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46751704303928236825640645 8765944556986544404807621)
              ·
                refine ⟨1643614604434977075901429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8765944556986544404807621 1643614604434977075901429)
                ·
                  refine ⟨154088869165779100865759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1643614604434977075901429 154088869165779100865759)
                  ·
                    rfl

theorem cell23_2700783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 5].length) (baseStart_2700783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700783 prefixEnd_2700783 := by exact prefixLift 2700783
  have htrace : WordTrace (prefixWord ++ tailWord_2700783) baseStart_2700783 baseEnd_2700783 := by
    simpa [prefixWord, tailWord_2700783, baseEnd_2700783] using wordTrace_append hprefix tailTrace_2700783
  have hstable : (prefixWord ++ tailWord_2700783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700783).length < 2 ^ (prefixWord ++ tailWord_2700783).sum := by decide
  have hdescent : baseEnd_2700783 < baseStart_2700783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700796 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 1, 7]
def baseStart_2700796 : Nat := 118140960795 + 2700796 * 2 ^ 59
def prefixEnd_2700796 : Nat := 4983230072969 + 3 ^ 40 * 2700796 * 2
def baseEnd_2700796 : Nat := 462268832580173452309757

theorem tailTrace_2700796 : CollatzResearch.WordTrace tailWord_2700796 prefixEnd_2700796 462268832580173452309757 := by
  unfold tailWord_2700796
  simp only [CollatzResearch.WordTrace]
  refine ⟨49253061361742413039593121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65670748482323217386124161 49253061361742413039593121)
  ·
    refine ⟨36939796021306809779694841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49253061361742413039593121 36939796021306809779694841)
    ·
      refine ⟨27704847015980107334771131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36939796021306809779694841 27704847015980107334771131)
      ·
        refine ⟨41557270523970161002156697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27704847015980107334771131 41557270523970161002156697)
        ·
          refine ⟨31167952892977620751617523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41557270523970161002156697 31167952892977620751617523)
          ·
            refine ⟨46751929339466431127426285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31167952892977620751617523 46751929339466431127426285)
            ·
              refine ⟨17531973502299911672784857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46751929339466431127426285 17531973502299911672784857)
              ·
                refine ⟨13148980126724933754588643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17531973502299911672784857 13148980126724933754588643)
                ·
                  refine ⟨19723470190087400631882965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13148980126724933754588643 19723470190087400631882965)
                  ·
                    refine ⟨462268832580173452309757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19723470190087400631882965 462268832580173452309757)
                    ·
                      rfl

theorem cell23_2700796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_2700796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700796 prefixEnd_2700796 := by exact prefixLift 2700796
  have htrace : WordTrace (prefixWord ++ tailWord_2700796) baseStart_2700796 baseEnd_2700796 := by
    simpa [prefixWord, tailWord_2700796, baseEnd_2700796] using wordTrace_append hprefix tailTrace_2700796
  have hstable : (prefixWord ++ tailWord_2700796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700796).length < 2 ^ (prefixWord ++ tailWord_2700796).sum := by decide
  have hdescent : baseEnd_2700796 < baseStart_2700796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700833 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_2700833 : Nat := 118140960795 + 2700833 * 2 ^ 59
def prefixEnd_2700833 : Nat := 4983230072969 + 3 ^ 40 * 2700833 * 2
def baseEnd_2700833 : Nat := 1386825496524736712166601

theorem tailTrace_2700833 : CollatzResearch.WordTrace tailWord_2700833 prefixEnd_2700833 1386825496524736712166601 := by
  unfold tailWord_2700833
  simp only [CollatzResearch.WordTrace]
  refine ⟨98507472224350781398283153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65671648149567187598855435 98507472224350781398283153)
  ·
    refine ⟨73880604168263086048712365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98507472224350781398283153 73880604168263086048712365)
    ·
      refine ⟨27705226563098657268267137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73880604168263086048712365 27705226563098657268267137)
      ·
        refine ⟨20778919922323992951200353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27705226563098657268267137 20778919922323992951200353)
        ·
          refine ⟨15584189941742994713400265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20778919922323992951200353 15584189941742994713400265)
          ·
            refine ⟨11688142456307246035050199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15584189941742994713400265 11688142456307246035050199)
            ·
              refine ⟨17532213684460869052575299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11688142456307246035050199 17532213684460869052575299)
              ·
                refine ⟨26298320526691303578862949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17532213684460869052575299 26298320526691303578862949)
                ·
                  refine ⟨4930935098754619421036803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26298320526691303578862949 4930935098754619421036803)
                  ·
                    refine ⟨7396402648131929131555205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4930935098754619421036803 7396402648131929131555205)
                    ·
                      refine ⟨1386825496524736712166601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7396402648131929131555205 1386825496524736712166601)
                      ·
                        rfl

theorem cell23_2700833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_2700833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700833 prefixEnd_2700833 := by exact prefixLift 2700833
  have htrace : WordTrace (prefixWord ++ tailWord_2700833) baseStart_2700833 baseEnd_2700833 := by
    simpa [prefixWord, tailWord_2700833, baseEnd_2700833] using wordTrace_append hprefix tailTrace_2700833
  have hstable : (prefixWord ++ tailWord_2700833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700833).length < 2 ^ (prefixWord ++ tailWord_2700833).sum := by decide
  have hdescent : baseEnd_2700833 < baseStart_2700833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700840 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_2700840 : Nat := 118140960795 + 2700840 * 2 ^ 59
def prefixEnd_2700840 : Nat := 4983230072969 + 3 ^ 40 * 2700840 * 2
def baseEnd_2700840 : Nat := 1386829090889318184779069

theorem tailTrace_2700840 : CollatzResearch.WordTrace tailWord_2700840 prefixEnd_2700840 1386829090889318184779069 := by
  unfold tailWord_2700840
  simp only [CollatzResearch.WordTrace]
  refine ⟨49253863767662710796893987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65671818356883614395858649 49253863767662710796893987)
  ·
    refine ⟨73880795651494066195340981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49253863767662710796893987 73880795651494066195340981)
    ·
      refine ⟨6926324592327568705813217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73880795651494066195340981 6926324592327568705813217)
      ·
        refine ⟨5194743444245676529359913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6926324592327568705813217 5194743444245676529359913)
        ·
          refine ⟨3896057583184257397019935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5194743444245676529359913 3896057583184257397019935)
          ·
            refine ⟨5844086374776386095529903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3896057583184257397019935 5844086374776386095529903)
            ·
              refine ⟨8766129562164579143294855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5844086374776386095529903 8766129562164579143294855)
              ·
                refine ⟨13149194343246868714942283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8766129562164579143294855 13149194343246868714942283)
                ·
                  refine ⟨19723791514870303072413425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13149194343246868714942283 19723791514870303072413425)
                  ·
                    refine ⟨14792843636152727304310069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19723791514870303072413425 14792843636152727304310069)
                    ·
                      refine ⟨1386829090889318184779069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14792843636152727304310069 1386829090889318184779069)
                      ·
                        rfl

theorem cell23_2700840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_2700840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700840 prefixEnd_2700840 := by exact prefixLift 2700840
  have htrace : WordTrace (prefixWord ++ tailWord_2700840) baseStart_2700840 baseEnd_2700840 := by
    simpa [prefixWord, tailWord_2700840, baseEnd_2700840] using wordTrace_append hprefix tailTrace_2700840
  have hstable : (prefixWord ++ tailWord_2700840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700840).length < 2 ^ (prefixWord ++ tailWord_2700840).sum := by decide
  have hdescent : baseEnd_2700840 < baseStart_2700840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700903 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 3, 5]
def baseStart_2700903 : Nat := 118140960795 + 2700903 * 2 ^ 59
def prefixEnd_2700903 : Nat := 4983230072969 + 3 ^ 40 * 2700903 * 2
def baseEnd_2700903 : Nat := 462287146723517146097093

theorem tailTrace_2700903 : CollatzResearch.WordTrace tailWord_2700903 prefixEnd_2700903 462287146723517146097093 := by
  unfold tailWord_2700903
  simp only [CollatzResearch.WordTrace]
  refine ⟨98510025334097183353331363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65673350222731455568887575 98510025334097183353331363)
  ·
    refine ⟨147765038001145775029997045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98510025334097183353331363 147765038001145775029997045)
    ·
      refine ⟨13852972312607416409062223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147765038001145775029997045 13852972312607416409062223)
      ·
        refine ⟨20779458468911124613593335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13852972312607416409062223 20779458468911124613593335)
        ·
          refine ⟨31169187703366686920390003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20779458468911124613593335 31169187703366686920390003)
          ·
            refine ⟨46753781555050030380585005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31169187703366686920390003 46753781555050030380585005)
            ·
              refine ⟨17532668083143761392719377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46753781555050030380585005 17532668083143761392719377)
              ·
                refine ⟨13149501062357821044539533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17532668083143761392719377 13149501062357821044539533)
                ·
                  refine ⟨4931062898384182891702325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13149501062357821044539533 4931062898384182891702325)
                  ·
                    refine ⟨462287146723517146097093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4931062898384182891702325 462287146723517146097093)
                    ·
                      rfl

theorem cell23_2700903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_2700903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700903 prefixEnd_2700903 := by exact prefixLift 2700903
  have htrace : WordTrace (prefixWord ++ tailWord_2700903) baseStart_2700903 baseEnd_2700903 := by
    simpa [prefixWord, tailWord_2700903, baseEnd_2700903] using wordTrace_append hprefix tailTrace_2700903
  have hstable : (prefixWord ++ tailWord_2700903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700903).length < 2 ^ (prefixWord ++ tailWord_2700903).sum := by decide
  have hdescent : baseEnd_2700903 < baseStart_2700903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700917 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_2700917 : Nat := 118140960795 + 2700917 * 2 ^ 59
def prefixEnd_2700917 : Nat := 4983230072969 + 3 ^ 40 * 2700917 * 2
def baseEnd_2700917 : Nat := 1386868628899714383516215

theorem tailTrace_2700917 : CollatzResearch.WordTrace tailWord_2700917 prefixEnd_2700917 1386868628899714383516215 := by
  unfold tailWord_2700917
  simp only [CollatzResearch.WordTrace]
  refine ⟨98510535956046463744341005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65673690637364309162894003 98510535956046463744341005)
  ·
    refine ⟨36941450983517423904127877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98510535956046463744341005 36941450983517423904127877)
    ·
      refine ⟨6926522059409516982023977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36941450983517423904127877 6926522059409516982023977)
      ·
        refine ⟨5194891544557137736517983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6926522059409516982023977 5194891544557137736517983)
        ·
          refine ⟨7792337316835706604776975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5194891544557137736517983 7792337316835706604776975)
          ·
            refine ⟨11688505975253559907165463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7792337316835706604776975 11688505975253559907165463)
            ·
              refine ⟨17532758962880339860748195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11688505975253559907165463 17532758962880339860748195)
              ·
                refine ⟨26299138444320509791122293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17532758962880339860748195 26299138444320509791122293)
                ·
                  refine ⟨2465544229155047792917715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26299138444320509791122293 2465544229155047792917715)
                  ·
                    refine ⟨3698316343732571689376573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2465544229155047792917715 3698316343732571689376573)
                    ·
                      refine ⟨1386868628899714383516215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3698316343732571689376573 1386868628899714383516215)
                      ·
                        rfl

theorem cell23_2700917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_2700917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700917 prefixEnd_2700917 := by exact prefixLift 2700917
  have htrace : WordTrace (prefixWord ++ tailWord_2700917) baseStart_2700917 baseEnd_2700917 := by
    simpa [prefixWord, tailWord_2700917, baseEnd_2700917] using wordTrace_append hprefix tailTrace_2700917
  have hstable : (prefixWord ++ tailWord_2700917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700917).length < 2 ^ (prefixWord ++ tailWord_2700917).sum := by decide
  have hdescent : baseEnd_2700917 < baseStart_2700917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700923 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 4]
def baseStart_2700923 : Nat := 118140960795 + 2700923 * 2 ^ 59
def prefixEnd_2700923 : Nat := 4983230072969 + 3 ^ 40 * 2700923 * 2
def baseEnd_2700923 : Nat := 1386871709783641360041187

theorem tailTrace_2700923 : CollatzResearch.WordTrace tailWord_2700923 prefixEnd_2700923 1386871709783641360041187 := by
  unfold tailWord_2700923
  simp only [CollatzResearch.WordTrace]
  refine ⟨98510754794024726769059423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65673836529349817846039615 98510754794024726769059423)
  ·
    refine ⟨147766132191037090153589135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98510754794024726769059423 147766132191037090153589135)
    ·
      refine ⟨221649198286555635230383703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147766132191037090153589135 221649198286555635230383703)
      ·
        refine ⟨332473797429833452845575555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221649198286555635230383703 332473797429833452845575555)
        ·
          refine ⟨498710696144750179268363333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332473797429833452845575555 498710696144750179268363333)
          ·
            refine ⟨93508255527140658612818125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 498710696144750179268363333 93508255527140658612818125)
            ·
              refine ⟨35065595822677746979806797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93508255527140658612818125 35065595822677746979806797)
              ·
                refine ⟨13149598433504155117427549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35065595822677746979806797 13149598433504155117427549)
                ·
                  refine ⟨4931099412564058169035331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13149598433504155117427549 4931099412564058169035331)
                  ·
                    refine ⟨7396649118846087253552997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4931099412564058169035331 7396649118846087253552997)
                    ·
                      refine ⟨1386871709783641360041187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7396649118846087253552997 1386871709783641360041187)
                      ·
                        rfl

theorem cell23_2700923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 4].length) (baseStart_2700923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700923 prefixEnd_2700923 := by exact prefixLift 2700923
  have htrace : WordTrace (prefixWord ++ tailWord_2700923) baseStart_2700923 baseEnd_2700923 := by
    simpa [prefixWord, tailWord_2700923, baseEnd_2700923] using wordTrace_append hprefix tailTrace_2700923
  have hstable : (prefixWord ++ tailWord_2700923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700923).length < 2 ^ (prefixWord ++ tailWord_2700923).sum := by decide
  have hdescent : baseEnd_2700923 < baseStart_2700923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700933 : List Nat := [1, 3, 1, 1, 4, 1, 1, 4, 1, 6]
def baseStart_2700933 : Nat := 118140960795 + 2700933 * 2 ^ 59
def prefixEnd_2700933 : Nat := 4983230072969 + 3 ^ 40 * 2700933 * 2
def baseEnd_2700933 : Nat := 462292281530062106972047

theorem tailTrace_2700933 : CollatzResearch.WordTrace tailWord_2700933 prefixEnd_2700933 462292281530062106972047 := by
  unfold tailWord_2700933
  simp only [CollatzResearch.WordTrace]
  refine ⟨98511119523988498476923453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65674079682658998984615635 98511119523988498476923453)
  ·
    refine ⟨36941669821495686928846295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98511119523988498476923453 36941669821495686928846295)
    ·
      refine ⟨55412504732243530393269443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36941669821495686928846295 55412504732243530393269443)
      ·
        refine ⟨83118757098365295589904165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55412504732243530393269443 83118757098365295589904165)
        ·
          refine ⟨15584766955943492923107031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83118757098365295589904165 15584766955943492923107031)
          ·
            refine ⟨23377150433915239384660547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15584766955943492923107031 23377150433915239384660547)
            ·
              refine ⟨35065725650872859076990821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23377150433915239384660547 35065725650872859076990821)
              ·
                refine ⟨6574823559538661076935779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35065725650872859076990821 6574823559538661076935779)
                ·
                  refine ⟨9862235339307991615403669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6574823559538661076935779 9862235339307991615403669)
                  ·
                    refine ⟨462292281530062106972047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9862235339307991615403669 462292281530062106972047)
                    ·
                      rfl

theorem cell23_2700933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_2700933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700933 prefixEnd_2700933 := by exact prefixLift 2700933
  have htrace : WordTrace (prefixWord ++ tailWord_2700933) baseStart_2700933 baseEnd_2700933 := by
    simpa [prefixWord, tailWord_2700933, baseEnd_2700933] using wordTrace_append hprefix tailTrace_2700933
  have hstable : (prefixWord ++ tailWord_2700933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700933).length < 2 ^ (prefixWord ++ tailWord_2700933).sum := by decide
  have hdescent : baseEnd_2700933 < baseStart_2700933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700940 : List Nat := [2, 2, 1, 2, 1, 1, 5, 3, 1, 1, 4]
def baseStart_2700940 : Nat := 118140960795 + 2700940 * 2 ^ 59
def prefixEnd_2700940 : Nat := 4983230072969 + 3 ^ 40 * 2700940 * 2
def baseEnd_2700940 : Nat := 1386880438954767793528609

theorem tailTrace_2700940 : CollatzResearch.WordTrace tailWord_2700940 prefixEnd_2700940 1386880438954767793528609 := by
  unfold tailWord_2700940
  simp only [CollatzResearch.WordTrace]
  refine ⟨49255687417481569336214137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65674249889975425781618849 49255687417481569336214137)
  ·
    refine ⟨36941765563111177002160603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49255687417481569336214137 36941765563111177002160603)
    ·
      refine ⟨55412648344666765503240905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36941765563111177002160603 55412648344666765503240905)
      ·
        refine ⟨41559486258500074127430679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55412648344666765503240905 41559486258500074127430679)
        ·
          refine ⟨62339229387750111191146019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41559486258500074127430679 62339229387750111191146019)
          ·
            refine ⟨93508844081625166786719029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62339229387750111191146019 93508844081625166786719029)
            ·
              refine ⟨8766454132652359386254909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93508844081625166786719029 8766454132652359386254909)
              ·
                refine ⟨3287420299744634769845591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8766454132652359386254909 3287420299744634769845591)
                ·
                  refine ⟨4931130449616952154768387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3287420299744634769845591 4931130449616952154768387)
                  ·
                    refine ⟨7396695674425428232152581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4931130449616952154768387 7396695674425428232152581)
                    ·
                      refine ⟨1386880438954767793528609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7396695674425428232152581 1386880438954767793528609)
                      ·
                        rfl

theorem cell23_2700940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_2700940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700940 prefixEnd_2700940 := by exact prefixLift 2700940
  have htrace : WordTrace (prefixWord ++ tailWord_2700940) baseStart_2700940 baseEnd_2700940 := by
    simpa [prefixWord, tailWord_2700940, baseEnd_2700940] using wordTrace_append hprefix tailTrace_2700940
  have hstable : (prefixWord ++ tailWord_2700940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700940).length < 2 ^ (prefixWord ++ tailWord_2700940).sum := by decide
  have hdescent : baseEnd_2700940 < baseStart_2700940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700960 : List Nat := [2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 5]
def baseStart_2700960 : Nat := 118140960795 + 2700960 * 2 ^ 59
def prefixEnd_2700960 : Nat := 4983230072969 + 3 ^ 40 * 2700960 * 2
def baseEnd_2700960 : Nat := 1386890708567857715278517

theorem tailTrace_2700960 : CollatzResearch.WordTrace tailWord_2700960 prefixEnd_2700960 1386890708567857715278517 := by
  unfold tailWord_2700960
  simp only [CollatzResearch.WordTrace]
  refine ⟨49256052147445341044078167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65674736196593788058770889 49256052147445341044078167)
  ·
    refine ⟨73884078221168011566117251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49256052147445341044078167 73884078221168011566117251)
    ·
      refine ⟨110826117331752017349175877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73884078221168011566117251 110826117331752017349175877)
      ·
        refine ⟨20779896999703503252970477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110826117331752017349175877 20779896999703503252970477)
        ·
          refine ⟨7792461374888813719863929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20779896999703503252970477 7792461374888813719863929)
          ·
            refine ⟨5844346031166610289897947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7792461374888813719863929 5844346031166610289897947)
            ·
              refine ⟨8766519046749915434846921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5844346031166610289897947 8766519046749915434846921)
              ·
                refine ⟨6574889285062436576135191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8766519046749915434846921 6574889285062436576135191)
                ·
                  refine ⟨9862333927593654864202787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6574889285062436576135191 9862333927593654864202787)
                  ·
                    refine ⟨14793500891390482296304181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9862333927593654864202787 14793500891390482296304181)
                    ·
                      refine ⟨1386890708567857715278517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14793500891390482296304181 1386890708567857715278517)
                      ·
                        rfl

theorem cell23_2700960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_2700960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2700960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2700960 prefixEnd_2700960 := by exact prefixLift 2700960
  have htrace : WordTrace (prefixWord ++ tailWord_2700960) baseStart_2700960 baseEnd_2700960 := by
    simpa [prefixWord, tailWord_2700960, baseEnd_2700960] using wordTrace_append hprefix tailTrace_2700960
  have hstable : (prefixWord ++ tailWord_2700960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700960).length < 2 ^ (prefixWord ++ tailWord_2700960).sum := by decide
  have hdescent : baseEnd_2700960 < baseStart_2700960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701014 : List Nat := [5, 2, 1, 3, 1, 1, 2, 8]
def baseStart_2701014 : Nat := 118140960795 + 2701014 * 2 ^ 59
def prefixEnd_2701014 : Nat := 4983230072969 + 3 ^ 40 * 2701014 * 2
def baseEnd_2701014 : Nat := 51367349500859277926047

theorem tailTrace_2701014 : CollatzResearch.WordTrace tailWord_2701014 prefixEnd_2701014 51367349500859277926047 := by
  unfold tailWord_2701014
  simp only [CollatzResearch.WordTrace]
  refine ⟨6157129614793440581913881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65676049224463366207081397 6157129614793440581913881)
  ·
    refine ⟨4617847211095080436435411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6157129614793440581913881 4617847211095080436435411)
    ·
      refine ⟨6926770816642620654653117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4617847211095080436435411 6926770816642620654653117)
      ·
        refine ⟨2597539056240982745494919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6926770816642620654653117 2597539056240982745494919)
        ·
          refine ⟨3896308584361474118242379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2597539056240982745494919 3896308584361474118242379)
          ·
            refine ⟨5844462876542211177363569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3896308584361474118242379 5844462876542211177363569)
            ·
              refine ⟨4383347157406658383022677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5844462876542211177363569 4383347157406658383022677)
              ·
                refine ⟨51367349500859277926047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4383347157406658383022677 51367349500859277926047)
                ·
                  rfl

theorem cell23_2701014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_2701014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701014 prefixEnd_2701014 := by exact prefixLift 2701014
  have htrace : WordTrace (prefixWord ++ tailWord_2701014) baseStart_2701014 baseEnd_2701014 := by
    simpa [prefixWord, tailWord_2701014, baseEnd_2701014] using wordTrace_append hprefix tailTrace_2701014
  have hstable : (prefixWord ++ tailWord_2701014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701014).length < 2 ^ (prefixWord ++ tailWord_2701014).sum := by decide
  have hdescent : baseEnd_2701014 < baseStart_2701014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701023 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 1, 8]
def baseStart_2701023 : Nat := 118140960795 + 2701023 * 2 ^ 59
def prefixEnd_2701023 : Nat := 4983230072969 + 3 ^ 40 * 2701023 * 2
def baseEnd_2701023 : Nat := 462307685949696989596909

theorem tailTrace_2701023 : CollatzResearch.WordTrace tailWord_2701023 prefixEnd_2701023 462307685949696989596909 := by
  unfold tailWord_2701023
  simp only [CollatzResearch.WordTrace]
  refine ⟨98514402093662443847699723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65676268062441629231799815 98514402093662443847699723)
  ·
    refine ⟨147771603140493665771549585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98514402093662443847699723 147771603140493665771549585)
    ·
      refine ⟨110828702355370249328662189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147771603140493665771549585 110828702355370249328662189)
      ·
        refine ⟨41560763383263843498248321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110828702355370249328662189 41560763383263843498248321)
        ·
          refine ⟨31170572537447882623686241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41560763383263843498248321 31170572537447882623686241)
          ·
            refine ⟨23377929403085911967764681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31170572537447882623686241 23377929403085911967764681)
            ·
              refine ⟨17533447052314433975823511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23377929403085911967764681 17533447052314433975823511)
              ·
                refine ⟨26300170578471650963735267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17533447052314433975823511 26300170578471650963735267)
                ·
                  refine ⟨39450255867707476445602901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26300170578471650963735267 39450255867707476445602901)
                  ·
                    refine ⟨462307685949696989596909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39450255867707476445602901 462307685949696989596909)
                    ·
                      rfl

theorem cell23_2701023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 8].length) (baseStart_2701023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701023 prefixEnd_2701023 := by exact prefixLift 2701023
  have htrace : WordTrace (prefixWord ++ tailWord_2701023) baseStart_2701023 baseEnd_2701023 := by
    simpa [prefixWord, tailWord_2701023, baseEnd_2701023] using wordTrace_append hprefix tailTrace_2701023
  have hstable : (prefixWord ++ tailWord_2701023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701023).length < 2 ^ (prefixWord ++ tailWord_2701023).sum := by decide
  have hdescent : baseEnd_2701023 < baseStart_2701023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701024 : List Nat := [2, 1, 1, 3, 1, 2, 6, 1, 2, 1, 3]
def baseStart_2701024 : Nat := 118140960795 + 2701024 * 2 ^ 59
def prefixEnd_2701024 : Nat := 4983230072969 + 3 ^ 40 * 2701024 * 2
def baseEnd_2701024 : Nat := 1386923571329745464878223

theorem tailTrace_2701024 : CollatzResearch.WordTrace tailWord_2701024 prefixEnd_2701024 1386923571329745464878223 := by
  unfold tailWord_2701024
  simp only [CollatzResearch.WordTrace]
  refine ⟨49257219283329410509243063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65676292377772547345657417 49257219283329410509243063)
  ·
    refine ⟨73885828924994115763864595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49257219283329410509243063 73885828924994115763864595)
    ·
      refine ⟨110828743387491173645796893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73885828924994115763864595 110828743387491173645796893)
      ·
        refine ⟨41560778770309190117173835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110828743387491173645796893 41560778770309190117173835)
        ·
          refine ⟨62341168155463785175760753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41560778770309190117173835 62341168155463785175760753)
          ·
            refine ⟨46755876116597838881820565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62341168155463785175760753 46755876116597838881820565)
            ·
              refine ⟨2191681692965523697585339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46755876116597838881820565 2191681692965523697585339)
              ·
                refine ⟨3287522539448285546378009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2191681692965523697585339 3287522539448285546378009)
                ·
                  refine ⟨2465641904586214159783507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3287522539448285546378009 2465641904586214159783507)
                  ·
                    refine ⟨3698462856879321239675261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2465641904586214159783507 3698462856879321239675261)
                    ·
                      refine ⟨1386923571329745464878223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3698462856879321239675261 1386923571329745464878223)
                      ·
                        rfl

theorem cell23_2701024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_2701024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701024 prefixEnd_2701024 := by exact prefixLift 2701024
  have htrace : WordTrace (prefixWord ++ tailWord_2701024) baseStart_2701024 baseEnd_2701024 := by
    simpa [prefixWord, tailWord_2701024, baseEnd_2701024] using wordTrace_append hprefix tailTrace_2701024
  have hstable : (prefixWord ++ tailWord_2701024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701024).length < 2 ^ (prefixWord ++ tailWord_2701024).sum := by decide
  have hdescent : baseEnd_2701024 < baseStart_2701024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701034 : List Nat := [3, 1, 3, 1, 1, 1, 5, 2, 1, 3, 2]
def baseStart_2701034 : Nat := 118140960795 + 2701034 * 2 ^ 59
def prefixEnd_2701034 : Nat := 4983230072969 + 3 ^ 40 * 2701034 * 2
def baseEnd_2701034 : Nat := 1386928706136290425753177

theorem tailTrace_2701034 : CollatzResearch.WordTrace tailWord_2701034 prefixEnd_2701034 1386928706136290425753177 := by
  unfold tailWord_2701034
  simp only [CollatzResearch.WordTrace]
  refine ⟨24628700824155648181587539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65676535531081728484233437 24628700824155648181587539)
  ·
    refine ⟨36943051236233472272381309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24628700824155648181587539 36943051236233472272381309)
    ·
      refine ⟨13853644213587552102142991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36943051236233472272381309 13853644213587552102142991)
      ·
        refine ⟨20780466320381328153214487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13853644213587552102142991 20780466320381328153214487)
        ·
          refine ⟨31170699480571992229821731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20780466320381328153214487 31170699480571992229821731)
          ·
            refine ⟨46756049220857988344732597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31170699480571992229821731 46756049220857988344732597)
            ·
              refine ⟨4383379614455436407318681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46756049220857988344732597 4383379614455436407318681)
              ·
                refine ⟨3287534710841577305489011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4383379614455436407318681 3287534710841577305489011)
                ·
                  refine ⟨4931302066262365958233517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3287534710841577305489011 4931302066262365958233517)
                  ·
                    refine ⟨1849238274848387234337569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4931302066262365958233517 1849238274848387234337569)
                    ·
                      refine ⟨1386928706136290425753177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1849238274848387234337569 1386928706136290425753177)
                      ·
                        rfl

theorem cell23_2701034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_2701034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701034 prefixEnd_2701034 := by exact prefixLift 2701034
  have htrace : WordTrace (prefixWord ++ tailWord_2701034) baseStart_2701034 baseEnd_2701034 := by
    simpa [prefixWord, tailWord_2701034, baseEnd_2701034] using wordTrace_append hprefix tailTrace_2701034
  have hstable : (prefixWord ++ tailWord_2701034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701034).length < 2 ^ (prefixWord ++ tailWord_2701034).sum := by decide
  have hdescent : baseEnd_2701034 < baseStart_2701034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701047 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 6, 2, 2]
def baseStart_2701047 : Nat := 118140960795 + 2701047 * 2 ^ 59
def prefixEnd_2701047 : Nat := 4983230072969 + 3 ^ 40 * 2701047 * 2
def baseEnd_2701047 : Nat := 1386935381384798874890617

theorem tailTrace_2701047 : CollatzResearch.WordTrace tailWord_2701047 prefixEnd_2701047 1386935381384798874890617 := by
  unfold tailWord_2701047
  simp only [CollatzResearch.WordTrace]
  refine ⟨98515277445575495946573395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65676851630383663964382263 98515277445575495946573395)
  ·
    refine ⟨147772916168363243919860093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98515277445575495946573395 147772916168363243919860093)
    ·
      refine ⟨55414843563136216469947535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147772916168363243919860093 55414843563136216469947535)
      ·
        refine ⟨83122265344704324704921303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55414843563136216469947535 83122265344704324704921303)
        ·
          refine ⟨124683398017056487057381955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83122265344704324704921303 124683398017056487057381955)
          ·
            refine ⟨187025097025584730586072933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124683398017056487057381955 187025097025584730586072933)
            ·
              refine ⟨35067205692297136984888675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187025097025584730586072933 35067205692297136984888675)
              ·
                refine ⟨52600808538445705477333013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35067205692297136984888675 52600808538445705477333013)
                ·
                  refine ⟨2465662900239642444249985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52600808538445705477333013 2465662900239642444249985)
                  ·
                    refine ⟨1849247175179731833187489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2465662900239642444249985 1849247175179731833187489)
                    ·
                      refine ⟨1386935381384798874890617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1849247175179731833187489 1386935381384798874890617)
                      ·
                        rfl

theorem cell23_2701047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 2, 2].length) (baseStart_2701047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701047 prefixEnd_2701047 := by exact prefixLift 2701047
  have htrace : WordTrace (prefixWord ++ tailWord_2701047) baseStart_2701047 baseEnd_2701047 := by
    simpa [prefixWord, tailWord_2701047, baseEnd_2701047] using wordTrace_append hprefix tailTrace_2701047
  have hstable : (prefixWord ++ tailWord_2701047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701047).length < 2 ^ (prefixWord ++ tailWord_2701047).sum := by decide
  have hdescent : baseEnd_2701047 < baseStart_2701047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701053 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 11]
def baseStart_2701053 : Nat := 118140960795 + 2701053 * 2 ^ 59
def prefixEnd_2701053 : Nat := 4983230072969 + 3 ^ 40 * 2701053 * 2
def baseEnd_2701053 : Nat := 154104273585413983490621

theorem tailTrace_2701053 : CollatzResearch.WordTrace tailWord_2701053 prefixEnd_2701053 154104273585413983490621 := by
  unfold tailWord_2701053
  simp only [CollatzResearch.WordTrace]
  refine ⟨98515496283553758971291813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65676997522369172647527875 98515496283553758971291813)
  ·
    refine ⟨18471655553166329807117215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98515496283553758971291813 18471655553166329807117215)
    ·
      refine ⟨27707483329749494710675823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18471655553166329807117215 27707483329749494710675823)
      ·
        refine ⟨41561224994624242066013735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27707483329749494710675823 41561224994624242066013735)
        ·
          refine ⟨62341837491936363099020603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41561224994624242066013735 62341837491936363099020603)
          ·
            refine ⟨93512756237904544648530905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62341837491936363099020603 93512756237904544648530905)
            ·
              refine ⟨70134567178428408486398179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93512756237904544648530905 70134567178428408486398179)
              ·
                refine ⟨105201850767642612729597269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70134567178428408486398179 105201850767642612729597269)
                ·
                  refine ⟨154104273585413983490621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 105201850767642612729597269 154104273585413983490621)
                  ·
                    rfl

theorem cell23_2701053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_2701053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701053 prefixEnd_2701053 := by exact prefixLift 2701053
  have htrace : WordTrace (prefixWord ++ tailWord_2701053) baseStart_2701053 baseEnd_2701053 := by
    simpa [prefixWord, tailWord_2701053, baseEnd_2701053] using wordTrace_append hprefix tailTrace_2701053
  have hstable : (prefixWord ++ tailWord_2701053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701053).length < 2 ^ (prefixWord ++ tailWord_2701053).sum := by decide
  have hdescent : baseEnd_2701053 < baseStart_2701053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701073 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 8]
def baseStart_2701073 : Nat := 118140960795 + 2701073 * 2 ^ 59
def prefixEnd_2701073 : Nat := 4983230072969 + 3 ^ 40 * 2701073 * 2
def baseEnd_2701073 : Nat := 1386948731881815773165497

theorem tailTrace_2701073 : CollatzResearch.WordTrace tailWord_2701073 prefixEnd_2701073 1386948731881815773165497 := by
  unfold tailWord_2701073
  simp only [CollatzResearch.WordTrace]
  refine ⟨98516225743481302387019873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65677483828987534924679915 98516225743481302387019873)
  ·
    refine ⟨73887169307610976790264905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98516225743481302387019873 73887169307610976790264905)
    ·
      refine ⟨55415376980708232592698679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73887169307610976790264905 55415376980708232592698679)
      ·
        refine ⟨83123065471062348889048019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55415376980708232592698679 83123065471062348889048019)
        ·
          refine ⟨124684598206593523333572029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83123065471062348889048019 124684598206593523333572029)
          ·
            refine ⟨46756724327472571250089511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124684598206593523333572029 46756724327472571250089511)
            ·
              refine ⟨70135086491208856875134267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46756724327472571250089511 70135086491208856875134267)
              ·
                refine ⟨105202629736813285312701401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70135086491208856875134267 105202629736813285312701401)
                ·
                  refine ⟨78901972302609963984526051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105202629736813285312701401 78901972302609963984526051)
                  ·
                    refine ⟨118352958453914945976789077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78901972302609963984526051 118352958453914945976789077)
                    ·
                      refine ⟨1386948731881815773165497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 118352958453914945976789077 1386948731881815773165497)
                      ·
                        rfl

theorem cell23_2701073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_2701073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701073 prefixEnd_2701073 := by exact prefixLift 2701073
  have htrace : WordTrace (prefixWord ++ tailWord_2701073) baseStart_2701073 baseEnd_2701073 := by
    simpa [prefixWord, tailWord_2701073, baseEnd_2701073] using wordTrace_append hprefix tailTrace_2701073
  have hstable : (prefixWord ++ tailWord_2701073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701073).length < 2 ^ (prefixWord ++ tailWord_2701073).sum := by decide
  have hdescent : baseEnd_2701073 < baseStart_2701073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701080 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 1, 5, 3]
def baseStart_2701080 : Nat := 118140960795 + 2701080 * 2 ^ 59
def prefixEnd_2701080 : Nat := 4983230072969 + 3 ^ 40 * 2701080 * 2
def baseEnd_2701080 : Nat := 1386952326246397245777965

theorem tailTrace_2701080 : CollatzResearch.WordTrace tailWord_2701080 prefixEnd_2701080 1386952326246397245777965 := by
  unfold tailWord_2701080
  simp only [CollatzResearch.WordTrace]
  refine ⟨49258240527227971291262347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65677654036303961721683129 49258240527227971291262347)
  ·
    refine ⟨73887360790841956936893521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49258240527227971291262347 73887360790841956936893521)
    ·
      refine ⟨55415520593131467702670141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73887360790841956936893521 55415520593131467702670141)
      ·
        refine ⟨20780820222424300388501303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55415520593131467702670141 20780820222424300388501303)
        ·
          refine ⟨31171230333636450582751955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20780820222424300388501303 31171230333636450582751955)
          ·
            refine ⟨46756845500454675874127933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31171230333636450582751955 46756845500454675874127933)
            ·
              refine ⟨17533817062670503452797975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46756845500454675874127933 17533817062670503452797975)
              ·
                refine ⟨26300725594005755179196963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17533817062670503452797975 26300725594005755179196963)
                ·
                  refine ⟨39451088391008632768795445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26300725594005755179196963 39451088391008632768795445)
                  ·
                    refine ⟨3698539536657059322074573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39451088391008632768795445 3698539536657059322074573)
                    ·
                      refine ⟨1386952326246397245777965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3698539536657059322074573 1386952326246397245777965)
                      ·
                        rfl

theorem cell23_2701080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_2701080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701080 prefixEnd_2701080 := by exact prefixLift 2701080
  have htrace : WordTrace (prefixWord ++ tailWord_2701080) baseStart_2701080 baseEnd_2701080 := by
    simpa [prefixWord, tailWord_2701080, baseEnd_2701080] using wordTrace_append hprefix tailTrace_2701080
  have hstable : (prefixWord ++ tailWord_2701080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701080).length < 2 ^ (prefixWord ++ tailWord_2701080).sum := by decide
  have hdescent : baseEnd_2701080 < baseStart_2701080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701083 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 3, 7]
def baseStart_2701083 : Nat := 118140960795 + 2701083 * 2 ^ 59
def prefixEnd_2701083 : Nat := 4983230072969 + 3 ^ 40 * 2701083 * 2
def baseEnd_2701083 : Nat := 462317955562786911346817

theorem tailTrace_2701083 : CollatzResearch.WordTrace tailWord_2701083 prefixEnd_2701083 462317955562786911346817 := by
  unfold tailWord_2701083
  simp only [CollatzResearch.WordTrace]
  refine ⟨98516590473445074094883903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65677726982296716063255935 98516590473445074094883903)
  ·
    refine ⟨147774885710167611142325855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98516590473445074094883903 147774885710167611142325855)
    ·
      refine ⟨221662328565251416713488783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147774885710167611142325855 221662328565251416713488783)
      ·
        refine ⟨332493492847877125070233175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221662328565251416713488783 332493492847877125070233175)
        ·
          refine ⟨498740239271815687605349763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332493492847877125070233175 498740239271815687605349763)
          ·
            refine ⟨748110358907723531408024645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498740239271815687605349763 748110358907723531408024645)
            ·
              refine ⟨140270692295198162139004621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 748110358907723531408024645 140270692295198162139004621)
              ·
                refine ⟨52601509610699310802126733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140270692295198162139004621 52601509610699310802126733)
                ·
                  refine ⟨19725566104012241550797525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52601509610699310802126733 19725566104012241550797525)
                  ·
                    refine ⟨462317955562786911346817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19725566104012241550797525 462317955562786911346817)
                    ·
                      rfl

theorem cell23_2701083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 7].length) (baseStart_2701083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701083 prefixEnd_2701083 := by exact prefixLift 2701083
  have htrace : WordTrace (prefixWord ++ tailWord_2701083) baseStart_2701083 baseEnd_2701083 := by
    simpa [prefixWord, tailWord_2701083, baseEnd_2701083] using wordTrace_append hprefix tailTrace_2701083
  have hstable : (prefixWord ++ tailWord_2701083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701083).length < 2 ^ (prefixWord ++ tailWord_2701083).sum := by decide
  have hdescent : baseEnd_2701083 < baseStart_2701083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701100 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 1, 7]
def baseStart_2701100 : Nat := 118140960795 + 2701100 * 2 ^ 59
def prefixEnd_2701100 : Nat := 4983230072969 + 3 ^ 40 * 2701100 * 2
def baseEnd_2701100 : Nat := 462320865286495722509291

theorem tailTrace_2701100 : CollatzResearch.WordTrace tailWord_2701100 prefixEnd_2701100 462320865286495722509291 := by
  unfold tailWord_2701100
  simp only [CollatzResearch.WordTrace]
  refine ⟨49258605257191742999126377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65678140342922323998835169 49258605257191742999126377)
  ·
    refine ⟨36943953942893807249344783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49258605257191742999126377 36943953942893807249344783)
    ·
      refine ⟨55415930914340710874017175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36943953942893807249344783 55415930914340710874017175)
      ·
        refine ⟨83123896371511066311025763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55415930914340710874017175 83123896371511066311025763)
        ·
          refine ⟨124685844557266599466538645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83123896371511066311025763 124685844557266599466538645)
          ·
            refine ⟨5844648963621871849993999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 124685844557266599466538645 5844648963621871849993999)
            ·
              refine ⟨8766973445432807774990999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5844648963621871849993999 8766973445432807774990999)
              ·
                refine ⟨13150460168149211662486499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8766973445432807774990999 13150460168149211662486499)
                ·
                  refine ⟨19725690252223817493729749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13150460168149211662486499 19725690252223817493729749)
                  ·
                    refine ⟨462320865286495722509291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19725690252223817493729749 462320865286495722509291)
                    ·
                      rfl

theorem cell23_2701100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_2701100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701100 prefixEnd_2701100 := by exact prefixLift 2701100
  have htrace : WordTrace (prefixWord ++ tailWord_2701100) baseStart_2701100 baseEnd_2701100 := by
    simpa [prefixWord, tailWord_2701100, baseEnd_2701100] using wordTrace_append hprefix tailTrace_2701100
  have hstable : (prefixWord ++ tailWord_2701100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701100).length < 2 ^ (prefixWord ++ tailWord_2701100).sum := by decide
  have hdescent : baseEnd_2701100 < baseStart_2701100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701157 : List Nat := [1, 3, 1, 3, 1, 1, 1, 5, 2, 2, 3]
def baseStart_2701157 : Nat := 118140960795 + 2701157 * 2 ^ 59
def prefixEnd_2701157 : Nat := 4983230072969 + 3 ^ 40 * 2701157 * 2
def baseEnd_2701157 : Nat := 1386991864256793444515111

theorem tailTrace_2701157 : CollatzResearch.WordTrace tailWord_2701157 prefixEnd_2701157 1386991864256793444515111 := by
  unfold tailWord_2701157
  simp only [CollatzResearch.WordTrace]
  refine ⟨98519289475176984733077725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65679526316784656488718483 98519289475176984733077725)
  ·
    refine ⟨36944733553191369274904147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98519289475176984733077725 36944733553191369274904147)
    ·
      refine ⟨55417100329787053912356221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36944733553191369274904147 55417100329787053912356221)
      ·
        refine ⟨20781412623670145217133583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55417100329787053912356221 20781412623670145217133583)
        ·
          refine ⟨31172118935505217825700375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20781412623670145217133583 31172118935505217825700375)
          ·
            refine ⟨46758178403257826738550563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31172118935505217825700375 46758178403257826738550563)
            ·
              refine ⟨70137267604886740107825845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46758178403257826738550563 70137267604886740107825845)
              ·
                refine ⟨6575368837958131885108673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70137267604886740107825845 6575368837958131885108673)
                ·
                  refine ⟨4931526628468598913831505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6575368837958131885108673 4931526628468598913831505)
                  ·
                    refine ⟨3698644971351449185373629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4931526628468598913831505 3698644971351449185373629)
                    ·
                      refine ⟨1386991864256793444515111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3698644971351449185373629 1386991864256793444515111)
                      ·
                        rfl

theorem cell23_2701157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_2701157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701157 prefixEnd_2701157 := by exact prefixLift 2701157
  have htrace : WordTrace (prefixWord ++ tailWord_2701157) baseStart_2701157 baseEnd_2701157 := by
    simpa [prefixWord, tailWord_2701157, baseEnd_2701157] using wordTrace_append hprefix tailTrace_2701157
  have hstable : (prefixWord ++ tailWord_2701157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701157).length < 2 ^ (prefixWord ++ tailWord_2701157).sum := by decide
  have hdescent : baseEnd_2701157 < baseStart_2701157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701160 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 10]
def baseStart_2701160 : Nat := 118140960795 + 2701160 * 2 ^ 59
def prefixEnd_2701160 : Nat := 4983230072969 + 3 ^ 40 * 2701160 * 2
def baseEnd_2701160 : Nat := 154110378299861881419733

theorem tailTrace_2701160 : CollatzResearch.WordTrace tailWord_2701160 prefixEnd_2701160 154110378299861881419733 := by
  unfold tailWord_2701160
  simp only [CollatzResearch.WordTrace]
  refine ⟨49259699447083058122718467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65679599262777410830291289 49259699447083058122718467)
  ·
    refine ⟨73889549170624587184077701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49259699447083058122718467 73889549170624587184077701)
    ·
      refine ⟨13854290469492110097014569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73889549170624587184077701 13854290469492110097014569)
      ·
        refine ⟨10390717852119082572760927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13854290469492110097014569 10390717852119082572760927)
        ·
          refine ⟨15586076778178623859141391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10390717852119082572760927 15586076778178623859141391)
          ·
            refine ⟨23379115167267935788712087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15586076778178623859141391 23379115167267935788712087)
            ·
              refine ⟨35068672750901903683068131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23379115167267935788712087 35068672750901903683068131)
              ·
                refine ⟨52603009126352855524602197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35068672750901903683068131 52603009126352855524602197)
                ·
                  refine ⟨154110378299861881419733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 52603009126352855524602197 154110378299861881419733)
                  ·
                    rfl

theorem cell23_2701160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 10].length) (baseStart_2701160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701160 prefixEnd_2701160 := by exact prefixLift 2701160
  have htrace : WordTrace (prefixWord ++ tailWord_2701160) baseStart_2701160 baseEnd_2701160 := by
    simpa [prefixWord, tailWord_2701160, baseEnd_2701160] using wordTrace_append hprefix tailTrace_2701160
  have hstable : (prefixWord ++ tailWord_2701160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701160).length < 2 ^ (prefixWord ++ tailWord_2701160).sum := by decide
  have hdescent : baseEnd_2701160 < baseStart_2701160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701194 : List Nat := [3, 1, 2, 4, 2, 1, 1, 3, 6]
def baseStart_2701194 : Nat := 118140960795 + 2701194 * 2 ^ 59
def prefixEnd_2701194 : Nat := 4983230072969 + 3 ^ 40 * 2701194 * 2
def baseEnd_2701194 : Nat := 154112318115667755528049

theorem tailTrace_2701194 : CollatzResearch.WordTrace tailWord_2701194 prefixEnd_2701194 154112318115667755528049 := by
  unfold tailWord_2701194
  simp only [CollatzResearch.WordTrace]
  refine ⟨24630159744010735013043659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65680425984028626701449757 24630159744010735013043659)
  ·
    refine ⟨36945239616016102519565489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24630159744010735013043659 36945239616016102519565489)
    ·
      refine ⟨27708929712012076889674117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36945239616016102519565489 27708929712012076889674117)
      ·
        refine ⟨5195424321002264416813897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27708929712012076889674117 5195424321002264416813897)
        ·
          refine ⟨3896568240751698312610423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5195424321002264416813897 3896568240751698312610423)
          ·
            refine ⟨5844852361127547468915635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3896568240751698312610423 5844852361127547468915635)
            ·
              refine ⟨8767278541691321203373453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5844852361127547468915635 8767278541691321203373453)
              ·
                refine ⟨3287729453134245451265045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8767278541691321203373453 3287729453134245451265045)
                ·
                  refine ⟨154112318115667755528049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3287729453134245451265045 154112318115667755528049)
                  ·
                    rfl

theorem cell23_2701194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 6].length) (baseStart_2701194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701194 prefixEnd_2701194 := by exact prefixLift 2701194
  have htrace : WordTrace (prefixWord ++ tailWord_2701194) baseStart_2701194 baseEnd_2701194 := by
    simpa [prefixWord, tailWord_2701194, baseEnd_2701194] using wordTrace_append hprefix tailTrace_2701194
  have hstable : (prefixWord ++ tailWord_2701194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701194).length < 2 ^ (prefixWord ++ tailWord_2701194).sum := by decide
  have hdescent : baseEnd_2701194 < baseStart_2701194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701207 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 3, 5]
def baseStart_2701207 : Nat := 118140960795 + 2701207 * 2 ^ 59
def prefixEnd_2701207 : Nat := 4983230072969 + 3 ^ 40 * 2701207 * 2
def baseEnd_2701207 : Nat := 462339179429839416296627

theorem tailTrace_2701207 : CollatzResearch.WordTrace tailWord_2701207 prefixEnd_2701207 462339179429839416296627 := by
  unfold tailWord_2701207
  simp only [CollatzResearch.WordTrace]
  refine ⟨98521113124995843272397875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65680742083330562181598583 98521113124995843272397875)
  ·
    refine ⟨147781669687493764908596813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98521113124995843272397875 147781669687493764908596813)
    ·
      refine ⟨55418126132810161840723805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147781669687493764908596813 55418126132810161840723805)
      ·
        refine ⟨20781797299803810690271427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55418126132810161840723805 20781797299803810690271427)
        ·
          refine ⟨31172695949705716035407141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20781797299803810690271427 31172695949705716035407141)
          ·
            refine ⟨5844880490569821756638839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31172695949705716035407141 5844880490569821756638839)
            ·
              refine ⟨8767320735854732634958259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5844880490569821756638839 8767320735854732634958259)
              ·
                refine ⟨13150981103782098952437389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8767320735854732634958259 13150981103782098952437389)
                ·
                  refine ⟨4931617913918287107164021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13150981103782098952437389 4931617913918287107164021)
                  ·
                    refine ⟨462339179429839416296627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4931617913918287107164021 462339179429839416296627)
                    ·
                      rfl

theorem cell23_2701207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_2701207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701207 prefixEnd_2701207 := by exact prefixLift 2701207
  have htrace : WordTrace (prefixWord ++ tailWord_2701207) baseStart_2701207 baseEnd_2701207 := by
    simpa [prefixWord, tailWord_2701207, baseEnd_2701207] using wordTrace_append hprefix tailTrace_2701207
  have hstable : (prefixWord ++ tailWord_2701207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701207).length < 2 ^ (prefixWord ++ tailWord_2701207).sum := by decide
  have hdescent : baseEnd_2701207 < baseStart_2701207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701247 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 3]
def baseStart_2701247 : Nat := 118140960795 + 2701247 * 2 ^ 59
def prefixEnd_2701247 : Nat := 4983230072969 + 3 ^ 40 * 2701247 * 2
def baseEnd_2701247 : Nat := 1387038077515698092389697

theorem tailTrace_2701247 : CollatzResearch.WordTrace tailWord_2701247 prefixEnd_2701247 1387038077515698092389697 := by
  unfold tailWord_2701247
  simp only [CollatzResearch.WordTrace]
  refine ⟨98522572044850930103853995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65681714696567286735902663 98522572044850930103853995)
  ·
    refine ⟨147783858067276395155780993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98522572044850930103853995 147783858067276395155780993)
    ·
      refine ⟨110837893550457296366835745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147783858067276395155780993 110837893550457296366835745)
      ·
        refine ⟨83128420162842972275126809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110837893550457296366835745 83128420162842972275126809)
        ·
          refine ⟨62346315122132229206345107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83128420162842972275126809 62346315122132229206345107)
          ·
            refine ⟨93519472683198343809517661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62346315122132229206345107 93519472683198343809517661)
            ·
              refine ⟨35069802256199378928569123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93519472683198343809517661 35069802256199378928569123)
              ·
                refine ⟨52604703384299068392853685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35069802256199378928569123 52604703384299068392853685)
                ·
                  refine ⟨4931690942278037661830033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52604703384299068392853685 4931690942278037661830033)
                  ·
                    refine ⟨3698768206708528246372525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4931690942278037661830033 3698768206708528246372525)
                    ·
                      refine ⟨1387038077515698092389697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3698768206708528246372525 1387038077515698092389697)
                      ·
                        rfl

theorem cell23_2701247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_2701247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701247 prefixEnd_2701247 := by exact prefixLift 2701247
  have htrace : WordTrace (prefixWord ++ tailWord_2701247) baseStart_2701247 baseEnd_2701247 := by
    simpa [prefixWord, tailWord_2701247, baseEnd_2701247] using wordTrace_append hprefix tailTrace_2701247
  have hstable : (prefixWord ++ tailWord_2701247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701247).length < 2 ^ (prefixWord ++ tailWord_2701247).sum := by decide
  have hdescent : baseEnd_2701247 < baseStart_2701247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701281 : List Nat := [1, 2, 3, 1, 2, 1, 6, 1, 1, 2, 3]
def baseStart_2701281 : Nat := 118140960795 + 2701281 * 2 ^ 59
def prefixEnd_2701281 : Nat := 4983230072969 + 3 ^ 40 * 2701281 * 2
def baseEnd_2701281 : Nat := 1387055535857950959364541

theorem tailTrace_2701281 : CollatzResearch.WordTrace tailWord_2701281 prefixEnd_2701281 1387055535857950959364541 := by
  unfold tailWord_2701281
  simp only [CollatzResearch.WordTrace]
  refine ⟨98523812126727753910591697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65682541417818502607061131 98523812126727753910591697)
  ·
    refine ⟨73892859095045815432943773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98523812126727753910591697 73892859095045815432943773)
    ·
      refine ⟨27709822160642180787353915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73892859095045815432943773 27709822160642180787353915)
      ·
        refine ⟨41564733240963271181030873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27709822160642180787353915 41564733240963271181030873)
        ·
          refine ⟨31173549930722453385773155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41564733240963271181030873 31173549930722453385773155)
          ·
            refine ⟨46760324896083680078659733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31173549930722453385773155 46760324896083680078659733)
            ·
              refine ⟨2191890229503922503687175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46760324896083680078659733 2191890229503922503687175)
              ·
                refine ⟨3287835344255883755530763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2191890229503922503687175 3287835344255883755530763)
                ·
                  refine ⟨4931753016383825633296145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3287835344255883755530763 4931753016383825633296145)
                  ·
                    refine ⟨3698814762287869224972109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4931753016383825633296145 3698814762287869224972109)
                    ·
                      refine ⟨1387055535857950959364541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3698814762287869224972109 1387055535857950959364541)
                      ·
                        rfl

theorem cell23_2701281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_2701281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701281 prefixEnd_2701281 := by exact prefixLift 2701281
  have htrace : WordTrace (prefixWord ++ tailWord_2701281) baseStart_2701281 baseEnd_2701281 := by
    simpa [prefixWord, tailWord_2701281, baseEnd_2701281] using wordTrace_append hprefix tailTrace_2701281
  have hstable : (prefixWord ++ tailWord_2701281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701281).length < 2 ^ (prefixWord ++ tailWord_2701281).sum := by decide
  have hdescent : baseEnd_2701281 < baseStart_2701281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701304 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 5, 3, 2]
def baseStart_2701304 : Nat := 118140960795 + 2701304 * 2 ^ 59
def prefixEnd_2701304 : Nat := 4983230072969 + 3 ^ 40 * 2701304 * 2
def baseEnd_2701304 : Nat := 1387067345913004369376935

theorem tailTrace_2701304 : CollatzResearch.WordTrace tailWord_2701304 prefixEnd_2701304 1387067345913004369376935 := by
  unfold tailWord_2701304
  simp only [CollatzResearch.WordTrace]
  refine ⟨49262325502822214419339483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65683100670429619225785977 49262325502822214419339483)
  ·
    refine ⟨73893488254233321629009225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49262325502822214419339483 73893488254233321629009225)
    ·
      refine ⟨55420116190674991221756919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73893488254233321629009225 55420116190674991221756919)
      ·
        refine ⟨83130174286012486832635379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55420116190674991221756919 83130174286012486832635379)
        ·
          refine ⟨124695261429018730248953069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83130174286012486832635379 124695261429018730248953069)
          ·
            refine ⟨46760723035882023843357401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124695261429018730248953069 46760723035882023843357401)
            ·
              refine ⟨35070542276911517882518051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46760723035882023843357401 35070542276911517882518051)
              ·
                refine ⟨52605813415367276823777077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35070542276911517882518051 52605813415367276823777077)
                ·
                  refine ⟨4931795007690682202229101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52605813415367276823777077 4931795007690682202229101)
                  ·
                    refine ⟨1849423127884005825835913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4931795007690682202229101 1849423127884005825835913)
                    ·
                      refine ⟨1387067345913004369376935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1849423127884005825835913 1387067345913004369376935)
                      ·
                        rfl

theorem cell23_2701304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 5, 3, 2].length) (baseStart_2701304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701304 prefixEnd_2701304 := by exact prefixLift 2701304
  have htrace : WordTrace (prefixWord ++ tailWord_2701304) baseStart_2701304 baseEnd_2701304 := by
    simpa [prefixWord, tailWord_2701304, baseEnd_2701304] using wordTrace_append hprefix tailTrace_2701304
  have hstable : (prefixWord ++ tailWord_2701304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701304).length < 2 ^ (prefixWord ++ tailWord_2701304).sum := by decide
  have hdescent : baseEnd_2701304 < baseStart_2701304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701337 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 1, 6, 3]
def baseStart_2701337 : Nat := 118140960795 + 2701337 * 2 ^ 59
def prefixEnd_2701337 : Nat := 4983230072969 + 3 ^ 40 * 2701337 * 2
def baseEnd_2701337 : Nat := 1387084290774602740264283

theorem tailTrace_2701337 : CollatzResearch.WordTrace tailWord_2701337 prefixEnd_2701337 1387084290774602740264283 := by
  unfold tailWord_2701337
  simp only [CollatzResearch.WordTrace]
  refine ⟨98525854614524875474630265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65683903076349916983086843 98525854614524875474630265)
  ·
    refine ⟨73894390960893656605972699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98525854614524875474630265 73894390960893656605972699)
    ·
      refine ⟨110841586441340484908959049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73894390960893656605972699 110841586441340484908959049)
      ·
        refine ⟨83131189831005363681719287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110841586441340484908959049 83131189831005363681719287)
        ·
          refine ⟨124696784746508045522578931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83131189831005363681719287 124696784746508045522578931)
          ·
            refine ⟨187045177119762068283868397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124696784746508045522578931 187045177119762068283868397)
            ·
              refine ⟨70141941419910775606450649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187045177119762068283868397 70141941419910775606450649)
              ·
                refine ⟨52606456064933081704837987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70141941419910775606450649 52606456064933081704837987)
                ·
                  refine ⟨78909684097399622557256981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52606456064933081704837987 78909684097399622557256981)
                  ·
                    refine ⟨3698891442065607307371421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78909684097399622557256981 3698891442065607307371421)
                    ·
                      refine ⟨1387084290774602740264283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3698891442065607307371421 1387084290774602740264283)
                      ·
                        rfl

theorem cell23_2701337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_2701337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701337 prefixEnd_2701337 := by exact prefixLift 2701337
  have htrace : WordTrace (prefixWord ++ tailWord_2701337) baseStart_2701337 baseEnd_2701337 := by
    simpa [prefixWord, tailWord_2701337, baseEnd_2701337] using wordTrace_append hprefix tailTrace_2701337
  have hstable : (prefixWord ++ tailWord_2701337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701337).length < 2 ^ (prefixWord ++ tailWord_2701337).sum := by decide
  have hdescent : baseEnd_2701337 < baseStart_2701337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701387 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 6, 5]
def baseStart_2701387 : Nat := 118140960795 + 2701387 * 2 ^ 59
def prefixEnd_2701387 : Nat := 4983230072969 + 3 ^ 40 * 2701387 * 2
def baseEnd_2701387 : Nat := 462369988269109181546351

theorem tailTrace_2701387 : CollatzResearch.WordTrace tailWord_2701387 prefixEnd_2701387 462369988269109181546351 := by
  unfold tailWord_2701387
  simp only [CollatzResearch.WordTrace]
  refine ⟨98527678264343734013950415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65685118842895822675966943 98527678264343734013950415)
  ·
    refine ⟨147791517396515601020925623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98527678264343734013950415 147791517396515601020925623)
    ·
      refine ⟨221687276094773401531388435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147791517396515601020925623 221687276094773401531388435)
      ·
        refine ⟨332530914142160102297082653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221687276094773401531388435 332530914142160102297082653)
        ·
          refine ⟨124699092803310038361405995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332530914142160102297082653 124699092803310038361405995)
          ·
            refine ⟨187048639204965057542108993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124699092803310038361405995 187048639204965057542108993)
            ·
              refine ⟨140286479403723793156581745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187048639204965057542108993 140286479403723793156581745)
              ·
                refine ⟨105214859552792844867436309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140286479403723793156581745 105214859552792844867436309)
                ·
                  refine ⟨4931946541537164603161077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105214859552792844867436309 4931946541537164603161077)
                  ·
                    refine ⟨462369988269109181546351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4931946541537164603161077 462369988269109181546351)
                    ·
                      rfl

theorem cell23_2701387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 5].length) (baseStart_2701387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701387 prefixEnd_2701387 := by exact prefixLift 2701387
  have htrace : WordTrace (prefixWord ++ tailWord_2701387) baseStart_2701387 baseEnd_2701387 := by
    simpa [prefixWord, tailWord_2701387, baseEnd_2701387] using wordTrace_append hprefix tailTrace_2701387
  have hstable : (prefixWord ++ tailWord_2701387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701387).length < 2 ^ (prefixWord ++ tailWord_2701387).sum := by decide
  have hdescent : baseEnd_2701387 < baseStart_2701387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701408 : List Nat := [2, 1, 1, 3, 2, 5, 2, 2, 5]
def baseStart_2701408 : Nat := 118140960795 + 2701408 * 2 ^ 59
def prefixEnd_2701408 : Nat := 4983230072969 + 3 ^ 40 * 2701408 * 2
def baseEnd_2701408 : Nat := 154124527544563551386273

theorem tailTrace_2701408 : CollatzResearch.WordTrace tailWord_2701408 prefixEnd_2701408 154124527544563551386273 := by
  unfold tailWord_2701408
  simp only [CollatzResearch.WordTrace]
  refine ⟨49264222098633827300232439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65685629464845103066976585 49264222098633827300232439)
  ·
    refine ⟨73896333147950740950348659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49264222098633827300232439 73896333147950740950348659)
    ·
      refine ⟨110844499721926111425522989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73896333147950740950348659 110844499721926111425522989)
      ·
        refine ⟨41566687395722291784571121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110844499721926111425522989 41566687395722291784571121)
        ·
          refine ⟨31175015546791718838428341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41566687395722291784571121 31175015546791718838428341)
          ·
            refine ⟨2922657707511723641102657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31175015546791718838428341 2922657707511723641102657)
            ·
              refine ⟨2191993280633792730826993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2922657707511723641102657 2191993280633792730826993)
              ·
                refine ⟨1643994960475344548120245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2191993280633792730826993 1643994960475344548120245)
                ·
                  refine ⟨154124527544563551386273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1643994960475344548120245 154124527544563551386273)
                  ·
                    rfl

theorem cell23_2701408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 5].length) (baseStart_2701408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701408 prefixEnd_2701408 := by exact prefixLift 2701408
  have htrace : WordTrace (prefixWord ++ tailWord_2701408) baseStart_2701408 baseEnd_2701408 := by
    simpa [prefixWord, tailWord_2701408, baseEnd_2701408] using wordTrace_append hprefix tailTrace_2701408
  have hstable : (prefixWord ++ tailWord_2701408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701408).length < 2 ^ (prefixWord ++ tailWord_2701408).sum := by decide
  have hdescent : baseEnd_2701408 < baseStart_2701408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701441 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_2701441 : Nat := 118140960795 + 2701441 * 2 ^ 59
def prefixEnd_2701441 : Nat := 4983230072969 + 3 ^ 40 * 2701441 * 2
def baseEnd_2701441 : Nat := 1387137692762670333363805

theorem tailTrace_2701441 : CollatzResearch.WordTrace tailWord_2701441 prefixEnd_2701441 1387137692762670333363805 := by
  unfold tailWord_2701441
  simp only [CollatzResearch.WordTrace]
  refine ⟨98529647806148101236416177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65686431870765400824277451 98529647806148101236416177)
  ·
    refine ⟨73897235854611075927312133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98529647806148101236416177 73897235854611075927312133)
    ·
      refine ⟨13855731722739576736371025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73897235854611075927312133 13855731722739576736371025)
      ·
        refine ⟨10391798792054682552278269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13855731722739576736371025 10391798792054682552278269)
        ·
          refine ⟨3896924547020505957104351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10391798792054682552278269 3896924547020505957104351)
          ·
            refine ⟨5845386820530758935656527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3896924547020505957104351 5845386820530758935656527)
            ·
              refine ⟨8768080230796138403484791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5845386820530758935656527 8768080230796138403484791)
              ·
                refine ⟨13152120346194207605227187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8768080230796138403484791 13152120346194207605227187)
                ·
                  refine ⟨19728180519291311407840781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13152120346194207605227187 19728180519291311407840781)
                  ·
                    refine ⟨7398067694734241777940293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19728180519291311407840781 7398067694734241777940293)
                    ·
                      refine ⟨1387137692762670333363805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7398067694734241777940293 1387137692762670333363805)
                      ·
                        rfl

theorem cell23_2701441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_2701441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701441 prefixEnd_2701441 := by exact prefixLift 2701441
  have htrace : WordTrace (prefixWord ++ tailWord_2701441) baseStart_2701441 baseEnd_2701441 := by
    simpa [prefixWord, tailWord_2701441, baseEnd_2701441] using wordTrace_append hprefix tailTrace_2701441
  have hstable : (prefixWord ++ tailWord_2701441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701441).length < 2 ^ (prefixWord ++ tailWord_2701441).sum := by decide
  have hdescent : baseEnd_2701441 < baseStart_2701441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701457 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 7]
def baseStart_2701457 : Nat := 118140960795 + 2701457 * 2 ^ 59
def prefixEnd_2701457 : Nat := 4983230072969 + 3 ^ 40 * 2701457 * 2
def baseEnd_2701457 : Nat := 1387145908453142270763731

theorem tailTrace_2701457 : CollatzResearch.WordTrace tailWord_2701457 prefixEnd_2701457 1387145908453142270763731 := by
  unfold tailWord_2701457
  simp only [CollatzResearch.WordTrace]
  refine ⟨98530231374090135968998625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65686820916060090645999083 98530231374090135968998625)
  ·
    refine ⟨73897673530567601976748969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98530231374090135968998625 73897673530567601976748969)
    ·
      refine ⟨55423255147925701482561727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73897673530567601976748969 55423255147925701482561727)
      ·
        refine ⟨83134882721888552223842591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55423255147925701482561727 83134882721888552223842591)
        ·
          refine ⟨124702324082832828335763887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83134882721888552223842591 124702324082832828335763887)
          ·
            refine ⟨187053486124249242503645831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124702324082832828335763887 187053486124249242503645831)
            ·
              refine ⟨280580229186373863755468747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187053486124249242503645831 280580229186373863755468747)
              ·
                refine ⟨420870343779560795633203121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280580229186373863755468747 420870343779560795633203121)
                ·
                  refine ⟨315652757834670596724902341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 420870343779560795633203121 315652757834670596724902341)
                  ·
                    refine ⟨59184892094000736885919189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 315652757834670596724902341 59184892094000736885919189)
                    ·
                      refine ⟨1387145908453142270763731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59184892094000736885919189 1387145908453142270763731)
                      ·
                        rfl

theorem cell23_2701457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_2701457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701457 prefixEnd_2701457 := by exact prefixLift 2701457
  have htrace : WordTrace (prefixWord ++ tailWord_2701457) baseStart_2701457 baseEnd_2701457 := by
    simpa [prefixWord, tailWord_2701457, baseEnd_2701457] using wordTrace_append hprefix tailTrace_2701457
  have hstable : (prefixWord ++ tailWord_2701457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701457).length < 2 ^ (prefixWord ++ tailWord_2701457).sum := by decide
  have hdescent : baseEnd_2701457 < baseStart_2701457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701467 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 8]
def baseStart_2701467 : Nat := 118140960795 + 2701467 * 2 ^ 59
def prefixEnd_2701467 : Nat := 4983230072969 + 3 ^ 40 * 2701467 * 2
def baseEnd_2701467 : Nat := 1387151043259687231638685

theorem tailTrace_2701467 : CollatzResearch.WordTrace tailWord_2701467 prefixEnd_2701467 1387151043259687231638685 := by
  unfold tailWord_2701467
  simp only [CollatzResearch.WordTrace]
  refine ⟨98530596104053907676862655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65687064069369271784575103 98530596104053907676862655)
  ·
    refine ⟨147795894156080861515293983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98530596104053907676862655 147795894156080861515293983)
    ·
      refine ⟨221693841234121292272940975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147795894156080861515293983 221693841234121292272940975)
      ·
        refine ⟨332540761851181938409411463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221693841234121292272940975 332540761851181938409411463)
        ·
          refine ⟨498811142776772907614117195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332540761851181938409411463 498811142776772907614117195)
          ·
            refine ⟨748216714165159361421175793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498811142776772907614117195 748216714165159361421175793)
            ·
              refine ⟨561162535623869521065881845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 748216714165159361421175793 561162535623869521065881845)
              ·
                refine ⟨52608987714737767599926423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 561162535623869521065881845 52608987714737767599926423)
                ·
                  refine ⟨78913481572106651399889635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52608987714737767599926423 78913481572106651399889635)
                  ·
                    refine ⟨118370222358159977099834453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78913481572106651399889635 118370222358159977099834453)
                    ·
                      refine ⟨1387151043259687231638685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 118370222358159977099834453 1387151043259687231638685)
                      ·
                        rfl

theorem cell23_2701467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 8].length) (baseStart_2701467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701467 prefixEnd_2701467 := by exact prefixLift 2701467
  have htrace : WordTrace (prefixWord ++ tailWord_2701467) baseStart_2701467 baseEnd_2701467 := by
    simpa [prefixWord, tailWord_2701467, baseEnd_2701467] using wordTrace_append hprefix tailTrace_2701467
  have hstable : (prefixWord ++ tailWord_2701467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701467).length < 2 ^ (prefixWord ++ tailWord_2701467).sum := by decide
  have hdescent : baseEnd_2701467 < baseStart_2701467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701468 : List Nat := [2, 2, 3, 2, 1, 1, 1, 6, 1, 4]
def baseStart_2701468 : Nat := 118140960795 + 2701468 * 2 ^ 59
def prefixEnd_2701468 : Nat := 4983230072969 + 3 ^ 40 * 2701468 * 2
def baseEnd_2701468 : Nat := 462383852246780575908727

theorem tailTrace_2701468 : CollatzResearch.WordTrace tailWord_2701468 prefixEnd_2701468 462383852246780575908727 := by
  unfold tailWord_2701468
  simp only [CollatzResearch.WordTrace]
  refine ⟨49265316288525142423824529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65687088384700189898432705 49265316288525142423824529)
  ·
    refine ⟨36948987216393856817868397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49265316288525142423824529 36948987216393856817868397)
    ·
      refine ⟨13855870206147696306700649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36948987216393856817868397 13855870206147696306700649)
      ·
        refine ⟨10391902654610772230025487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13855870206147696306700649 10391902654610772230025487)
        ·
          refine ⟨15587853981916158345038231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10391902654610772230025487 15587853981916158345038231)
          ·
            refine ⟨23381780972874237517557347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15587853981916158345038231 23381780972874237517557347)
            ·
              refine ⟨35072671459311356276336021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23381780972874237517557347 35072671459311356276336021)
              ·
                refine ⟨1644031474655219825453251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35072671459311356276336021 1644031474655219825453251)
                ·
                  refine ⟨2466047211982829738179877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644031474655219825453251 2466047211982829738179877)
                  ·
                    refine ⟨462383852246780575908727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2466047211982829738179877 462383852246780575908727)
                    ·
                      rfl

theorem cell23_2701468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_2701468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701468 prefixEnd_2701468 := by exact prefixLift 2701468
  have htrace : WordTrace (prefixWord ++ tailWord_2701468) baseStart_2701468 baseEnd_2701468 := by
    simpa [prefixWord, tailWord_2701468, baseEnd_2701468] using wordTrace_append hprefix tailTrace_2701468
  have hstable : (prefixWord ++ tailWord_2701468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701468).length < 2 ^ (prefixWord ++ tailWord_2701468).sum := by decide
  have hdescent : baseEnd_2701468 < baseStart_2701468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701502 : List Nat := [4, 2, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_2701502 : Nat := 118140960795 + 2701502 * 2 ^ 59
def prefixEnd_2701502 : Nat := 4983230072969 + 3 ^ 40 * 2701502 * 2
def baseEnd_2701502 : Nat := 462389671694198198233675

theorem tailTrace_2701502 : CollatzResearch.WordTrace tailWord_2701502 prefixEnd_2701502 462389671694198198233675 := by
  unfold tailWord_2701502
  simp only [CollatzResearch.WordTrace]
  refine ⟨12316484082365888581798345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65687915105951405769591173 12316484082365888581798345)
  ·
    refine ⟨9237363061774416436348759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12316484082365888581798345 9237363061774416436348759)
    ·
      refine ⟨13856044592661624654523139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9237363061774416436348759 13856044592661624654523139)
      ·
        refine ⟨20784066888992436981784709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13856044592661624654523139 20784066888992436981784709)
        ·
          refine ⟨3897012541686081934084633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20784066888992436981784709 3897012541686081934084633)
          ·
            refine ⟨2922759406264561450563475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3897012541686081934084633 2922759406264561450563475)
            ·
              refine ⟨4384139109396842175845213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2922759406264561450563475 4384139109396842175845213)
              ·
                refine ⟨1644052166023815815941955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4384139109396842175845213 1644052166023815815941955)
                ·
                  refine ⟨2466078249035723723912933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644052166023815815941955 2466078249035723723912933)
                  ·
                    refine ⟨462389671694198198233675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2466078249035723723912933 462389671694198198233675)
                    ·
                      rfl

theorem cell23_2701502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_2701502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701502 prefixEnd_2701502 := by exact prefixLift 2701502
  have htrace : WordTrace (prefixWord ++ tailWord_2701502) baseStart_2701502 baseEnd_2701502 := by
    simpa [prefixWord, tailWord_2701502, baseEnd_2701502] using wordTrace_append hprefix tailTrace_2701502
  have hstable : (prefixWord ++ tailWord_2701502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701502).length < 2 ^ (prefixWord ++ tailWord_2701502).sum := by decide
  have hdescent : baseEnd_2701502 < baseStart_2701502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701518 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2]
def baseStart_2701518 : Nat := 118140960795 + 2701518 * 2 ^ 59
def prefixEnd_2701518 : Nat := 4983230072969 + 3 ^ 40 * 2701518 * 2
def baseEnd_2701518 : Nat := 1387177230773066532100951

theorem tailTrace_2701518 : CollatzResearch.WordTrace tailWord_2701518 prefixEnd_2701518 1387177230773066532100951 := by
  unfold tailWord_2701518
  simp only [CollatzResearch.WordTrace]
  refine ⟨12316557028358642923371151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65688304151246095591312805 12316557028358642923371151)
  ·
    refine ⟨18474835542537964385056727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12316557028358642923371151 18474835542537964385056727)
    ·
      refine ⟨27712253313806946577585091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18474835542537964385056727 27712253313806946577585091)
      ·
        refine ⟨41568379970710419866377637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27712253313806946577585091 41568379970710419866377637)
        ·
          refine ⟨7794071244508203724945807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41568379970710419866377637 7794071244508203724945807)
          ·
            refine ⟨11691106866762305587418711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7794071244508203724945807 11691106866762305587418711)
            ·
              refine ⟨17536660300143458381128067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11691106866762305587418711 17536660300143458381128067)
              ·
                refine ⟨26304990450215187571692101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17536660300143458381128067 26304990450215187571692101)
                ·
                  refine ⟨4932185709415347669692269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26304990450215187571692101 4932185709415347669692269)
                  ·
                    refine ⟨1849569641030755376134601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4932185709415347669692269 1849569641030755376134601)
                    ·
                      refine ⟨1387177230773066532100951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1849569641030755376134601 1387177230773066532100951)
                      ·
                        rfl

theorem cell23_2701518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_2701518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701518 prefixEnd_2701518 := by exact prefixLift 2701518
  have htrace : WordTrace (prefixWord ++ tailWord_2701518) baseStart_2701518 baseEnd_2701518 := by
    simpa [prefixWord, tailWord_2701518, baseEnd_2701518] using wordTrace_append hprefix tailTrace_2701518
  have hstable : (prefixWord ++ tailWord_2701518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701518).length < 2 ^ (prefixWord ++ tailWord_2701518).sum := by decide
  have hdescent : baseEnd_2701518 < baseStart_2701518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701532 : List Nat := [2, 2, 5, 2, 1, 2, 2, 1, 6]
def baseStart_2701532 : Nat := 118140960795 + 2701532 * 2 ^ 59
def prefixEnd_2701532 : Nat := 4983230072969 + 3 ^ 40 * 2701532 * 2
def baseEnd_2701532 : Nat := 154131602166914386369543

theorem tailTrace_2701532 : CollatzResearch.WordTrace tailWord_2701532 prefixEnd_2701532 154131602166914386369543 := by
  unfold tailWord_2701532
  simp only [CollatzResearch.WordTrace]
  refine ⟨49266483424409211888989425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65688644565878949185319233 49266483424409211888989425)
  ·
    refine ⟨36949862568306908916742069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49266483424409211888989425 36949862568306908916742069)
    ·
      refine ⟨3464049615778772710944569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36949862568306908916742069 3464049615778772710944569)
      ·
        refine ⟨2598037211834079533208427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3464049615778772710944569 2598037211834079533208427)
        ·
          refine ⟨3897055817751119299812641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2598037211834079533208427 3897055817751119299812641)
          ·
            refine ⟨2922791863313339474859481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3897055817751119299812641 2922791863313339474859481)
            ·
              refine ⟨2192093897485004606144611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2922791863313339474859481 2192093897485004606144611)
              ·
                refine ⟨3288140846227506909216917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2192093897485004606144611 3288140846227506909216917)
                ·
                  refine ⟨154131602166914386369543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3288140846227506909216917 154131602166914386369543)
                  ·
                    rfl

theorem cell23_2701532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 6].length) (baseStart_2701532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701532 prefixEnd_2701532 := by exact prefixLift 2701532
  have htrace : WordTrace (prefixWord ++ tailWord_2701532) baseStart_2701532 baseEnd_2701532 := by
    simpa [prefixWord, tailWord_2701532, baseEnd_2701532] using wordTrace_append hprefix tailTrace_2701532
  have hstable : (prefixWord ++ tailWord_2701532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701532).length < 2 ^ (prefixWord ++ tailWord_2701532).sum := by decide
  have hdescent : baseEnd_2701532 < baseStart_2701532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701548 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 5, 2, 2]
def baseStart_2701548 : Nat := 118140960795 + 2701548 * 2 ^ 59
def prefixEnd_2701548 : Nat := 4983230072969 + 3 ^ 40 * 2701548 * 2
def baseEnd_2701548 : Nat := 1387192635192701414725813

theorem tailTrace_2701548 : CollatzResearch.WordTrace tailWord_2701548 prefixEnd_2701548 1387192635192701414725813 := by
  unfold tailWord_2701548
  simp only [CollatzResearch.WordTrace]
  refine ⟨49266775208380229255280649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65689033611173639007040865 49266775208380229255280649)
  ·
    refine ⟨36950081406285171941460487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49266775208380229255280649 36950081406285171941460487)
    ·
      refine ⟨55425122109427757912190731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36950081406285171941460487 55425122109427757912190731)
      ·
        refine ⟨83137683164141636868286097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55425122109427757912190731 83137683164141636868286097)
        ·
          refine ⟨62353262373106227651214573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83137683164141636868286097 62353262373106227651214573)
          ·
            refine ⟨23382473389914835369205465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62353262373106227651214573 23382473389914835369205465)
            ·
              refine ⟨17536855042436126526904099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23382473389914835369205465 17536855042436126526904099)
              ·
                refine ⟨26305282563654189790356149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17536855042436126526904099 26305282563654189790356149)
                ·
                  refine ⟨2466120240342580292845889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26305282563654189790356149 2466120240342580292845889)
                  ·
                    refine ⟨1849590180256935219634417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2466120240342580292845889 1849590180256935219634417)
                    ·
                      refine ⟨1387192635192701414725813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1849590180256935219634417 1387192635192701414725813)
                      ·
                        rfl

theorem cell23_2701548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 2, 2].length) (baseStart_2701548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701548 prefixEnd_2701548 := by exact prefixLift 2701548
  have htrace : WordTrace (prefixWord ++ tailWord_2701548) baseStart_2701548 baseEnd_2701548 := by
    simpa [prefixWord, tailWord_2701548, baseEnd_2701548] using wordTrace_append hprefix tailTrace_2701548
  have hstable : (prefixWord ++ tailWord_2701548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701548).length < 2 ^ (prefixWord ++ tailWord_2701548).sum := by decide
  have hdescent : baseEnd_2701548 < baseStart_2701548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701582 : List Nat := [4, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2]
def baseStart_2701582 : Nat := 118140960795 + 2701582 * 2 ^ 59
def prefixEnd_2701582 : Nat := 4983230072969 + 3 ^ 40 * 2701582 * 2
def baseEnd_2701582 : Nat := 1387210093534954281700657

theorem tailTrace_2701582 : CollatzResearch.WordTrace tailWord_2701582 prefixEnd_2701582 1387210093534954281700657 := by
  unfold tailWord_2701582
  simp only [CollatzResearch.WordTrace]
  refine ⟨12316848812329660289662375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65689860332424854878199333 12316848812329660289662375)
  ·
    refine ⟨18475273218494490434493563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12316848812329660289662375 18475273218494490434493563)
    ·
      refine ⟨27712909827741735651740345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18475273218494490434493563 27712909827741735651740345)
      ·
        refine ⟨20784682370806301738805259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27712909827741735651740345 20784682370806301738805259)
        ·
          refine ⟨31177023556209452608207889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20784682370806301738805259 31177023556209452608207889)
          ·
            refine ⟨23382767667157089456155917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31177023556209452608207889 23382767667157089456155917)
            ·
              refine ⟨8768537875183908546058469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23382767667157089456155917 8768537875183908546058469)
              ·
                refine ⟨1644100851596982852385963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8768537875183908546058469 1644100851596982852385963)
                ·
                  refine ⟨2466151277395474278578945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644100851596982852385963 2466151277395474278578945)
                  ·
                    refine ⟨1849613458046605708934209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2466151277395474278578945 1849613458046605708934209)
                    ·
                      refine ⟨1387210093534954281700657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1849613458046605708934209 1387210093534954281700657)
                      ·
                        rfl

theorem cell23_2701582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_2701582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701582 prefixEnd_2701582 := by exact prefixLift 2701582
  have htrace : WordTrace (prefixWord ++ tailWord_2701582) baseStart_2701582 baseEnd_2701582 := by
    simpa [prefixWord, tailWord_2701582, baseEnd_2701582] using wordTrace_append hprefix tailTrace_2701582
  have hstable : (prefixWord ++ tailWord_2701582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701582).length < 2 ^ (prefixWord ++ tailWord_2701582).sum := by decide
  have hdescent : baseEnd_2701582 < baseStart_2701582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701691 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 4, 5]
def baseStart_2701691 : Nat := 118140960795 + 2701691 * 2 ^ 59
def prefixEnd_2701691 : Nat := 4983230072969 + 3 ^ 40 * 2701691 * 2
def baseEnd_2701691 : Nat := 462422020975431451745885

theorem tailTrace_2701691 : CollatzResearch.WordTrace tailWord_2701691 prefixEnd_2701691 462422020975431451745885 := by
  unfold tailWord_2701691
  simp only [CollatzResearch.WordTrace]
  refine ⟨98538766055242393933016927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65692510703494929288677951 98538766055242393933016927)
  ·
    refine ⟨147808149082863590899525391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98538766055242393933016927 147808149082863590899525391)
    ·
      refine ⟨221712223624295386349288087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147808149082863590899525391 221712223624295386349288087)
      ·
        refine ⟨332568335436443079523932131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221712223624295386349288087 332568335436443079523932131)
        ·
          refine ⟨498852503154664619285898197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332568335436443079523932131 498852503154664619285898197)
          ·
            refine ⟨11691855542687452014513239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 498852503154664619285898197 11691855542687452014513239)
            ·
              refine ⟨17537783314031178021769859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11691855542687452014513239 17537783314031178021769859)
              ·
                refine ⟨26306674971046767032654789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17537783314031178021769859 26306674971046767032654789)
                ·
                  refine ⟨4932501557071268818622773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26306674971046767032654789 4932501557071268818622773)
                  ·
                    refine ⟨462422020975431451745885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4932501557071268818622773 462422020975431451745885)
                    ·
                      rfl

theorem cell23_2701691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 5].length) (baseStart_2701691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701691 prefixEnd_2701691 := by exact prefixLift 2701691
  have htrace : WordTrace (prefixWord ++ tailWord_2701691) baseStart_2701691 baseEnd_2701691 := by
    simpa [prefixWord, tailWord_2701691, baseEnd_2701691] using wordTrace_append hprefix tailTrace_2701691
  have hstable : (prefixWord ++ tailWord_2701691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701691).length < 2 ^ (prefixWord ++ tailWord_2701691).sum := by decide
  have hdescent : baseEnd_2701691 < baseStart_2701691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701725 : List Nat := [1, 4, 2, 1, 4, 1, 2, 1, 2, 5]
def baseStart_2701725 : Nat := 118140960795 + 2701725 * 2 ^ 59
def prefixEnd_2701725 : Nat := 4983230072969 + 3 ^ 40 * 2701725 * 2
def baseEnd_2701725 : Nat := 462427840422849074070833

theorem tailTrace_2701725 : CollatzResearch.WordTrace tailWord_2701725 prefixEnd_2701725 462427840422849074070833 := by
  unfold tailWord_2701725
  simp only [CollatzResearch.WordTrace]
  refine ⟨98540006137119217739754629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65693337424746145159836419 98540006137119217739754629)
  ·
    refine ⟨18476251150709853326203993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98540006137119217739754629 18476251150709853326203993)
    ·
      refine ⟨13857188363032389994652995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18476251150709853326203993 13857188363032389994652995)
      ·
        refine ⟨20785782544548584991979493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13857188363032389994652995 20785782544548584991979493)
        ·
          refine ⟨3897334227102859685996155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20785782544548584991979493 3897334227102859685996155)
          ·
            refine ⟨5846001340654289528994233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3897334227102859685996155 5846001340654289528994233)
            ·
              refine ⟨4384501005490717146745675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5846001340654289528994233 4384501005490717146745675)
              ·
                refine ⟨6576751508236075720118513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4384501005490717146745675 6576751508236075720118513)
                ·
                  refine ⟨4932563631177056790088885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6576751508236075720118513 4932563631177056790088885)
                  ·
                    refine ⟨462427840422849074070833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4932563631177056790088885 462427840422849074070833)
                    ·
                      rfl

theorem cell23_2701725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_2701725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701725 prefixEnd_2701725 := by exact prefixLift 2701725
  have htrace : WordTrace (prefixWord ++ tailWord_2701725) baseStart_2701725 baseEnd_2701725 := by
    simpa [prefixWord, tailWord_2701725, baseEnd_2701725] using wordTrace_append hprefix tailTrace_2701725
  have hstable : (prefixWord ++ tailWord_2701725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701725).length < 2 ^ (prefixWord ++ tailWord_2701725).sum := by decide
  have hdescent : baseEnd_2701725 < baseStart_2701725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701728 : List Nat := [2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 4]
def baseStart_2701728 : Nat := 118140960795 + 2701728 * 2 ^ 59
def prefixEnd_2701728 : Nat := 4983230072969 + 3 ^ 40 * 2701728 * 2
def baseEnd_2701728 : Nat := 1387285061710510710474985

theorem tailTrace_2701728 : CollatzResearch.WordTrace tailWord_2701728 prefixEnd_2701728 1387285061710510710474985 := by
  unfold tailWord_2701728
  simp only [CollatzResearch.WordTrace]
  refine ⟨49270057778054174626056919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65693410370738899501409225 49270057778054174626056919)
  ·
    refine ⟨73905086667081261939085379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49270057778054174626056919 73905086667081261939085379)
    ·
      refine ⟨110857630000621892908628069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73905086667081261939085379 110857630000621892908628069)
      ·
        refine ⟨20785805625116604920367763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110857630000621892908628069 20785805625116604920367763)
        ·
          refine ⟨31178708437674907380551645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20785805625116604920367763 31178708437674907380551645)
          ·
            refine ⟨11692015664128090267706867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31178708437674907380551645 11692015664128090267706867)
            ·
              refine ⟨17538023496192135401560301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11692015664128090267706867 17538023496192135401560301)
              ·
                refine ⟨6576758811072050775585113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17538023496192135401560301 6576758811072050775585113)
                ·
                  refine ⟨4932569108304038081688835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6576758811072050775585113 4932569108304038081688835)
                  ·
                    refine ⟨7398853662456057122533253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4932569108304038081688835 7398853662456057122533253)
                    ·
                      refine ⟨1387285061710510710474985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7398853662456057122533253 1387285061710510710474985)
                      ·
                        rfl

theorem cell23_2701728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_2701728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701728 prefixEnd_2701728 := by exact prefixLift 2701728
  have htrace : WordTrace (prefixWord ++ tailWord_2701728) baseStart_2701728 baseEnd_2701728 := by
    simpa [prefixWord, tailWord_2701728, baseEnd_2701728] using wordTrace_append hprefix tailTrace_2701728
  have hstable : (prefixWord ++ tailWord_2701728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701728).length < 2 ^ (prefixWord ++ tailWord_2701728).sum := by decide
  have hdescent : baseEnd_2701728 < baseStart_2701728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701768 : List Nat := [2, 1, 3, 1, 3, 2, 2, 3, 6]
def baseStart_2701768 : Nat := 118140960795 + 2701768 * 2 ^ 59
def prefixEnd_2701768 : Nat := 4983230072969 + 3 ^ 40 * 2701768 * 2
def baseEnd_2701768 : Nat := 154145066770743394886089

theorem tailTrace_2701768 : CollatzResearch.WordTrace tailWord_2701768 prefixEnd_2701768 154145066770743394886089 := by
  unfold tailWord_2701768
  simp only [CollatzResearch.WordTrace]
  refine ⟨49270787237981718041784979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65694382983975624055713305 49270787237981718041784979)
  ·
    refine ⟨73906180856972577062677469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49270787237981718041784979 73906180856972577062677469)
    ·
      refine ⟨27714817821364716398504051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73906180856972577062677469 27714817821364716398504051)
      ·
        refine ⟨41572226732047074597756077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27714817821364716398504051 41572226732047074597756077)
        ·
          refine ⟨15589585024517652974158529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41572226732047074597756077 15589585024517652974158529)
          ·
            refine ⟨11692188768388239730618897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15589585024517652974158529 11692188768388239730618897)
            ·
              refine ⟨8769141576291179797964173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11692188768388239730618897 8769141576291179797964173)
              ·
                refine ⟨3288428091109192424236565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8769141576291179797964173 3288428091109192424236565)
                ·
                  refine ⟨154145066770743394886089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3288428091109192424236565 154145066770743394886089)
                  ·
                    rfl

theorem cell23_2701768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 6].length) (baseStart_2701768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701768 prefixEnd_2701768 := by exact prefixLift 2701768
  have htrace : WordTrace (prefixWord ++ tailWord_2701768) baseStart_2701768 baseEnd_2701768 := by
    simpa [prefixWord, tailWord_2701768, baseEnd_2701768] using wordTrace_append hprefix tailTrace_2701768
  have hstable : (prefixWord ++ tailWord_2701768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701768).length < 2 ^ (prefixWord ++ tailWord_2701768).sum := by decide
  have hdescent : baseEnd_2701768 < baseStart_2701768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701818 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4]
def baseStart_2701818 : Nat := 118140960795 + 2701818 * 2 ^ 59
def prefixEnd_2701818 : Nat := 4983230072969 + 3 ^ 40 * 2701818 * 2
def baseEnd_2701818 : Nat := 1387331274969415358349571

theorem tailTrace_2701818 : CollatzResearch.WordTrace tailWord_2701818 prefixEnd_2701818 1387331274969415358349571 := by
  unfold tailWord_2701818
  simp only [CollatzResearch.WordTrace]
  refine ⟨24635849531445573655722527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65695598750521529748593405 24635849531445573655722527)
  ·
    refine ⟨36953774297168360483583791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24635849531445573655722527 36953774297168360483583791)
    ·
      refine ⟨55430661445752540725375687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36953774297168360483583791 55430661445752540725375687)
      ·
        refine ⟨83145992168628811088063531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55430661445752540725375687 83145992168628811088063531)
        ·
          refine ⟨124718988252943216632095297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83145992168628811088063531 124718988252943216632095297)
          ·
            refine ⟨93539241189707412474071473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124718988252943216632095297 93539241189707412474071473)
            ·
              refine ⟨70154430892280559355553605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93539241189707412474071473 70154430892280559355553605)
              ·
                refine ⟨13153955792302604879166301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70154430892280559355553605 13153955792302604879166301)
                ·
                  refine ⟨4932733422113476829687363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13153955792302604879166301 4932733422113476829687363)
                  ·
                    refine ⟨7399100133170215244531045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4932733422113476829687363 7399100133170215244531045)
                    ·
                      refine ⟨1387331274969415358349571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7399100133170215244531045 1387331274969415358349571)
                      ·
                        rfl

theorem cell23_2701818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_2701818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701818 prefixEnd_2701818 := by exact prefixLift 2701818
  have htrace : WordTrace (prefixWord ++ tailWord_2701818) baseStart_2701818 baseEnd_2701818 := by
    simpa [prefixWord, tailWord_2701818, baseEnd_2701818] using wordTrace_append hprefix tailTrace_2701818
  have hstable : (prefixWord ++ tailWord_2701818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701818).length < 2 ^ (prefixWord ++ tailWord_2701818).sum := by decide
  have hdescent : baseEnd_2701818 < baseStart_2701818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701835 : List Nat := [1, 1, 1, 1, 7, 1, 1, 4, 1, 1, 4]
def baseStart_2701835 : Nat := 118140960795 + 2701835 * 2 ^ 59
def prefixEnd_2701835 : Nat := 4983230072969 + 3 ^ 40 * 2701835 * 2
def baseEnd_2701835 : Nat := 1387340004140541791836993

theorem tailTrace_2701835 : CollatzResearch.WordTrace tailWord_2701835 prefixEnd_2701835 1387340004140541791836993 := by
  unfold tailWord_2701835
  simp only [CollatzResearch.WordTrace]
  refine ⟨98544018166720706526258959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65696012111147137684172639 98544018166720706526258959)
  ·
    refine ⟨147816027250081059789388439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98544018166720706526258959 147816027250081059789388439)
    ·
      refine ⟨221724040875121589684082659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147816027250081059789388439 221724040875121589684082659)
      ·
        refine ⟨332586061312682384526123989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221724040875121589684082659 332586061312682384526123989)
        ·
          refine ⟨7794985812015993387331031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 332586061312682384526123989 7794985812015993387331031)
          ·
            refine ⟨11692478718023990080996547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7794985812015993387331031 11692478718023990080996547)
            ·
              refine ⟨17538718077035985121494821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11692478718023990080996547 17538718077035985121494821)
              ·
                refine ⟨3288509639444247210280279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17538718077035985121494821 3288509639444247210280279)
                ·
                  refine ⟨4932764459166370815420419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3288509639444247210280279 4932764459166370815420419)
                  ·
                    refine ⟨7399146688749556223130629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4932764459166370815420419 7399146688749556223130629)
                    ·
                      refine ⟨1387340004140541791836993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7399146688749556223130629 1387340004140541791836993)
                      ·
                        rfl

theorem cell23_2701835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 1, 4].length) (baseStart_2701835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701835 prefixEnd_2701835 := by exact prefixLift 2701835
  have htrace : WordTrace (prefixWord ++ tailWord_2701835) baseStart_2701835 baseEnd_2701835 := by
    simpa [prefixWord, tailWord_2701835, baseEnd_2701835] using wordTrace_append hprefix tailTrace_2701835
  have hstable : (prefixWord ++ tailWord_2701835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701835).length < 2 ^ (prefixWord ++ tailWord_2701835).sum := by decide
  have hdescent : baseEnd_2701835 < baseStart_2701835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701863 : List Nat := [1, 1, 7, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_2701863 : Nat := 118140960795 + 2701863 * 2 ^ 59
def prefixEnd_2701863 : Nat := 4983230072969 + 3 ^ 40 * 2701863 * 2
def baseEnd_2701863 : Nat := 1387354381598867682286865

theorem tailTrace_2701863 : CollatzResearch.WordTrace tailWord_2701863 prefixEnd_2701863 1387354381598867682286865 := by
  unfold tailWord_2701863
  simp only [CollatzResearch.WordTrace]
  refine ⟨98545039410619267308278243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65696692940412844872185495 98545039410619267308278243)
  ·
    refine ⟨147817559115928900962417365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98545039410619267308278243 147817559115928900962417365)
    ·
      refine ⟨3464474041779583616306657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 147817559115928900962417365 3464474041779583616306657)
      ·
        refine ⟨2598355531334687712229993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3464474041779583616306657 2598355531334687712229993)
        ·
          refine ⟨1948766648501015784172495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2598355531334687712229993 1948766648501015784172495)
          ·
            refine ⟨2923149972751523676258743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1948766648501015784172495 2923149972751523676258743)
            ·
              refine ⟨4384724959127285514388115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923149972751523676258743 4384724959127285514388115)
              ·
                refine ⟨6577087438690928271582173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4384724959127285514388115 6577087438690928271582173)
                ·
                  refine ⟨2466407789509098101843315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6577087438690928271582173 2466407789509098101843315)
                  ·
                    refine ⟨3699611684263647152764973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2466407789509098101843315 3699611684263647152764973)
                    ·
                      refine ⟨1387354381598867682286865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3699611684263647152764973 1387354381598867682286865)
                      ·
                        rfl

theorem cell23_2701863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_2701863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701863 prefixEnd_2701863 := by exact prefixLift 2701863
  have htrace : WordTrace (prefixWord ++ tailWord_2701863) baseStart_2701863 baseEnd_2701863 := by
    simpa [prefixWord, tailWord_2701863, baseEnd_2701863] using wordTrace_append hprefix tailTrace_2701863
  have hstable : (prefixWord ++ tailWord_2701863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701863).length < 2 ^ (prefixWord ++ tailWord_2701863).sum := by decide
  have hdescent : baseEnd_2701863 < baseStart_2701863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701886 : List Nat := [4, 2, 1, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_2701886 : Nat := 118140960795 + 2701886 * 2 ^ 59
def prefixEnd_2701886 : Nat := 4983230072969 + 3 ^ 40 * 2701886 * 2
def baseEnd_2701886 : Nat := 1387366191653921092299259

theorem tailTrace_2701886 : CollatzResearch.WordTrace tailWord_2701886 prefixEnd_2701886 1387366191653921092299259 := by
  unfold tailWord_2701886
  simp only [CollatzResearch.WordTrace]
  refine ⟨12318234786191992779545689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65697252193023961490910341 12318234786191992779545689)
  ·
    refine ⟨9238676089643994584659267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12318234786191992779545689 9238676089643994584659267)
    ·
      refine ⟨13858014134465991876988901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9238676089643994584659267 13858014134465991876988901)
      ·
        refine ⟨2598377650212373476935419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13858014134465991876988901 2598377650212373476935419)
        ·
          refine ⟨3897566475318560215403129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2598377650212373476935419 3897566475318560215403129)
          ·
            refine ⟨2923174856488920161552347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3897566475318560215403129 2923174856488920161552347)
            ·
              refine ⟨4384762284733380242328521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923174856488920161552347 4384762284733380242328521)
              ·
                refine ⟨3288571713550035181746391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4384762284733380242328521 3288571713550035181746391)
                ·
                  refine ⟨4932857570325052772619587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3288571713550035181746391 4932857570325052772619587)
                  ·
                    refine ⟨7399286355487579158929381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4932857570325052772619587 7399286355487579158929381)
                    ·
                      refine ⟨1387366191653921092299259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7399286355487579158929381 1387366191653921092299259)
                      ·
                        rfl

theorem cell23_2701886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_2701886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701886 prefixEnd_2701886 := by exact prefixLift 2701886
  have htrace : WordTrace (prefixWord ++ tailWord_2701886) baseStart_2701886 baseEnd_2701886 := by
    simpa [prefixWord, tailWord_2701886, baseEnd_2701886] using wordTrace_append hprefix tailTrace_2701886
  have hstable : (prefixWord ++ tailWord_2701886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701886).length < 2 ^ (prefixWord ++ tailWord_2701886).sum := by decide
  have hdescent : baseEnd_2701886 < baseStart_2701886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701889 : List Nat := [1, 2, 5, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_2701889 : Nat := 118140960795 + 2701889 * 2 ^ 59
def prefixEnd_2701889 : Nat := 4983230072969 + 3 ^ 40 * 2701889 * 2
def baseEnd_2701889 : Nat := 1387367732095884580561745

theorem tailTrace_2701889 : CollatzResearch.WordTrace tailWord_2701889 prefixEnd_2701889 1387367732095884580561745 := by
  unfold tailWord_2701889
  simp only [CollatzResearch.WordTrace]
  refine ⟨98545987708525073748724721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65697325139016715832483147 98545987708525073748724721)
  ·
    refine ⟨73909490781393805311543541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98545987708525073748724721 73909490781393805311543541)
    ·
      refine ⟨6929014760755669247957207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73909490781393805311543541 6929014760755669247957207)
      ·
        refine ⟨10393522141133503871935811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6929014760755669247957207 10393522141133503871935811)
        ·
          refine ⟨15590283211700255807903717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10393522141133503871935811 15590283211700255807903717)
          ·
            refine ⟨2923178102193797963981947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15590283211700255807903717 2923178102193797963981947)
            ·
              refine ⟨4384767153290696945972921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923178102193797963981947 4384767153290696945972921)
              ·
                refine ⟨3288575364968022709479691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4384767153290696945972921 3288575364968022709479691)
                ·
                  refine ⟨4932863047452034064219537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3288575364968022709479691 4932863047452034064219537)
                  ·
                    refine ⟨3699647285589025548164653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4932863047452034064219537 3699647285589025548164653)
                    ·
                      refine ⟨1387367732095884580561745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3699647285589025548164653 1387367732095884580561745)
                      ·
                        rfl

theorem cell23_2701889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_2701889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701889 prefixEnd_2701889 := by exact prefixLift 2701889
  have htrace : WordTrace (prefixWord ++ tailWord_2701889) baseStart_2701889 baseEnd_2701889 := by
    simpa [prefixWord, tailWord_2701889, baseEnd_2701889] using wordTrace_append hprefix tailTrace_2701889
  have hstable : (prefixWord ++ tailWord_2701889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701889).length < 2 ^ (prefixWord ++ tailWord_2701889).sum := by decide
  have hdescent : baseEnd_2701889 < baseStart_2701889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701912 : List Nat := [2, 1, 2, 2, 1, 2, 2, 5, 1, 3, 2]
def baseStart_2701912 : Nat := 118140960795 + 2701912 * 2 ^ 59
def prefixEnd_2701912 : Nat := 4983230072969 + 3 ^ 40 * 2701912 * 2
def baseEnd_2701912 : Nat := 1387379542150937990574139

theorem tailTrace_2701912 : CollatzResearch.WordTrace tailWord_2701912 prefixEnd_2701912 1387379542150937990574139 := by
  unfold tailWord_2701912
  simp only [CollatzResearch.WordTrace]
  refine ⟨49273413293720874338405995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65697884391627832451207993 49273413293720874338405995)
  ·
    refine ⟨73910119940581311507608993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49273413293720874338405995 73910119940581311507608993)
    ·
      refine ⟨55432589955435983630706745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73910119940581311507608993 55432589955435983630706745)
      ·
        refine ⟨41574442466576987723030059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55432589955435983630706745 41574442466576987723030059)
        ·
          refine ⟨62361663699865481584545089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41574442466576987723030059 62361663699865481584545089)
          ·
            refine ⟨46771247774899111188408817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62361663699865481584545089 46771247774899111188408817)
            ·
              refine ⟨35078435831174333391306613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46771247774899111188408817 35078435831174333391306613)
              ·
                refine ⟨3288603359172593755434995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35078435831174333391306613 3288603359172593755434995)
                ·
                  refine ⟨4932905038758890633152493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3288603359172593755434995 4932905038758890633152493)
                  ·
                    refine ⟨1849839389534583987432185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4932905038758890633152493 1849839389534583987432185)
                    ·
                      refine ⟨1387379542150937990574139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1849839389534583987432185 1387379542150937990574139)
                      ·
                        rfl

theorem cell23_2701912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_2701912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701912 prefixEnd_2701912 := by exact prefixLift 2701912
  have htrace : WordTrace (prefixWord ++ tailWord_2701912) baseStart_2701912 baseEnd_2701912 := by
    simpa [prefixWord, tailWord_2701912, baseEnd_2701912] using wordTrace_append hprefix tailTrace_2701912
  have hstable : (prefixWord ++ tailWord_2701912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701912).length < 2 ^ (prefixWord ++ tailWord_2701912).sum := by decide
  have hdescent : baseEnd_2701912 < baseStart_2701912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701948 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 9]
def baseStart_2701948 : Nat := 118140960795 + 2701948 * 2 ^ 59
def prefixEnd_2701948 : Nat := 4983230072969 + 3 ^ 40 * 2701948 * 2
def baseEnd_2701948 : Nat := 154155336383833316635997

theorem tailTrace_2701948 : CollatzResearch.WordTrace tailWord_2701948 prefixEnd_2701948 154155336383833316635997 := by
  unfold tailWord_2701948
  simp only [CollatzResearch.WordTrace]
  refine ⟨49274069807655663412561249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65698759743540884550081665 49274069807655663412561249)
  ·
    refine ⟨36955552355741747559420937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49274069807655663412561249 36955552355741747559420937)
    ·
      refine ⟨27716664266806310669565703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36955552355741747559420937 27716664266806310669565703)
      ·
        refine ⟨41574996400209466004348555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27716664266806310669565703 41574996400209466004348555)
        ·
          refine ⟨62362494600314199006522833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41574996400209466004348555 62362494600314199006522833)
          ·
            refine ⟨46771870950235649254892125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62362494600314199006522833 46771870950235649254892125)
            ·
              refine ⟨17539451606338368470584547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46771870950235649254892125 17539451606338368470584547)
              ·
                refine ⟨26309177409507552705876821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17539451606338368470584547 26309177409507552705876821)
                ·
                  refine ⟨154155336383833316635997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26309177409507552705876821 154155336383833316635997)
                  ·
                    rfl

theorem cell23_2701948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 9].length) (baseStart_2701948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701948 prefixEnd_2701948 := by exact prefixLift 2701948
  have htrace : WordTrace (prefixWord ++ tailWord_2701948) baseStart_2701948 baseEnd_2701948 := by
    simpa [prefixWord, tailWord_2701948, baseEnd_2701948] using wordTrace_append hprefix tailTrace_2701948
  have hstable : (prefixWord ++ tailWord_2701948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701948).length < 2 ^ (prefixWord ++ tailWord_2701948).sum := by decide
  have hdescent : baseEnd_2701948 < baseStart_2701948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701972 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_2701972 : Nat := 118140960795 + 2701972 * 2 ^ 59
def prefixEnd_2701972 : Nat := 4983230072969 + 3 ^ 40 * 2701972 * 2
def baseEnd_2701972 : Nat := 1387410350990207755823863

theorem tailTrace_2701972 : CollatzResearch.WordTrace tailWord_2701972 prefixEnd_2701972 1387410350990207755823863 := by
  unfold tailWord_2701972
  simp only [CollatzResearch.WordTrace]
  refine ⟨49274507483612189461998085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65699343311482919282664113 49274507483612189461998085)
  ·
    refine ⟨9238970153177285524124641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49274507483612189461998085 9238970153177285524124641)
    ·
      refine ⟨6929227614882964143093481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9238970153177285524124641 6929227614882964143093481)
      ·
        refine ⟨5196920711162223107320111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6929227614882964143093481 5196920711162223107320111)
        ·
          refine ⟨7795381066743334660980167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5196920711162223107320111 7795381066743334660980167)
          ·
            refine ⟨11693071600115001991470251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7795381066743334660980167 11693071600115001991470251)
            ·
              refine ⟨17539607400172502987205377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11693071600115001991470251 17539607400172502987205377)
              ·
                refine ⟨13154705550129377240404033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17539607400172502987205377 13154705550129377240404033)
                ·
                  refine ⟨9866029162597032930303025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13154705550129377240404033 9866029162597032930303025)
                  ·
                    refine ⟨7399521871947774697727269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9866029162597032930303025 7399521871947774697727269)
                    ·
                      refine ⟨1387410350990207755823863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7399521871947774697727269 1387410350990207755823863)
                      ·
                        rfl

theorem cell23_2701972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_2701972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701972 prefixEnd_2701972 := by exact prefixLift 2701972
  have htrace : WordTrace (prefixWord ++ tailWord_2701972) baseStart_2701972 baseEnd_2701972 := by
    simpa [prefixWord, tailWord_2701972, baseEnd_2701972] using wordTrace_append hprefix tailTrace_2701972
  have hstable : (prefixWord ++ tailWord_2701972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701972).length < 2 ^ (prefixWord ++ tailWord_2701972).sum := by decide
  have hdescent : baseEnd_2701972 < baseStart_2701972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701975 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 3]
def baseStart_2701975 : Nat := 118140960795 + 2701975 * 2 ^ 59
def prefixEnd_2701975 : Nat := 4983230072969 + 3 ^ 40 * 2701975 * 2
def baseEnd_2701975 : Nat := 1387411891432171244086349

theorem tailTrace_2701975 : CollatzResearch.WordTrace tailWord_2701975 prefixEnd_2701975 1387411891432171244086349 := by
  unfold tailWord_2701975
  simp only [CollatzResearch.WordTrace]
  refine ⟨98549124386213510436355379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65699416257475673624236919 98549124386213510436355379)
  ·
    refine ⟨147823686579320265654533069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98549124386213510436355379 147823686579320265654533069)
    ·
      refine ⟨55433882467245099620449901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147823686579320265654533069 55433882467245099620449901)
      ·
        refine ⟨20787705925216912357668713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55433882467245099620449901 20787705925216912357668713)
        ·
          refine ⟨15590779443912684268251535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20787705925216912357668713 15590779443912684268251535)
          ·
            refine ⟨23386169165869026402377303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15590779443912684268251535 23386169165869026402377303)
            ·
              refine ⟨35079253748803539603565955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23386169165869026402377303 35079253748803539603565955)
              ·
                refine ⟨52618880623205309405348933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35079253748803539603565955 52618880623205309405348933)
                ·
                  refine ⟨9866040116850995513502925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52618880623205309405348933 9866040116850995513502925)
                  ·
                    refine ⟨3699765043819123317563597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9866040116850995513502925 3699765043819123317563597)
                    ·
                      refine ⟨1387411891432171244086349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3699765043819123317563597 1387411891432171244086349)
                      ·
                        rfl

theorem cell23_2701975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_2701975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701975 prefixEnd_2701975 := by exact prefixLift 2701975
  have htrace : WordTrace (prefixWord ++ tailWord_2701975) baseStart_2701975 baseEnd_2701975 := by
    simpa [prefixWord, tailWord_2701975, baseEnd_2701975] using wordTrace_append hprefix tailTrace_2701975
  have hstable : (prefixWord ++ tailWord_2701975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701975).length < 2 ^ (prefixWord ++ tailWord_2701975).sum := by decide
  have hdescent : baseEnd_2701975 < baseStart_2701975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701982 : List Nat := [4, 3, 1, 1, 1, 1, 4, 1, 7]
def baseStart_2701982 : Nat := 118140960795 + 2701982 * 2 ^ 59
def prefixEnd_2701982 : Nat := 4983230072969 + 3 ^ 40 * 2701982 * 2
def baseEnd_2701982 : Nat := 154157276199639190744313

theorem tailTrace_2701982 : CollatzResearch.WordTrace tailWord_2701982 prefixEnd_2701982 154157276199639190744313 := by
  unfold tailWord_2701982
  simp only [CollatzResearch.WordTrace]
  refine ⟨12318672462148518828982525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65699586464792100421240133 12318672462148518828982525)
  ·
    refine ⟨4619502173305694560868447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12318672462148518828982525 4619502173305694560868447)
    ·
      refine ⟨6929253259958541841302671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4619502173305694560868447 6929253259958541841302671)
      ·
        refine ⟨10393879889937812761954007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6929253259958541841302671 10393879889937812761954007)
        ·
          refine ⟨15590819834906719142931011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10393879889937812761954007 15590819834906719142931011)
          ·
            refine ⟨23386229752360078714396517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15590819834906719142931011 23386229752360078714396517)
            ·
              refine ⟨4384918078567514758949347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23386229752360078714396517 4384918078567514758949347)
              ·
                refine ⟨6577377117851272138424021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4384918078567514758949347 6577377117851272138424021)
                ·
                  refine ⟨154157276199639190744313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6577377117851272138424021 154157276199639190744313)
                  ·
                    rfl

theorem cell23_2701982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_2701982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2701982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2701982 prefixEnd_2701982 := by exact prefixLift 2701982
  have htrace : WordTrace (prefixWord ++ tailWord_2701982) baseStart_2701982 baseEnd_2701982 := by
    simpa [prefixWord, tailWord_2701982, baseEnd_2701982] using wordTrace_append hprefix tailTrace_2701982
  have hstable : (prefixWord ++ tailWord_2701982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701982).length < 2 ^ (prefixWord ++ tailWord_2701982).sum := by decide
  have hdescent : baseEnd_2701982 < baseStart_2701982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702015 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 4]
def baseStart_2702015 : Nat := 118140960795 + 2702015 * 2 ^ 59
def prefixEnd_2702015 : Nat := 4983230072969 + 3 ^ 40 * 2702015 * 2
def baseEnd_2702015 : Nat := 1387432430658351087586165

theorem tailTrace_2702015 : CollatzResearch.WordTrace tailWord_2702015 prefixEnd_2702015 1387432430658351087586165 := by
  unfold tailWord_2702015
  simp only [CollatzResearch.WordTrace]
  refine ⟨98550583306068597267811499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65700388870712398178540999 98550583306068597267811499)
  ·
    refine ⟨147825874959102895901717249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98550583306068597267811499 147825874959102895901717249)
    ·
      refine ⟨110869406219327171926287937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147825874959102895901717249 110869406219327171926287937)
      ·
        refine ⟨83152054664495378944715953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110869406219327171926287937 83152054664495378944715953)
        ·
          refine ⟨62364040998371534208536965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83152054664495378944715953 62364040998371534208536965)
          ·
            refine ⟨11693257687194662664100681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62364040998371534208536965 11693257687194662664100681)
            ·
              refine ⟨8769943265395996998075511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11693257687194662664100681 8769943265395996998075511)
              ·
                refine ⟨13154914898093995497113267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8769943265395996998075511 13154914898093995497113267)
                ·
                  refine ⟨19732372347140993245669901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13154914898093995497113267 19732372347140993245669901)
                  ·
                    refine ⟨7399639630177872467126213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19732372347140993245669901 7399639630177872467126213)
                    ·
                      refine ⟨1387432430658351087586165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7399639630177872467126213 1387432430658351087586165)
                      ·
                        rfl

theorem cell23_2702015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_2702015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702015 prefixEnd_2702015 := by exact prefixLift 2702015
  have htrace : WordTrace (prefixWord ++ tailWord_2702015) baseStart_2702015 baseEnd_2702015 := by
    simpa [prefixWord, tailWord_2702015, baseEnd_2702015] using wordTrace_append hprefix tailTrace_2702015
  have hstable : (prefixWord ++ tailWord_2702015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702015).length < 2 ^ (prefixWord ++ tailWord_2702015).sum := by decide
  have hdescent : baseEnd_2702015 < baseStart_2702015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702092 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 3, 5, 2]
def baseStart_2702092 : Nat := 118140960795 + 2702092 * 2 ^ 59
def prefixEnd_2702092 : Nat := 4983230072969 + 3 ^ 40 * 2702092 * 2
def baseEnd_2702092 : Nat := 1387471968668747286323311

theorem tailTrace_2702092 : CollatzResearch.WordTrace tailWord_2702092 prefixEnd_2702092 1387471968668747286323311 := by
  unfold tailWord_2702092
  simp only [CollatzResearch.WordTrace]
  refine ⟨49276695863394819709182265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65702261151193092945576353 49276695863394819709182265)
  ·
    refine ⟨36957521897546114781886699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49276695863394819709182265 36957521897546114781886699)
    ·
      refine ⟨55436282846319172172830049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36957521897546114781886699 55436282846319172172830049)
      ·
        refine ⟨41577212134739379129622537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55436282846319172172830049 41577212134739379129622537)
        ·
          refine ⟨31182909101054534347216903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41577212134739379129622537 31182909101054534347216903)
          ·
            refine ⟨46774363651581801520825355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31182909101054534347216903 46774363651581801520825355)
            ·
              refine ⟨70161545477372702281238033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46774363651581801520825355 70161545477372702281238033)
              ·
                refine ⟨52621159108029526710928525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70161545477372702281238033 52621159108029526710928525)
                ·
                  refine ⟨19732934665511072516598197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52621159108029526710928525 19732934665511072516598197)
                  ·
                    refine ⟨1849962624891663048431081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19732934665511072516598197 1849962624891663048431081)
                    ·
                      refine ⟨1387471968668747286323311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1849962624891663048431081 1387471968668747286323311)
                      ·
                        rfl

theorem cell23_2702092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_2702092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702092 prefixEnd_2702092 := by exact prefixLift 2702092
  have htrace : WordTrace (prefixWord ++ tailWord_2702092) baseStart_2702092 baseEnd_2702092 := by
    simpa [prefixWord, tailWord_2702092, baseEnd_2702092] using wordTrace_append hprefix tailTrace_2702092
  have hstable : (prefixWord ++ tailWord_2702092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702092).length < 2 ^ (prefixWord ++ tailWord_2702092).sum := by decide
  have hdescent : baseEnd_2702092 < baseStart_2702092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702116 : List Nat := [2, 3, 1, 3, 3, 1, 1, 2, 3, 1, 3]
def baseStart_2702116 : Nat := 118140960795 + 2702116 * 2 ^ 59
def prefixEnd_2702116 : Nat := 4983230072969 + 3 ^ 40 * 2702116 * 2
def baseEnd_2702116 : Nat := 1387484292204455192423201

theorem tailTrace_2702116 : CollatzResearch.WordTrace tailWord_2702116 prefixEnd_2702116 1387484292204455192423201 := by
  unfold tailWord_2702116
  simp only [CollatzResearch.WordTrace]
  refine ⟨49277133539351345758619101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65702844719135127678158801 49277133539351345758619101)
  ·
    refine ⟨18478925077256754659482163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49277133539351345758619101 18478925077256754659482163)
    ·
      refine ⟨27718387615885131989223245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18478925077256754659482163 27718387615885131989223245)
      ·
        refine ⟨10394395355956924495958717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27718387615885131989223245 10394395355956924495958717)
        ·
          refine ⟨3897898258483846685984519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10394395355956924495958717 3897898258483846685984519)
          ·
            refine ⟨5846847387725770028976779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3897898258483846685984519 5846847387725770028976779)
            ·
              refine ⟨8770271081588655043465169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5846847387725770028976779 8770271081588655043465169)
              ·
                refine ⟨6577703311191491282598877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8770271081588655043465169 6577703311191491282598877)
                ·
                  refine ⟨2466638741696809230974579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6577703311191491282598877 2466638741696809230974579)
                  ·
                    refine ⟨3699958112545213846461869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2466638741696809230974579 3699958112545213846461869)
                    ·
                      refine ⟨1387484292204455192423201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3699958112545213846461869 1387484292204455192423201)
                      ·
                        rfl

theorem cell23_2702116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_2702116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702116 prefixEnd_2702116 := by exact prefixLift 2702116
  have htrace : WordTrace (prefixWord ++ tailWord_2702116) baseStart_2702116 baseEnd_2702116 := by
    simpa [prefixWord, tailWord_2702116, baseEnd_2702116] using wordTrace_append hprefix tailTrace_2702116
  have hstable : (prefixWord ++ tailWord_2702116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702116).length < 2 ^ (prefixWord ++ tailWord_2702116).sum := by decide
  have hdescent : baseEnd_2702116 < baseStart_2702116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702126 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_2702126 : Nat := 118140960795 + 2702126 * 2 ^ 59
def prefixEnd_2702126 : Nat := 4983230072969 + 3 ^ 40 * 2702126 * 2
def baseEnd_2702126 : Nat := 1387489427011000153298155

theorem tailTrace_2702126 : CollatzResearch.WordTrace tailWord_2702126 prefixEnd_2702126 1387489427011000153298155 := by
  unfold tailWord_2702126
  simp only [CollatzResearch.WordTrace]
  refine ⟨12319328976083307903137779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65703087872444308816734821 12319328976083307903137779)
  ·
    refine ⟨18478993464124961854706669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12319328976083307903137779 18478993464124961854706669)
    ·
      refine ⟨6929622549046860695515001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18478993464124961854706669 6929622549046860695515001)
      ·
        refine ⟨5197216911785145521636251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6929622549046860695515001 5197216911785145521636251)
        ·
          refine ⟨7795825367677718282454377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5197216911785145521636251 7795825367677718282454377)
          ·
            refine ⟨5846869025758288711840783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7795825367677718282454377 5846869025758288711840783)
            ·
              refine ⟨8770303538637433067761175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5846869025758288711840783 8770303538637433067761175)
              ·
                refine ⟨13155455307956149601641763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8770303538637433067761175 13155455307956149601641763)
                ·
                  refine ⟨19733182961934224402462645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13155455307956149601641763 19733182961934224402462645)
                  ·
                    refine ⟨1849985902681333537730873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19733182961934224402462645 1849985902681333537730873)
                    ·
                      refine ⟨1387489427011000153298155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1849985902681333537730873 1387489427011000153298155)
                      ·
                        rfl

theorem cell23_2702126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_2702126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702126 prefixEnd_2702126 := by exact prefixLift 2702126
  have htrace : WordTrace (prefixWord ++ tailWord_2702126) baseStart_2702126 baseEnd_2702126 := by
    simpa [prefixWord, tailWord_2702126, baseEnd_2702126] using wordTrace_append hprefix tailTrace_2702126
  have hstable : (prefixWord ++ tailWord_2702126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702126).length < 2 ^ (prefixWord ++ tailWord_2702126).sum := by decide
  have hdescent : baseEnd_2702126 < baseStart_2702126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702133 : List Nat := [1, 3, 3, 1, 3, 2, 2, 3, 1, 1, 3]
def baseStart_2702133 : Nat := 118140960795 + 2702133 * 2 ^ 59
def prefixEnd_2702133 : Nat := 4983230072969 + 3 ^ 40 * 2702133 * 2
def baseEnd_2702133 : Nat := 1387493021375581625910623

theorem tailTrace_2702133 : CollatzResearch.WordTrace tailWord_2702133 prefixEnd_2702133 1387493021375581625910623 := by
  unfold tailWord_2702133
  simp only [CollatzResearch.WordTrace]
  refine ⟨98554887119641103420607053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65703258079760735613738035 98554887119641103420607053)
  ·
    refine ⟨36958082669865413782727645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98554887119641103420607053 36958082669865413782727645)
    ·
      refine ⟨13859281001199530168522867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36958082669865413782727645 13859281001199530168522867)
      ·
        refine ⟨20788921501799295252784301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13859281001199530168522867 20788921501799295252784301)
        ·
          refine ⟨7795845563174735719794113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20788921501799295252784301 7795845563174735719794113)
          ·
            refine ⟨5846884172381051789845585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7795845563174735719794113 5846884172381051789845585)
            ·
              refine ⟨4385163129285788842384189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5846884172381051789845585 4385163129285788842384189)
              ·
                refine ⟨1644436173482170815894071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4385163129285788842384189 1644436173482170815894071)
                ·
                  refine ⟨2466654260223256223841107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644436173482170815894071 2466654260223256223841107)
                  ·
                    refine ⟨3699981390334884335761661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2466654260223256223841107 3699981390334884335761661)
                    ·
                      refine ⟨1387493021375581625910623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3699981390334884335761661 1387493021375581625910623)
                      ·
                        rfl

theorem cell23_2702133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_2702133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702133 prefixEnd_2702133 := by exact prefixLift 2702133
  have htrace : WordTrace (prefixWord ++ tailWord_2702133) baseStart_2702133 baseEnd_2702133 := by
    simpa [prefixWord, tailWord_2702133, baseEnd_2702133] using wordTrace_append hprefix tailTrace_2702133
  have hstable : (prefixWord ++ tailWord_2702133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702133).length < 2 ^ (prefixWord ++ tailWord_2702133).sum := by decide
  have hdescent : baseEnd_2702133 < baseStart_2702133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702150 : List Nat := [6, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_2702150 : Nat := 118140960795 + 2702150 * 2 ^ 59
def prefixEnd_2702150 : Nat := 4983230072969 + 3 ^ 40 * 2702150 * 2
def baseEnd_2702150 : Nat := 1387501750546708059398045

theorem tailTrace_2702150 : CollatzResearch.WordTrace tailWord_2702150 prefixEnd_2702150 1387501750546708059398045 := by
  unfold tailWord_2702150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3079859598768109853874247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65703671440386343549317269 3079859598768109853874247)
  ·
    refine ⟨4619789398152164780811371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3079859598768109853874247 4619789398152164780811371)
    ·
      refine ⟨6929684097228247171217057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4619789398152164780811371 6929684097228247171217057)
      ·
        refine ⟨5197263072921185378412793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6929684097228247171217057 5197263072921185378412793)
        ·
          refine ⟨3897947304690889033809595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5197263072921185378412793 3897947304690889033809595)
          ·
            refine ⟨5846920957036333550714393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3897947304690889033809595 5846920957036333550714393)
            ·
              refine ⟨4385190717777250163035795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5846920957036333550714393 4385190717777250163035795)
              ·
                refine ⟨6577786076665875244553693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4385190717777250163035795 6577786076665875244553693)
                ·
                  refine ⟨2466669778749703216707635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6577786076665875244553693 2466669778749703216707635)
                  ·
                    refine ⟨3700004668124554825061453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2466669778749703216707635 3700004668124554825061453)
                    ·
                      refine ⟨1387501750546708059398045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3700004668124554825061453 1387501750546708059398045)
                      ·
                        rfl

theorem cell23_2702150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_2702150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702150 prefixEnd_2702150 := by exact prefixLift 2702150
  have htrace : WordTrace (prefixWord ++ tailWord_2702150) baseStart_2702150 baseEnd_2702150 := by
    simpa [prefixWord, tailWord_2702150, baseEnd_2702150] using wordTrace_append hprefix tailTrace_2702150
  have hstable : (prefixWord ++ tailWord_2702150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702150).length < 2 ^ (prefixWord ++ tailWord_2702150).sum := by decide
  have hdescent : baseEnd_2702150 < baseStart_2702150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702156 : List Nat := [2, 2, 1, 3, 3, 1, 1, 3, 3, 2, 2]
def baseStart_2702156 : Nat := 118140960795 + 2702156 * 2 ^ 59
def prefixEnd_2702156 : Nat := 4983230072969 + 3 ^ 40 * 2702156 * 2
def baseEnd_2702156 : Nat := 1387504831430635035923017

theorem tailTrace_2702156 : CollatzResearch.WordTrace tailWord_2702156 prefixEnd_2702156 1387504831430635035923017 := by
  unfold tailWord_2702156
  simp only [CollatzResearch.WordTrace]
  refine ⟨49277862999278889174347161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65703817332371852232462881 49277862999278889174347161)
  ·
    refine ⟨36958397249459166880760371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49277862999278889174347161 36958397249459166880760371)
    ·
      refine ⟨55437595874188750321140557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36958397249459166880760371 55437595874188750321140557)
      ·
        refine ⟨20789098452820781370427709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55437595874188750321140557 20789098452820781370427709)
        ·
          refine ⟨7795911919807793013910391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20789098452820781370427709 7795911919807793013910391)
          ·
            refine ⟨11693867879711689520865587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7795911919807793013910391 11693867879711689520865587)
            ·
              refine ⟨17540801819567534281298381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11693867879711689520865587 17540801819567534281298381)
              ·
                refine ⟨6577800682337825355486893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17540801819567534281298381 6577800682337825355486893)
                ·
                  refine ⟨2466675255876684508307585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6577800682337825355486893 2466675255876684508307585)
                  ·
                    refine ⟨1850006441907513381230689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2466675255876684508307585 1850006441907513381230689)
                    ·
                      refine ⟨1387504831430635035923017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1850006441907513381230689 1387504831430635035923017)
                      ·
                        rfl

theorem cell23_2702156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_2702156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702156 prefixEnd_2702156 := by exact prefixLift 2702156
  have htrace : WordTrace (prefixWord ++ tailWord_2702156) baseStart_2702156 baseEnd_2702156 := by
    simpa [prefixWord, tailWord_2702156, baseEnd_2702156] using wordTrace_append hprefix tailTrace_2702156
  have hstable : (prefixWord ++ tailWord_2702156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702156).length < 2 ^ (prefixWord ++ tailWord_2702156).sum := by decide
  have hdescent : baseEnd_2702156 < baseStart_2702156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702169 : List Nat := [1, 2, 1, 2, 2, 6, 1, 1, 1, 2, 4]
def baseStart_2702169 : Nat := 118140960795 + 2702169 * 2 ^ 59
def prefixEnd_2702169 : Nat := 4983230072969 + 3 ^ 40 * 2702169 * 2
def baseEnd_2702169 : Nat := 1387511506679143485060457

theorem tailTrace_2702169 : CollatzResearch.WordTrace tailWord_2702169 prefixEnd_2702169 1387511506679143485060457 := by
  unfold tailWord_2702169
  simp only [CollatzResearch.WordTrace]
  refine ⟨98556200147510681568917561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65704133431673787712611707 98556200147510681568917561)
  ·
    refine ⟨73917150110633011176688171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98556200147510681568917561 73917150110633011176688171)
    ·
      refine ⟨110875725165949516765032257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73917150110633011176688171 110875725165949516765032257)
      ·
        refine ⟨83156793874462137573774193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110875725165949516765032257 83156793874462137573774193)
        ·
          refine ⟨62367595405846603180330645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83156793874462137573774193 62367595405846603180330645)
          ·
            refine ⟨2923481034649059524077999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62367595405846603180330645 2923481034649059524077999)
            ·
              refine ⟨4385221551973589286116999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923481034649059524077999 4385221551973589286116999)
              ·
                refine ⟨6577832327960383929175499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4385221551973589286116999 6577832327960383929175499)
                ·
                  refine ⟨9866748491940575893763249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6577832327960383929175499 9866748491940575893763249)
                  ·
                    refine ⟨7400061368955431920322437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9866748491940575893763249 7400061368955431920322437)
                    ·
                      refine ⟨1387511506679143485060457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7400061368955431920322437 1387511506679143485060457)
                      ·
                        rfl

theorem cell23_2702169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 2, 4].length) (baseStart_2702169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702169 prefixEnd_2702169 := by exact prefixLift 2702169
  have htrace : WordTrace (prefixWord ++ tailWord_2702169) baseStart_2702169 baseEnd_2702169 := by
    simpa [prefixWord, tailWord_2702169, baseEnd_2702169] using wordTrace_append hprefix tailTrace_2702169
  have hstable : (prefixWord ++ tailWord_2702169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702169).length < 2 ^ (prefixWord ++ tailWord_2702169).sum := by decide
  have hdescent : baseEnd_2702169 < baseStart_2702169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702179 : List Nat := [1, 1, 1, 5, 3, 3, 2, 7]
def baseStart_2702179 : Nat := 118140960795 + 2702179 * 2 ^ 59
def prefixEnd_2702179 : Nat := 4983230072969 + 3 ^ 40 * 2702179 * 2
def baseEnd_2702179 : Nat := 51389505240210683182793

theorem tailTrace_2702179 : CollatzResearch.WordTrace tailWord_2702179 prefixEnd_2702179 51389505240210683182793 := by
  unfold tailWord_2702179
  simp only [CollatzResearch.WordTrace]
  refine ⟨98556564877474453276781591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65704376584982968851187727 98556564877474453276781591)
  ·
    refine ⟨147834847316211679915172387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98556564877474453276781591 147834847316211679915172387)
    ·
      refine ⟨221752270974317519872758581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147834847316211679915172387 221752270974317519872758581)
      ·
        refine ⟨20789275403842267488071117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 221752270974317519872758581 20789275403842267488071117)
        ·
          refine ⟨7795978276440850308026669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20789275403842267488071117 7795978276440850308026669)
          ·
            refine ⟨2923491853665318865510001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7795978276440850308026669 2923491853665318865510001)
            ·
              refine ⟨2192618890248989149132501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2923491853665318865510001 2192618890248989149132501)
              ·
                refine ⟨51389505240210683182793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2192618890248989149132501 51389505240210683182793)
                ·
                  rfl

theorem cell23_2702179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 7].length) (baseStart_2702179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702179 prefixEnd_2702179 := by exact prefixLift 2702179
  have htrace : WordTrace (prefixWord ++ tailWord_2702179) baseStart_2702179 baseEnd_2702179 := by
    simpa [prefixWord, tailWord_2702179, baseEnd_2702179] using wordTrace_append hprefix tailTrace_2702179
  have hstable : (prefixWord ++ tailWord_2702179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702179).length < 2 ^ (prefixWord ++ tailWord_2702179).sum := by decide
  have hdescent : baseEnd_2702179 < baseStart_2702179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702212 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_2702212 : Nat := 118140960795 + 2702212 * 2 ^ 59
def prefixEnd_2702212 : Nat := 4983230072969 + 3 ^ 40 * 2702212 * 2
def baseEnd_2702212 : Nat := 1387533586347286816822759

theorem tailTrace_2702212 : CollatzResearch.WordTrace tailWord_2702212 prefixEnd_2702212 1387533586347286816822759 := by
  unfold tailWord_2702212
  simp only [CollatzResearch.WordTrace]
  refine ⟨49278884243177449956366445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65705178990903266608488593 49278884243177449956366445)
  ·
    refine ⟨18479581591191543733637417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49278884243177449956366445 18479581591191543733637417)
    ·
      refine ⟨13859686193393657800228063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18479581591191543733637417 13859686193393657800228063)
      ·
        refine ⟨20789529290090486700342095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13859686193393657800228063 20789529290090486700342095)
        ·
          refine ⟨31184293935135730050513143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20789529290090486700342095 31184293935135730050513143)
          ·
            refine ⟨46776440902703595075769715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31184293935135730050513143 46776440902703595075769715)
            ·
              refine ⟨70164661354055392613654573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46776440902703595075769715 70164661354055392613654573)
              ·
                refine ⟨26311748007770772230120465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70164661354055392613654573 26311748007770772230120465)
                ·
                  refine ⟨19733811005828079172590349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26311748007770772230120465 19733811005828079172590349)
                  ·
                    refine ⟨7400179127185529689721381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19733811005828079172590349 7400179127185529689721381)
                    ·
                      refine ⟨1387533586347286816822759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7400179127185529689721381 1387533586347286816822759)
                      ·
                        rfl

theorem cell23_2702212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_2702212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702212 prefixEnd_2702212 := by exact prefixLift 2702212
  have htrace : WordTrace (prefixWord ++ tailWord_2702212) baseStart_2702212 baseEnd_2702212 := by
    simpa [prefixWord, tailWord_2702212, baseEnd_2702212] using wordTrace_append hprefix tailTrace_2702212
  have hstable : (prefixWord ++ tailWord_2702212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702212).length < 2 ^ (prefixWord ++ tailWord_2702212).sum := by decide
  have hdescent : baseEnd_2702212 < baseStart_2702212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702282 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 1, 7]
def baseStart_2702282 : Nat := 118140960795 + 2702282 * 2 ^ 59
def prefixEnd_2702282 : Nat := 4983230072969 + 3 ^ 40 * 2702282 * 2
def baseEnd_2702282 : Nat := 462523176664367180982479

theorem tailTrace_2702282 : CollatzResearch.WordTrace tailWord_2702282 prefixEnd_2702282 462523176664367180982479 := by
  unfold tailWord_2702282
  simp only [CollatzResearch.WordTrace]
  refine ⟨24640080399025325466945275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65706881064067534578520733 24640080399025325466945275)
  ·
    refine ⟨36960120598537988200417913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24640080399025325466945275 36960120598537988200417913)
    ·
      refine ⟨27720090448903491150313435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36960120598537988200417913 27720090448903491150313435)
      ·
        refine ⟨41580135673355236725470153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27720090448903491150313435 41580135673355236725470153)
        ·
          refine ⟨31185101755016427544102615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41580135673355236725470153 31185101755016427544102615)
          ·
            refine ⟨46777652632524641316153923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31185101755016427544102615 46777652632524641316153923)
            ·
              refine ⟨70166478948786961974230885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46777652632524641316153923 70166478948786961974230885)
              ·
                refine ⟨13156214802897555370168291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70166478948786961974230885 13156214802897555370168291)
                ·
                  refine ⟨19734322204346333055252437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13156214802897555370168291 19734322204346333055252437)
                  ·
                    refine ⟨462523176664367180982479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19734322204346333055252437 462523176664367180982479)
                    ·
                      rfl

theorem cell23_2702282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_2702282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702282 prefixEnd_2702282 := by exact prefixLift 2702282
  have htrace : WordTrace (prefixWord ++ tailWord_2702282) baseStart_2702282 baseEnd_2702282 := by
    simpa [prefixWord, tailWord_2702282, baseEnd_2702282] using wordTrace_append hprefix tailTrace_2702282
  have hstable : (prefixWord ++ tailWord_2702282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702282).length < 2 ^ (prefixWord ++ tailWord_2702282).sum := by decide
  have hdescent : baseEnd_2702282 < baseStart_2702282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702289 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 2, 5, 2]
def baseStart_2702289 : Nat := 118140960795 + 2702289 * 2 ^ 59
def prefixEnd_2702289 : Nat := 4983230072969 + 3 ^ 40 * 2702289 * 2
def baseEnd_2702289 : Nat := 1387573124357683015559905

theorem tailTrace_2702289 : CollatzResearch.WordTrace tailWord_2702289 prefixEnd_2702289 1387573124357683015559905 := by
  unfold tailWord_2702289
  simp only [CollatzResearch.WordTrace]
  refine ⟨98560576907075942063285921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65707051271383961375523947 98560576907075942063285921)
  ·
    refine ⟨73920432680306956547464441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98560576907075942063285921 73920432680306956547464441)
    ·
      refine ⟨55440324510230217410598331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73920432680306956547464441 55440324510230217410598331)
      ·
        refine ⟨83160486765345326115897497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55440324510230217410598331 83160486765345326115897497)
        ·
          refine ⟨62370365074008994586923123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83160486765345326115897497 62370365074008994586923123)
          ·
            refine ⟨93555547611013491880384685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62370365074008994586923123 93555547611013491880384685)
            ·
              refine ⟨35083330354130059455144257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93555547611013491880384685 35083330354130059455144257)
              ·
                refine ⟨26312497765597544591358193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35083330354130059455144257 26312497765597544591358193)
                ·
                  refine ⟨19734373324198158443518645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26312497765597544591358193 19734373324198158443518645)
                  ·
                    refine ⟨1850097499143577354079873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19734373324198158443518645 1850097499143577354079873)
                    ·
                      refine ⟨1387573124357683015559905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1850097499143577354079873 1387573124357683015559905)
                      ·
                        rfl

theorem cell23_2702289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 5, 2].length) (baseStart_2702289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702289 prefixEnd_2702289 := by exact prefixLift 2702289
  have htrace : WordTrace (prefixWord ++ tailWord_2702289) baseStart_2702289 baseEnd_2702289 := by
    simpa [prefixWord, tailWord_2702289, baseEnd_2702289] using wordTrace_append hprefix tailTrace_2702289
  have hstable : (prefixWord ++ tailWord_2702289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702289).length < 2 ^ (prefixWord ++ tailWord_2702289).sum := by decide
  have hdescent : baseEnd_2702289 < baseStart_2702289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702346 : List Nat := [3, 1, 2, 2, 3, 1, 2, 2, 3, 4]
def baseStart_2702346 : Nat := 118140960795 + 2702346 * 2 ^ 59
def prefixEnd_2702346 : Nat := 4983230072969 + 3 ^ 40 * 2702346 * 2
def baseEnd_2702346 : Nat := 462534130918329764182381

theorem tailTrace_2702346 : CollatzResearch.WordTrace tailWord_2702346 prefixEnd_2702346 462534130918329764182381 := by
  unfold tailWord_2702346
  simp only [CollatzResearch.WordTrace]
  refine ⟨24640663966967360199527723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65708437245246293865407261 24640663966967360199527723)
  ·
    refine ⟨36960995950451040299291585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24640663966967360199527723 36960995950451040299291585)
    ·
      refine ⟨27720746962838280224468689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36960995950451040299291585 27720746962838280224468689)
      ·
        refine ⟨20790560222128710168351517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27720746962838280224468689 20790560222128710168351517)
        ·
          refine ⟨7796460083298266313131819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20790560222128710168351517 7796460083298266313131819)
          ·
            refine ⟨11694690124947399469697729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7796460083298266313131819 11694690124947399469697729)
            ·
              refine ⟨8771017593710549602273297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11694690124947399469697729 8771017593710549602273297)
              ·
                refine ⟨6578263195282912201704973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8771017593710549602273297 6578263195282912201704973)
                ·
                  refine ⟨2466848698231092075639365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6578263195282912201704973 2466848698231092075639365)
                  ·
                    refine ⟨462534130918329764182381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2466848698231092075639365 462534130918329764182381)
                    ·
                      rfl

theorem cell23_2702346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_2702346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702346 prefixEnd_2702346 := by exact prefixLift 2702346
  have htrace : WordTrace (prefixWord ++ tailWord_2702346) baseStart_2702346 baseEnd_2702346 := by
    simpa [prefixWord, tailWord_2702346, baseEnd_2702346] using wordTrace_append hprefix tailTrace_2702346
  have hstable : (prefixWord ++ tailWord_2702346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702346).length < 2 ^ (prefixWord ++ tailWord_2702346).sum := by decide
  have hdescent : baseEnd_2702346 < baseStart_2702346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702354 : List Nat := [3, 2, 5, 1, 2, 1, 1, 3, 5]
def baseStart_2702354 : Nat := 118140960795 + 2702354 * 2 ^ 59
def prefixEnd_2702354 : Nat := 4983230072969 + 3 ^ 40 * 2702354 * 2
def baseEnd_2702354 : Nat := 154178500066691695694123

theorem tailTrace_2702354 : CollatzResearch.WordTrace tailWord_2702354 prefixEnd_2702354 154178500066691695694123 := by
  unfold tailWord_2702354
  simp only [CollatzResearch.WordTrace]
  refine ⟨24640736912960114541100529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65708631767893638776268077 24640736912960114541100529)
  ·
    refine ⟨18480552684720085905825397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24640736912960114541100529 18480552684720085905825397)
    ·
      refine ⟨1732551814192508053671131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18480552684720085905825397 1732551814192508053671131)
      ·
        refine ⟨2598827721288762080506697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1732551814192508053671131 2598827721288762080506697)
        ·
          refine ⟨1949120790966571560380023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2598827721288762080506697 1949120790966571560380023)
          ·
            refine ⟨2923681186449857340570035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1949120790966571560380023 2923681186449857340570035)
            ·
              refine ⟨4385521779674786010855053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923681186449857340570035 4385521779674786010855053)
              ·
                refine ⟨1644570667378044754070645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4385521779674786010855053 1644570667378044754070645)
                ·
                  refine ⟨154178500066691695694123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1644570667378044754070645 154178500066691695694123)
                  ·
                    rfl

theorem cell23_2702354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_2702354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702354 prefixEnd_2702354 := by exact prefixLift 2702354
  have htrace : WordTrace (prefixWord ++ tailWord_2702354) baseStart_2702354 baseEnd_2702354 := by
    simpa [prefixWord, tailWord_2702354, baseEnd_2702354] using wordTrace_append hprefix tailTrace_2702354
  have hstable : (prefixWord ++ tailWord_2702354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702354).length < 2 ^ (prefixWord ++ tailWord_2702354).sum := by decide
  have hdescent : baseEnd_2702354 < baseStart_2702354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702359 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 8]
def baseStart_2702359 : Nat := 118140960795 + 2702359 * 2 ^ 59
def prefixEnd_2702359 : Nat := 4983230072969 + 3 ^ 40 * 2702359 * 2
def baseEnd_2702359 : Nat := 154178785333721971298287

theorem tailTrace_2702359 : CollatzResearch.WordTrace tailWord_2702359 prefixEnd_2702359 154178785333721971298287 := by
  unfold tailWord_2702359
  simp only [CollatzResearch.WordTrace]
  refine ⟨98563130016822344018334131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65708753344548229345556087 98563130016822344018334131)
  ·
    refine ⟨147844695025233516027501197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98563130016822344018334131 147844695025233516027501197)
    ·
      refine ⟨55441760634462568510312949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147844695025233516027501197 55441760634462568510312949)
      ·
        refine ⟨5197665059480865797841839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55441760634462568510312949 5197665059480865797841839)
        ·
          refine ⟨7796497589221298696762759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5197665059480865797841839 7796497589221298696762759)
          ·
            refine ⟨11694746383831948045144139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7796497589221298696762759 11694746383831948045144139)
            ·
              refine ⟨17542119575747922067716209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11694746383831948045144139 17542119575747922067716209)
              ·
                refine ⟨13156589681810941550787157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17542119575747922067716209 13156589681810941550787157)
                ·
                  refine ⟨154178785333721971298287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13156589681810941550787157 154178785333721971298287)
                  ·
                    rfl

theorem cell23_2702359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 8].length) (baseStart_2702359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702359 prefixEnd_2702359 := by exact prefixLift 2702359
  have htrace : WordTrace (prefixWord ++ tailWord_2702359) baseStart_2702359 baseEnd_2702359 := by
    simpa [prefixWord, tailWord_2702359, baseEnd_2702359] using wordTrace_append hprefix tailTrace_2702359
  have hstable : (prefixWord ++ tailWord_2702359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702359).length < 2 ^ (prefixWord ++ tailWord_2702359).sum := by decide
  have hdescent : baseEnd_2702359 < baseStart_2702359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702389 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 3, 5]
def baseStart_2702389 : Nat := 118140960795 + 2702389 * 2 ^ 59
def prefixEnd_2702389 : Nat := 4983230072969 + 3 ^ 40 * 2702389 * 2
def baseEnd_2702389 : Nat := 462541490807710874769815

theorem tailTrace_2702389 : CollatzResearch.WordTrace tailWord_2702389 prefixEnd_2702389 462541490807710874769815 := by
  unfold tailWord_2702389
  simp only [CollatzResearch.WordTrace]
  refine ⟨98564224206713659141926221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65709482804475772761284147 98564224206713659141926221)
  ·
    refine ⟨36961584077517622178222333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98564224206713659141926221 36961584077517622178222333)
    ·
      refine ⟨13860594029069108316833375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36961584077517622178222333 13860594029069108316833375)
      ·
        refine ⟨20790891043603662475250063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13860594029069108316833375 20790891043603662475250063)
        ·
          refine ⟨31186336565405493712875095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20790891043603662475250063 31186336565405493712875095)
          ·
            refine ⟨46779504848108240569312643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31186336565405493712875095 46779504848108240569312643)
            ·
              refine ⟨70169257272162360853968965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46779504848108240569312643 70169257272162360853968965)
              ·
                refine ⟨13156735738530442660119181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70169257272162360853968965 13156735738530442660119181)
                ·
                  refine ⟨4933775901948915997544693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13156735738530442660119181 4933775901948915997544693)
                  ·
                    refine ⟨462541490807710874769815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4933775901948915997544693 462541490807710874769815)
                    ·
                      rfl

theorem cell23_2702389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_2702389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702389 prefixEnd_2702389 := by exact prefixLift 2702389
  have htrace : WordTrace (prefixWord ++ tailWord_2702389) baseStart_2702389 baseEnd_2702389 := by
    simpa [prefixWord, tailWord_2702389, baseEnd_2702389] using wordTrace_append hprefix tailTrace_2702389
  have hstable : (prefixWord ++ tailWord_2702389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702389).length < 2 ^ (prefixWord ++ tailWord_2702389).sum := by decide
  have hdescent : baseEnd_2702389 < baseStart_2702389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702393 : List Nat := [1, 2, 1, 5, 2, 3, 2, 1, 6]
def baseStart_2702393 : Nat := 118140960795 + 2702393 * 2 ^ 59
def prefixEnd_2702393 : Nat := 4983230072969 + 3 ^ 40 * 2702393 * 2
def baseEnd_2702393 : Nat := 154180725149527845406603

theorem tailTrace_2702393 : CollatzResearch.WordTrace tailWord_2702393 prefixEnd_2702393 154180725149527845406603 := by
  unfold tailWord_2702393
  simp only [CollatzResearch.WordTrace]
  refine ⟨98564370098699167825071833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65709580065799445216714555 98564370098699167825071833)
  ·
    refine ⟨73923277574024375868803875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98564370098699167825071833 73923277574024375868803875)
    ·
      refine ⟨110884916361036563803205813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73923277574024375868803875 110884916361036563803205813)
      ·
        refine ⟨10395460908847177856550545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110884916361036563803205813 10395460908847177856550545)
        ·
          refine ⟨7796595681635383392412909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10395460908847177856550545 7796595681635383392412909)
          ·
            refine ⟨2923723380613268772154841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7796595681635383392412909 2923723380613268772154841)
            ·
              refine ⟨2192792535459951579116131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2923723380613268772154841 2192792535459951579116131)
              ·
                refine ⟨3289188803189927368674197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2192792535459951579116131 3289188803189927368674197)
                ·
                  refine ⟨154180725149527845406603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3289188803189927368674197 154180725149527845406603)
                  ·
                    rfl

theorem cell23_2702393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 6].length) (baseStart_2702393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702393 prefixEnd_2702393 := by exact prefixLift 2702393
  have htrace : WordTrace (prefixWord ++ tailWord_2702393) baseStart_2702393 baseEnd_2702393 := by
    simpa [prefixWord, tailWord_2702393, baseEnd_2702393] using wordTrace_append hprefix tailTrace_2702393
  have hstable : (prefixWord ++ tailWord_2702393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702393).length < 2 ^ (prefixWord ++ tailWord_2702393).sum := by decide
  have hdescent : baseEnd_2702393 < baseStart_2702393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702493 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_2702493 : Nat := 118140960795 + 2702493 * 2 ^ 59
def prefixEnd_2702493 : Nat := 4983230072969 + 3 ^ 40 * 2702493 * 2
def baseEnd_2702493 : Nat := 1387677874411200217408967

theorem tailTrace_2702493 : CollatzResearch.WordTrace tailWord_2702493 prefixEnd_2702493 1387677874411200217408967 := by
  unfold tailWord_2702493
  simp only [CollatzResearch.WordTrace]
  refine ⟨98568017398336884903712133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65712011598891256602474755 98568017398336884903712133)
  ·
    refine ⟨18481503262188165919446025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98568017398336884903712133 18481503262188165919446025)
    ·
      refine ⟨13861127446641124439584519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18481503262188165919446025 13861127446641124439584519)
      ·
        refine ⟨20791691169961686659376779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13861127446641124439584519 20791691169961686659376779)
        ·
          refine ⟨31187536754942529989065169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20791691169961686659376779 31187536754942529989065169)
          ·
            refine ⟨23390652566206897491798877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31187536754942529989065169 23390652566206897491798877)
            ·
              refine ⟨8771494712327586559424579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23390652566206897491798877 8771494712327586559424579)
              ·
                refine ⟨13157242068491379839136869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8771494712327586559424579 13157242068491379839136869)
                ·
                  refine ⟨2466982887842133719838163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13157242068491379839136869 2466982887842133719838163)
                  ·
                    refine ⟨3700474331763200579757245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2466982887842133719838163 3700474331763200579757245)
                    ·
                      refine ⟨1387677874411200217408967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3700474331763200579757245 1387677874411200217408967)
                      ·
                        rfl

theorem cell23_2702493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_2702493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702493 prefixEnd_2702493 := by exact prefixLift 2702493
  have htrace : WordTrace (prefixWord ++ tailWord_2702493) baseStart_2702493 baseEnd_2702493 := by
    simpa [prefixWord, tailWord_2702493, baseEnd_2702493] using wordTrace_append hprefix tailTrace_2702493
  have hstable : (prefixWord ++ tailWord_2702493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702493).length < 2 ^ (prefixWord ++ tailWord_2702493).sum := by decide
  have hdescent : baseEnd_2702493 < baseStart_2702493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702494 : List Nat := [4, 3, 1, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_2702494 : Nat := 118140960795 + 2702494 * 2 ^ 59
def prefixEnd_2702494 : Nat := 4983230072969 + 3 ^ 40 * 2702494 * 2
def baseEnd_2702494 : Nat := 1387678387891854713496463

theorem tailTrace_2702494 : CollatzResearch.WordTrace tailWord_2702494 prefixEnd_2702494 1387678387891854713496463 := by
  unfold tailWord_2702494
  simp only [CollatzResearch.WordTrace]
  refine ⟨12321006733916657759312317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65712035914222174716332357 12321006733916657759312317)
  ·
    refine ⟨4620377525218746659742119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12321006733916657759312317 4620377525218746659742119)
    ·
      refine ⟨6930566287828119989613179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4620377525218746659742119 6930566287828119989613179)
      ·
        refine ⟨10395849431742179984419769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6930566287828119989613179 10395849431742179984419769)
        ·
          refine ⟨7796887073806634988314827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10395849431742179984419769 7796887073806634988314827)
          ·
            refine ⟨11695330610709952482472241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7796887073806634988314827 11695330610709952482472241)
            ·
              refine ⟨8771497958032464361854181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11695330610709952482472241 8771497958032464361854181)
              ·
                refine ⟨1644655867131087067847659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8771497958032464361854181 1644655867131087067847659)
                ·
                  refine ⟨2466983800696630601771489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644655867131087067847659 2466983800696630601771489)
                  ·
                    refine ⟨1850237850522472951328617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2466983800696630601771489 1850237850522472951328617)
                    ·
                      refine ⟨1387678387891854713496463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1850237850522472951328617 1387678387891854713496463)
                      ·
                        rfl

theorem cell23_2702494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_2702494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702494 prefixEnd_2702494 := by exact prefixLift 2702494
  have htrace : WordTrace (prefixWord ++ tailWord_2702494) baseStart_2702494 baseEnd_2702494 := by
    simpa [prefixWord, tailWord_2702494, baseEnd_2702494] using wordTrace_append hprefix tailTrace_2702494
  have hstable : (prefixWord ++ tailWord_2702494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702494).length < 2 ^ (prefixWord ++ tailWord_2702494).sum := by decide
  have hdescent : baseEnd_2702494 < baseStart_2702494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702499 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 4]
def baseStart_2702499 : Nat := 118140960795 + 2702499 * 2 ^ 59
def prefixEnd_2702499 : Nat := 4983230072969 + 3 ^ 40 * 2702499 * 2
def baseEnd_2702499 : Nat := 1387680955295127193933939

theorem tailTrace_2702499 : CollatzResearch.WordTrace tailWord_2702499 prefixEnd_2702499 1387680955295127193933939 := by
  unfold tailWord_2702499
  simp only [CollatzResearch.WordTrace]
  refine ⟨98568236236315147928430551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65712157490876765285620367 98568236236315147928430551)
  ·
    refine ⟨147852354354472721892645827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98568236236315147928430551 147852354354472721892645827)
    ·
      refine ⟨221778531531709082838968741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147852354354472721892645827 221778531531709082838968741)
      ·
        refine ⟨41583474662195453032306639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221778531531709082838968741 41583474662195453032306639)
        ·
          refine ⟨62375211993293179548459959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41583474662195453032306639 62375211993293179548459959)
          ·
            refine ⟨93562817989939769322689939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62375211993293179548459959 93562817989939769322689939)
            ·
              refine ⟨140344226984909653984034909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93562817989939769322689939 140344226984909653984034909)
              ·
                refine ⟨52629085119341120244013091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140344226984909653984034909 52629085119341120244013091)
                ·
                  refine ⟨78943627679011680366019637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52629085119341120244013091 78943627679011680366019637)
                  ·
                    refine ⟨7400965094907345034314341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78943627679011680366019637 7400965094907345034314341)
                    ·
                      refine ⟨1387680955295127193933939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7400965094907345034314341 1387680955295127193933939)
                      ·
                        rfl

theorem cell23_2702499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_2702499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702499 prefixEnd_2702499 := by exact prefixLift 2702499
  have htrace : WordTrace (prefixWord ++ tailWord_2702499) baseStart_2702499 baseEnd_2702499 := by
    simpa [prefixWord, tailWord_2702499, baseEnd_2702499] using wordTrace_append hprefix tailTrace_2702499
  have hstable : (prefixWord ++ tailWord_2702499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702499).length < 2 ^ (prefixWord ++ tailWord_2702499).sum := by decide
  have hdescent : baseEnd_2702499 < baseStart_2702499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702637 : List Nat := [1, 5, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_2702637 : Nat := 118140960795 + 2702637 * 2 ^ 59
def prefixEnd_2702637 : Nat := 4983230072969 + 3 ^ 40 * 2702637 * 2
def baseEnd_2702637 : Nat := 462583938541815884669435

theorem tailTrace_2702637 : CollatzResearch.WordTrace tailWord_2702637 prefixEnd_2702637 462583938541815884669435 := by
  unfold tailWord_2702637
  simp only [CollatzResearch.WordTrace]
  refine ⟨98573269509815197496954165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65715513006543464997969443 98573269509815197496954165)
  ·
    refine ⟨9241244016545174765339453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98573269509815197496954165 9241244016545174765339453)
    ·
      refine ⟨3465466506204440537002295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9241244016545174765339453 3465466506204440537002295)
      ·
        refine ⟨5198199759306660805503443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3465466506204440537002295 5198199759306660805503443)
        ·
          refine ⟨7797299638959991208255165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5198199759306660805503443 7797299638959991208255165)
          ·
            refine ⟨2923987364609996703095687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7797299638959991208255165 2923987364609996703095687)
            ·
              refine ⟨4385981046914995054643531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923987364609996703095687 4385981046914995054643531)
              ·
                refine ⟨6578971570372492581965297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4385981046914995054643531 6578971570372492581965297)
                ·
                  refine ⟨4934228677779369436473973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6578971570372492581965297 4934228677779369436473973)
                  ·
                    refine ⟨462583938541815884669435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4934228677779369436473973 462583938541815884669435)
                    ·
                      rfl

theorem cell23_2702637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_2702637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702637 prefixEnd_2702637 := by exact prefixLift 2702637
  have htrace : WordTrace (prefixWord ++ tailWord_2702637) baseStart_2702637 baseEnd_2702637 := by
    simpa [prefixWord, tailWord_2702637, baseEnd_2702637] using wordTrace_append hprefix tailTrace_2702637
  have hstable : (prefixWord ++ tailWord_2702637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702637).length < 2 ^ (prefixWord ++ tailWord_2702637).sum := by decide
  have hdescent : baseEnd_2702637 < baseStart_2702637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702643 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 3]
def baseStart_2702643 : Nat := 118140960795 + 2702643 * 2 ^ 59
def prefixEnd_2702643 : Nat := 4983230072969 + 3 ^ 40 * 2702643 * 2
def baseEnd_2702643 : Nat := 1387754896509374630533277

theorem tailTrace_2702643 : CollatzResearch.WordTrace tailWord_2702643 prefixEnd_2702643 1387754896509374630533277 := by
  unfold tailWord_2702643
  simp only [CollatzResearch.WordTrace]
  refine ⟨98573488347793460521672583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65715658898528973681115055 98573488347793460521672583)
  ·
    refine ⟨147860232521690190782508875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98573488347793460521672583 147860232521690190782508875)
    ·
      refine ⟨221790348782535286173763313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147860232521690190782508875 221790348782535286173763313)
      ·
        refine ⟨166342761586901464630322485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221790348782535286173763313 166342761586901464630322485)
        ·
          refine ⟨15594633898772012309092733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166342761586901464630322485 15594633898772012309092733)
          ·
            refine ⟨5847987712039504615909775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15594633898772012309092733 5847987712039504615909775)
            ·
              refine ⟨8771981568059256923864663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5847987712039504615909775 8771981568059256923864663)
              ·
                refine ⟨13157972352088885385796995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8771981568059256923864663 13157972352088885385796995)
                ·
                  refine ⟨19736958528133328078695493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13157972352088885385796995 19736958528133328078695493)
                  ·
                    refine ⟨3700679724024999014755405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19736958528133328078695493 3700679724024999014755405)
                    ·
                      refine ⟨1387754896509374630533277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3700679724024999014755405 1387754896509374630533277)
                      ·
                        rfl

theorem cell23_2702643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 3].length) (baseStart_2702643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702643 prefixEnd_2702643 := by exact prefixLift 2702643
  have htrace : WordTrace (prefixWord ++ tailWord_2702643) baseStart_2702643 baseEnd_2702643 := by
    simpa [prefixWord, tailWord_2702643, baseEnd_2702643] using wordTrace_append hprefix tailTrace_2702643
  have hstable : (prefixWord ++ tailWord_2702643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702643).length < 2 ^ (prefixWord ++ tailWord_2702643).sum := by decide
  have hdescent : baseEnd_2702643 < baseStart_2702643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702663 : List Nat := [1, 1, 4, 1, 2, 3, 3, 2, 6]
def baseStart_2702663 : Nat := 118140960795 + 2702663 * 2 ^ 59
def prefixEnd_2702663 : Nat := 4983230072969 + 3 ^ 40 * 2702663 * 2
def baseEnd_2702663 : Nat := 154196129569162728031465

theorem tailTrace_2702663 : CollatzResearch.WordTrace tailWord_2702663 prefixEnd_2702663 154196129569162728031465 := by
  unfold tailWord_2702663
  simp only [CollatzResearch.WordTrace]
  refine ⟨98574217807721003937400643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65716145205147335958267095 98574217807721003937400643)
  ·
    refine ⟨147861326711581505906100965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98574217807721003937400643 147861326711581505906100965)
    ·
      refine ⟨27723998758421532357393931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147861326711581505906100965 27723998758421532357393931)
      ·
        refine ⟨41585998137632298536090897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27723998758421532357393931 41585998137632298536090897)
        ·
          refine ⟨31189498603224223902068173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41585998137632298536090897 31189498603224223902068173)
          ·
            refine ⟨11696061976209083963275565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31189498603224223902068173 11696061976209083963275565)
            ·
              refine ⟨4386023241078406486228337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11696061976209083963275565 4386023241078406486228337)
              ·
                refine ⟨3289517430808804864671253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4386023241078406486228337 3289517430808804864671253)
                ·
                  refine ⟨154196129569162728031465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3289517430808804864671253 154196129569162728031465)
                  ·
                    rfl

theorem cell23_2702663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 6].length) (baseStart_2702663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702663 prefixEnd_2702663 := by exact prefixLift 2702663
  have htrace : WordTrace (prefixWord ++ tailWord_2702663) baseStart_2702663 baseEnd_2702663 := by
    simpa [prefixWord, tailWord_2702663, baseEnd_2702663] using wordTrace_append hprefix tailTrace_2702663
  have hstable : (prefixWord ++ tailWord_2702663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702663).length < 2 ^ (prefixWord ++ tailWord_2702663).sum := by decide
  have hdescent : baseEnd_2702663 < baseStart_2702663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702700 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 1, 5, 2]
def baseStart_2702700 : Nat := 118140960795 + 2702700 * 2 ^ 59
def prefixEnd_2702700 : Nat := 4983230072969 + 3 ^ 40 * 2702700 * 2
def baseEnd_2702700 : Nat := 1387784164906680907520515

theorem tailTrace_2702700 : CollatzResearch.WordTrace tailWord_2702700 prefixEnd_2702700 1387784164906680907520515 := by
  unfold tailWord_2702700
  simp only [CollatzResearch.WordTrace]
  refine ⟨49287783654293479628248777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65717044872391306170998369 49287783654293479628248777)
  ·
    refine ⟨36965837740720109721186583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49287783654293479628248777 36965837740720109721186583)
    ·
      refine ⟨55448756611080164581779875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36965837740720109721186583 55448756611080164581779875)
      ·
        refine ⟨83173134916620246872669813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55448756611080164581779875 83173134916620246872669813)
        ·
          refine ⟨7797481398433148144312795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83173134916620246872669813 7797481398433148144312795)
          ·
            refine ⟨11696222097649722216469193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7797481398433148144312795 11696222097649722216469193)
            ·
              refine ⟨8772166573237291662351895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11696222097649722216469193 8772166573237291662351895)
              ·
                refine ⟨13158249859855937493527843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8772166573237291662351895 13158249859855937493527843)
                ·
                  refine ⟨19737374789783906240291765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13158249859855937493527843 19737374789783906240291765)
                  ·
                    refine ⟨1850378886542241210027353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19737374789783906240291765 1850378886542241210027353)
                    ·
                      refine ⟨1387784164906680907520515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1850378886542241210027353 1387784164906680907520515)
                      ·
                        rfl

theorem cell23_2702700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 5, 2].length) (baseStart_2702700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702700 prefixEnd_2702700 := by exact prefixLift 2702700
  have htrace : WordTrace (prefixWord ++ tailWord_2702700) baseStart_2702700 baseEnd_2702700 := by
    simpa [prefixWord, tailWord_2702700, baseEnd_2702700] using wordTrace_append hprefix tailTrace_2702700
  have hstable : (prefixWord ++ tailWord_2702700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702700).length < 2 ^ (prefixWord ++ tailWord_2702700).sum := by decide
  have hdescent : baseEnd_2702700 < baseStart_2702700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702718 : List Nat := [4, 2, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2702718 : Nat := 118140960795 + 2702718 * 2 ^ 59
def prefixEnd_2702718 : Nat := 4983230072969 + 3 ^ 40 * 2702718 * 2
def baseEnd_2702718 : Nat := 462597802519487279031811

theorem tailTrace_2702718 : CollatzResearch.WordTrace tailWord_2702718 prefixEnd_2702718 462597802519487279031811 := by
  unfold tailWord_2702718
  simp only [CollatzResearch.WordTrace]
  refine ⟨12322027977815218541331601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65717482548347832220435205 12322027977815218541331601)
  ·
    refine ⟨9241520983361413905998701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12322027977815218541331601 9241520983361413905998701)
    ·
      refine ⟨3465570368760530214749513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9241520983361413905998701 3465570368760530214749513)
      ·
        refine ⟨2599177776570397661062135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3465570368760530214749513 2599177776570397661062135)
        ·
          refine ⟨3898766664855596491593203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2599177776570397661062135 3898766664855596491593203)
          ·
            refine ⟨5848149997283394737389805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3898766664855596491593203 5848149997283394737389805)
            ·
              refine ⟨2193056248981273026521177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5848149997283394737389805 2193056248981273026521177)
              ·
                refine ⟨1644792186735954769890883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2193056248981273026521177 1644792186735954769890883)
                ·
                  refine ⟨2467188280103932154836325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644792186735954769890883 2467188280103932154836325)
                  ·
                    refine ⟨462597802519487279031811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2467188280103932154836325 462597802519487279031811)
                    ·
                      rfl

theorem cell23_2702718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2702718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702718 prefixEnd_2702718 := by exact prefixLift 2702718
  have htrace : WordTrace (prefixWord ++ tailWord_2702718) baseStart_2702718 baseEnd_2702718 := by
    simpa [prefixWord, tailWord_2702718, baseEnd_2702718] using wordTrace_append hprefix tailTrace_2702718
  have hstable : (prefixWord ++ tailWord_2702718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702718).length < 2 ^ (prefixWord ++ tailWord_2702718).sum := by decide
  have hdescent : baseEnd_2702718 < baseStart_2702718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702743 : List Nat := [1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 4]
def baseStart_2702743 : Nat := 118140960795 + 2702743 * 2 ^ 59
def prefixEnd_2702743 : Nat := 4983230072969 + 3 ^ 40 * 2702743 * 2
def baseEnd_2702743 : Nat := 1387806244574824239282817

theorem tailTrace_2702743 : CollatzResearch.WordTrace tailWord_2702743 prefixEnd_2702743 1387806244574824239282817 := by
  unfold tailWord_2702743
  simp only [CollatzResearch.WordTrace]
  refine ⟨98577135647431177600312883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65718090431620785066875255 98577135647431177600312883)
  ·
    refine ⟨147865703471146766400469325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98577135647431177600312883 147865703471146766400469325)
    ·
      refine ⟨55449638801680037400175997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147865703471146766400469325 55449638801680037400175997)
      ·
        refine ⟨20793614550630014025065999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55449638801680037400175997 20793614550630014025065999)
        ·
          refine ⟨31190421825945021037598999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20793614550630014025065999 31190421825945021037598999)
          ·
            refine ⟨46785632738917531556398499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31190421825945021037598999 46785632738917531556398499)
            ·
              refine ⟨70178449108376297334597749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46785632738917531556398499 70178449108376297334597749)
              ·
                refine ⟨6579229603910277875118539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70178449108376297334597749 6579229603910277875118539)
                ·
                  refine ⟨9868844405865416812677809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6579229603910277875118539 9868844405865416812677809)
                  ·
                    refine ⟨7401633304399062609508357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9868844405865416812677809 7401633304399062609508357)
                    ·
                      refine ⟨1387806244574824239282817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7401633304399062609508357 1387806244574824239282817)
                      ·
                        rfl

theorem cell23_2702743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_2702743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702743 prefixEnd_2702743 := by exact prefixLift 2702743
  have htrace : WordTrace (prefixWord ++ tailWord_2702743) baseStart_2702743 baseEnd_2702743 := by
    simpa [prefixWord, tailWord_2702743, baseEnd_2702743] using wordTrace_append hprefix tailTrace_2702743
  have hstable : (prefixWord ++ tailWord_2702743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702743).length < 2 ^ (prefixWord ++ tailWord_2702743).sum := by decide
  have hdescent : baseEnd_2702743 < baseStart_2702743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702744 : List Nat := [2, 1, 2, 5, 3, 1, 1, 2, 1, 5]
def baseStart_2702744 : Nat := 118140960795 + 2702744 * 2 ^ 59
def prefixEnd_2702744 : Nat := 4983230072969 + 3 ^ 40 * 2702744 * 2
def baseEnd_2702744 : Nat := 462602252685159578456771

theorem tailTrace_2702744 : CollatzResearch.WordTrace tailWord_2702744 prefixEnd_2702744 462602252685159578456771 := by
  unfold tailWord_2702744
  simp only [CollatzResearch.WordTrace]
  refine ⟨49288586060213777385549643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65718114746951703180732857 49288586060213777385549643)
  ·
    refine ⟨73932879090320666078324465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49288586060213777385549643 73932879090320666078324465)
    ·
      refine ⟨55449659317740499558743349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73932879090320666078324465 55449659317740499558743349)
      ·
        refine ⟨5198405561038171833632189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55449659317740499558743349 5198405561038171833632189)
        ·
          refine ⟨1949402085389314437612071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5198405561038171833632189 1949402085389314437612071)
          ·
            refine ⟨2924103128083971656418107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1949402085389314437612071 2924103128083971656418107)
            ·
              refine ⟨4386154692125957484627161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2924103128083971656418107 4386154692125957484627161)
              ·
                refine ⟨3289616019094468113470371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4386154692125957484627161 3289616019094468113470371)
                ·
                  refine ⟨4934424028641702170205557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3289616019094468113470371 4934424028641702170205557)
                  ·
                    refine ⟨462602252685159578456771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4934424028641702170205557 462602252685159578456771)
                    ·
                      rfl

theorem cell23_2702744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 1, 5].length) (baseStart_2702744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702744 prefixEnd_2702744 := by exact prefixLift 2702744
  have htrace : WordTrace (prefixWord ++ tailWord_2702744) baseStart_2702744 baseEnd_2702744 := by
    simpa [prefixWord, tailWord_2702744, baseEnd_2702744] using wordTrace_append hprefix tailTrace_2702744
  have hstable : (prefixWord ++ tailWord_2702744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702744).length < 2 ^ (prefixWord ++ tailWord_2702744).sum := by decide
  have hdescent : baseEnd_2702744 < baseStart_2702744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702923 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 6]
def baseStart_2702923 : Nat := 118140960795 + 2702923 * 2 ^ 59
def prefixEnd_2702923 : Nat := 4983230072969 + 3 ^ 40 * 2702923 * 2
def baseEnd_2702923 : Nat := 1387898671092633535031989

theorem tailTrace_2702923 : CollatzResearch.WordTrace tailWord_2702923 prefixEnd_2702923 1387898671092633535031989 := by
  unfold tailWord_2702923
  simp only [CollatzResearch.WordTrace]
  refine ⟨98583700786779068341865423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65722467191186045561243615 98583700786779068341865423)
  ·
    refine ⟨147875551180168602512798135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98583700786779068341865423 147875551180168602512798135)
    ·
      refine ⟨221813326770252903769197203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147875551180168602512798135 221813326770252903769197203)
      ·
        refine ⟨332719990155379355653795805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221813326770252903769197203 332719990155379355653795805)
        ·
          refine ⟨124769996308267258370173427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332719990155379355653795805 124769996308267258370173427)
          ·
            refine ⟨187154994462400887555260141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124769996308267258370173427 187154994462400887555260141)
            ·
              refine ⟨70183122923400332833222553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187154994462400887555260141 70183122923400332833222553)
              ·
                refine ⟨52637342192550249624916915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70183122923400332833222553 52637342192550249624916915)
                ·
                  refine ⟨78956013288825374437375373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52637342192550249624916915 78956013288825374437375373)
                  ·
                    refine ⟨29608504983309515414015765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78956013288825374437375373 29608504983309515414015765)
                    ·
                      refine ⟨1387898671092633535031989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29608504983309515414015765 1387898671092633535031989)
                      ·
                        rfl

theorem cell23_2702923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 6].length) (baseStart_2702923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702923 prefixEnd_2702923 := by exact prefixLift 2702923
  have htrace : WordTrace (prefixWord ++ tailWord_2702923) baseStart_2702923 baseEnd_2702923 := by
    simpa [prefixWord, tailWord_2702923, baseEnd_2702923] using wordTrace_append hprefix tailTrace_2702923
  have hstable : (prefixWord ++ tailWord_2702923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702923).length < 2 ^ (prefixWord ++ tailWord_2702923).sum := by decide
  have hdescent : baseEnd_2702923 < baseStart_2702923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702947 : List Nat := [1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 3]
def baseStart_2702947 : Nat := 118140960795 + 2702947 * 2 ^ 59
def prefixEnd_2702947 : Nat := 4983230072969 + 3 ^ 40 * 2702947 * 2
def baseEnd_2702947 : Nat := 1387910994628341441131879

theorem tailTrace_2702947 : CollatzResearch.WordTrace tailWord_2702947 prefixEnd_2702947 1387910994628341441131879 := by
  unfold tailWord_2702947
  simp only [CollatzResearch.WordTrace]
  refine ⟨98584576138692120440739095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65723050759128080293826063 98584576138692120440739095)
  ·
    refine ⟨147876864208038180661108643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98584576138692120440739095 147876864208038180661108643)
    ·
      refine ⟨221815296312057270991662965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147876864208038180661108643 221815296312057270991662965)
      ·
        refine ⟨20795184029255369155468403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 221815296312057270991662965 20795184029255369155468403)
        ·
          refine ⟨31192776043883053733202605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20795184029255369155468403 31192776043883053733202605)
          ·
            refine ⟨11697291016456145149950977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31192776043883053733202605 11697291016456145149950977)
            ·
              refine ⟨8772968262342108862463233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11697291016456145149950977 8772968262342108862463233)
              ·
                refine ⟨6579726196756581646847425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8772968262342108862463233 6579726196756581646847425)
                ·
                  refine ⟨4934794647567436235135569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6579726196756581646847425 4934794647567436235135569)
                  ·
                    refine ⟨3701095985675577176351677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4934794647567436235135569 3701095985675577176351677)
                    ·
                      refine ⟨1387910994628341441131879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3701095985675577176351677 1387910994628341441131879)
                      ·
                        rfl

theorem cell23_2702947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_2702947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702947 prefixEnd_2702947 := by exact prefixLift 2702947
  have htrace : WordTrace (prefixWord ++ tailWord_2702947) baseStart_2702947 baseEnd_2702947 := by
    simpa [prefixWord, tailWord_2702947, baseEnd_2702947] using wordTrace_append hprefix tailTrace_2702947
  have hstable : (prefixWord ++ tailWord_2702947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702947).length < 2 ^ (prefixWord ++ tailWord_2702947).sum := by decide
  have hdescent : baseEnd_2702947 < baseStart_2702947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702987 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 1, 5, 2]
def baseStart_2702987 : Nat := 118140960795 + 2702987 * 2 ^ 59
def prefixEnd_2702987 : Nat := 4983230072969 + 3 ^ 40 * 2702987 * 2
def baseEnd_2702987 : Nat := 1387931533854521284631695

theorem tailTrace_2702987 : CollatzResearch.WordTrace tailWord_2702987 prefixEnd_2702987 1387931533854521284631695 := by
  unfold tailWord_2702987
  simp only [CollatzResearch.WordTrace]
  refine ⟨98586035058547207272195215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65724023372364804848130143 98586035058547207272195215)
  ·
    refine ⟨147879052587820810908292823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98586035058547207272195215 147879052587820810908292823)
    ·
      refine ⟨221818578881731216362439235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147879052587820810908292823 221818578881731216362439235)
      ·
        refine ⟨332727868322596824543658853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221818578881731216362439235 332727868322596824543658853)
        ·
          refine ⟨62386475310486904601936035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 332727868322596824543658853 62386475310486904601936035)
          ·
            refine ⟨93579712965730356902904053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62386475310486904601936035 93579712965730356902904053)
            ·
              refine ⟨8773098090537220959647255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93579712965730356902904053 8773098090537220959647255)
              ·
                refine ⟨13159647135805831439470883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8773098090537220959647255 13159647135805831439470883)
                ·
                  refine ⟨19739470703708747159206325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13159647135805831439470883 19739470703708747159206325)
                  ·
                    refine ⟨1850575378472695046175593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19739470703708747159206325 1850575378472695046175593)
                    ·
                      refine ⟨1387931533854521284631695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1850575378472695046175593 1387931533854521284631695)
                      ·
                        rfl

theorem cell23_2702987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 5, 2].length) (baseStart_2702987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2702987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2702987 prefixEnd_2702987 := by exact prefixLift 2702987
  have htrace : WordTrace (prefixWord ++ tailWord_2702987) baseStart_2702987 baseEnd_2702987 := by
    simpa [prefixWord, tailWord_2702987, baseEnd_2702987] using wordTrace_append hprefix tailTrace_2702987
  have hstable : (prefixWord ++ tailWord_2702987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702987).length < 2 ^ (prefixWord ++ tailWord_2702987).sum := by decide
  have hdescent : baseEnd_2702987 < baseStart_2702987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703034 : List Nat := [3, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4]
def baseStart_2703034 : Nat := 118140960795 + 2703034 * 2 ^ 59
def prefixEnd_2703034 : Nat := 4983230072969 + 3 ^ 40 * 2703034 * 2
def baseEnd_2703034 : Nat := 1387955667445282600743979

theorem tailTrace_2703034 : CollatzResearch.WordTrace tailWord_2703034 prefixEnd_2703034 1387955667445282600743979 := by
  unfold tailWord_2703034
  simp only [CollatzResearch.WordTrace]
  refine ⟨24646937322344233574789039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65725166192917956199437437 24646937322344233574789039)
  ·
    refine ⟨36970405983516350362183559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24646937322344233574789039 36970405983516350362183559)
    ·
      refine ⟨55455608975274525543275339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36970405983516350362183559 55455608975274525543275339)
      ·
        refine ⟨83183413462911788314913009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55455608975274525543275339 83183413462911788314913009)
        ·
          refine ⟨62387560097183841236184757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83183413462911788314913009 62387560097183841236184757)
          ·
            refine ⟨5848833759110985115892321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62387560097183841236184757 5848833759110985115892321)
            ·
              refine ⟨4386625319333238836919241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5848833759110985115892321 4386625319333238836919241)
              ·
                refine ⟨3289968989499929127689431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4386625319333238836919241 3289968989499929127689431)
                ·
                  refine ⟨4934953484249893691534147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3289968989499929127689431 4934953484249893691534147)
                  ·
                    refine ⟨7402430226374840537301221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4934953484249893691534147 7402430226374840537301221)
                    ·
                      refine ⟨1387955667445282600743979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7402430226374840537301221 1387955667445282600743979)
                      ·
                        rfl

theorem cell23_2703034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4].length) (baseStart_2703034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703034 prefixEnd_2703034 := by exact prefixLift 2703034
  have htrace : WordTrace (prefixWord ++ tailWord_2703034) baseStart_2703034 baseEnd_2703034 := by
    simpa [prefixWord, tailWord_2703034, baseEnd_2703034] using wordTrace_append hprefix tailTrace_2703034
  have hstable : (prefixWord ++ tailWord_2703034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703034).length < 2 ^ (prefixWord ++ tailWord_2703034).sum := by decide
  have hdescent : baseEnd_2703034 < baseStart_2703034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703040 : List Nat := [2, 1, 1, 2, 4, 1, 3, 9]
def baseStart_2703040 : Nat := 118140960795 + 2703040 * 2 ^ 59
def prefixEnd_2703040 : Nat := 4983230072969 + 3 ^ 40 * 2703040 * 2
def baseEnd_2703040 : Nat := 51405879567748502861813

theorem tailTrace_2703040 : CollatzResearch.WordTrace tailWord_2703040 prefixEnd_2703040 51405879567748502861813 := by
  unfold tailWord_2703040
  simp only [CollatzResearch.WordTrace]
  refine ⟨49293984063677598661937287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65725312084903464882583049 49293984063677598661937287)
  ·
    refine ⟨73940976095516397992905931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49293984063677598661937287 73940976095516397992905931)
    ·
      refine ⟨110911464143274596989358897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73940976095516397992905931 110911464143274596989358897)
      ·
        refine ⟨83183598107455947742019173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110911464143274596989358897 83183598107455947742019173)
        ·
          refine ⟨15596924645147990201628595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83183598107455947742019173 15596924645147990201628595)
          ·
            refine ⟨23395386967721985302442893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15596924645147990201628595 23395386967721985302442893)
            ·
              refine ⟨8773270112895744488416085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23395386967721985302442893 8773270112895744488416085)
              ·
                refine ⟨51405879567748502861813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8773270112895744488416085 51405879567748502861813)
                ·
                  rfl

theorem cell23_2703040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 9].length) (baseStart_2703040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703040 prefixEnd_2703040 := by exact prefixLift 2703040
  have htrace : WordTrace (prefixWord ++ tailWord_2703040) baseStart_2703040 baseEnd_2703040 := by
    simpa [prefixWord, tailWord_2703040, baseEnd_2703040] using wordTrace_append hprefix tailTrace_2703040
  have hstable : (prefixWord ++ tailWord_2703040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703040).length < 2 ^ (prefixWord ++ tailWord_2703040).sum := by decide
  have hdescent : baseEnd_2703040 < baseStart_2703040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703054 : List Nat := [4, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3]
def baseStart_2703054 : Nat := 118140960795 + 2703054 * 2 ^ 59
def prefixEnd_2703054 : Nat := 4983230072969 + 3 ^ 40 * 2703054 * 2
def baseEnd_2703054 : Nat := 1387965937058372522493887

theorem tailTrace_2703054 : CollatzResearch.WordTrace tailWord_2703054 prefixEnd_2703054 1387965937058372522493887 := by
  unfold tailWord_2703054
  simp only [CollatzResearch.WordTrace]
  refine ⟨12323559843663059714360527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65725652499536318476589477 12323559843663059714360527)
  ·
    refine ⟨18485339765494589571540791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12323559843663059714360527 18485339765494589571540791)
    ·
      refine ⟨27728009648241884357311187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18485339765494589571540791 27728009648241884357311187)
      ·
        refine ⟨41592014472362826535966781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27728009648241884357311187 41592014472362826535966781)
        ·
          refine ⟨15597005427136059950987543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41592014472362826535966781 15597005427136059950987543)
          ·
            refine ⟨23395508140704089926481315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15597005427136059950987543 23395508140704089926481315)
            ·
              refine ⟨35093262211056134889721973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23395508140704089926481315 35093262211056134889721973)
              ·
                refine ⟨3289993332286512645911435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35093262211056134889721973 3289993332286512645911435)
                ·
                  refine ⟨4934989998429768968867153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3289993332286512645911435 4934989998429768968867153)
                  ·
                    refine ⟨3701242498822326726650365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4934989998429768968867153 3701242498822326726650365)
                    ·
                      refine ⟨1387965937058372522493887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3701242498822326726650365 1387965937058372522493887)
                      ·
                        rfl

theorem cell23_2703054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_2703054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703054 prefixEnd_2703054 := by exact prefixLift 2703054
  have htrace : WordTrace (prefixWord ++ tailWord_2703054) baseStart_2703054 baseEnd_2703054 := by
    simpa [prefixWord, tailWord_2703054, baseEnd_2703054] using wordTrace_append hprefix tailTrace_2703054
  have hstable : (prefixWord ++ tailWord_2703054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703054).length < 2 ^ (prefixWord ++ tailWord_2703054).sum := by decide
  have hdescent : baseEnd_2703054 < baseStart_2703054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703062 : List Nat := [5, 2, 1, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_2703062 : Nat := 118140960795 + 2703062 * 2 ^ 59
def prefixEnd_2703062 : Nat := 4983230072969 + 3 ^ 40 * 2703062 * 2
def baseEnd_2703062 : Nat := 1387970044903608491193851

theorem tailTrace_2703062 : CollatzResearch.WordTrace tailWord_2703062 prefixEnd_2703062 1387970044903608491193851 := by
  unfold tailWord_2703062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6161798158329718442573465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65725847022183663387450293 6161798158329718442573465)
  ·
    refine ⟨4621348618747288831930099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6161798158329718442573465 4621348618747288831930099)
    ·
      refine ⟨6932022928120933247895149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4621348618747288831930099 6932022928120933247895149)
      ·
        refine ⟨2599508598045349967960681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6932022928120933247895149 2599508598045349967960681)
        ·
          refine ⟨1949631448534012475970511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2599508598045349967960681 1949631448534012475970511)
          ·
            refine ⟨2924447172801018713955767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1949631448534012475970511 2924447172801018713955767)
            ·
              refine ⟨4386670759201528070933651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2924447172801018713955767 4386670759201528070933651)
              ·
                refine ⟨6580006138802292106400477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4386670759201528070933651 6580006138802292106400477)
                ·
                  refine ⟨2467502302050859539900179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6580006138802292106400477 2467502302050859539900179)
                  ·
                    refine ⟨3701253453076289309850269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2467502302050859539900179 3701253453076289309850269)
                    ·
                      refine ⟨1387970044903608491193851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3701253453076289309850269 1387970044903608491193851)
                      ·
                        rfl

theorem cell23_2703062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_2703062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703062 prefixEnd_2703062 := by exact prefixLift 2703062
  have htrace : WordTrace (prefixWord ++ tailWord_2703062) baseStart_2703062 baseEnd_2703062 := by
    simpa [prefixWord, tailWord_2703062, baseEnd_2703062] using wordTrace_append hprefix tailTrace_2703062
  have hstable : (prefixWord ++ tailWord_2703062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703062).length < 2 ^ (prefixWord ++ tailWord_2703062).sum := by decide
  have hdescent : baseEnd_2703062 < baseStart_2703062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703137 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_2703137 : Nat := 118140960795 + 2703137 * 2 ^ 59
def prefixEnd_2703137 : Nat := 4983230072969 + 3 ^ 40 * 2703137 * 2
def baseEnd_2703137 : Nat := 1388008555952695697756005

theorem tailTrace_2703137 : CollatzResearch.WordTrace tailWord_2703137 prefixEnd_2703137 1388008555952695697756005 := by
  unfold tailWord_2703137
  simp only [CollatzResearch.WordTrace]
  refine ⟨98591506008003782890155665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65727670672002521926770443 98591506008003782890155665)
  ·
    refine ⟨73943629506002837167616749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98591506008003782890155665 73943629506002837167616749)
    ·
      refine ⟨27728861064751063937856281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73943629506002837167616749 27728861064751063937856281)
      ·
        refine ⟨20796645798563297953392211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27728861064751063937856281 20796645798563297953392211)
        ·
          refine ⟨31194968697844946930088317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20796645798563297953392211 31194968697844946930088317)
          ·
            refine ⟨11698113261691855098783119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31194968697844946930088317 11698113261691855098783119)
            ·
              refine ⟨17547169892537782648174679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11698113261691855098783119 17547169892537782648174679)
              ·
                refine ⟨26320754838806673972262019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17547169892537782648174679 26320754838806673972262019)
                ·
                  refine ⟨39481132258210010958393029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26320754838806673972262019 39481132258210010958393029)
                  ·
                    refine ⟨7402712298414377054698693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39481132258210010958393029 7402712298414377054698693)
                    ·
                      refine ⟨1388008555952695697756005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7402712298414377054698693 1388008555952695697756005)
                      ·
                        rfl

theorem cell23_2703137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_2703137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703137 prefixEnd_2703137 := by exact prefixLift 2703137
  have htrace : WordTrace (prefixWord ++ tailWord_2703137) baseStart_2703137 baseEnd_2703137 := by
    simpa [prefixWord, tailWord_2703137, baseEnd_2703137] using wordTrace_append hprefix tailTrace_2703137
  have hstable : (prefixWord ++ tailWord_2703137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703137).length < 2 ^ (prefixWord ++ tailWord_2703137).sum := by decide
  have hdescent : baseEnd_2703137 < baseStart_2703137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703141 : List Nat := [1, 3, 1, 2, 3, 3, 2, 1, 1, 4, 2]
def baseStart_2703141 : Nat := 118140960795 + 2703141 * 2 ^ 59
def prefixEnd_2703141 : Nat := 4983230072969 + 3 ^ 40 * 2703141 * 2
def baseEnd_2703141 : Nat := 1388010609875313682105987

theorem tailTrace_2703141 : CollatzResearch.WordTrace tailWord_2703141 prefixEnd_2703141 1388010609875313682105987 := by
  unfold tailWord_2703141
  simp only [CollatzResearch.WordTrace]
  refine ⟨98591651899989291573301277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65727767933326194382200851 98591651899989291573301277)
  ·
    refine ⟨36971869462495984339987979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98591651899989291573301277 36971869462495984339987979)
    ·
      refine ⟨55457804193743976509981969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36971869462495984339987979 55457804193743976509981969)
      ·
        refine ⟨41593353145307982382486477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55457804193743976509981969 41593353145307982382486477)
        ·
          refine ⟨15597507429490493393432429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41593353145307982382486477 15597507429490493393432429)
          ·
            refine ⟨5849065286058935022537161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15597507429490493393432429 5849065286058935022537161)
            ·
              refine ⟨4386798964544201266902871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5849065286058935022537161 4386798964544201266902871)
              ·
                refine ⟨6580198446816301900354307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4386798964544201266902871 6580198446816301900354307)
                ·
                  refine ⟨9870297670224452850531461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6580198446816301900354307 9870297670224452850531461)
                  ·
                    refine ⟨1850680813167084909474649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9870297670224452850531461 1850680813167084909474649)
                    ·
                      refine ⟨1388010609875313682105987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1850680813167084909474649 1388010609875313682105987)
                      ·
                        rfl

theorem cell23_2703141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_2703141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703141 prefixEnd_2703141 := by exact prefixLift 2703141
  have htrace : WordTrace (prefixWord ++ tailWord_2703141) baseStart_2703141 baseEnd_2703141 := by
    simpa [prefixWord, tailWord_2703141, baseEnd_2703141] using wordTrace_append hprefix tailTrace_2703141
  have hstable : (prefixWord ++ tailWord_2703141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703141).length < 2 ^ (prefixWord ++ tailWord_2703141).sum := by decide
  have hdescent : baseEnd_2703141 < baseStart_2703141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703158 : List Nat := [5, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_2703158 : Nat := 118140960795 + 2703158 * 2 ^ 59
def prefixEnd_2703158 : Nat := 4983230072969 + 3 ^ 40 * 2703158 * 2
def baseEnd_2703158 : Nat := 1388019339046440115593409

theorem tailTrace_2703158 : CollatzResearch.WordTrace tailWord_2703158 prefixEnd_2703158 1388019339046440115593409 := by
  unfold tailWord_2703158
  simp only [CollatzResearch.WordTrace]
  refine ⟨6162016996307981467291883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65728181293951802317780085 6162016996307981467291883)
  ·
    refine ⟨9243025494461972200937825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6162016996307981467291883 9243025494461972200937825)
    ·
      refine ⟨6932269120846479150703369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9243025494461972200937825 6932269120846479150703369)
      ·
        refine ⟨5199201840634859363027527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6932269120846479150703369 5199201840634859363027527)
        ·
          refine ⟨7798802760952289044541291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5199201840634859363027527 7798802760952289044541291)
          ·
            refine ⟨11698204141428433566811937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7798802760952289044541291 11698204141428433566811937)
            ·
              refine ⟨8773653106071325175108953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11698204141428433566811937 8773653106071325175108953)
              ·
                refine ⟨6580239829553493881331715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8773653106071325175108953 6580239829553493881331715)
                ·
                  refine ⟨9870359744330240821997573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6580239829553493881331715 9870359744330240821997573)
                  ·
                    refine ⟨1850692452061920154124545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9870359744330240821997573 1850692452061920154124545)
                    ·
                      refine ⟨1388019339046440115593409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1850692452061920154124545 1388019339046440115593409)
                      ·
                        rfl

theorem cell23_2703158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_2703158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703158 prefixEnd_2703158 := by exact prefixLift 2703158
  have htrace : WordTrace (prefixWord ++ tailWord_2703158) baseStart_2703158 baseEnd_2703158 := by
    simpa [prefixWord, tailWord_2703158, baseEnd_2703158] using wordTrace_append hprefix tailTrace_2703158
  have hstable : (prefixWord ++ tailWord_2703158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703158).length < 2 ^ (prefixWord ++ tailWord_2703158).sum := by decide
  have hdescent : baseEnd_2703158 < baseStart_2703158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703164 : List Nat := [2, 2, 2, 2, 1, 1, 3, 5, 5]
def baseStart_2703164 : Nat := 118140960795 + 2703164 * 2 ^ 59
def prefixEnd_2703164 : Nat := 4983230072969 + 3 ^ 40 * 2703164 * 2
def baseEnd_2703164 : Nat := 154224713325596343568709

theorem tailTrace_2703164 : CollatzResearch.WordTrace tailWord_2703164 prefixEnd_2703164 154224713325596343568709 := by
  unfold tailWord_2703164
  simp only [CollatzResearch.WordTrace]
  refine ⟨49296245389452983250694273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65728327185937311000925697 49296245389452983250694273)
  ·
    refine ⟨36972184042089737438020705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49296245389452983250694273 36972184042089737438020705)
    ·
      refine ⟨27729138031567303078515529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36972184042089737438020705 27729138031567303078515529)
      ·
        refine ⟨20796853523675477308886647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27729138031567303078515529 20796853523675477308886647)
        ·
          refine ⟨31195280285513215963329971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20796853523675477308886647 31195280285513215963329971)
          ·
            refine ⟨46792920428269823944994957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31195280285513215963329971 46792920428269823944994957)
            ·
              refine ⟨17547345160601183979373109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46792920428269823944994957 17547345160601183979373109)
              ·
                refine ⟨1645063608806360998066229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17547345160601183979373109 1645063608806360998066229)
                ·
                  refine ⟨154224713325596343568709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1645063608806360998066229 154224713325596343568709)
                  ·
                    rfl

theorem cell23_2703164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 5].length) (baseStart_2703164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703164 prefixEnd_2703164 := by exact prefixLift 2703164
  have htrace : WordTrace (prefixWord ++ tailWord_2703164) baseStart_2703164 baseEnd_2703164 := by
    simpa [prefixWord, tailWord_2703164, baseEnd_2703164] using wordTrace_append hprefix tailTrace_2703164
  have hstable : (prefixWord ++ tailWord_2703164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703164).length < 2 ^ (prefixWord ++ tailWord_2703164).sum := by decide
  have hdescent : baseEnd_2703164 < baseStart_2703164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703177 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 4, 5]
def baseStart_2703177 : Nat := 118140960795 + 2703177 * 2 ^ 59
def prefixEnd_2703177 : Nat := 4983230072969 + 3 ^ 40 * 2703177 * 2
def baseEnd_2703177 : Nat := 462676365059625180418607

theorem tailTrace_2703177 : CollatzResearch.WordTrace tailWord_2703177 prefixEnd_2703177 462676365059625180418607 := by
  unfold tailWord_2703177
  simp only [CollatzResearch.WordTrace]
  refine ⟨98592964927858869721611785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65728643285239246481074523 98592964927858869721611785)
  ·
    refine ⟨73944723695894152291208839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98592964927858869721611785 73944723695894152291208839)
    ·
      refine ⟨110917085543841228436813259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73944723695894152291208839 110917085543841228436813259)
      ·
        refine ⟨166375628315761842655219889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110917085543841228436813259 166375628315761842655219889)
        ·
          refine ⟨124781721236821381991414917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166375628315761842655219889 124781721236821381991414917)
          ·
            refine ⟨23396572731904009123390297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124781721236821381991414917 23396572731904009123390297)
            ·
              refine ⟨17547429548928006842542723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23396572731904009123390297 17547429548928006842542723)
              ·
                refine ⟨26321144323392010263814085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17547429548928006842542723 26321144323392010263814085)
                ·
                  refine ⟨4935214560636001924465141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26321144323392010263814085 4935214560636001924465141)
                  ·
                    refine ⟨462676365059625180418607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4935214560636001924465141 462676365059625180418607)
                    ·
                      rfl

theorem cell23_2703177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 5].length) (baseStart_2703177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703177 prefixEnd_2703177 := by exact prefixLift 2703177
  have htrace : WordTrace (prefixWord ++ tailWord_2703177) baseStart_2703177 baseEnd_2703177 := by
    simpa [prefixWord, tailWord_2703177, baseEnd_2703177] using wordTrace_append hprefix tailTrace_2703177
  have hstable : (prefixWord ++ tailWord_2703177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703177).length < 2 ^ (prefixWord ++ tailWord_2703177).sum := by decide
  have hdescent : baseEnd_2703177 < baseStart_2703177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703181 : List Nat := [1, 6, 1, 2, 1, 2, 2, 1, 7]
def baseStart_2703181 : Nat := 118140960795 + 2703181 * 2 ^ 59
def prefixEnd_2703181 : Nat := 4983230072969 + 3 ^ 40 * 2703181 * 2
def baseEnd_2703181 : Nat := 154225683233499280622867

theorem tailTrace_2703181 : CollatzResearch.WordTrace tailWord_2703181 prefixEnd_2703181 154225683233499280622867 := by
  unfold tailWord_2703181
  simp only [CollatzResearch.WordTrace]
  refine ⟨98593110819844378404757397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65728740546562918936504931 98593110819844378404757397)
  ·
    refine ⟨4621552069680205237723003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 98593110819844378404757397 4621552069680205237723003)
    ·
      refine ⟨6932328104520307856584505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4621552069680205237723003 6932328104520307856584505)
      ·
        refine ⟨5199246078390230892438379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6932328104520307856584505 5199246078390230892438379)
        ·
          refine ⟨7798869117585346338657569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5199246078390230892438379 7798869117585346338657569)
          ·
            refine ⟨5849151838189009753993177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7798869117585346338657569 5849151838189009753993177)
            ·
              refine ⟨4386863878641757315494883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5849151838189009753993177 4386863878641757315494883)
              ·
                refine ⟨6580295817962635973242325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4386863878641757315494883 6580295817962635973242325)
                ·
                  refine ⟨154225683233499280622867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6580295817962635973242325 154225683233499280622867)
                  ·
                    rfl

theorem cell23_2703181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_2703181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703181 prefixEnd_2703181 := by exact prefixLift 2703181
  have htrace : WordTrace (prefixWord ++ tailWord_2703181) baseStart_2703181 baseEnd_2703181 := by
    simpa [prefixWord, tailWord_2703181, baseEnd_2703181] using wordTrace_append hprefix tailTrace_2703181
  have hstable : (prefixWord ++ tailWord_2703181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703181).length < 2 ^ (prefixWord ++ tailWord_2703181).sum := by decide
  have hdescent : baseEnd_2703181 < baseStart_2703181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703207 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 2, 8]
def baseStart_2703207 : Nat := 118140960795 + 2703207 * 2 ^ 59
def prefixEnd_2703207 : Nat := 4983230072969 + 3 ^ 40 * 2703207 * 2
def baseEnd_2703207 : Nat := 462681499866170141293561

theorem tailTrace_2703207 : CollatzResearch.WordTrace tailWord_2703207 prefixEnd_2703207 462681499866170141293561 := by
  unfold tailWord_2703207
  simp only [CollatzResearch.WordTrace]
  refine ⟨98594059117750184845203875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65729372745166789896802583 98594059117750184845203875)
  ·
    refine ⟨147891088676625277267805813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98594059117750184845203875 147891088676625277267805813)
    ·
      refine ⟨13864789563433619743856795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147891088676625277267805813 13864789563433619743856795)
      ·
        refine ⟨20797184345150429615785193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13864789563433619743856795 20797184345150429615785193)
        ·
          refine ⟨15597888258862822211838895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20797184345150429615785193 15597888258862822211838895)
          ·
            refine ⟨23396832388294233317758343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15597888258862822211838895 23396832388294233317758343)
            ·
              refine ⟨35095248582441349976637515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23396832388294233317758343 35095248582441349976637515)
              ·
                refine ⟨52642872873662024964956273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35095248582441349976637515 52642872873662024964956273)
                ·
                  refine ⟨39482154655246518723717205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52642872873662024964956273 39482154655246518723717205)
                  ·
                    refine ⟨462681499866170141293561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39482154655246518723717205 462681499866170141293561)
                    ·
                      rfl

theorem cell23_2703207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_2703207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703207 prefixEnd_2703207 := by exact prefixLift 2703207
  have htrace : WordTrace (prefixWord ++ tailWord_2703207) baseStart_2703207 baseEnd_2703207 := by
    simpa [prefixWord, tailWord_2703207, baseEnd_2703207] using wordTrace_append hprefix tailTrace_2703207
  have hstable : (prefixWord ++ tailWord_2703207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703207).length < 2 ^ (prefixWord ++ tailWord_2703207).sum := by decide
  have hdescent : baseEnd_2703207 < baseStart_2703207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703237 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 8]
def baseStart_2703237 : Nat := 118140960795 + 2703237 * 2 ^ 59
def prefixEnd_2703237 : Nat := 4983230072969 + 3 ^ 40 * 2703237 * 2
def baseEnd_2703237 : Nat := 154228878224238367389505

theorem tailTrace_2703237 : CollatzResearch.WordTrace tailWord_2703237 prefixEnd_2703237 154228878224238367389505 := by
  unfold tailWord_2703237
  simp only [CollatzResearch.WordTrace]
  refine ⟨98595153307641499968795965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65730102205094333312530643 98595153307641499968795965)
  ·
    refine ⟨36973182490365562488298487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98595153307641499968795965 36973182490365562488298487)
    ·
      refine ⟨55459773735548343732447731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36973182490365562488298487 55459773735548343732447731)
      ·
        refine ⟨83189660603322515598671597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55459773735548343732447731 83189660603322515598671597)
        ·
          refine ⟨31196122726245943349501849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83189660603322515598671597 31196122726245943349501849)
          ·
            refine ⟨23397092044684457512126387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31196122726245943349501849 23397092044684457512126387)
            ·
              refine ⟨35095638067026686268189581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23397092044684457512126387 35095638067026686268189581)
              ·
                refine ⟨13160864275135007350571093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35095638067026686268189581 13160864275135007350571093)
                ·
                  refine ⟨154228878224238367389505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13160864275135007350571093 154228878224238367389505)
                  ·
                    rfl

theorem cell23_2703237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 8].length) (baseStart_2703237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703237 prefixEnd_2703237 := by exact prefixLift 2703237
  have htrace : WordTrace (prefixWord ++ tailWord_2703237) baseStart_2703237 baseEnd_2703237 := by
    simpa [prefixWord, tailWord_2703237, baseEnd_2703237] using wordTrace_append hprefix tailTrace_2703237
  have hstable : (prefixWord ++ tailWord_2703237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703237).length < 2 ^ (prefixWord ++ tailWord_2703237).sum := by decide
  have hdescent : baseEnd_2703237 < baseStart_2703237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703257 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 1, 2, 6]
def baseStart_2703257 : Nat := 118140960795 + 2703257 * 2 ^ 59
def prefixEnd_2703257 : Nat := 4983230072969 + 3 ^ 40 * 2703257 * 2
def baseEnd_2703257 : Nat := 1388070173631235228255453

theorem tailTrace_2703257 : CollatzResearch.WordTrace tailWord_2703257 prefixEnd_2703257 1388070173631235228255453 := by
  unfold tailWord_2703257
  simp only [CollatzResearch.WordTrace]
  refine ⟨98595882767569043384524025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65730588511712695589682683 98595882767569043384524025)
  ·
    refine ⟨73946912075676782538393019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98595882767569043384524025 73946912075676782538393019)
    ·
      refine ⟨110920368113515173807589529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73946912075676782538393019 110920368113515173807589529)
      ·
        refine ⟨83190276085136380355692147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110920368113515173807589529 83190276085136380355692147)
        ·
          refine ⟨124785414127704570533538221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83190276085136380355692147 124785414127704570533538221)
          ·
            refine ⟨46794530297889213950076833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124785414127704570533538221 46794530297889213950076833)
            ·
              refine ⟨35095897723416910462557625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46794530297889213950076833 35095897723416910462557625)
              ·
                refine ⟨26321923292562682846918219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35095897723416910462557625 26321923292562682846918219)
                ·
                  refine ⟨39482884938844024270377329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26321923292562682846918219 39482884938844024270377329)
                  ·
                    refine ⟨29612163704133018202782997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39482884938844024270377329 29612163704133018202782997)
                    ·
                      refine ⟨1388070173631235228255453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29612163704133018202782997 1388070173631235228255453)
                      ·
                        rfl

theorem cell23_2703257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_2703257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703257 prefixEnd_2703257 := by exact prefixLift 2703257
  have htrace : WordTrace (prefixWord ++ tailWord_2703257) baseStart_2703257 baseEnd_2703257 := by
    simpa [prefixWord, tailWord_2703257, baseEnd_2703257] using wordTrace_append hprefix tailTrace_2703257
  have hstable : (prefixWord ++ tailWord_2703257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703257).length < 2 ^ (prefixWord ++ tailWord_2703257).sum := by decide
  have hdescent : baseEnd_2703257 < baseStart_2703257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703335 : List Nat := [1, 1, 5, 2, 3, 2, 2, 1, 1, 5]
def baseStart_2703335 : Nat := 118140960795 + 2703335 * 2 ^ 59
def prefixEnd_2703335 : Nat := 4983230072969 + 3 ^ 40 * 2703335 * 2
def baseEnd_2703335 : Nat := 462703408374095307693365

theorem tailTrace_2703335 : CollatzResearch.WordTrace tailWord_2703335 prefixEnd_2703335 462703408374095307693365 := by
  unfold tailWord_2703335
  simp only [CollatzResearch.WordTrace]
  refine ⟨98598727661286462705863459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65732485107524308470575639 98598727661286462705863459)
  ·
    refine ⟨147898091491929694058795189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98598727661286462705863459 147898091491929694058795189)
    ·
      refine ⟨13865446077368408818012049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147898091491929694058795189 13865446077368408818012049)
      ·
        refine ⟨10399084558026306613509037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13865446077368408818012049 10399084558026306613509037)
        ·
          refine ⟨3899656709259864980065889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10399084558026306613509037 3899656709259864980065889)
          ·
            refine ⟨2924742531944898735049417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3899656709259864980065889 2924742531944898735049417)
            ·
              refine ⟨2193556898958674051287063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2924742531944898735049417 2193556898958674051287063)
              ·
                refine ⟨3290335348438011076930595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2193556898958674051287063 3290335348438011076930595)
                ·
                  refine ⟨4935503022657016615395893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3290335348438011076930595 4935503022657016615395893)
                  ·
                    refine ⟨462703408374095307693365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4935503022657016615395893 462703408374095307693365)
                    ·
                      rfl

theorem cell23_2703335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_2703335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703335 prefixEnd_2703335 := by exact prefixLift 2703335
  have htrace : WordTrace (prefixWord ++ tailWord_2703335) baseStart_2703335 baseEnd_2703335 := by
    simpa [prefixWord, tailWord_2703335, baseEnd_2703335] using wordTrace_append hprefix tailTrace_2703335
  have hstable : (prefixWord ++ tailWord_2703335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703335).length < 2 ^ (prefixWord ++ tailWord_2703335).sum := by decide
  have hdescent : baseEnd_2703335 < baseStart_2703335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703338 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 5, 2, 2]
def baseStart_2703338 : Nat := 118140960795 + 2703338 * 2 ^ 59
def prefixEnd_2703338 : Nat := 4983230072969 + 3 ^ 40 * 2703338 * 2
def baseEnd_2703338 : Nat := 1388111765564249411342581

theorem tailTrace_2703338 : CollatzResearch.WordTrace tailWord_2703338 prefixEnd_2703338 1388111765564249411342581 := by
  unfold tailWord_2703338
  simp only [CollatzResearch.WordTrace]
  refine ⟨24649709270068898554555667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65732558053517062812148445 24649709270068898554555667)
  ·
    refine ⟨36974563905103347831833501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24649709270068898554555667 36974563905103347831833501)
    ·
      refine ⟨13865461464413755436937563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36974563905103347831833501 13865461464413755436937563)
      ·
        refine ⟨20798192196620633155406345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13865461464413755436937563 20798192196620633155406345)
        ·
          refine ⟨15598644147465474866554759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20798192196620633155406345 15598644147465474866554759)
          ·
            refine ⟨23397966221198212299832139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15598644147465474866554759 23397966221198212299832139)
            ·
              refine ⟨35096949331797318449748209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23397966221198212299832139 35096949331797318449748209)
              ·
                refine ⟨26322711998847988837311157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35096949331797318449748209 26322711998847988837311157)
                ·
                  refine ⟨2467754249891998953497921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26322711998847988837311157 2467754249891998953497921)
                  ·
                    refine ⟨1850815687418999215123441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2467754249891998953497921 1850815687418999215123441)
                    ·
                      refine ⟨1388111765564249411342581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1850815687418999215123441 1388111765564249411342581)
                      ·
                        rfl

theorem cell23_2703338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_2703338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703338 prefixEnd_2703338 := by exact prefixLift 2703338
  have htrace : WordTrace (prefixWord ++ tailWord_2703338) baseStart_2703338 baseEnd_2703338 := by
    simpa [prefixWord, tailWord_2703338, baseEnd_2703338] using wordTrace_append hprefix tailTrace_2703338
  have hstable : (prefixWord ++ tailWord_2703338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703338).length < 2 ^ (prefixWord ++ tailWord_2703338).sum := by decide
  have hdescent : baseEnd_2703338 < baseStart_2703338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703354 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3]
def baseStart_2703354 : Nat := 118140960795 + 2703354 * 2 ^ 59
def prefixEnd_2703354 : Nat := 4983230072969 + 3 ^ 40 * 2703354 * 2
def baseEnd_2703354 : Nat := 1388119981254721348742507

theorem tailTrace_2703354 : CollatzResearch.WordTrace tailWord_2703354 prefixEnd_2703354 1388119981254721348742507 := by
  unfold tailWord_2703354
  simp only [CollatzResearch.WordTrace]
  refine ⟨24649855162054407237701279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65732947098811752633870077 24649855162054407237701279)
  ·
    refine ⟨36974782743081610856551919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24649855162054407237701279 36974782743081610856551919)
    ·
      refine ⟨55462174114622416284827879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36974782743081610856551919 55462174114622416284827879)
      ·
        refine ⟨83193261171933624427241819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55462174114622416284827879 83193261171933624427241819)
        ·
          refine ⟨124789891757900436640862729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83193261171933624427241819 124789891757900436640862729)
          ·
            refine ⟨93592418818425327480647047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124789891757900436640862729 93592418818425327480647047)
            ·
              refine ⟨140388628227637991220970571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93592418818425327480647047 140388628227637991220970571)
              ·
                refine ⟨210582942341456986831455857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140388628227637991220970571 210582942341456986831455857)
                ·
                  refine ⟨157937206756092740123591893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210582942341456986831455857 157937206756092740123591893)
                  ·
                    refine ⟨3701653283345923596646685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 157937206756092740123591893 3701653283345923596646685)
                    ·
                      refine ⟨1388119981254721348742507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3701653283345923596646685 1388119981254721348742507)
                      ·
                        rfl

theorem cell23_2703354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_2703354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703354 prefixEnd_2703354 := by exact prefixLift 2703354
  have htrace : WordTrace (prefixWord ++ tailWord_2703354) baseStart_2703354 baseEnd_2703354 := by
    simpa [prefixWord, tailWord_2703354, baseEnd_2703354] using wordTrace_append hprefix tailTrace_2703354
  have hstable : (prefixWord ++ tailWord_2703354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703354).length < 2 ^ (prefixWord ++ tailWord_2703354).sum := by decide
  have hdescent : baseEnd_2703354 < baseStart_2703354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703355 : List Nat := [1, 1, 1, 1, 1, 3, 6, 4, 1, 2, 2]
def baseStart_2703355 : Nat := 118140960795 + 2703355 * 2 ^ 59
def prefixEnd_2703355 : Nat := 4983230072969 + 3 ^ 40 * 2703355 * 2
def baseEnd_2703355 : Nat := 1388120494735375844830003

theorem tailTrace_2703355 : CollatzResearch.WordTrace tailWord_2703355 prefixEnd_2703355 1388120494735375844830003 := by
  unfold tailWord_2703355
  simp only [CollatzResearch.WordTrace]
  refine ⟨98599457121214006121591519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65732971414142670747727679 98599457121214006121591519)
  ·
    refine ⟨147899185681821009182387279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98599457121214006121591519 147899185681821009182387279)
    ·
      refine ⟨221848778522731513773580919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147899185681821009182387279 221848778522731513773580919)
      ·
        refine ⟨332773167784097270660371379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221848778522731513773580919 332773167784097270660371379)
        ·
          refine ⟨499159751676145905990557069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332773167784097270660371379 499159751676145905990557069)
          ·
            refine ⟨187184906878554714746458901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 499159751676145905990557069 187184906878554714746458901)
            ·
              refine ⟨8774292509932252253740261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 187184906878554714746458901 8774292509932252253740261)
              ·
                refine ⟨1645179845612297297576299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8774292509932252253740261 1645179845612297297576299)
                ·
                  refine ⟨2467769768418445946364449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1645179845612297297576299 2467769768418445946364449)
                  ·
                    refine ⟨1850827326313834459773337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2467769768418445946364449 1850827326313834459773337)
                    ·
                      refine ⟨1388120494735375844830003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1850827326313834459773337 1388120494735375844830003)
                      ·
                        rfl

theorem cell23_2703355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 1, 2, 2].length) (baseStart_2703355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703355 prefixEnd_2703355 := by exact prefixLift 2703355
  have htrace : WordTrace (prefixWord ++ tailWord_2703355) baseStart_2703355 baseEnd_2703355 := by
    simpa [prefixWord, tailWord_2703355, baseEnd_2703355] using wordTrace_append hprefix tailTrace_2703355
  have hstable : (prefixWord ++ tailWord_2703355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703355).length < 2 ^ (prefixWord ++ tailWord_2703355).sum := by decide
  have hdescent : baseEnd_2703355 < baseStart_2703355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703358 : List Nat := [4, 2, 2, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2703358 : Nat := 118140960795 + 2703358 * 2 ^ 59
def prefixEnd_2703358 : Nat := 4983230072969 + 3 ^ 40 * 2703358 * 2
def baseEnd_2703358 : Nat := 1388122035177339333092489

theorem tailTrace_2703358 : CollatzResearch.WordTrace tailWord_2703358 prefixEnd_2703358 1388122035177339333092489 := by
  unfold tailWord_2703358
  simp only [CollatzResearch.WordTrace]
  refine ⟨12324945817525392204243841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65733044360135425089300485 12324945817525392204243841)
  ·
    refine ⟨9243709363144044153182881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12324945817525392204243841 9243709363144044153182881)
    ·
      refine ⟨6932782022358033114887161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9243709363144044153182881 6932782022358033114887161)
      ·
        refine ⟨5199586516768524836165371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6932782022358033114887161 5199586516768524836165371)
        ·
          refine ⟨7799379775152787254248057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5199586516768524836165371 7799379775152787254248057)
          ·
            refine ⟨5849534831364590440686043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7799379775152787254248057 5849534831364590440686043)
            ·
              refine ⟨8774302247046885661029065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5849534831364590440686043 8774302247046885661029065)
              ·
                refine ⟨6580726685285164245771799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8774302247046885661029065 6580726685285164245771799)
                ·
                  refine ⟨9871090027927746368657699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6580726685285164245771799 9871090027927746368657699)
                  ·
                    refine ⟨14806635041891619552986549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9871090027927746368657699 14806635041891619552986549)
                    ·
                      refine ⟨1388122035177339333092489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14806635041891619552986549 1388122035177339333092489)
                      ·
                        rfl

theorem cell23_2703358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2703358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703358 prefixEnd_2703358 := by exact prefixLift 2703358
  have htrace : WordTrace (prefixWord ++ tailWord_2703358) baseStart_2703358 baseEnd_2703358 := by
    simpa [prefixWord, tailWord_2703358, baseEnd_2703358] using wordTrace_append hprefix tailTrace_2703358
  have hstable : (prefixWord ++ tailWord_2703358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703358).length < 2 ^ (prefixWord ++ tailWord_2703358).sum := by decide
  have hdescent : baseEnd_2703358 < baseStart_2703358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703384 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 1, 4, 5]
def baseStart_2703384 : Nat := 118140960795 + 2703384 * 2 ^ 59
def prefixEnd_2703384 : Nat := 4983230072969 + 3 ^ 40 * 2703384 * 2
def baseEnd_2703384 : Nat := 1388135385674356231367369

theorem tailTrace_2703384 : CollatzResearch.WordTrace tailWord_2703384 prefixEnd_2703384 1388135385674356231367369 := by
  unfold tailWord_2703384
  simp only [CollatzResearch.WordTrace]
  refine ⟨49300257419054472037198603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65733676558739296049598137 49300257419054472037198603)
  ·
    refine ⟨73950386128581708055797905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49300257419054472037198603 73950386128581708055797905)
    ·
      refine ⟨55462789596436281041848429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73950386128581708055797905 55462789596436281041848429)
      ·
        refine ⟨20798546098663605390693161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55462789596436281041848429 20798546098663605390693161)
        ·
          refine ⟨15598909573997704043019871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20798546098663605390693161 15598909573997704043019871)
          ·
            refine ⟨23398364360996556064529807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15598909573997704043019871 23398364360996556064529807)
            ·
              refine ⟨35097546541494834096794711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23398364360996556064529807 35097546541494834096794711)
              ·
                refine ⟨52646319812242251145192067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35097546541494834096794711 52646319812242251145192067)
                ·
                  refine ⟨78969479718363376717788101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52646319812242251145192067 78969479718363376717788101)
                  ·
                    refine ⟨14806777447193133134585269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78969479718363376717788101 14806777447193133134585269)
                    ·
                      refine ⟨1388135385674356231367369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14806777447193133134585269 1388135385674356231367369)
                      ·
                        rfl

theorem cell23_2703384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_2703384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703384 prefixEnd_2703384 := by exact prefixLift 2703384
  have htrace : WordTrace (prefixWord ++ tailWord_2703384) baseStart_2703384 baseEnd_2703384 := by
    simpa [prefixWord, tailWord_2703384, baseEnd_2703384] using wordTrace_append hprefix tailTrace_2703384
  have hstable : (prefixWord ++ tailWord_2703384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703384).length < 2 ^ (prefixWord ++ tailWord_2703384).sum := by decide
  have hdescent : baseEnd_2703384 < baseStart_2703384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703388 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_2703388 : Nat := 118140960795 + 2703388 * 2 ^ 59
def prefixEnd_2703388 : Nat := 4983230072969 + 3 ^ 40 * 2703388 * 2
def baseEnd_2703388 : Nat := 1388137439596974215717351

theorem tailTrace_2703388 : CollatzResearch.WordTrace tailWord_2703388 prefixEnd_2703388 1388137439596974215717351 := by
  unfold tailWord_2703388
  simp only [CollatzResearch.WordTrace]
  refine ⟨49300330365047226378771409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65733773820062968505028545 49300330365047226378771409)
  ·
    refine ⟨36975247773785419784078557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49300330365047226378771409 36975247773785419784078557)
    ·
      refine ⟨13865717915169532419029459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36975247773785419784078557 13865717915169532419029459)
      ·
        refine ⟨20798576872754298628544189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13865717915169532419029459 20798576872754298628544189)
        ·
          refine ⟨7799466327282861985704071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20798576872754298628544189 7799466327282861985704071)
          ·
            refine ⟨11699199490924292978556107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7799466327282861985704071 11699199490924292978556107)
            ·
              refine ⟨17548799236386439467834161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11699199490924292978556107 17548799236386439467834161)
              ·
                refine ⟨13161599427289829600875621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17548799236386439467834161 13161599427289829600875621)
                ·
                  refine ⟨2467799892616843050164179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13161599427289829600875621 2467799892616843050164179)
                  ·
                    refine ⟨3701699838925264575246269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2467799892616843050164179 3701699838925264575246269)
                    ·
                      refine ⟨1388137439596974215717351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3701699838925264575246269 1388137439596974215717351)
                      ·
                        rfl

theorem cell23_2703388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_2703388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703388 prefixEnd_2703388 := by exact prefixLift 2703388
  have htrace : WordTrace (prefixWord ++ tailWord_2703388) baseStart_2703388 baseEnd_2703388 := by
    simpa [prefixWord, tailWord_2703388, baseEnd_2703388] using wordTrace_append hprefix tailTrace_2703388
  have hstable : (prefixWord ++ tailWord_2703388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703388).length < 2 ^ (prefixWord ++ tailWord_2703388).sum := by decide
  have hdescent : baseEnd_2703388 < baseStart_2703388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703389 : List Nat := [1, 4, 2, 2, 2, 3, 1, 3, 1, 2, 2]
def baseStart_2703389 : Nat := 118140960795 + 2703389 * 2 ^ 59
def prefixEnd_2703389 : Nat := 4983230072969 + 3 ^ 40 * 2703389 * 2
def baseEnd_2703389 : Nat := 1388137953077628711804847

theorem tailTrace_2703389 : CollatzResearch.WordTrace tailWord_2703389 prefixEnd_2703389 1388137953077628711804847 := by
  unfold tailWord_2703389
  simp only [CollatzResearch.WordTrace]
  refine ⟨98600697203090829928329221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65733798135393886618886147 98600697203090829928329221)
  ·
    refine ⟨18487630725579530611561729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98600697203090829928329221 18487630725579530611561729)
    ·
      refine ⟨13865723044184647958671297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18487630725579530611561729 13865723044184647958671297)
      ·
        refine ⟨10399292283138485969003473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13865723044184647958671297 10399292283138485969003473)
        ·
          refine ⟨7799469212353864476752605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10399292283138485969003473 7799469212353864476752605)
          ·
            refine ⟨2924800954632699178782227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7799469212353864476752605 2924800954632699178782227)
            ·
              refine ⟨4387201431949048768173341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2924800954632699178782227 4387201431949048768173341)
              ·
                refine ⟨1645200536980893288065003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4387201431949048768173341 1645200536980893288065003)
                ·
                  refine ⟨2467800805471339932097505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1645200536980893288065003 2467800805471339932097505)
                  ·
                    refine ⟨1850850604103504949073129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2467800805471339932097505 1850850604103504949073129)
                    ·
                      refine ⟨1388137953077628711804847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1850850604103504949073129 1388137953077628711804847)
                      ·
                        rfl

theorem cell23_2703389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_2703389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703389 prefixEnd_2703389 := by exact prefixLift 2703389
  have htrace : WordTrace (prefixWord ++ tailWord_2703389) baseStart_2703389 baseEnd_2703389 := by
    simpa [prefixWord, tailWord_2703389, baseEnd_2703389] using wordTrace_append hprefix tailTrace_2703389
  have hstable : (prefixWord ++ tailWord_2703389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703389).length < 2 ^ (prefixWord ++ tailWord_2703389).sum := by decide
  have hdescent : baseEnd_2703389 < baseStart_2703389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703404 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 2, 6]
def baseStart_2703404 : Nat := 118140960795 + 2703404 * 2 ^ 59
def prefixEnd_2703404 : Nat := 4983230072969 + 3 ^ 40 * 2703404 * 2
def baseEnd_2703404 : Nat := 462715218429148717705759

theorem tailTrace_2703404 : CollatzResearch.WordTrace tailWord_2703404 prefixEnd_2703404 462715218429148717705759 := by
  unfold tailWord_2703404
  simp only [CollatzResearch.WordTrace]
  refine ⟨49300622149018243745062633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65734162865357658326750177 49300622149018243745062633)
  ·
    refine ⟨36975466611763682808796975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49300622149018243745062633 36975466611763682808796975)
    ·
      refine ⟨55463199917645524213195463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36975466611763682808796975 55463199917645524213195463)
      ·
        refine ⟨83194799876468286319793195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55463199917645524213195463 83194799876468286319793195)
        ·
          refine ⟨124792199814702429479689793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83194799876468286319793195 124792199814702429479689793)
          ·
            refine ⟨93594149861026822109767345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124792199814702429479689793 93594149861026822109767345)
            ·
              refine ⟨70195612395770116582325509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93594149861026822109767345 70195612395770116582325509)
              ·
                refine ⟨13161677324206896859186033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70195612395770116582325509 13161677324206896859186033)
                ·
                  refine ⟨9871257993155172644389525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13161677324206896859186033 9871257993155172644389525)
                  ·
                    refine ⟨462715218429148717705759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9871257993155172644389525 462715218429148717705759)
                    ·
                      rfl

theorem cell23_2703404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_2703404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703404 prefixEnd_2703404 := by exact prefixLift 2703404
  have htrace : WordTrace (prefixWord ++ tailWord_2703404) baseStart_2703404 baseEnd_2703404 := by
    simpa [prefixWord, tailWord_2703404, baseEnd_2703404] using wordTrace_append hprefix tailTrace_2703404
  have hstable : (prefixWord ++ tailWord_2703404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703404).length < 2 ^ (prefixWord ++ tailWord_2703404).sum := by decide
  have hdescent : baseEnd_2703404 < baseStart_2703404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703422 : List Nat := [4, 2, 1, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_2703422 : Nat := 118140960795 + 2703422 * 2 ^ 59
def prefixEnd_2703422 : Nat := 4983230072969 + 3 ^ 40 * 2703422 * 2
def baseEnd_2703422 : Nat := 1388154897939227082692195

theorem tailTrace_2703422 : CollatzResearch.WordTrace tailWord_2703422 prefixEnd_2703422 1388154897939227082692195 := by
  unfold tailWord_2703422
  simp only [CollatzResearch.WordTrace]
  refine ⟨12325237601496409570535065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65734600541314184376187013 12325237601496409570535065)
  ·
    refine ⟨9243928201122307177901299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12325237601496409570535065 9243928201122307177901299)
    ·
      refine ⟨13865892301683460766851949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9243928201122307177901299 13865892301683460766851949)
      ·
        refine ⟨5199709613131297787569481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13865892301683460766851949 5199709613131297787569481)
        ·
          refine ⟨3899782209848473340677111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5199709613131297787569481 3899782209848473340677111)
          ·
            refine ⟨5849673314772710011015667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3899782209848473340677111 5849673314772710011015667)
            ·
              refine ⟨8774509972159065016523501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5849673314772710011015667 8774509972159065016523501)
              ·
                refine ⟨3290441239559649381196313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8774509972159065016523501 3290441239559649381196313)
                ·
                  refine ⟨2467830929669737035897235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3290441239559649381196313 2467830929669737035897235)
                  ·
                    refine ⟨3701746394504605553845853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2467830929669737035897235 3701746394504605553845853)
                    ·
                      refine ⟨1388154897939227082692195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3701746394504605553845853 1388154897939227082692195)
                      ·
                        rfl

theorem cell23_2703422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_2703422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703422 prefixEnd_2703422 := by exact prefixLift 2703422
  have htrace : WordTrace (prefixWord ++ tailWord_2703422) baseStart_2703422 baseEnd_2703422 := by
    simpa [prefixWord, tailWord_2703422, baseEnd_2703422] using wordTrace_append hprefix tailTrace_2703422
  have hstable : (prefixWord ++ tailWord_2703422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703422).length < 2 ^ (prefixWord ++ tailWord_2703422).sum := by decide
  have hdescent : baseEnd_2703422 < baseStart_2703422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703434 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 9]
def baseStart_2703434 : Nat := 118140960795 + 2703434 * 2 ^ 59
def prefixEnd_2703434 : Nat := 4983230072969 + 3 ^ 40 * 2703434 * 2
def baseEnd_2703434 : Nat := 154240117745231226193571

theorem tailTrace_2703434 : CollatzResearch.WordTrace tailWord_2703434 prefixEnd_2703434 154240117745231226193571 := by
  unfold tailWord_2703434
  simp only [CollatzResearch.WordTrace]
  refine ⟨24650584621981950653429339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65734892325285201742478237 24650584621981950653429339)
  ·
    refine ⟨36975876932972925980144009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24650584621981950653429339 36975876932972925980144009)
    ·
      refine ⟨27731907699729694485108007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36975876932972925980144009 27731907699729694485108007)
      ·
        refine ⟨41597861549594541727662011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27731907699729694485108007 41597861549594541727662011)
        ·
          refine ⟨62396792324391812591493017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41597861549594541727662011 62396792324391812591493017)
          ·
            refine ⟨46797594243293859443619763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62396792324391812591493017 46797594243293859443619763)
            ·
              refine ⟨70196391364940789165429645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46797594243293859443619763 70196391364940789165429645)
              ·
                refine ⟨26323646761852795937036117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70196391364940789165429645 26323646761852795937036117)
                ·
                  refine ⟨154240117745231226193571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26323646761852795937036117 154240117745231226193571)
                  ·
                    rfl

theorem cell23_2703434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 9].length) (baseStart_2703434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703434 prefixEnd_2703434 := by exact prefixLift 2703434
  have htrace : WordTrace (prefixWord ++ tailWord_2703434) baseStart_2703434 baseEnd_2703434 := by
    simpa [prefixWord, tailWord_2703434, baseEnd_2703434] using wordTrace_append hprefix tailTrace_2703434
  have hstable : (prefixWord ++ tailWord_2703434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703434).length < 2 ^ (prefixWord ++ tailWord_2703434).sum := by decide
  have hdescent : baseEnd_2703434 < baseStart_2703434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703468 : List Nat := [2, 2, 1, 1, 3, 4, 1, 4, 5]
def baseStart_2703468 : Nat := 118140960795 + 2703468 * 2 ^ 59
def prefixEnd_2703468 : Nat := 4983230072969 + 3 ^ 40 * 2703468 * 2
def baseEnd_2703468 : Nat := 154242057561037100301887

theorem tailTrace_2703468 : CollatzResearch.WordTrace tailWord_2703468 prefixEnd_2703468 154242057561037100301887 := by
  unfold tailWord_2703468
  simp only [CollatzResearch.WordTrace]
  refine ⟨49301789284902313210227529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65735719046536417613636705 49301789284902313210227529)
  ·
    refine ⟨36976341963676734907670647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49301789284902313210227529 36976341963676734907670647)
    ·
      refine ⟨55464512945515102361505971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36976341963676734907670647 55464512945515102361505971)
      ·
        refine ⟨83196769418272653542258957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55464512945515102361505971 83196769418272653542258957)
        ·
          refine ⟨31198788531852245078347109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83196769418272653542258957 31198788531852245078347109)
          ·
            refine ⟨5849772849722295952190083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31198788531852245078347109 5849772849722295952190083)
            ·
              refine ⟨8774659274583443928285125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5849772849722295952190083 8774659274583443928285125)
              ·
                refine ⟨1645248613984395736553461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8774659274583443928285125 1645248613984395736553461)
                ·
                  refine ⟨154242057561037100301887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1645248613984395736553461 154242057561037100301887)
                  ·
                    rfl

theorem cell23_2703468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 5].length) (baseStart_2703468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703468 prefixEnd_2703468 := by exact prefixLift 2703468
  have htrace : WordTrace (prefixWord ++ tailWord_2703468) baseStart_2703468 baseEnd_2703468 := by
    simpa [prefixWord, tailWord_2703468, baseEnd_2703468] using wordTrace_append hprefix tailTrace_2703468
  have hstable : (prefixWord ++ tailWord_2703468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703468).length < 2 ^ (prefixWord ++ tailWord_2703468).sum := by decide
  have hdescent : baseEnd_2703468 < baseStart_2703468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703478 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_2703478 : Nat := 118140960795 + 2703478 * 2 ^ 59
def prefixEnd_2703478 : Nat := 4983230072969 + 3 ^ 40 * 2703478 * 2
def baseEnd_2703478 : Nat := 1388183652855878863591937

theorem tailTrace_2703478 : CollatzResearch.WordTrace tailWord_2703478 prefixEnd_2703478 1388183652855878863591937 := by
  unfold tailWord_2703478
  simp only [CollatzResearch.WordTrace]
  refine ⟨6162746456235524883019943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65735962199845598752212725 6162746456235524883019943)
  ·
    refine ⟨9244119684353287324529915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6162746456235524883019943 9244119684353287324529915)
    ·
      refine ⟨13866179526529930986794873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9244119684353287324529915 13866179526529930986794873)
      ·
        refine ⟨10399634644897448240096155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13866179526529930986794873 10399634644897448240096155)
        ·
          refine ⟨15599451967346172360144233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10399634644897448240096155 15599451967346172360144233)
          ·
            refine ⟨11699588975509629270108175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15599451967346172360144233 11699588975509629270108175)
            ·
              refine ⟨17549383463264443905162263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11699588975509629270108175 17549383463264443905162263)
              ·
                refine ⟨26324075194896665857743395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17549383463264443905162263 26324075194896665857743395)
                ·
                  refine ⟨39486112792344998786615093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26324075194896665857743395 39486112792344998786615093)
                  ·
                    refine ⟨3701823074282343636245165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39486112792344998786615093 3701823074282343636245165)
                    ·
                      refine ⟨1388183652855878863591937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3701823074282343636245165 1388183652855878863591937)
                      ·
                        rfl

theorem cell23_2703478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_2703478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703478 prefixEnd_2703478 := by exact prefixLift 2703478
  have htrace : WordTrace (prefixWord ++ tailWord_2703478) baseStart_2703478 baseEnd_2703478 := by
    simpa [prefixWord, tailWord_2703478, baseEnd_2703478] using wordTrace_append hprefix tailTrace_2703478
  have hstable : (prefixWord ++ tailWord_2703478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703478).length < 2 ^ (prefixWord ++ tailWord_2703478).sum := by decide
  have hdescent : baseEnd_2703478 < baseStart_2703478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703498 : List Nat := [3, 1, 2, 3, 1, 2, 3, 1, 2, 5]
def baseStart_2703498 : Nat := 118140960795 + 2703498 * 2 ^ 59
def prefixEnd_2703498 : Nat := 4983230072969 + 3 ^ 40 * 2703498 * 2
def baseEnd_2703498 : Nat := 462731307489656261780615

theorem tailTrace_2703498 : CollatzResearch.WordTrace tailWord_2703498 prefixEnd_2703498 462731307489656261780615 := by
  unfold tailWord_2703498
  simp only [CollatzResearch.WordTrace]
  refine ⟨24651168189923985386011787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65736448506463961029364765 24651168189923985386011787)
  ·
    refine ⟨36976752284885978079017681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24651168189923985386011787 36976752284885978079017681)
    ·
      refine ⟨27732564213664483559263261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36976752284885978079017681 27732564213664483559263261)
      ·
        refine ⟨10399711580124181334723723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27732564213664483559263261 10399711580124181334723723)
        ·
          refine ⟨15599567370186272002085585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10399711580124181334723723 15599567370186272002085585)
          ·
            refine ⟨11699675527639704001564189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15599567370186272002085585 11699675527639704001564189)
            ·
              refine ⟨4387378322864889000586571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11699675527639704001564189 4387378322864889000586571)
              ·
                refine ⟨6581067484297333500879857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4387378322864889000586571 6581067484297333500879857)
                ·
                  refine ⟨4935800613223000125659893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6581067484297333500879857 4935800613223000125659893)
                  ·
                    refine ⟨462731307489656261780615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4935800613223000125659893 462731307489656261780615)
                    ·
                      rfl

theorem cell23_2703498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_2703498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703498 prefixEnd_2703498 := by exact prefixLift 2703498
  have htrace : WordTrace (prefixWord ++ tailWord_2703498) baseStart_2703498 baseEnd_2703498 := by
    simpa [prefixWord, tailWord_2703498, baseEnd_2703498] using wordTrace_append hprefix tailTrace_2703498
  have hstable : (prefixWord ++ tailWord_2703498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703498).length < 2 ^ (prefixWord ++ tailWord_2703498).sum := by decide
  have hdescent : baseEnd_2703498 < baseStart_2703498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703551 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 3]
def baseStart_2703551 : Nat := 118140960795 + 2703551 * 2 ^ 59
def prefixEnd_2703551 : Nat := 4983230072969 + 3 ^ 40 * 2703551 * 2
def baseEnd_2703551 : Nat := 1388221136943657077979101

theorem tailTrace_2703551 : CollatzResearch.WordTrace tailWord_2703551 prefixEnd_2703551 1388221136943657077979101 := by
  unfold tailWord_2703551
  simp only [CollatzResearch.WordTrace]
  refine ⟨98606605828503931595726507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65737737219002621063817671 98606605828503931595726507)
  ·
    refine ⟨147909908742755897393589761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98606605828503931595726507 147909908742755897393589761)
    ·
      refine ⟨110932431557066923045192321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147909908742755897393589761 110932431557066923045192321)
      ·
        refine ⟨83199323667800192283894241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110932431557066923045192321 83199323667800192283894241)
        ·
          refine ⟨62399492750850144212920681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83199323667800192283894241 62399492750850144212920681)
          ·
            refine ⟨46799619563137608159690511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62399492750850144212920681 46799619563137608159690511)
            ·
              refine ⟨70199429344706412239535767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46799619563137608159690511 70199429344706412239535767)
              ·
                refine ⟨105299144017059618359303651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70199429344706412239535767 105299144017059618359303651)
                ·
                  refine ⟨157948716025589427538955477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105299144017059618359303651 157948716025589427538955477)
                  ·
                    refine ⟨3701923031849752207944269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 157948716025589427538955477 3701923031849752207944269)
                    ·
                      refine ⟨1388221136943657077979101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3701923031849752207944269 1388221136943657077979101)
                      ·
                        rfl

theorem cell23_2703551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_2703551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703551 prefixEnd_2703551 := by exact prefixLift 2703551
  have htrace : WordTrace (prefixWord ++ tailWord_2703551) baseStart_2703551 baseEnd_2703551 := by
    simpa [prefixWord, tailWord_2703551, baseEnd_2703551] using wordTrace_append hprefix tailTrace_2703551
  have hstable : (prefixWord ++ tailWord_2703551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703551).length < 2 ^ (prefixWord ++ tailWord_2703551).sum := by decide
  have hdescent : baseEnd_2703551 < baseStart_2703551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703608 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 2, 6, 2]
def baseStart_2703608 : Nat := 118140960795 + 2703608 * 2 ^ 59
def prefixEnd_2703608 : Nat := 4983230072969 + 3 ^ 40 * 2703608 * 2
def baseEnd_2703608 : Nat := 1388250405340963354966339

theorem tailTrace_2703608 : CollatzResearch.WordTrace tailWord_2703608 prefixEnd_2703608 1388250405340963354966339 := by
  unfold tailWord_2703608
  simp only [CollatzResearch.WordTrace]
  refine ⟨49304342394648715165275739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65739123192864953553700985 49304342394648715165275739)
  ·
    refine ⟨73956513591973072747913609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49304342394648715165275739 73956513591973072747913609)
    ·
      refine ⟨55467385193979804560935207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73956513591973072747913609 55467385193979804560935207)
      ·
        refine ⟨83201077790969706841402811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55467385193979804560935207 83201077790969706841402811)
        ·
          refine ⟨124801616686454560262104217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83201077790969706841402811 124801616686454560262104217)
          ·
            refine ⟨93601212514840920196578163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124801616686454560262104217 93601212514840920196578163)
            ·
              refine ⟨140401818772261380294867245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93601212514840920196578163 140401818772261380294867245)
              ·
                refine ⟨52650682039598017610575217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140401818772261380294867245 52650682039598017610575217)
                ·
                  refine ⟨39488011529698513207931413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52650682039598017610575217 39488011529698513207931413)
                  ·
                    refine ⟨1851000540454617806621785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39488011529698513207931413 1851000540454617806621785)
                    ·
                      refine ⟨1388250405340963354966339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1851000540454617806621785 1388250405340963354966339)
                      ·
                        rfl

theorem cell23_2703608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 6, 2].length) (baseStart_2703608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703608 prefixEnd_2703608 := by exact prefixLift 2703608
  have htrace : WordTrace (prefixWord ++ tailWord_2703608) baseStart_2703608 baseEnd_2703608 := by
    simpa [prefixWord, tailWord_2703608, baseEnd_2703608] using wordTrace_append hprefix tailTrace_2703608
  have hstable : (prefixWord ++ tailWord_2703608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703608).length < 2 ^ (prefixWord ++ tailWord_2703608).sum := by decide
  have hdescent : baseEnd_2703608 < baseStart_2703608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703612 : List Nat := [2, 2, 2, 1, 4, 2, 2, 1, 2, 3, 2]
def baseStart_2703612 : Nat := 118140960795 + 2703612 * 2 ^ 59
def prefixEnd_2703612 : Nat := 4983230072969 + 3 ^ 40 * 2703612 * 2
def baseEnd_2703612 : Nat := 1388252459263581339316321

theorem tailTrace_2703612 : CollatzResearch.WordTrace tailWord_2703612 prefixEnd_2703612 1388252459263581339316321 := by
  unfold tailWord_2703612
  simp only [CollatzResearch.WordTrace]
  refine ⟨49304415340641469506848545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65739220454188626009131393 49304415340641469506848545)
  ·
    refine ⟨36978311505481102130136409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49304415340641469506848545 36978311505481102130136409)
    ·
      refine ⟨27733733629110826597602307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36978311505481102130136409 27733733629110826597602307)
      ·
        refine ⟨41600600443666239896403461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27733733629110826597602307 41600600443666239896403461)
        ·
          refine ⟨7800112583187419980575649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41600600443666239896403461 7800112583187419980575649)
          ·
            refine ⟨5850084437390564985431737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7800112583187419980575649 5850084437390564985431737)
            ·
              refine ⟨4387563328042923739073803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5850084437390564985431737 4387563328042923739073803)
              ·
                refine ⟨6581344992064385608610705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4387563328042923739073803 6581344992064385608610705)
                ·
                  refine ⟨4936008744048289206458029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6581344992064385608610705 4936008744048289206458029)
                  ·
                    refine ⟨1851003279018108452421761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4936008744048289206458029 1851003279018108452421761)
                    ·
                      refine ⟨1388252459263581339316321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1851003279018108452421761 1388252459263581339316321)
                      ·
                        rfl

theorem cell23_2703612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_2703612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703612 prefixEnd_2703612 := by exact prefixLift 2703612
  have htrace : WordTrace (prefixWord ++ tailWord_2703612) baseStart_2703612 baseEnd_2703612 := by
    simpa [prefixWord, tailWord_2703612, baseEnd_2703612] using wordTrace_append hprefix tailTrace_2703612
  have hstable : (prefixWord ++ tailWord_2703612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703612).length < 2 ^ (prefixWord ++ tailWord_2703612).sum := by decide
  have hdescent : baseEnd_2703612 < baseStart_2703612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703621 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 3, 1, 6]
def baseStart_2703621 : Nat := 118140960795 + 2703621 * 2 ^ 59
def prefixEnd_2703621 : Nat := 4983230072969 + 3 ^ 40 * 2703621 * 2
def baseEnd_2703621 : Nat := 1388257080589471804103779

theorem tailTrace_2703621 : CollatzResearch.WordTrace tailWord_2703621 prefixEnd_2703621 1388257080589471804103779 := by
  unfold tailWord_2703621
  simp only [CollatzResearch.WordTrace]
  refine ⟨98609158938250333550774717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65739439292166889033849811 98609158938250333550774717)
  ·
    refine ⟨36978434601843875081540519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98609158938250333550774717 36978434601843875081540519)
    ·
      refine ⟨55467651902765812622310779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36978434601843875081540519 55467651902765812622310779)
      ·
        refine ⟨83201477854148718933466169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55467651902765812622310779 83201477854148718933466169)
        ·
          refine ⟨62401108390611539200099627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83201477854148718933466169 62401108390611539200099627)
          ·
            refine ⟨93601662585917308800149441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62401108390611539200099627 93601662585917308800149441)
            ·
              refine ⟨70201246939437981600112081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93601662585917308800149441 70201246939437981600112081)
              ·
                refine ⟨52650935204578486200084061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70201246939437981600112081 52650935204578486200084061)
                ·
                  refine ⟨19744100701716932325031523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52650935204578486200084061 19744100701716932325031523)
                  ·
                    refine ⟨29616151052575398487547285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19744100701716932325031523 29616151052575398487547285)
                    ·
                      refine ⟨1388257080589471804103779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29616151052575398487547285 1388257080589471804103779)
                      ·
                        rfl

theorem cell23_2703621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_2703621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703621 prefixEnd_2703621 := by exact prefixLift 2703621
  have htrace : WordTrace (prefixWord ++ tailWord_2703621) baseStart_2703621 baseEnd_2703621 := by
    simpa [prefixWord, tailWord_2703621, baseEnd_2703621] using wordTrace_append hprefix tailTrace_2703621
  have hstable : (prefixWord ++ tailWord_2703621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703621).length < 2 ^ (prefixWord ++ tailWord_2703621).sum := by decide
  have hdescent : baseEnd_2703621 < baseStart_2703621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703648 : List Nat := [2, 1, 1, 5, 2, 1, 3, 8]
def baseStart_2703648 : Nat := 118140960795 + 2703648 * 2 ^ 59
def prefixEnd_2703648 : Nat := 4983230072969 + 3 ^ 40 * 2703648 * 2
def baseEnd_2703648 : Nat := 51417442391375674017265

theorem tailTrace_2703648 : CollatzResearch.WordTrace tailWord_2703648 prefixEnd_2703648 51417442391375674017265 := by
  unfold tailWord_2703648
  simp only [CollatzResearch.WordTrace]
  refine ⟨49305071854576258581003799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65740095806101678108005065 49305071854576258581003799)
  ·
    refine ⟨73957607781864387871505699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49305071854576258581003799 73957607781864387871505699)
    ·
      refine ⟨110936411672796581807258549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73957607781864387871505699 110936411672796581807258549)
      ·
        refine ⟨10400288594324679544430489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110936411672796581807258549 10400288594324679544430489)
        ·
          refine ⟨7800216445743509658322867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10400288594324679544430489 7800216445743509658322867)
          ·
            refine ⟨11700324668615264487484301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7800216445743509658322867 11700324668615264487484301)
            ·
              refine ⟨4387621750730724182806613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11700324668615264487484301 4387621750730724182806613)
              ·
                refine ⟨51417442391375674017265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4387621750730724182806613 51417442391375674017265)
                ·
                  rfl

theorem cell23_2703648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 8].length) (baseStart_2703648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703648 prefixEnd_2703648 := by exact prefixLift 2703648
  have htrace : WordTrace (prefixWord ++ tailWord_2703648) baseStart_2703648 baseEnd_2703648 := by
    simpa [prefixWord, tailWord_2703648, baseEnd_2703648] using wordTrace_append hprefix tailTrace_2703648
  have hstable : (prefixWord ++ tailWord_2703648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703648).length < 2 ^ (prefixWord ++ tailWord_2703648).sum := by decide
  have hdescent : baseEnd_2703648 < baseStart_2703648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703665 : List Nat := [1, 2, 2, 3, 4, 1, 3, 7]
def baseStart_2703665 : Nat := 118140960795 + 2703665 * 2 ^ 59
def prefixEnd_2703665 : Nat := 4983230072969 + 3 ^ 40 * 2703665 * 2
def baseEnd_2703665 : Nat := 51417765694009986368651

theorem tailTrace_2703665 : CollatzResearch.WordTrace tailWord_2703665 prefixEnd_2703665 51417765694009986368651 := by
  unfold tailWord_2703665
  simp only [CollatzResearch.WordTrace]
  refine ⟨98610763750090929065376449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65740509166727286043584299 98610763750090929065376449)
  ·
    refine ⟨73958072812568196799032337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98610763750090929065376449 73958072812568196799032337)
    ·
      refine ⟨55468554609426147599274253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73958072812568196799032337 55468554609426147599274253)
      ·
        refine ⟨20800707978534805349727845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55468554609426147599274253 20800707978534805349727845)
        ·
          refine ⟨3900132745975276003073971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20800707978534805349727845 3900132745975276003073971)
          ·
            refine ⟨5850199118962914004610957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3900132745975276003073971 5850199118962914004610957)
            ·
              refine ⟨2193824669611092751729109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5850199118962914004610957 2193824669611092751729109)
              ·
                refine ⟨51417765694009986368651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2193824669611092751729109 51417765694009986368651)
                ·
                  rfl

theorem cell23_2703665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 7].length) (baseStart_2703665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703665 prefixEnd_2703665 := by exact prefixLift 2703665
  have htrace : WordTrace (prefixWord ++ tailWord_2703665) baseStart_2703665 baseEnd_2703665 := by
    simpa [prefixWord, tailWord_2703665, baseEnd_2703665] using wordTrace_append hprefix tailTrace_2703665
  have hstable : (prefixWord ++ tailWord_2703665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703665).length < 2 ^ (prefixWord ++ tailWord_2703665).sum := by decide
  have hdescent : baseEnd_2703665 < baseStart_2703665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703698 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_2703698 : Nat := 118140960795 + 2703698 * 2 ^ 59
def prefixEnd_2703698 : Nat := 4983230072969 + 3 ^ 40 * 2703698 * 2
def baseEnd_2703698 : Nat := 1388296618599868002840925

theorem tailTrace_2703698 : CollatzResearch.WordTrace tailWord_2703698 prefixEnd_2703698 1388296618599868002840925 := by
  unfold tailWord_2703698
  simp only [CollatzResearch.WordTrace]
  refine ⟨24652991839742843925331937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65741311572647583800885165 24652991839742843925331937)
  ·
    refine ⟨18489743879807132943998953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24652991839742843925331937 18489743879807132943998953)
    ·
      refine ⟨13867307909855349707999215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18489743879807132943998953 13867307909855349707999215)
      ·
        refine ⟨20800961864783024561998823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13867307909855349707999215 20800961864783024561998823)
        ·
          refine ⟨31201442797174536842998235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20800961864783024561998823 31201442797174536842998235)
          ·
            refine ⟨46802164195761805264497353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31201442797174536842998235 46802164195761805264497353)
            ·
              refine ⟨35101623146821353948373015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46802164195761805264497353 35101623146821353948373015)
              ·
                refine ⟨52652434720232030922559523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35101623146821353948373015 52652434720232030922559523)
                ·
                  refine ⟨78978652080348046383839285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52652434720232030922559523 78978652080348046383839285)
                  ·
                    refine ⟨7404248632532629348484933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78978652080348046383839285 7404248632532629348484933)
                    ·
                      refine ⟨1388296618599868002840925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7404248632532629348484933 1388296618599868002840925)
                      ·
                        rfl

theorem cell23_2703698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_2703698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703698 prefixEnd_2703698 := by exact prefixLift 2703698
  have htrace : WordTrace (prefixWord ++ tailWord_2703698) baseStart_2703698 baseEnd_2703698 := by
    simpa [prefixWord, tailWord_2703698, baseEnd_2703698] using wordTrace_append hprefix tailTrace_2703698
  have hstable : (prefixWord ++ tailWord_2703698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703698).length < 2 ^ (prefixWord ++ tailWord_2703698).sum := by decide
  have hdescent : baseEnd_2703698 < baseStart_2703698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703719 : List Nat := [1, 1, 5, 1, 3, 2, 2, 2, 1, 3, 2]
def baseStart_2703719 : Nat := 118140960795 + 2703719 * 2 ^ 59
def prefixEnd_2703719 : Nat := 4983230072969 + 3 ^ 40 * 2703719 * 2
def baseEnd_2703719 : Nat := 1388307401693612420678329

theorem tailTrace_2703719 : CollatzResearch.WordTrace tailWord_2703719 prefixEnd_2703719 1388307401693612420678329 := by
  unfold tailWord_2703719
  simp only [CollatzResearch.WordTrace]
  refine ⟨98612733291895296287842211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65741822194596864191894807 98612733291895296287842211)
  ·
    refine ⟨147919099937842944431763317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98612733291895296287842211 147919099937842944431763317)
    ·
      refine ⟨13867415619172776040477811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147919099937842944431763317 13867415619172776040477811)
      ·
        refine ⟨20801123428759164060716717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13867415619172776040477811 20801123428759164060716717)
        ·
          refine ⟨7800421285784686522768769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20801123428759164060716717 7800421285784686522768769)
          ·
            refine ⟨5850315964338514892076577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7800421285784686522768769 5850315964338514892076577)
            ·
              refine ⟨4387736973253886169057433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5850315964338514892076577 4387736973253886169057433)
              ·
                refine ⟨3290802729940414626793075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4387736973253886169057433 3290802729940414626793075)
                ·
                  refine ⟨4936204094910621940189613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3290802729940414626793075 4936204094910621940189613)
                  ·
                    refine ⟨1851076535591483227571105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4936204094910621940189613 1851076535591483227571105)
                    ·
                      refine ⟨1388307401693612420678329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1851076535591483227571105 1388307401693612420678329)
                      ·
                        rfl

theorem cell23_2703719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_2703719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703719 prefixEnd_2703719 := by exact prefixLift 2703719
  have htrace : WordTrace (prefixWord ++ tailWord_2703719) baseStart_2703719 baseEnd_2703719 := by
    simpa [prefixWord, tailWord_2703719, baseEnd_2703719] using wordTrace_append hprefix tailTrace_2703719
  have hstable : (prefixWord ++ tailWord_2703719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703719).length < 2 ^ (prefixWord ++ tailWord_2703719).sum := by decide
  have hdescent : baseEnd_2703719 < baseStart_2703719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703748 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_2703748 : Nat := 118140960795 + 2703748 * 2 ^ 59
def prefixEnd_2703748 : Nat := 4983230072969 + 3 ^ 40 * 2703748 * 2
def baseEnd_2703748 : Nat := 1388322292632592807215695

theorem tailTrace_2703748 : CollatzResearch.WordTrace tailWord_2703748 prefixEnd_2703748 1388322292632592807215695 := by
  unfold tailWord_2703748
  simp only [CollatzResearch.WordTrace]
  refine ⟨49306895504395117120323949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65742527339193489493765265 49306895504395117120323949)
  ·
    refine ⟨18490085814148168920121481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49306895504395117120323949 18490085814148168920121481)
    ·
      refine ⟨13867564360611126690091111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18490085814148168920121481 13867564360611126690091111)
      ·
        refine ⟨20801346540916690035136667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13867564360611126690091111 20801346540916690035136667)
        ·
          refine ⟨31202019811375035052705001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20801346540916690035136667 31202019811375035052705001)
          ·
            refine ⟨23401514858531276289528751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31202019811375035052705001 23401514858531276289528751)
            ·
              refine ⟨35102272287796914434293127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23401514858531276289528751 35102272287796914434293127)
              ·
                refine ⟨52653408431695371651439691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35102272287796914434293127 52653408431695371651439691)
                ·
                  refine ⟨78980112647543057477159537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52653408431695371651439691 78980112647543057477159537)
                  ·
                    refine ⟨59235084485657293107869653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78980112647543057477159537 59235084485657293107869653)
                    ·
                      refine ⟨1388322292632592807215695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59235084485657293107869653 1388322292632592807215695)
                      ·
                        rfl

theorem cell23_2703748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_2703748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703748 prefixEnd_2703748 := by exact prefixLift 2703748
  have htrace : WordTrace (prefixWord ++ tailWord_2703748) baseStart_2703748 baseEnd_2703748 := by
    simpa [prefixWord, tailWord_2703748, baseEnd_2703748] using wordTrace_append hprefix tailTrace_2703748
  have hstable : (prefixWord ++ tailWord_2703748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703748).length < 2 ^ (prefixWord ++ tailWord_2703748).sum := by decide
  have hdescent : baseEnd_2703748 < baseStart_2703748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703755 : List Nat := [1, 1, 1, 1, 4, 6, 1, 1, 7]
def baseStart_2703755 : Nat := 118140960795 + 2703755 * 2 ^ 59
def prefixEnd_2703755 : Nat := 4983230072969 + 3 ^ 40 * 2703755 * 2
def baseEnd_2703755 : Nat := 154258431888574919980907

theorem tailTrace_2703755 : CollatzResearch.WordTrace tailWord_2703755 prefixEnd_2703755 154258431888574919980907 := by
  unfold tailWord_2703755
  simp only [CollatzResearch.WordTrace]
  refine ⟨98614046319764874436152719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65742697546509916290768479 98614046319764874436152719)
  ·
    refine ⟨147921069479647311654229079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98614046319764874436152719 147921069479647311654229079)
    ·
      refine ⟨221881604219470967481343619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147921069479647311654229079 221881604219470967481343619)
      ·
        refine ⟨332822406329206451222015429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221881604219470967481343619 332822406329206451222015429)
        ·
          refine ⟨62404201186726209604127893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 332822406329206451222015429 62404201186726209604127893)
          ·
            refine ⟨2925196930627791075193495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62404201186726209604127893 2925196930627791075193495)
            ·
              refine ⟨4387795395941686612790243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2925196930627791075193495 4387795395941686612790243)
              ·
                refine ⟨6581693093912529919185365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4387795395941686612790243 6581693093912529919185365)
                ·
                  refine ⟨154258431888574919980907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6581693093912529919185365 154258431888574919980907)
                  ·
                    rfl

theorem cell23_2703755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 7].length) (baseStart_2703755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703755 prefixEnd_2703755 := by exact prefixLift 2703755
  have htrace : WordTrace (prefixWord ++ tailWord_2703755) baseStart_2703755 baseEnd_2703755 := by
    simpa [prefixWord, tailWord_2703755, baseEnd_2703755] using wordTrace_append hprefix tailTrace_2703755
  have hstable : (prefixWord ++ tailWord_2703755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703755).length < 2 ^ (prefixWord ++ tailWord_2703755).sum := by decide
  have hdescent : baseEnd_2703755 < baseStart_2703755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703808 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 5]
def baseStart_2703808 : Nat := 118140960795 + 2703808 * 2 ^ 59
def prefixEnd_2703808 : Nat := 4983230072969 + 3 ^ 40 * 2703808 * 2
def baseEnd_2703808 : Nat := 1388353101471862572465419

theorem tailTrace_2703808 : CollatzResearch.WordTrace tailWord_2703808 prefixEnd_2703808 1388353101471862572465419 := by
  unfold tailWord_2703808
  simp only [CollatzResearch.WordTrace]
  refine ⟨49307989694286432243916039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65743986259048576325221385 49307989694286432243916039)
  ·
    refine ⟨73961984541429648365874059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49307989694286432243916039 73961984541429648365874059)
    ·
      refine ⟨110942976812144472548811089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73961984541429648365874059 110942976812144472548811089)
      ·
        refine ⟨83207232609108354411608317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110942976812144472548811089 83207232609108354411608317)
        ·
          refine ⟨31202712228415632904353119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83207232609108354411608317 31202712228415632904353119)
          ·
            refine ⟨46804068342623449356529679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31202712228415632904353119 46804068342623449356529679)
            ·
              refine ⟨70206102513935174034794519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46804068342623449356529679 70206102513935174034794519)
              ·
                refine ⟨105309153770902761052191779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70206102513935174034794519 105309153770902761052191779)
                ·
                  refine ⟨157963730656354141578287669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105309153770902761052191779 157963730656354141578287669)
                  ·
                    refine ⟨14809099749033200772964469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 157963730656354141578287669 14809099749033200772964469)
                    ·
                      refine ⟨1388353101471862572465419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14809099749033200772964469 1388353101471862572465419)
                      ·
                        rfl

theorem cell23_2703808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_2703808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703808 prefixEnd_2703808 := by exact prefixLift 2703808
  have htrace : WordTrace (prefixWord ++ tailWord_2703808) baseStart_2703808 baseEnd_2703808 := by
    simpa [prefixWord, tailWord_2703808, baseEnd_2703808] using wordTrace_append hprefix tailTrace_2703808
  have hstable : (prefixWord ++ tailWord_2703808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703808).length < 2 ^ (prefixWord ++ tailWord_2703808).sum := by decide
  have hdescent : baseEnd_2703808 < baseStart_2703808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703825 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 4, 2, 3]
def baseStart_2703825 : Nat := 118140960795 + 2703825 * 2 ^ 59
def prefixEnd_2703825 : Nat := 4983230072969 + 3 ^ 40 * 2703825 * 2
def baseEnd_2703825 : Nat := 1388361830642989005952841

theorem tailTrace_2703825 : CollatzResearch.WordTrace tailWord_2703825 prefixEnd_2703825 1388361830642989005952841 := by
  unfold tailWord_2703825
  simp only [CollatzResearch.WordTrace]
  refine ⟨98616599429511276391200929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65744399619674184260800619 98616599429511276391200929)
  ·
    refine ⟨73962449572133457293400697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98616599429511276391200929 73962449572133457293400697)
    ·
      refine ⟨55471837179100092970050523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73962449572133457293400697 55471837179100092970050523)
      ·
        refine ⟨83207755768650139455075785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55471837179100092970050523 83207755768650139455075785)
        ·
          refine ⟨62405816826487604591306839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83207755768650139455075785 62405816826487604591306839)
          ·
            refine ⟨93608725239731406886960259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62405816826487604591306839 93608725239731406886960259)
            ·
              refine ⟨140413087859597110330440389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93608725239731406886960259 140413087859597110330440389)
              ·
                refine ⟨26327453973674458186957573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140413087859597110330440389 26327453973674458186957573)
                ·
                  refine ⟨4936397620063960910054545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26327453973674458186957573 4936397620063960910054545)
                  ·
                    refine ⟨3702298215047970682540909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4936397620063960910054545 3702298215047970682540909)
                    ·
                      refine ⟨1388361830642989005952841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3702298215047970682540909 1388361830642989005952841)
                      ·
                        rfl

theorem cell23_2703825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_2703825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703825 prefixEnd_2703825 := by exact prefixLift 2703825
  have htrace : WordTrace (prefixWord ++ tailWord_2703825) baseStart_2703825 baseEnd_2703825 := by
    simpa [prefixWord, tailWord_2703825, baseEnd_2703825] using wordTrace_append hprefix tailTrace_2703825
  have hstable : (prefixWord ++ tailWord_2703825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703825).length < 2 ^ (prefixWord ++ tailWord_2703825).sum := by decide
  have hdescent : baseEnd_2703825 < baseStart_2703825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703879 : List Nat := [1, 1, 4, 3, 3, 1, 3, 1, 6]
def baseStart_2703879 : Nat := 118140960795 + 2703879 * 2 ^ 59
def prefixEnd_2703879 : Nat := 4983230072969 + 3 ^ 40 * 2703879 * 2
def baseEnd_2703879 : Nat := 154265506510925754964177

theorem tailTrace_2703879 : CollatzResearch.WordTrace tailWord_2703879 prefixEnd_2703879 154265506510925754964177 := by
  unfold tailWord_2703879
  simp only [CollatzResearch.WordTrace]
  refine ⟨98618568971315643613666691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65745712647543762409111127 98618568971315643613666691)
  ·
    refine ⟨147927853456973465420500037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98618568971315643613666691 147927853456973465420500037)
    ·
      refine ⟨27736472523182524766343757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147927853456973465420500037 27736472523182524766343757)
      ·
        refine ⟨10401177196193446787378909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27736472523182524766343757 10401177196193446787378909)
        ·
          refine ⟨3900441448572542545267091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10401177196193446787378909 3900441448572542545267091)
          ·
            refine ⟨5850662172858813817900637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3900441448572542545267091 5850662172858813817900637)
            ·
              refine ⟨2193998314822055181712739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5850662172858813817900637 2193998314822055181712739)
              ·
                refine ⟨3290997472233082772569109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2193998314822055181712739 3290997472233082772569109)
                ·
                  refine ⟨154265506510925754964177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3290997472233082772569109 154265506510925754964177)
                  ·
                    rfl

theorem cell23_2703879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 6].length) (baseStart_2703879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703879 prefixEnd_2703879 := by exact prefixLift 2703879
  have htrace : WordTrace (prefixWord ++ tailWord_2703879) baseStart_2703879 baseEnd_2703879 := by
    simpa [prefixWord, tailWord_2703879, baseEnd_2703879] using wordTrace_append hprefix tailTrace_2703879
  have hstable : (prefixWord ++ tailWord_2703879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703879).length < 2 ^ (prefixWord ++ tailWord_2703879).sum := by decide
  have hdescent : baseEnd_2703879 < baseStart_2703879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703882 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 3, 5, 2]
def baseStart_2703882 : Nat := 118140960795 + 2703882 * 2 ^ 59
def prefixEnd_2703882 : Nat := 4983230072969 + 3 ^ 40 * 2703882 * 2
def baseEnd_2703882 : Nat := 1388391099040295282940079

theorem tailTrace_2703882 : CollatzResearch.WordTrace tailWord_2703882 prefixEnd_2703882 1388391099040295282940079 := by
  unfold tailWord_2703882
  simp only [CollatzResearch.WordTrace]
  refine ⟨24654669597576193781506475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65745785593536516750683933 24654669597576193781506475)
  ·
    refine ⟨36982004396364290672259713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24654669597576193781506475 36982004396364290672259713)
    ·
      refine ⟨27736503297273218004194785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36982004396364290672259713 27736503297273218004194785)
      ·
        refine ⟨20802377472954913503146089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27736503297273218004194785 20802377472954913503146089)
        ·
          refine ⟨15601783104716185127359567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20802377472954913503146089 15601783104716185127359567)
          ·
            refine ⟨23402674657074277691039351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15601783104716185127359567 23402674657074277691039351)
            ·
              refine ⟨35104011985611416536559027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23402674657074277691039351 35104011985611416536559027)
              ·
                refine ⟨52656017978417124804838541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35104011985611416536559027 52656017978417124804838541)
                ·
                  refine ⟨19746006741906421801814453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52656017978417124804838541 19746006741906421801814453)
                  ·
                    refine ⟨1851188132053727043920105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19746006741906421801814453 1851188132053727043920105)
                    ·
                      refine ⟨1388391099040295282940079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1851188132053727043920105 1388391099040295282940079)
                      ·
                        rfl

theorem cell23_2703882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_2703882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703882 prefixEnd_2703882 := by exact prefixLift 2703882
  have htrace : WordTrace (prefixWord ++ tailWord_2703882) baseStart_2703882 baseEnd_2703882 := by
    simpa [prefixWord, tailWord_2703882, baseEnd_2703882] using wordTrace_append hprefix tailTrace_2703882
  have hstable : (prefixWord ++ tailWord_2703882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703882).length < 2 ^ (prefixWord ++ tailWord_2703882).sum := by decide
  have hdescent : baseEnd_2703882 < baseStart_2703882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703905 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 3, 6]
def baseStart_2703905 : Nat := 118140960795 + 2703905 * 2 ^ 59
def prefixEnd_2703905 : Nat := 4983230072969 + 3 ^ 40 * 2703905 * 2
def baseEnd_2703905 : Nat := 462800969698449564317491

theorem tailTrace_2703905 : CollatzResearch.WordTrace tailWord_2703905 prefixEnd_2703905 462800969698449564317491 := by
  unfold tailWord_2703905
  simp only [CollatzResearch.WordTrace]
  refine ⟨98619517269221450054113169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65746344846147633369408779 98619517269221450054113169)
  ·
    refine ⟨73964637951916087540584877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98619517269221450054113169 73964637951916087540584877)
    ·
      refine ⟨27736739231968532827719329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73964637951916087540584877 27736739231968532827719329)
      ·
        refine ⟨20802554423976399620789497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27736739231968532827719329 20802554423976399620789497)
        ·
          refine ⟨15601915817982299715592123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20802554423976399620789497 15601915817982299715592123)
          ·
            refine ⟨23402873726973449573388185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15601915817982299715592123 23402873726973449573388185)
            ·
              refine ⟨17552155295230087180041139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23402873726973449573388185 17552155295230087180041139)
              ·
                refine ⟨26328232942845130770061709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17552155295230087180041139 26328232942845130770061709)
                ·
                  refine ⟨9873087353566924038773141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26328232942845130770061709 9873087353566924038773141)
                  ·
                    refine ⟨462800969698449564317491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9873087353566924038773141 462800969698449564317491)
                    ·
                      rfl

theorem cell23_2703905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_2703905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703905 prefixEnd_2703905 := by exact prefixLift 2703905
  have htrace : WordTrace (prefixWord ++ tailWord_2703905) baseStart_2703905 baseEnd_2703905 := by
    simpa [prefixWord, tailWord_2703905, baseEnd_2703905] using wordTrace_append hprefix tailTrace_2703905
  have hstable : (prefixWord ++ tailWord_2703905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703905).length < 2 ^ (prefixWord ++ tailWord_2703905).sum := by decide
  have hdescent : baseEnd_2703905 < baseStart_2703905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703917 : List Nat := [1, 5, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_2703917 : Nat := 118140960795 + 2703917 * 2 ^ 59
def prefixEnd_2703917 : Nat := 4983230072969 + 3 ^ 40 * 2703917 * 2
def baseEnd_2703917 : Nat := 462803023621067548667473

theorem tailTrace_2703917 : CollatzResearch.WordTrace tailWord_2703917 prefixEnd_2703917 462803023621067548667473 := by
  unfold tailWord_2703917
  simp only [CollatzResearch.WordTrace]
  refine ⟨98619954945177976103550005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65746636630118650735700003 98619954945177976103550005)
  ·
    refine ⟨9245620776110435259707813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98619954945177976103550005 9245620776110435259707813)
    ·
      refine ⟨1733553895520706611195215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9245620776110435259707813 1733553895520706611195215)
      ·
        refine ⟨2600330843281059916792823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1733553895520706611195215 2600330843281059916792823)
        ·
          refine ⟨3900496264921589875189235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2600330843281059916792823 3900496264921589875189235)
          ·
            refine ⟨5850744397382384812783853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3900496264921589875189235 5850744397382384812783853)
            ·
              refine ⟨2194029149018394304793945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5850744397382384812783853 2194029149018394304793945)
              ·
                refine ⟨1645521861763795728595459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2194029149018394304793945 1645521861763795728595459)
                ·
                  refine ⟨2468282792645693592893189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1645521861763795728595459 2468282792645693592893189)
                  ·
                    refine ⟨462803023621067548667473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2468282792645693592893189 462803023621067548667473)
                    ·
                      rfl

theorem cell23_2703917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_2703917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703917 prefixEnd_2703917 := by exact prefixLift 2703917
  have htrace : WordTrace (prefixWord ++ tailWord_2703917) baseStart_2703917 baseEnd_2703917 := by
    simpa [prefixWord, tailWord_2703917, baseEnd_2703917] using wordTrace_append hprefix tailTrace_2703917
  have hstable : (prefixWord ++ tailWord_2703917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703917).length < 2 ^ (prefixWord ++ tailWord_2703917).sum := by decide
  have hdescent : baseEnd_2703917 < baseStart_2703917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703922 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 4, 4]
def baseStart_2703922 : Nat := 118140960795 + 2703922 * 2 ^ 59
def prefixEnd_2703922 : Nat := 4983230072969 + 3 ^ 40 * 2703922 * 2
def baseEnd_2703922 : Nat := 462803879422158375479965

theorem tailTrace_2703922 : CollatzResearch.WordTrace tailWord_2703922 prefixEnd_2703922 462803879422158375479965 := by
  unfold tailWord_2703922
  simp only [CollatzResearch.WordTrace]
  refine ⟨24655034327539965489370505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65746758206773241304988013 24655034327539965489370505)
  ·
    refine ⟨18491275745654974117027879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24655034327539965489370505 18491275745654974117027879)
    ·
      refine ⟨27736913618482461175541819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18491275745654974117027879 27736913618482461175541819)
      ·
        refine ⟨41605370427723691763312729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27736913618482461175541819 41605370427723691763312729)
        ·
          refine ⟨31204027820792768822484547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41605370427723691763312729 31204027820792768822484547)
          ·
            refine ⟨46806041731189153233726821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31204027820792768822484547 46806041731189153233726821)
            ·
              refine ⟨8776132824597966231323779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46806041731189153233726821 8776132824597966231323779)
              ·
                refine ⟨13164199236896949346985669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8776132824597966231323779 13164199236896949346985669)
                ·
                  refine ⟨2468287356918178002559813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13164199236896949346985669 2468287356918178002559813)
                  ·
                    refine ⟨462803879422158375479965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2468287356918178002559813 462803879422158375479965)
                    ·
                      rfl

theorem cell23_2703922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_2703922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703922 prefixEnd_2703922 := by exact prefixLift 2703922
  have htrace : WordTrace (prefixWord ++ tailWord_2703922) baseStart_2703922 baseEnd_2703922 := by
    simpa [prefixWord, tailWord_2703922, baseEnd_2703922] using wordTrace_append hprefix tailTrace_2703922
  have hstable : (prefixWord ++ tailWord_2703922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703922).length < 2 ^ (prefixWord ++ tailWord_2703922).sum := by decide
  have hdescent : baseEnd_2703922 < baseStart_2703922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703925 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_2703925 : Nat := 118140960795 + 2703925 * 2 ^ 59
def prefixEnd_2703925 : Nat := 4983230072969 + 3 ^ 40 * 2703925 * 2
def baseEnd_2703925 : Nat := 1388413178708438614702381

theorem tailTrace_2703925 : CollatzResearch.WordTrace tailWord_2703925 prefixEnd_2703925 1388413178708438614702381 := by
  unfold tailWord_2703925
  simp only [CollatzResearch.WordTrace]
  refine ⟨98620246729148993469841229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65746831152765995646560819 98620246729148993469841229)
  ·
    refine ⟨36982592523430872551190461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98620246729148993469841229 36982592523430872551190461)
    ·
      refine ⟨13868472196286577206696423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36982592523430872551190461 13868472196286577206696423)
      ·
        refine ⟨20802708294429865810044635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13868472196286577206696423 20802708294429865810044635)
        ·
          refine ⟨31204062441644798715066953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20802708294429865810044635 31204062441644798715066953)
          ·
            refine ⟨23403046831233599036300215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31204062441644798715066953 23403046831233599036300215)
            ·
              refine ⟨35104570246850398554450323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23403046831233599036300215 35104570246850398554450323)
              ·
                refine ⟨52656855370275597831675485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35104570246850398554450323 52656855370275597831675485)
                ·
                  refine ⟨19746320763853349186878307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52656855370275597831675485 19746320763853349186878307)
                  ·
                    refine ⟨29619481145780023780317461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19746320763853349186878307 29619481145780023780317461)
                    ·
                      refine ⟨1388413178708438614702381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29619481145780023780317461 1388413178708438614702381)
                      ·
                        rfl

theorem cell23_2703925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_2703925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703925 prefixEnd_2703925 := by exact prefixLift 2703925
  have htrace : WordTrace (prefixWord ++ tailWord_2703925) baseStart_2703925 baseEnd_2703925 := by
    simpa [prefixWord, tailWord_2703925, baseEnd_2703925] using wordTrace_append hprefix tailTrace_2703925
  have hstable : (prefixWord ++ tailWord_2703925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703925).length < 2 ^ (prefixWord ++ tailWord_2703925).sum := by decide
  have hdescent : baseEnd_2703925 < baseStart_2703925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703932 : List Nat := [2, 2, 2, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_2703932 : Nat := 118140960795 + 2703932 * 2 ^ 59
def prefixEnd_2703932 : Nat := 4983230072969 + 3 ^ 40 * 2703932 * 2
def baseEnd_2703932 : Nat := 1388416773073020087314849

theorem tailTrace_2703932 : CollatzResearch.WordTrace tailWord_2703932 prefixEnd_2703932 1388416773073020087314849 := by
  unfold tailWord_2703932
  simp only [CollatzResearch.WordTrace]
  refine ⟨49310251020061816832673025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65747001360082422443564033 49310251020061816832673025)
  ·
    refine ⟨36982688265046362624504769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49310251020061816832673025 36982688265046362624504769)
    ·
      refine ⟨27737016198784771968378577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36982688265046362624504769 27737016198784771968378577)
      ·
        refine ⟨20802762149088578976283933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27737016198784771968378577 20802762149088578976283933)
        ·
          refine ⟨7801035805908217116106475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20802762149088578976283933 7801035805908217116106475)
          ·
            refine ⟨11701553708862325674159713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7801035805908217116106475 11701553708862325674159713)
            ·
              refine ⟨8776165281646744255619785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11701553708862325674159713 8776165281646744255619785)
              ·
                refine ⟨6582123961235058191714839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8776165281646744255619785 6582123961235058191714839)
                ·
                  refine ⟨9873185941852587287572259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6582123961235058191714839 9873185941852587287572259)
                  ·
                    refine ⟨14809778912778880931358389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9873185941852587287572259 14809778912778880931358389)
                    ·
                      refine ⟨1388416773073020087314849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14809778912778880931358389 1388416773073020087314849)
                      ·
                        rfl

theorem cell23_2703932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_2703932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703932 prefixEnd_2703932 := by exact prefixLift 2703932
  have htrace : WordTrace (prefixWord ++ tailWord_2703932) baseStart_2703932 baseEnd_2703932 := by
    simpa [prefixWord, tailWord_2703932, baseEnd_2703932] using wordTrace_append hprefix tailTrace_2703932
  have hstable : (prefixWord ++ tailWord_2703932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703932).length < 2 ^ (prefixWord ++ tailWord_2703932).sum := by decide
  have hdescent : baseEnd_2703932 < baseStart_2703932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703935 : List Nat := [1, 1, 2, 2, 3, 2, 4, 8]
def baseStart_2703935 : Nat := 118140960795 + 2703935 * 2 ^ 59
def prefixEnd_2703935 : Nat := 4983230072969 + 3 ^ 40 * 2703935 * 2
def baseEnd_2703935 : Nat := 51422900500554947243605

theorem tailTrace_2703935 : CollatzResearch.WordTrace tailWord_2703935 prefixEnd_2703935 51422900500554947243605 := by
  unfold tailWord_2703935
  simp only [CollatzResearch.WordTrace]
  refine ⟨98620611459112765177705259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65747074306075176785136839 98620611459112765177705259)
  ·
    refine ⟨147930917188669147766557889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98620611459112765177705259 147930917188669147766557889)
    ·
      refine ⟨110948187891501860824918417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147930917188669147766557889 110948187891501860824918417)
      ·
        refine ⟨83211140918626395618688813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110948187891501860824918417 83211140918626395618688813)
        ·
          refine ⟨31204177844484898357008305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83211140918626395618688813 31204177844484898357008305)
          ·
            refine ⟨23403133383363673767756229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31204177844484898357008305 23403133383363673767756229)
            ·
              refine ⟨4388087509380688831454293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23403133383363673767756229 4388087509380688831454293)
              ·
                refine ⟨51422900500554947243605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4388087509380688831454293 51422900500554947243605)
                ·
                  rfl

theorem cell23_2703935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 8].length) (baseStart_2703935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703935 prefixEnd_2703935 := by exact prefixLift 2703935
  have htrace : WordTrace (prefixWord ++ tailWord_2703935) baseStart_2703935 baseEnd_2703935 := by
    simpa [prefixWord, tailWord_2703935, baseEnd_2703935] using wordTrace_append hprefix tailTrace_2703935
  have hstable : (prefixWord ++ tailWord_2703935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703935).length < 2 ^ (prefixWord ++ tailWord_2703935).sum := by decide
  have hdescent : baseEnd_2703935 < baseStart_2703935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703982 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 2, 7]
def baseStart_2703982 : Nat := 118140960795 + 2703982 * 2 ^ 59
def prefixEnd_2703982 : Nat := 4983230072969 + 3 ^ 40 * 2703982 * 2
def baseEnd_2703982 : Nat := 462814149035248297229873

theorem tailTrace_2703982 : CollatzResearch.WordTrace tailWord_2703982 prefixEnd_2703982 462814149035248297229873 := by
  unfold tailWord_2703982
  simp only [CollatzResearch.WordTrace]
  refine ⟨12327790711242811525583275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65748217126628328136444133 12327790711242811525583275)
  ·
    refine ⟨18491686066864217288374913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12327790711242811525583275 18491686066864217288374913)
    ·
      refine ⟨13868764550148162966281185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18491686066864217288374913 13868764550148162966281185)
      ·
        refine ⟨10401573412611122224710889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13868764550148162966281185 10401573412611122224710889)
        ·
          refine ⟨7801180059458341668533167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10401573412611122224710889 7801180059458341668533167)
          ·
            refine ⟨11701770089187512502799751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7801180059458341668533167 11701770089187512502799751)
            ·
              refine ⟨17552655133781268754199627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11701770089187512502799751 17552655133781268754199627)
              ·
                refine ⟨26328982700671903131299441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17552655133781268754199627 26328982700671903131299441)
                ·
                  refine ⟨19746737025503927348474581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26328982700671903131299441 19746737025503927348474581)
                  ·
                    refine ⟨462814149035248297229873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19746737025503927348474581 462814149035248297229873)
                    ·
                      rfl

theorem cell23_2703982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_2703982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2703982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2703982 prefixEnd_2703982 := by exact prefixLift 2703982
  have htrace : WordTrace (prefixWord ++ tailWord_2703982) baseStart_2703982 baseEnd_2703982 := by
    simpa [prefixWord, tailWord_2703982, baseEnd_2703982] using wordTrace_append hprefix tailTrace_2703982
  have hstable : (prefixWord ++ tailWord_2703982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703982).length < 2 ^ (prefixWord ++ tailWord_2703982).sum := by decide
  have hdescent : baseEnd_2703982 < baseStart_2703982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704019 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 6, 2, 2]
def baseStart_2704019 : Nat := 118140960795 + 2704019 * 2 ^ 59
def prefixEnd_2704019 : Nat := 4983230072969 + 3 ^ 40 * 2704019 * 2
def baseEnd_2704019 : Nat := 1388461445889961246926949

theorem tailTrace_2704019 : CollatzResearch.WordTrace tailWord_2704019 prefixEnd_2704019 1388461445889961246926949 := by
  unfold tailWord_2704019
  simp only [CollatzResearch.WordTrace]
  refine ⟨98623675190808447523763111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65749116793872298349175407 98623675190808447523763111)
  ·
    refine ⟨147935512786212671285644667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98623675190808447523763111 147935512786212671285644667)
    ·
      refine ⟨221903269179319006928467001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147935512786212671285644667 221903269179319006928467001)
      ·
        refine ⟨166427451884489255196350251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221903269179319006928467001 166427451884489255196350251)
        ·
          refine ⟨249641177826733882794525377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166427451884489255196350251 249641177826733882794525377)
          ·
            refine ⟨187230883370050412095894033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249641177826733882794525377 187230883370050412095894033)
            ·
              refine ⟨140423162527537809071920525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187230883370050412095894033 140423162527537809071920525)
              ·
                refine ⟨52658685947826678401970197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140423162527537809071920525 52658685947826678401970197)
                ·
                  refine ⟨2468375903804375550092353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52658685947826678401970197 2468375903804375550092353)
                  ·
                    refine ⟨1851281927853281662569265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2468375903804375550092353 1851281927853281662569265)
                    ·
                      refine ⟨1388461445889961246926949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1851281927853281662569265 1388461445889961246926949)
                      ·
                        rfl

theorem cell23_2704019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 2, 2].length) (baseStart_2704019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704019 prefixEnd_2704019 := by exact prefixLift 2704019
  have htrace : WordTrace (prefixWord ++ tailWord_2704019) baseStart_2704019 baseEnd_2704019 := by
    simpa [prefixWord, tailWord_2704019, baseEnd_2704019] using wordTrace_append hprefix tailTrace_2704019
  have hstable : (prefixWord ++ tailWord_2704019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704019).length < 2 ^ (prefixWord ++ tailWord_2704019).sum := by decide
  have hdescent : baseEnd_2704019 < baseStart_2704019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704025 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 9]
def baseStart_2704025 : Nat := 118140960795 + 2704025 * 2 ^ 59
def prefixEnd_2704025 : Nat := 4983230072969 + 3 ^ 40 * 2704025 * 2
def baseEnd_2704025 : Nat := 154273836308209802605769

theorem tailTrace_2704025 : CollatzResearch.WordTrace tailWord_2704025 prefixEnd_2704025 154273836308209802605769 := by
  unfold tailWord_2704025
  simp only [CollatzResearch.WordTrace]
  refine ⟨98623894028786710548481529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65749262685857807032321019 98623894028786710548481529)
  ·
    refine ⟨73967920521590032911361147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98623894028786710548481529 73967920521590032911361147)
    ·
      refine ⟨110951880782385049367041721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73967920521590032911361147 110951880782385049367041721)
      ·
        refine ⟨83213910586788787025281291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110951880782385049367041721 83213910586788787025281291)
        ·
          refine ⟨124820865880183180537921937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83213910586788787025281291 124820865880183180537921937)
          ·
            refine ⟨93615649410137385403441453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124820865880183180537921937 93615649410137385403441453)
            ·
              refine ⟨35105868528801519526290545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93615649410137385403441453 35105868528801519526290545)
              ·
                refine ⟨26329401396601139644717909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35105868528801519526290545 26329401396601139644717909)
                ·
                  refine ⟨154273836308209802605769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26329401396601139644717909 154273836308209802605769)
                  ·
                    rfl

theorem cell23_2704025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 9].length) (baseStart_2704025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704025 prefixEnd_2704025 := by exact prefixLift 2704025
  have htrace : WordTrace (prefixWord ++ tailWord_2704025) baseStart_2704025 baseEnd_2704025 := by
    simpa [prefixWord, tailWord_2704025, baseEnd_2704025] using wordTrace_append hprefix tailTrace_2704025
  have hstable : (prefixWord ++ tailWord_2704025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704025).length < 2 ^ (prefixWord ++ tailWord_2704025).sum := by decide
  have hdescent : baseEnd_2704025 < baseStart_2704025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704035 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 9]
def baseStart_2704035 : Nat := 118140960795 + 2704035 * 2 ^ 59
def prefixEnd_2704035 : Nat := 4983230072969 + 3 ^ 40 * 2704035 * 2
def baseEnd_2704035 : Nat := 1388469661580433184326875

theorem tailTrace_2704035 : CollatzResearch.WordTrace tailWord_2704035 prefixEnd_2704035 1388469661580433184326875 := by
  unfold tailWord_2704035
  simp only [CollatzResearch.WordTrace]
  refine ⟨98624258758750482256345559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65749505839166988170897039 98624258758750482256345559)
  ·
    refine ⟨147936388138125723384518339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98624258758750482256345559 147936388138125723384518339)
    ·
      refine ⟨221904582207188585076777509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147936388138125723384518339 221904582207188585076777509)
      ·
        refine ⟨41607109163847859701895783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221904582207188585076777509 41607109163847859701895783)
        ·
          refine ⟨62410663745771789552843675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41607109163847859701895783 62410663745771789552843675)
          ·
            refine ⟨93615995618657684329265513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62410663745771789552843675 93615995618657684329265513)
            ·
              refine ⟨70211996713993263246949135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93615995618657684329265513 70211996713993263246949135)
              ·
                refine ⟨105317995070989894870423703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70211996713993263246949135 105317995070989894870423703)
                ·
                  refine ⟨157976992606484842305635555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105317995070989894870423703 157976992606484842305635555)
                  ·
                    refine ⟨236965488909727263458453333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 157976992606484842305635555 236965488909727263458453333)
                    ·
                      refine ⟨1388469661580433184326875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 236965488909727263458453333 1388469661580433184326875)
                      ·
                        rfl

theorem cell23_2704035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_2704035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704035 prefixEnd_2704035 := by exact prefixLift 2704035
  have htrace : WordTrace (prefixWord ++ tailWord_2704035) baseStart_2704035 baseEnd_2704035 := by
    simpa [prefixWord, tailWord_2704035, baseEnd_2704035] using wordTrace_append hprefix tailTrace_2704035
  have hstable : (prefixWord ++ tailWord_2704035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704035).length < 2 ^ (prefixWord ++ tailWord_2704035).sum := by decide
  have hdescent : baseEnd_2704035 < baseStart_2704035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704036 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 4, 2, 2]
def baseStart_2704036 : Nat := 118140960795 + 2704036 * 2 ^ 59
def prefixEnd_2704036 : Nat := 4983230072969 + 3 ^ 40 * 2704036 * 2
def baseEnd_2704036 : Nat := 1388470175061087680414371

theorem tailTrace_2704036 : CollatzResearch.WordTrace tailWord_2704036 prefixEnd_2704036 1388470175061087680414371 := by
  unfold tailWord_2704036
  simp only [CollatzResearch.WordTrace]
  refine ⟨49312147615873429713565981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65749530154497906284754641 49312147615873429713565981)
  ·
    refine ⟨18492055355952536142587243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49312147615873429713565981 18492055355952536142587243)
    ·
      refine ⟨27738083033928804213880865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18492055355952536142587243 27738083033928804213880865)
      ·
        refine ⟨20803562275446603160410649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27738083033928804213880865 20803562275446603160410649)
        ·
          refine ⟨15602671706584952370307987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20803562275446603160410649 15602671706584952370307987)
          ·
            refine ⟨23404007559877428555461981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15602671706584952370307987 23404007559877428555461981)
            ·
              refine ⟨8776502834954035708298243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23404007559877428555461981 8776502834954035708298243)
              ·
                refine ⟨13164754252431053562447365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8776502834954035708298243 13164754252431053562447365)
                ·
                  refine ⟨2468391422330822542958881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13164754252431053562447365 2468391422330822542958881)
                  ·
                    refine ⟨1851293566748116907219161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2468391422330822542958881 1851293566748116907219161)
                    ·
                      refine ⟨1388470175061087680414371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1851293566748116907219161 1388470175061087680414371)
                      ·
                        rfl

theorem cell23_2704036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_2704036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704036 prefixEnd_2704036 := by exact prefixLift 2704036
  have htrace : WordTrace (prefixWord ++ tailWord_2704036) baseStart_2704036 baseEnd_2704036 := by
    simpa [prefixWord, tailWord_2704036, baseEnd_2704036] using wordTrace_append hprefix tailTrace_2704036
  have hstable : (prefixWord ++ tailWord_2704036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704036).length < 2 ^ (prefixWord ++ tailWord_2704036).sum := by decide
  have hdescent : baseEnd_2704036 < baseStart_2704036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704053 : List Nat := [1, 3, 3, 3, 1, 3, 1, 1, 1, 4, 2]
def baseStart_2704053 : Nat := 118140960795 + 2704053 * 2 ^ 59
def prefixEnd_2704053 : Nat := 4983230072969 + 3 ^ 40 * 2704053 * 2
def baseEnd_2704053 : Nat := 1388478904232214113901793

theorem tailTrace_2704053 : CollatzResearch.WordTrace tailWord_2704053 prefixEnd_2704053 1388478904232214113901793 := by
  unfold tailWord_2704053
  simp only [CollatzResearch.WordTrace]
  refine ⟨98624915272685271330500813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65749943515123514220333875 98624915272685271330500813)
  ·
    refine ⟨36984343227256976748937805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98624915272685271330500813 36984343227256976748937805)
    ·
      refine ⟨13869128710221366280851677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36984343227256976748937805 13869128710221366280851677)
      ·
        refine ⟨5200923266333012355319379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13869128710221366280851677 5200923266333012355319379)
        ·
          refine ⟨7801384899499518532979069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5200923266333012355319379 7801384899499518532979069)
          ·
            refine ⟨2925519337312319449867151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7801384899499518532979069 2925519337312319449867151)
            ·
              refine ⟨4388279005968479174800727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2925519337312319449867151 4388279005968479174800727)
              ·
                refine ⟨6582418508952718762201091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4388279005968479174800727 6582418508952718762201091)
                ·
                  refine ⟨9873627763429078143301637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6582418508952718762201091 9873627763429078143301637)
                  ·
                    refine ⟨1851305205642952151869057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9873627763429078143301637 1851305205642952151869057)
                    ·
                      refine ⟨1388478904232214113901793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1851305205642952151869057 1388478904232214113901793)
                      ·
                        rfl

theorem cell23_2704053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_2704053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704053 prefixEnd_2704053 := by exact prefixLift 2704053
  have htrace : WordTrace (prefixWord ++ tailWord_2704053) baseStart_2704053 baseEnd_2704053 := by
    simpa [prefixWord, tailWord_2704053, baseEnd_2704053] using wordTrace_append hprefix tailTrace_2704053
  have hstable : (prefixWord ++ tailWord_2704053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704053).length < 2 ^ (prefixWord ++ tailWord_2704053).sum := by decide
  have hdescent : baseEnd_2704053 < baseStart_2704053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704072 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 1, 7]
def baseStart_2704072 : Nat := 118140960795 + 2704072 * 2 ^ 59
def prefixEnd_2704072 : Nat := 4983230072969 + 3 ^ 40 * 2704072 * 2
def baseEnd_2704072 : Nat := 462829553454883179854735

theorem tailTrace_2704072 : CollatzResearch.WordTrace tailWord_2704072 prefixEnd_2704072 462829553454883179854735 := by
  unfold tailWord_2704072
  simp only [CollatzResearch.WordTrace]
  refine ⟨49312804129808218787721235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65750405506410958383628313 49312804129808218787721235)
  ·
    refine ⟨73969206194712328181581853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49312804129808218787721235 73969206194712328181581853)
    ·
      refine ⟨27738452323017123068093195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73969206194712328181581853 27738452323017123068093195)
      ·
        refine ⟨41607678484525684602139793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27738452323017123068093195 41607678484525684602139793)
        ·
          refine ⟨31205758863394263451604845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41607678484525684602139793 31205758863394263451604845)
          ·
            refine ⟨11702159573772848794351817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31205758863394263451604845 11702159573772848794351817)
            ·
              refine ⟨8776619680329636595763863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11702159573772848794351817 8776619680329636595763863)
              ·
                refine ⟨13164929520494454893645795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8776619680329636595763863 13164929520494454893645795)
                ·
                  refine ⟨19747394280741682340468693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13164929520494454893645795 19747394280741682340468693)
                  ·
                    refine ⟨462829553454883179854735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19747394280741682340468693 462829553454883179854735)
                    ·
                      rfl

theorem cell23_2704072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_2704072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704072 prefixEnd_2704072 := by exact prefixLift 2704072
  have htrace : WordTrace (prefixWord ++ tailWord_2704072) baseStart_2704072 baseEnd_2704072 := by
    simpa [prefixWord, tailWord_2704072, baseEnd_2704072] using wordTrace_append hprefix tailTrace_2704072
  have hstable : (prefixWord ++ tailWord_2704072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704072).length < 2 ^ (prefixWord ++ tailWord_2704072).sum := by decide
  have hdescent : baseEnd_2704072 < baseStart_2704072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704076 : List Nat := [2, 2, 1, 5, 1, 1, 3, 3, 5]
def baseStart_2704076 : Nat := 118140960795 + 2704076 * 2 ^ 59
def prefixEnd_2704076 : Nat := 4983230072969 + 3 ^ 40 * 2704076 * 2
def baseEnd_2704076 : Nat := 154276746031918613768243

theorem tailTrace_2704076 : CollatzResearch.WordTrace tailWord_2704076 prefixEnd_2704076 154276746031918613768243 := by
  unfold tailWord_2704076
  simp only [CollatzResearch.WordTrace]
  refine ⟨49312877075800973129294041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65750502767734630839058721 49312877075800973129294041)
  ·
    refine ⟨36984657806850729846970531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49312877075800973129294041 36984657806850729846970531)
    ·
      refine ⟨55476986710276094770455797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36984657806850729846970531 55476986710276094770455797)
      ·
        refine ⟨5200967504088383884730231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55476986710276094770455797 5200967504088383884730231)
        ·
          refine ⟨7801451256132575827095347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5200967504088383884730231 7801451256132575827095347)
          ·
            refine ⟨11702176884198863740643021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7801451256132575827095347 11702176884198863740643021)
            ·
              refine ⟨4388316331574573902741133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11702176884198863740643021 4388316331574573902741133)
              ·
                refine ⟨1645618624340465213527925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4388316331574573902741133 1645618624340465213527925)
                ·
                  refine ⟨154276746031918613768243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1645618624340465213527925 154276746031918613768243)
                  ·
                    rfl

theorem cell23_2704076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 5].length) (baseStart_2704076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704076 prefixEnd_2704076 := by exact prefixLift 2704076
  have htrace : WordTrace (prefixWord ++ tailWord_2704076) baseStart_2704076 baseEnd_2704076 := by
    simpa [prefixWord, tailWord_2704076, baseEnd_2704076] using wordTrace_append hprefix tailTrace_2704076
  have hstable : (prefixWord ++ tailWord_2704076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704076).length < 2 ^ (prefixWord ++ tailWord_2704076).sum := by decide
  have hdescent : baseEnd_2704076 < baseStart_2704076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704099 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 5]
def baseStart_2704099 : Nat := 118140960795 + 2704099 * 2 ^ 59
def prefixEnd_2704099 : Nat := 4983230072969 + 3 ^ 40 * 2704099 * 2
def baseEnd_2704099 : Nat := 1388502524342320933926581

theorem tailTrace_2704099 : CollatzResearch.WordTrace tailWord_2704099 prefixEnd_2704099 1388502524342320933926581 := by
  unfold tailWord_2704099
  simp only [CollatzResearch.WordTrace]
  refine ⟨98626593030518621186675351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65751062020345747457783567 98626593030518621186675351)
  ·
    refine ⟨147939889545777931780013027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98626593030518621186675351 147939889545777931780013027)
    ·
      refine ⟨221909834318666897670019541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147939889545777931780013027 221909834318666897670019541)
      ·
        refine ⟨5201011741843755414141083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 221909834318666897670019541 5201011741843755414141083)
        ·
          refine ⟨7801517612765633121211625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5201011741843755414141083 7801517612765633121211625)
          ·
            refine ⟨5851138209574224840908719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7801517612765633121211625 5851138209574224840908719)
            ·
              refine ⟨8776707314361337261363079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5851138209574224840908719 8776707314361337261363079)
              ·
                refine ⟨13165060971542005892044619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8776707314361337261363079 13165060971542005892044619)
                ·
                  refine ⟨19747591457313008838066929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13165060971542005892044619 19747591457313008838066929)
                  ·
                    refine ⟨14810693592984756628550197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19747591457313008838066929 14810693592984756628550197)
                    ·
                      refine ⟨1388502524342320933926581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14810693592984756628550197 1388502524342320933926581)
                      ·
                        rfl

theorem cell23_2704099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_2704099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704099 prefixEnd_2704099 := by exact prefixLift 2704099
  have htrace : WordTrace (prefixWord ++ tailWord_2704099) baseStart_2704099 baseEnd_2704099 := by
    simpa [prefixWord, tailWord_2704099, baseEnd_2704099] using wordTrace_append hprefix tailTrace_2704099
  have hstable : (prefixWord ++ tailWord_2704099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704099).length < 2 ^ (prefixWord ++ tailWord_2704099).sum := by decide
  have hdescent : baseEnd_2704099 < baseStart_2704099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
