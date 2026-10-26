import V185TrunkScan22Chunk160

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1438305 : List Nat := [1, 2, 3, 1, 1, 5, 2, 7]
def baseStart_1438305 : Nat := 118140960795 + 1438305 * 2 ^ 59
def prefixEnd_1438305 : Nat := 4983230072969 + 3 ^ 40 * 1438305 * 2
def baseEnd_1438305 : Nat := 54706799464081508057249

theorem tailTrace_1438305 : CollatzResearch.WordTrace tailWord_1438305 prefixEnd_1438305 54706799464081508057249 := by
  unfold tailWord_1438305
  simp only [CollatzResearch.WordTrace]
  refine ⟨52459293054274102782476369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34972862036182735188317579 52459293054274102782476369)
  ·
    refine ⟨39344469790705577086857277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52459293054274102782476369 39344469790705577086857277)
    ·
      refine ⟨14754176171514591407571479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39344469790705577086857277 14754176171514591407571479)
      ·
        refine ⟨22131264257271887111357219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14754176171514591407571479 22131264257271887111357219)
        ·
          refine ⟨33196896385907830667035829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22131264257271887111357219 33196896385907830667035829)
          ·
            refine ⟨3112209036178859125034609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33196896385907830667035829 3112209036178859125034609)
            ·
              refine ⟨2334156777134144343775957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3112209036178859125034609 2334156777134144343775957)
              ·
                refine ⟨54706799464081508057249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2334156777134144343775957 54706799464081508057249)
                ·
                  rfl

theorem cell22_1438305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 7].length) (baseStart_1438305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438305 prefixEnd_1438305 := by exact prefixLift 1438305
  have htrace : WordTrace (prefixWord ++ tailWord_1438305) baseStart_1438305 baseEnd_1438305 := by
    simpa [prefixWord, tailWord_1438305, baseEnd_1438305] using wordTrace_append hprefix tailTrace_1438305
  have hstable : (prefixWord ++ tailWord_1438305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438305).length < 2 ^ (prefixWord ++ tailWord_1438305).sum := by decide
  have hdescent : baseEnd_1438305 < baseStart_1438305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438309 : List Nat := [1, 3, 1, 3, 4, 1, 1, 3, 2, 3]
def baseStart_1438309 : Nat := 118140960795 + 1438309 * 2 ^ 59
def prefixEnd_1438309 : Nat := 4983230072969 + 3 ^ 40 * 1438309 * 2
def baseEnd_1438309 : Nat := 492362564458478895415229

theorem tailTrace_1438309 : CollatzResearch.WordTrace tailWord_1438309 prefixEnd_1438309 492362564458478895415229 := by
  unfold tailWord_1438309
  simp only [CollatzResearch.WordTrace]
  refine ⟨52459438946259611465621981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34972959297506407643747987 52459438946259611465621981)
  ·
    refine ⟨19672289604847354299608243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52459438946259611465621981 19672289604847354299608243)
    ·
      refine ⟨29508434407271031449412365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19672289604847354299608243 29508434407271031449412365)
      ·
        refine ⟨11065662902726636793529637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29508434407271031449412365 11065662902726636793529637)
        ·
          refine ⟨2074811794261244398786807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11065662902726636793529637 2074811794261244398786807)
          ·
            refine ⟨3112217691391866598180211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2074811794261244398786807 3112217691391866598180211)
            ·
              refine ⟨4668326537087799897270317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3112217691391866598180211 4668326537087799897270317)
              ·
                refine ⟨1750622451407924961476369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4668326537087799897270317 1750622451407924961476369)
                ·
                  refine ⟨1312966838555943721107277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1750622451407924961476369 1312966838555943721107277)
                  ·
                    refine ⟨492362564458478895415229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1312966838555943721107277 492362564458478895415229)
                    ·
                      rfl

theorem cell22_1438309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_1438309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438309 prefixEnd_1438309 := by exact prefixLift 1438309
  have htrace : WordTrace (prefixWord ++ tailWord_1438309) baseStart_1438309 baseEnd_1438309 := by
    simpa [prefixWord, tailWord_1438309, baseEnd_1438309] using wordTrace_append hprefix tailTrace_1438309
  have hstable : (prefixWord ++ tailWord_1438309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438309).length < 2 ^ (prefixWord ++ tailWord_1438309).sum := by decide
  have hdescent : baseEnd_1438309 < baseStart_1438309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438365 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_1438365 : Nat := 118140960795 + 1438365 * 2 ^ 59
def prefixEnd_1438365 : Nat := 4983230072969 + 3 ^ 40 * 1438365 * 2
def baseEnd_1438365 : Nat := 492381734402913416015057

theorem tailTrace_1438365 : CollatzResearch.WordTrace tailWord_1438365 prefixEnd_1438365 492381734402913416015057 := by
  unfold tailWord_1438365
  simp only [CollatzResearch.WordTrace]
  refine ⟨52461481434056733029660549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34974320956037822019773699 52461481434056733029660549)
  ·
    refine ⟨9836527768885637443061353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52461481434056733029660549 9836527768885637443061353)
    ·
      refine ⟨7377395826664228082296015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9836527768885637443061353 7377395826664228082296015)
      ·
        refine ⟨11066093739996342123444023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7377395826664228082296015 11066093739996342123444023)
        ·
          refine ⟨16599140609994513185166035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11066093739996342123444023 16599140609994513185166035)
          ·
            refine ⟨24898710914991769777749053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16599140609994513185166035 24898710914991769777749053)
            ·
              refine ⟨9337016593121913666655895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24898710914991769777749053 9337016593121913666655895)
              ·
                refine ⟨14005524889682870499983843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9337016593121913666655895 14005524889682870499983843)
                ·
                  refine ⟨21008287334524305749975765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14005524889682870499983843 21008287334524305749975765)
                  ·
                    refine ⟨492381734402913416015057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21008287334524305749975765 492381734402913416015057)
                    ·
                      rfl

theorem cell22_1438365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_1438365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438365 prefixEnd_1438365 := by exact prefixLift 1438365
  have htrace : WordTrace (prefixWord ++ tailWord_1438365) baseStart_1438365 baseEnd_1438365 := by
    simpa [prefixWord, tailWord_1438365, baseEnd_1438365] using wordTrace_append hprefix tailTrace_1438365
  have hstable : (prefixWord ++ tailWord_1438365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438365).length < 2 ^ (prefixWord ++ tailWord_1438365).sum := by decide
  have hdescent : baseEnd_1438365 < baseStart_1438365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438412 : List Nat := [2, 2, 1, 5, 1, 1, 1, 3, 6]
def baseStart_1438412 : Nat := 118140960795 + 1438412 * 2 ^ 59
def prefixEnd_1438412 : Nat := 4983230072969 + 3 ^ 40 * 1438412 * 2
def baseEnd_1438412 : Nat := 164132607821140320029971

theorem tailTrace_1438412 : CollatzResearch.WordTrace tailWord_1438412 prefixEnd_1438412 164132607821140320029971 := by
  unfold tailWord_1438412
  simp only [CollatzResearch.WordTrace]
  refine ⟨26231597832443230028310745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34975463776590973371080993 26231597832443230028310745)
  ·
    refine ⟨19673698374332422521233059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26231597832443230028310745 19673698374332422521233059)
    ·
      refine ⟨29510547561498633781849589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19673698374332422521233059 29510547561498633781849589)
      ·
        refine ⟨2766613833890496917048399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29510547561498633781849589 2766613833890496917048399)
        ·
          refine ⟨4149920750835745375572599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2766613833890496917048399 4149920750835745375572599)
          ·
            refine ⟨6224881126253618063358899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4149920750835745375572599 6224881126253618063358899)
            ·
              refine ⟨9337321689380427095038349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6224881126253618063358899 9337321689380427095038349)
              ·
                refine ⟨3501495633517660160639381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9337321689380427095038349 3501495633517660160639381)
                ·
                  refine ⟨164132607821140320029971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3501495633517660160639381 164132607821140320029971)
                  ·
                    rfl

theorem cell22_1438412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_1438412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438412 prefixEnd_1438412 := by exact prefixLift 1438412
  have htrace : WordTrace (prefixWord ++ tailWord_1438412) baseStart_1438412 baseEnd_1438412 := by
    simpa [prefixWord, tailWord_1438412, baseEnd_1438412] using wordTrace_append hprefix tailTrace_1438412
  have hstable : (prefixWord ++ tailWord_1438412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438412).length < 2 ^ (prefixWord ++ tailWord_1438412).sum := by decide
  have hdescent : baseEnd_1438412 < baseStart_1438412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438425 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 3, 6]
def baseStart_1438425 : Nat := 118140960795 + 1438425 * 2 ^ 59
def prefixEnd_1438425 : Nat := 4983230072969 + 3 ^ 40 * 1438425 * 2
def baseEnd_1438425 : Nat := 492402273629093259514873

theorem tailTrace_1438425 : CollatzResearch.WordTrace tailWord_1438425 prefixEnd_1438425 492402273629093259514873 := by
  unfold tailWord_1438425
  simp only [CollatzResearch.WordTrace]
  refine ⟨52463669813839363276844729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34975779875892908851229819 52463669813839363276844729)
  ·
    refine ⟨39347752360379522457633547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52463669813839363276844729 39347752360379522457633547)
    ·
      refine ⟨59021628540569283686450321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39347752360379522457633547 59021628540569283686450321)
      ·
        refine ⟨44266221405426962764837741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59021628540569283686450321 44266221405426962764837741)
        ·
          refine ⟨16599833027035111036814153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44266221405426962764837741 16599833027035111036814153)
          ·
            refine ⟨12449874770276333277610615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16599833027035111036814153 12449874770276333277610615)
            ·
              refine ⟨18674812155414499916415923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12449874770276333277610615 18674812155414499916415923)
              ·
                refine ⟨28012218233121749874623885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18674812155414499916415923 28012218233121749874623885)
                ·
                  refine ⟨10504581837420656202983957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28012218233121749874623885 10504581837420656202983957)
                  ·
                    refine ⟨492402273629093259514873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10504581837420656202983957 492402273629093259514873)
                    ·
                      rfl

theorem cell22_1438425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_1438425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438425 prefixEnd_1438425 := by exact prefixLift 1438425
  have htrace : WordTrace (prefixWord ++ tailWord_1438425) baseStart_1438425 baseEnd_1438425 := by
    simpa [prefixWord, tailWord_1438425, baseEnd_1438425] using wordTrace_append hprefix tailTrace_1438425
  have hstable : (prefixWord ++ tailWord_1438425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438425).length < 2 ^ (prefixWord ++ tailWord_1438425).sum := by decide
  have hdescent : baseEnd_1438425 < baseStart_1438425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438442 : List Nat := [3, 1, 3, 1, 1, 1, 1, 5, 2, 4]
def baseStart_1438442 : Nat := 118140960795 + 1438442 * 2 ^ 59
def prefixEnd_1438442 : Nat := 4983230072969 + 3 ^ 40 * 1438442 * 2
def baseEnd_1438442 : Nat := 492408093076510881839821

theorem tailTrace_1438442 : CollatzResearch.WordTrace tailWord_1438442 prefixEnd_1438442 492408093076510881839821 := by
  unfold tailWord_1438442
  simp only [CollatzResearch.WordTrace]
  refine ⟨13116072463694443795053395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34976193236518516786809053 13116072463694443795053395)
  ·
    refine ⟨19674108695541665692580093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13116072463694443795053395 19674108695541665692580093)
    ·
      refine ⟨7377790760828124634717535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19674108695541665692580093 7377790760828124634717535)
      ·
        refine ⟨11066686141242186952076303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7377790760828124634717535 11066686141242186952076303)
        ·
          refine ⟨16600029211863280428114455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11066686141242186952076303 16600029211863280428114455)
          ·
            refine ⟨24900043817794920642171683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16600029211863280428114455 24900043817794920642171683)
            ·
              refine ⟨37350065726692380963257525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24900043817794920642171683 37350065726692380963257525)
              ·
                refine ⟨3501568661877410715305393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37350065726692380963257525 3501568661877410715305393)
                ·
                  refine ⟨2626176496408058036479045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3501568661877410715305393 2626176496408058036479045)
                  ·
                    refine ⟨492408093076510881839821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2626176496408058036479045 492408093076510881839821)
                    ·
                      rfl

theorem cell22_1438442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_1438442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438442 prefixEnd_1438442 := by exact prefixLift 1438442
  have htrace : WordTrace (prefixWord ++ tailWord_1438442) baseStart_1438442 baseEnd_1438442 := by
    simpa [prefixWord, tailWord_1438442, baseEnd_1438442] using wordTrace_append hprefix tailTrace_1438442
  have hstable : (prefixWord ++ tailWord_1438442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438442).length < 2 ^ (prefixWord ++ tailWord_1438442).sum := by decide
  have hdescent : baseEnd_1438442 < baseStart_1438442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438446 : List Nat := [4, 1, 2, 1, 1, 5, 1, 3, 4]
def baseStart_1438446 : Nat := 118140960795 + 1438446 * 2 ^ 59
def prefixEnd_1438446 : Nat := 4983230072969 + 3 ^ 40 * 1438446 * 2
def baseEnd_1438446 : Nat := 164136487452752068246603

theorem tailTrace_1438446 : CollatzResearch.WordTrace tailWord_1438446 prefixEnd_1438446 164136487452752068246603 := by
  unfold tailWord_1438446
  simp only [CollatzResearch.WordTrace]
  refine ⟨6558054468345410482919899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34976290497842189242239461 6558054468345410482919899)
  ·
    refine ⟨9837081702518115724379849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6558054468345410482919899 9837081702518115724379849)
    ·
      refine ⟨7377811276888586793284887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9837081702518115724379849 7377811276888586793284887)
      ·
        refine ⟨11066716915332880189927331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7377811276888586793284887 11066716915332880189927331)
        ·
          refine ⟨16600075372999320284890997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11066716915332880189927331 16600075372999320284890997)
          ·
            refine ⟨1556257066218686276708531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16600075372999320284890997 1556257066218686276708531)
            ·
              refine ⟨2334385599328029415062797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556257066218686276708531 2334385599328029415062797)
              ·
                refine ⟨875394599748011030648549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2334385599328029415062797 875394599748011030648549)
                ·
                  refine ⟨164136487452752068246603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 875394599748011030648549 164136487452752068246603)
                  ·
                    rfl

theorem cell22_1438446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_1438446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438446 prefixEnd_1438446 := by exact prefixLift 1438446
  have htrace : WordTrace (prefixWord ++ tailWord_1438446) baseStart_1438446 baseEnd_1438446 := by
    simpa [prefixWord, tailWord_1438446, baseEnd_1438446] using wordTrace_append hprefix tailTrace_1438446
  have hstable : (prefixWord ++ tailWord_1438446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438446).length < 2 ^ (prefixWord ++ tailWord_1438446).sum := by decide
  have hdescent : baseEnd_1438446 < baseStart_1438446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438549 : List Nat := [1, 3, 2, 2, 2, 1, 2, 4, 1, 4]
def baseStart_1438549 : Nat := 118140960795 + 1438549 * 2 ^ 59
def prefixEnd_1438549 : Nat := 4983230072969 + 3 ^ 40 * 1438549 * 2
def baseEnd_1438549 : Nat := 492444721363198269414493

theorem tailTrace_1438549 : CollatzResearch.WordTrace tailWord_1438549 prefixEnd_1438549 492444721363198269414493 := by
  unfold tailWord_1438549
  simp only [CollatzResearch.WordTrace]
  refine ⟨52468192465390132454358701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34978794976926754969572467 52468192465390132454358701)
  ·
    refine ⟨19675572174521299670384513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52468192465390132454358701 19675572174521299670384513)
    ·
      refine ⟨14756679130890974752788385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19675572174521299670384513 14756679130890974752788385)
      ·
        refine ⟨11067509348168231064591289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14756679130890974752788385 11067509348168231064591289)
        ·
          refine ⟨8300632011126173298443467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11067509348168231064591289 8300632011126173298443467)
          ·
            refine ⟨12450948016689259947665201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8300632011126173298443467 12450948016689259947665201)
            ·
              refine ⟨9338211012516944960748901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12450948016689259947665201 9338211012516944960748901)
              ·
                refine ⟨1750914564846927180140419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9338211012516944960748901 1750914564846927180140419)
                ·
                  refine ⟨2626371847270390770210629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1750914564846927180140419 2626371847270390770210629)
                  ·
                    refine ⟨492444721363198269414493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2626371847270390770210629 492444721363198269414493)
                    ·
                      rfl

theorem cell22_1438549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_1438549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438549 prefixEnd_1438549 := by exact prefixLift 1438549
  have htrace : WordTrace (prefixWord ++ tailWord_1438549) baseStart_1438549 baseEnd_1438549 := by
    simpa [prefixWord, tailWord_1438549, baseEnd_1438549] using wordTrace_append hprefix tailTrace_1438549
  have hstable : (prefixWord ++ tailWord_1438549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438549).length < 2 ^ (prefixWord ++ tailWord_1438549).sum := by decide
  have hdescent : baseEnd_1438549 < baseStart_1438549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438581 : List Nat := [1, 3, 4, 1, 1, 2, 2, 4, 4]
def baseStart_1438581 : Nat := 118140960795 + 1438581 * 2 ^ 59
def prefixEnd_1438581 : Nat := 4983230072969 + 3 ^ 40 * 1438581 * 2
def baseEnd_1438581 : Nat := 164151891872386950871465

theorem tailTrace_1438581 : CollatzResearch.WordTrace tailWord_1438581 prefixEnd_1438581 164151891872386950871465 := by
  unfold tailWord_1438581
  simp only [CollatzResearch.WordTrace]
  refine ⟨52469359601274201919523597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34979573067516134613015731 52469359601274201919523597)
  ·
    refine ⟨19676009850477825719821349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52469359601274201919523597 19676009850477825719821349)
    ·
      refine ⟨3689251846964592322466503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19676009850477825719821349 3689251846964592322466503)
      ·
        refine ⟨5533877770446888483699755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3689251846964592322466503 5533877770446888483699755)
        ·
          refine ⟨8300816655670332725549633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5533877770446888483699755 8300816655670332725549633)
          ·
            refine ⟨6225612491752749544162225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8300816655670332725549633 6225612491752749544162225)
            ·
              refine ⟨4669209368814562158121669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6225612491752749544162225 4669209368814562158121669)
              ·
                refine ⟨875476756652730404647813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4669209368814562158121669 875476756652730404647813)
                ·
                  refine ⟨164151891872386950871465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 875476756652730404647813 164151891872386950871465)
                  ·
                    rfl

theorem cell22_1438581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_1438581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438581 prefixEnd_1438581 := by exact prefixLift 1438581
  have htrace : WordTrace (prefixWord ++ tailWord_1438581) baseStart_1438581 baseEnd_1438581 := by
    simpa [prefixWord, tailWord_1438581, baseEnd_1438581] using wordTrace_append hprefix tailTrace_1438581
  have hstable : (prefixWord ++ tailWord_1438581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438581).length < 2 ^ (prefixWord ++ tailWord_1438581).sum := by decide
  have hdescent : baseEnd_1438581 < baseStart_1438581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438624 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 5, 3]
def baseStart_1438624 : Nat := 118140960795 + 1438624 * 2 ^ 59
def prefixEnd_1438624 : Nat := 4983230072969 + 3 ^ 40 * 1438624 * 2
def baseEnd_1438624 : Nat := 492470395395923073789263

theorem tailTrace_1438624 : CollatzResearch.WordTrace tailWord_1438624 prefixEnd_1438624 492470395395923073789263 := by
  unfold tailWord_1438624
  simp only [CollatzResearch.WordTrace]
  refine ⟨26235463970059210131669463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34980618626745613508892617 26235463970059210131669463)
  ·
    refine ⟨39353195955088815197504195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26235463970059210131669463 39353195955088815197504195)
    ·
      refine ⟨59029793932633222796256293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39353195955088815197504195 59029793932633222796256293)
      ·
        refine ⟨11068086362368729274298055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59029793932633222796256293 11068086362368729274298055)
        ·
          refine ⟨16602129543553093911447083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11068086362368729274298055 16602129543553093911447083)
          ·
            refine ⟨24903194315329640867170625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16602129543553093911447083 24903194315329640867170625)
            ·
              refine ⟨18677395736497230650377969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24903194315329640867170625 18677395736497230650377969)
              ·
                refine ⟨14008046802372922987783477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18677395736497230650377969 14008046802372922987783477)
                ·
                  refine ⟨1313254387722461530104701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14008046802372922987783477 1313254387722461530104701)
                  ·
                    refine ⟨492470395395923073789263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1313254387722461530104701 492470395395923073789263)
                    ·
                      rfl

theorem cell22_1438624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 5, 3].length) (baseStart_1438624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438624 prefixEnd_1438624 := by exact prefixLift 1438624
  have htrace : WordTrace (prefixWord ++ tailWord_1438624) baseStart_1438624 baseEnd_1438624 := by
    simpa [prefixWord, tailWord_1438624, baseEnd_1438624] using wordTrace_append hprefix tailTrace_1438624
  have hstable : (prefixWord ++ tailWord_1438624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438624).length < 2 ^ (prefixWord ++ tailWord_1438624).sum := by decide
  have hdescent : baseEnd_1438624 < baseStart_1438624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438744 : List Nat := [2, 1, 2, 3, 2, 3, 9]
def baseStart_1438744 : Nat := 118140960795 + 1438744 * 2 ^ 59
def prefixEnd_1438744 : Nat := 4983230072969 + 3 ^ 40 * 1438744 * 2
def baseEnd_1438744 : Nat := 18241165698084546695885

theorem tailTrace_1438744 : CollatzResearch.WordTrace tailWord_1438744 prefixEnd_1438744 18241165698084546695885 := by
  unfold tailWord_1438744
  simp only [CollatzResearch.WordTrace]
  refine ⟨26237652349841840378853643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34983536466455787171804857 26237652349841840378853643)
  ·
    refine ⟨39356478524762760568280465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26237652349841840378853643 39356478524762760568280465)
    ·
      refine ⟨29517358893572070426210349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39356478524762760568280465 29517358893572070426210349)
      ·
        refine ⟨11069009585089526409828881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29517358893572070426210349 11069009585089526409828881)
        ·
          refine ⟨8301757188817144807371661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11069009585089526409828881 8301757188817144807371661)
          ·
            refine ⟨3113158945806429302764373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8301757188817144807371661 3113158945806429302764373)
            ·
              refine ⟨18241165698084546695885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3113158945806429302764373 18241165698084546695885)
              ·
                rfl

theorem cell22_1438744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 9].length) (baseStart_1438744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438744 prefixEnd_1438744 := by exact prefixLift 1438744
  have htrace : WordTrace (prefixWord ++ tailWord_1438744) baseStart_1438744 baseEnd_1438744 := by
    simpa [prefixWord, tailWord_1438744, baseEnd_1438744] using wordTrace_append hprefix tailTrace_1438744
  have hstable : (prefixWord ++ tailWord_1438744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438744).length < 2 ^ (prefixWord ++ tailWord_1438744).sum := by decide
  have hdescent : baseEnd_1438744 < baseStart_1438744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438748 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 4, 3]
def baseStart_1438748 : Nat := 118140960795 + 1438748 * 2 ^ 59
def prefixEnd_1438748 : Nat := 4983230072969 + 3 ^ 40 * 1438748 * 2
def baseEnd_1438748 : Nat := 492512843130028083688883

theorem tailTrace_1438748 : CollatzResearch.WordTrace tailWord_1438748 prefixEnd_1438748 492512843130028083688883 := by
  unfold tailWord_1438748
  simp only [CollatzResearch.WordTrace]
  refine ⟨26237725295834594720426449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34983633727779459627235265 26237725295834594720426449)
  ·
    refine ⟨19678293971875946040319837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26237725295834594720426449 19678293971875946040319837)
    ·
      refine ⟨7379360239453479765119939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19678293971875946040319837 7379360239453479765119939)
      ·
        refine ⟨11069040359180219647679909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7379360239453479765119939 11069040359180219647679909)
        ·
          refine ⟨2075445067346291183939983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11069040359180219647679909 2075445067346291183939983)
          ·
            refine ⟨3113167601019436775909975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2075445067346291183939983 3113167601019436775909975)
            ·
              refine ⟨4669751401529155163864963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3113167601019436775909975 4669751401529155163864963)
              ·
                refine ⟨7004627102293732745797445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4669751401529155163864963 7004627102293732745797445)
                ·
                  refine ⟨1313367581680074889837021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7004627102293732745797445 1313367581680074889837021)
                  ·
                    refine ⟨492512843130028083688883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1313367581680074889837021 492512843130028083688883)
                    ·
                      rfl

theorem cell22_1438748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_1438748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438748 prefixEnd_1438748 := by exact prefixLift 1438748
  have htrace : WordTrace (prefixWord ++ tailWord_1438748) baseStart_1438748 baseEnd_1438748 := by
    simpa [prefixWord, tailWord_1438748, baseEnd_1438748] using wordTrace_append hprefix tailTrace_1438748
  have hstable : (prefixWord ++ tailWord_1438748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438748).length < 2 ^ (prefixWord ++ tailWord_1438748).sum := by decide
  have hdescent : baseEnd_1438748 < baseStart_1438748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438789 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 7]
def baseStart_1438789 : Nat := 118140960795 + 1438789 * 2 ^ 59
def prefixEnd_1438789 : Nat := 4983230072969 + 3 ^ 40 * 1438789 * 2
def baseEnd_1438789 : Nat := 164175626089305881137919

theorem tailTrace_1438789 : CollatzResearch.WordTrace tailWord_1438789 prefixEnd_1438789 164175626089305881137919 := by
  unfold tailWord_1438789
  simp only [CollatzResearch.WordTrace]
  refine ⟨52476945984520653443095421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34984630656347102295396947 52476945984520653443095421)
  ·
    refine ⟨19678854744195245041160783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52476945984520653443095421 19678854744195245041160783)
    ·
      refine ⟨29518282116292867561741175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19678854744195245041160783 29518282116292867561741175)
      ·
        refine ⟨44277423174439301342611763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29518282116292867561741175 44277423174439301342611763)
        ·
          refine ⟨66416134761658952013917645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44277423174439301342611763 66416134761658952013917645)
          ·
            refine ⟨24906050535622107005219117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66416134761658952013917645 24906050535622107005219117)
            ·
              refine ⟨9339768950858290126957169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24906050535622107005219117 9339768950858290126957169)
              ·
                refine ⟨7004826713143717595217877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9339768950858290126957169 7004826713143717595217877)
                ·
                  refine ⟨164175626089305881137919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7004826713143717595217877 164175626089305881137919)
                  ·
                    rfl

theorem cell22_1438789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_1438789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438789 prefixEnd_1438789 := by exact prefixLift 1438789
  have htrace : WordTrace (prefixWord ++ tailWord_1438789) baseStart_1438789 baseEnd_1438789 := by
    simpa [prefixWord, tailWord_1438789, baseEnd_1438789] using wordTrace_append hprefix tailTrace_1438789
  have hstable : (prefixWord ++ tailWord_1438789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438789).length < 2 ^ (prefixWord ++ tailWord_1438789).sum := by decide
  have hdescent : baseEnd_1438789 < baseStart_1438789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438793 : List Nat := [1, 2, 1, 1, 2, 2, 2, 7, 1, 3]
def baseStart_1438793 : Nat := 118140960795 + 1438793 * 2 ^ 59
def prefixEnd_1438793 : Nat := 4983230072969 + 3 ^ 40 * 1438793 * 2
def baseEnd_1438793 : Nat := 492528247549662966313745

theorem tailTrace_1438793 : CollatzResearch.WordTrace tailWord_1438793 prefixEnd_1438793 492528247549662966313745 := by
  unfold tailWord_1438793
  simp only [CollatzResearch.WordTrace]
  refine ⟨52477091876506162126241033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34984727917670774750827355 52477091876506162126241033)
  ·
    refine ⟨39357818907379621594680775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52477091876506162126241033 39357818907379621594680775)
    ·
      refine ⟨59036728361069432392021163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39357818907379621594680775 59036728361069432392021163)
      ·
        refine ⟨88555092541604148588031745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59036728361069432392021163 88555092541604148588031745)
        ·
          refine ⟨66416319406203111441023809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88555092541604148588031745 66416319406203111441023809)
          ·
            refine ⟨49812239554652333580767857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66416319406203111441023809 49812239554652333580767857)
            ·
              refine ⟨37359179665989250185575893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49812239554652333580767857 37359179665989250185575893)
              ·
                refine ⟨875605773421623051224435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 37359179665989250185575893 875605773421623051224435)
                ·
                  refine ⟨1313408660132434576836653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875605773421623051224435 1313408660132434576836653)
                  ·
                    refine ⟨492528247549662966313745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1313408660132434576836653 492528247549662966313745)
                    ·
                      rfl

theorem cell22_1438793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 1, 3].length) (baseStart_1438793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438793 prefixEnd_1438793 := by exact prefixLift 1438793
  have htrace : WordTrace (prefixWord ++ tailWord_1438793) baseStart_1438793 baseEnd_1438793 := by
    simpa [prefixWord, tailWord_1438793, baseEnd_1438793] using wordTrace_append hprefix tailTrace_1438793
  have hstable : (prefixWord ++ tailWord_1438793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438793).length < 2 ^ (prefixWord ++ tailWord_1438793).sum := by decide
  have hdescent : baseEnd_1438793 < baseStart_1438793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438819 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 2, 8]
def baseStart_1438819 : Nat := 118140960795 + 1438819 * 2 ^ 59
def prefixEnd_1438819 : Nat := 4983230072969 + 3 ^ 40 * 1438819 * 2
def baseEnd_1438819 : Nat := 492537147881007565163665

theorem tailTrace_1438819 : CollatzResearch.WordTrace tailWord_1438819 prefixEnd_1438819 492537147881007565163665 := by
  unfold tailWord_1438819
  simp only [CollatzResearch.WordTrace]
  refine ⟨52478040174411968566687511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34985360116274645711125007 52478040174411968566687511)
  ·
    refine ⟨78717060261617952850031267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52478040174411968566687511 78717060261617952850031267)
    ·
      refine ⟨118075590392426929275046901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78717060261617952850031267 118075590392426929275046901)
      ·
        refine ⟨11069586599290024619535647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118075590392426929275046901 11069586599290024619535647)
        ·
          refine ⟨16604379898935036929303471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11069586599290024619535647 16604379898935036929303471)
          ·
            refine ⟨24906569848402555393955207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16604379898935036929303471 24906569848402555393955207)
            ·
              refine ⟨37359854772603833090932811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24906569848402555393955207 37359854772603833090932811)
              ·
                refine ⟨56039782158905749636399217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37359854772603833090932811 56039782158905749636399217)
                ·
                  refine ⟨42029836619179312227299413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56039782158905749636399217 42029836619179312227299413)
                  ·
                    refine ⟨492537147881007565163665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42029836619179312227299413 492537147881007565163665)
                    ·
                      rfl

theorem cell22_1438819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 8].length) (baseStart_1438819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438819 prefixEnd_1438819 := by exact prefixLift 1438819
  have htrace : WordTrace (prefixWord ++ tailWord_1438819) baseStart_1438819 baseEnd_1438819 := by
    simpa [prefixWord, tailWord_1438819, baseEnd_1438819] using wordTrace_append hprefix tailTrace_1438819
  have hstable : (prefixWord ++ tailWord_1438819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438819).length < 2 ^ (prefixWord ++ tailWord_1438819).sum := by decide
  have hdescent : baseEnd_1438819 < baseStart_1438819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438823 : List Nat := [1, 1, 5, 1, 1, 3, 4, 1, 5]
def baseStart_1438823 : Nat := 118140960795 + 1438823 * 2 ^ 59
def prefixEnd_1438823 : Nat := 4983230072969 + 3 ^ 40 * 1438823 * 2
def baseEnd_1438823 : Nat := 164179505720917629354551

theorem tailTrace_1438823 : CollatzResearch.WordTrace tailWord_1438823 prefixEnd_1438823 164179505720917629354551 := by
  unfold tailWord_1438823
  simp only [CollatzResearch.WordTrace]
  refine ⟨52478186066397477249833123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34985457377598318166555415 52478186066397477249833123)
  ·
    refine ⟨78717279099596215874749685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52478186066397477249833123 78717279099596215874749685)
    ·
      refine ⟨7379744915587145238257783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78717279099596215874749685 7379744915587145238257783)
      ·
        refine ⟨11069617373380717857386675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7379744915587145238257783 11069617373380717857386675)
        ·
          refine ⟨16604426060071076786080013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11069617373380717857386675 16604426060071076786080013)
          ·
            refine ⟨6226659772526653794780005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16604426060071076786080013 6226659772526653794780005)
            ·
              refine ⟨1167498707348747586521251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6226659772526653794780005 1167498707348747586521251)
              ·
                refine ⟨1751248061023121379781877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1167498707348747586521251 1751248061023121379781877)
                ·
                  refine ⟨164179505720917629354551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1751248061023121379781877 164179505720917629354551)
                  ·
                    rfl

theorem cell22_1438823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 5].length) (baseStart_1438823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438823 prefixEnd_1438823 := by exact prefixLift 1438823
  have htrace : WordTrace (prefixWord ++ tailWord_1438823) baseStart_1438823 baseEnd_1438823 := by
    simpa [prefixWord, tailWord_1438823, baseEnd_1438823] using wordTrace_append hprefix tailTrace_1438823
  have hstable : (prefixWord ++ tailWord_1438823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438823).length < 2 ^ (prefixWord ++ tailWord_1438823).sum := by decide
  have hdescent : baseEnd_1438823 < baseStart_1438823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438881 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 1, 6]
def baseStart_1438881 : Nat := 118140960795 + 1438881 * 2 ^ 59
def prefixEnd_1438881 : Nat := 4983230072969 + 3 ^ 40 * 1438881 * 2
def baseEnd_1438881 : Nat := 492558371748060070113475

theorem tailTrace_1438881 : CollatzResearch.WordTrace tailWord_1438881 prefixEnd_1438881 492558371748060070113475 := by
  unfold tailWord_1438881
  simp only [CollatzResearch.WordTrace]
  refine ⟨52480301500187353155444497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34986867666791568770296331 52480301500187353155444497)
  ·
    refine ⟨39360226125140514866583373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52480301500187353155444497 39360226125140514866583373)
    ·
      refine ⟨14760084796927693074968765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39360226125140514866583373 14760084796927693074968765)
      ·
        refine ⟨5535031798847884903113287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14760084796927693074968765 5535031798847884903113287)
        ·
          refine ⟨8302547698271827354669931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5535031798847884903113287 8302547698271827354669931)
          ·
            refine ⟨12453821547407741032004897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8302547698271827354669931 12453821547407741032004897)
            ·
              refine ⟨9340366160555805774003673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12453821547407741032004897 9340366160555805774003673)
              ·
                refine ⟨7005274620416854330502755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9340366160555805774003673 7005274620416854330502755)
                ·
                  refine ⟨10507911930625281495754133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7005274620416854330502755 10507911930625281495754133)
                  ·
                    refine ⟨492558371748060070113475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10507911930625281495754133 492558371748060070113475)
                    ·
                      rfl

theorem cell22_1438881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_1438881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438881 prefixEnd_1438881 := by exact prefixLift 1438881
  have htrace : WordTrace (prefixWord ++ tailWord_1438881) baseStart_1438881 baseEnd_1438881 := by
    simpa [prefixWord, tailWord_1438881, baseEnd_1438881] using wordTrace_append hprefix tailTrace_1438881
  have hstable : (prefixWord ++ tailWord_1438881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438881).length < 2 ^ (prefixWord ++ tailWord_1438881).sum := by decide
  have hdescent : baseEnd_1438881 < baseStart_1438881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438898 : List Nat := [3, 2, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_1438898 : Nat := 118140960795 + 1438898 * 2 ^ 59
def prefixEnd_1438898 : Nat := 4983230072969 + 3 ^ 40 * 1438898 * 2
def baseEnd_1438898 : Nat := 492564191195477692438423

theorem tailTrace_1438898 : CollatzResearch.WordTrace tailWord_1438898 prefixEnd_1438898 492564191195477692438423 := by
  unfold tailWord_1438898
  simp only [CollatzResearch.WordTrace]
  refine ⟨13120230385281441264703337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34987281027417176705875565 13120230385281441264703337)
  ·
    refine ⟨9840172788961080948527503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13120230385281441264703337 9840172788961080948527503)
    ·
      refine ⟨14760259183441621422791255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9840172788961080948527503 14760259183441621422791255)
      ·
        refine ⟨22140388775162432134186883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14760259183441621422791255 22140388775162432134186883)
        ·
          refine ⟨33210583162743648201280325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22140388775162432134186883 33210583162743648201280325)
          ·
            refine ⟨6226984343014434037740061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33210583162743648201280325 6226984343014434037740061)
            ·
              refine ⟨2335119128630412764152523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6226984343014434037740061 2335119128630412764152523)
              ·
                refine ⟨3502678692945619146228785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2335119128630412764152523 3502678692945619146228785)
                ·
                  refine ⟨2627009019709214359671589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3502678692945619146228785 2627009019709214359671589)
                  ·
                    refine ⟨492564191195477692438423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2627009019709214359671589 492564191195477692438423)
                    ·
                      rfl

theorem cell22_1438898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_1438898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438898 prefixEnd_1438898 := by exact prefixLift 1438898
  have htrace : WordTrace (prefixWord ++ tailWord_1438898) baseStart_1438898 baseEnd_1438898 := by
    simpa [prefixWord, tailWord_1438898, baseEnd_1438898] using wordTrace_append hprefix tailTrace_1438898
  have hstable : (prefixWord ++ tailWord_1438898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438898).length < 2 ^ (prefixWord ++ tailWord_1438898).sum := by decide
  have hdescent : baseEnd_1438898 < baseStart_1438898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438913 : List Nat := [1, 2, 6, 1, 1, 2, 9]
def baseStart_1438913 : Nat := 118140960795 + 1438913 * 2 ^ 59
def prefixEnd_1438913 : Nat := 4983230072969 + 3 ^ 40 * 1438913 * 2
def baseEnd_1438913 : Nat := 18243308370445283456051

theorem tailTrace_1438913 : CollatzResearch.WordTrace tailWord_1438913 prefixEnd_1438913 18243308370445283456051 := by
  unfold tailWord_1438913
  simp only [CollatzResearch.WordTrace]
  refine ⟨52481468636071422620609393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34987645757380948413739595 52481468636071422620609393)
  ·
    refine ⟨39361101477053566965457045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52481468636071422620609393 39361101477053566965457045)
    ·
      refine ⟨1845051631736885951505799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39361101477053566965457045 1845051631736885951505799)
      ·
        refine ⟨2767577447605328927258699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1845051631736885951505799 2767577447605328927258699)
        ·
          refine ⟨4151366171407993390888049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2767577447605328927258699 4151366171407993390888049)
          ·
            refine ⟨3113524628555995043166037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4151366171407993390888049 3113524628555995043166037)
            ·
              refine ⟨18243308370445283456051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3113524628555995043166037 18243308370445283456051)
              ·
                rfl

theorem cell22_1438913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 9].length) (baseStart_1438913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438913 prefixEnd_1438913 := by exact prefixLift 1438913
  have htrace : WordTrace (prefixWord ++ tailWord_1438913) baseStart_1438913 baseEnd_1438913 := by
    simpa [prefixWord, tailWord_1438913, baseEnd_1438913] using wordTrace_append hprefix tailTrace_1438913
  have hstable : (prefixWord ++ tailWord_1438913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438913).length < 2 ^ (prefixWord ++ tailWord_1438913).sum := by decide
  have hdescent : baseEnd_1438913 < baseStart_1438913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438934 : List Nat := [5, 2, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_1438934 : Nat := 118140960795 + 1438934 * 2 ^ 59
def prefixEnd_1438934 : Nat := 4983230072969 + 3 ^ 40 * 1438934 * 2
def baseEnd_1438934 : Nat := 492576514731185598538313

theorem tailTrace_1438934 : CollatzResearch.WordTrace tailWord_1438934 prefixEnd_1438934 492576514731185598538313 := by
  unfold tailWord_1438934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3280139660562208950445241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34988156379330228804749237 3280139660562208950445241)
  ·
    refine ⟨2460104745421656712833931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3280139660562208950445241 2460104745421656712833931)
    ·
      refine ⟨3690157118132485069250897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2460104745421656712833931 3690157118132485069250897)
      ·
        refine ⟨2767617838599363801938173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3690157118132485069250897 2767617838599363801938173)
        ·
          refine ⟨1037856689474761425726815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2767617838599363801938173 1037856689474761425726815)
          ·
            refine ⟨1556785034212142138590223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037856689474761425726815 1556785034212142138590223)
            ·
              refine ⟨2335177551318213207885335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556785034212142138590223 2335177551318213207885335)
              ·
                refine ⟨3502766326977319811828003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2335177551318213207885335 3502766326977319811828003)
                ·
                  refine ⟨5254149490465979717742005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3502766326977319811828003 5254149490465979717742005)
                  ·
                    refine ⟨492576514731185598538313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5254149490465979717742005 492576514731185598538313)
                    ·
                      rfl

theorem cell22_1438934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_1438934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438934 prefixEnd_1438934 := by exact prefixLift 1438934
  have htrace : WordTrace (prefixWord ++ tailWord_1438934) baseStart_1438934 baseEnd_1438934 := by
    simpa [prefixWord, tailWord_1438934, baseEnd_1438934] using wordTrace_append hprefix tailTrace_1438934
  have hstable : (prefixWord ++ tailWord_1438934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438934).length < 2 ^ (prefixWord ++ tailWord_1438934).sum := by decide
  have hdescent : baseEnd_1438934 < baseStart_1438934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438964 : List Nat := [2, 6, 1, 2, 2, 1, 8]
def baseStart_1438964 : Nat := 118140960795 + 1438964 * 2 ^ 59
def prefixEnd_1438964 : Nat := 4983230072969 + 3 ^ 40 * 1438964 * 2
def baseEnd_1438964 : Nat := 18243954975713908158823

theorem tailTrace_1438964 : CollatzResearch.WordTrace tailWord_1438964 prefixEnd_1438964 18243954975713908158823 := by
  unfold tailWord_1438964
  simp only [CollatzResearch.WordTrace]
  refine ⟨26241664379443329165357973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34988885839257772220477297 26241664379443329165357973)
  ·
    refine ⟨1230078017786406054626155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26241664379443329165357973 1230078017786406054626155)
    ·
      refine ⟨1845117026679609081939233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1230078017786406054626155 1845117026679609081939233)
      ·
        refine ⟨1383837770009706811454425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1845117026679609081939233 1383837770009706811454425)
        ·
          refine ⟨1037878327507280108590819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1383837770009706811454425 1037878327507280108590819)
          ·
            refine ⟨1556817491260920162886229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037878327507280108590819 1556817491260920162886229)
            ·
              refine ⟨18243954975713908158823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1556817491260920162886229 18243954975713908158823)
              ·
                rfl

theorem cell22_1438964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 8].length) (baseStart_1438964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438964 prefixEnd_1438964 := by exact prefixLift 1438964
  have htrace : WordTrace (prefixWord ++ tailWord_1438964) baseStart_1438964 baseEnd_1438964 := by
    simpa [prefixWord, tailWord_1438964, baseEnd_1438964] using wordTrace_append hprefix tailTrace_1438964
  have hstable : (prefixWord ++ tailWord_1438964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438964).length < 2 ^ (prefixWord ++ tailWord_1438964).sum := by decide
  have hdescent : baseEnd_1438964 < baseStart_1438964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439001 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 7, 5]
def baseStart_1439001 : Nat := 118140960795 + 1439001 * 2 ^ 59
def prefixEnd_1439001 : Nat := 4983230072969 + 3 ^ 40 * 1439001 * 2
def baseEnd_1439001 : Nat := 492599450200419757113107

theorem tailTrace_1439001 : CollatzResearch.WordTrace tailWord_1439001 prefixEnd_1439001 492599450200419757113107 := by
  unfold tailWord_1439001
  simp only [CollatzResearch.WordTrace]
  refine ⟨52484678259752613649812857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34989785506501742433208571 52484678259752613649812857)
  ·
    refine ⟨39363508694814460237359643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52484678259752613649812857 39363508694814460237359643)
    ·
      refine ⟨59045263042221690356039465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39363508694814460237359643 59045263042221690356039465)
      ·
        refine ⟨44283947281666267767029599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59045263042221690356039465 44283947281666267767029599)
        ·
          refine ⟨66425920922499401650544399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44283947281666267767029599 66425920922499401650544399)
          ·
            refine ⟨99638881383749102475816599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66425920922499401650544399 99638881383749102475816599)
            ·
              refine ⟨149458322075623653713724899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99638881383749102475816599 149458322075623653713724899)
              ·
                refine ⟨224187483113435480570587349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149458322075623653713724899 224187483113435480570587349)
                ·
                  refine ⟨5254394135471144075873141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 224187483113435480570587349 5254394135471144075873141)
                  ·
                    refine ⟨492599450200419757113107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5254394135471144075873141 492599450200419757113107)
                    ·
                      rfl

theorem cell22_1439001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_1439001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439001 prefixEnd_1439001 := by exact prefixLift 1439001
  have htrace : WordTrace (prefixWord ++ tailWord_1439001) baseStart_1439001 baseEnd_1439001 := by
    simpa [prefixWord, tailWord_1439001, baseEnd_1439001] using wordTrace_append hprefix tailTrace_1439001
  have hstable : (prefixWord ++ tailWord_1439001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439001).length < 2 ^ (prefixWord ++ tailWord_1439001).sum := by decide
  have hdescent : baseEnd_1439001 < baseStart_1439001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439005 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_1439005 : Nat := 118140960795 + 1439005 * 2 ^ 59
def prefixEnd_1439005 : Nat := 4983230072969 + 3 ^ 40 * 1439005 * 2
def baseEnd_1439005 : Nat := 492600819482165080013095

theorem tailTrace_1439005 : CollatzResearch.WordTrace tailWord_1439005 prefixEnd_1439005 492600819482165080013095 := by
  unfold tailWord_1439005
  simp only [CollatzResearch.WordTrace]
  refine ⟨52484824151738122332958469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34989882767825414888638979 52484824151738122332958469)
  ·
    refine ⟨9840904528450897937429713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52484824151738122332958469 9840904528450897937429713)
    ·
      refine ⟨7380678396338173453072285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9840904528450897937429713 7380678396338173453072285)
      ·
        refine ⟨2767754398626815044902107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7380678396338173453072285 2767754398626815044902107)
        ·
          refine ⟨4151631597940222567353161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2767754398626815044902107 4151631597940222567353161)
          ·
            refine ⟨3113723698455166925514871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4151631597940222567353161 3113723698455166925514871)
            ·
              refine ⟨4670585547682750388272307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3113723698455166925514871 4670585547682750388272307)
              ·
                refine ⟨7005878321524125582408461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4670585547682750388272307 7005878321524125582408461)
                ·
                  refine ⟨2627204370571547093403173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7005878321524125582408461 2627204370571547093403173)
                  ·
                    refine ⟨492600819482165080013095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2627204370571547093403173 492600819482165080013095)
                    ·
                      rfl

theorem cell22_1439005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_1439005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439005 prefixEnd_1439005 := by exact prefixLift 1439005
  have htrace : WordTrace (prefixWord ++ tailWord_1439005) baseStart_1439005 baseEnd_1439005 := by
    simpa [prefixWord, tailWord_1439005, baseEnd_1439005] using wordTrace_append hprefix tailTrace_1439005
  have hstable : (prefixWord ++ tailWord_1439005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439005).length < 2 ^ (prefixWord ++ tailWord_1439005).sum := by decide
  have hdescent : baseEnd_1439005 < baseStart_1439005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439030 : List Nat := [5, 1, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_1439030 : Nat := 118140960795 + 1439030 * 2 ^ 59
def prefixEnd_1439030 : Nat := 4983230072969 + 3 ^ 40 * 1439030 * 2
def baseEnd_1439030 : Nat := 492609377493073348138019

theorem tailTrace_1439030 : CollatzResearch.WordTrace tailWord_1439030 prefixEnd_1439030 492609377493073348138019 := by
  unfold tailWord_1439030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3280358498540471975163659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34990490651098367735079029 3280358498540471975163659)
  ·
    refine ⟨4920537747810707962745489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3280358498540471975163659 4920537747810707962745489)
    ·
      refine ⟨3690403310858030972059117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4920537747810707962745489 3690403310858030972059117)
      ·
        refine ⟨1383901241571761614522169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3690403310858030972059117 1383901241571761614522169)
        ·
          refine ⟨1037925931178821210891627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1383901241571761614522169 1037925931178821210891627)
          ·
            refine ⟨1556888896768231816337441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037925931178821210891627 1556888896768231816337441)
            ·
              refine ⟨1167666672576173862253081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1556888896768231816337441 1167666672576173862253081)
              ·
                refine ⟨875750004432130396689811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1167666672576173862253081 875750004432130396689811)
                ·
                  refine ⟨1313625006648195595034717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875750004432130396689811 1313625006648195595034717)
                  ·
                    refine ⟨492609377493073348138019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1313625006648195595034717 492609377493073348138019)
                    ·
                      rfl

theorem cell22_1439030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_1439030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439030 prefixEnd_1439030 := by exact prefixLift 1439030
  have htrace : WordTrace (prefixWord ++ tailWord_1439030) baseStart_1439030 baseEnd_1439030 := by
    simpa [prefixWord, tailWord_1439030, baseEnd_1439030] using wordTrace_append hprefix tailTrace_1439030
  have hstable : (prefixWord ++ tailWord_1439030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439030).length < 2 ^ (prefixWord ++ tailWord_1439030).sum := by decide
  have hdescent : baseEnd_1439030 < baseStart_1439030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439086 : List Nat := [4, 1, 2, 4, 1, 2, 1, 2, 2, 3]
def baseStart_1439086 : Nat := 118140960795 + 1439086 * 2 ^ 59
def prefixEnd_1439086 : Nat := 4983230072969 + 3 ^ 40 * 1439086 * 2
def baseEnd_1439086 : Nat := 492628547437507868737847

theorem tailTrace_1439086 : CollatzResearch.WordTrace tailWord_1439086 prefixEnd_1439086 492628547437507868737847 := by
  unfold tailWord_1439086
  simp only [CollatzResearch.WordTrace]
  refine ⟨6560972308055584145832139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34991852309629782111104741 6560972308055584145832139)
  ·
    refine ⟨9841458462083376218748209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6560972308055584145832139 9841458462083376218748209)
    ·
      refine ⟨7381093846562532164061157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9841458462083376218748209 7381093846562532164061157)
      ·
        refine ⟨1383955096230474780761467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7381093846562532164061157 1383955096230474780761467)
        ·
          refine ⟨2075932644345712171142201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1383955096230474780761467 2075932644345712171142201)
          ·
            refine ⟨1556949483259284128356651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2075932644345712171142201 1556949483259284128356651)
            ·
              refine ⟨2335424224888926192534977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556949483259284128356651 2335424224888926192534977)
              ·
                refine ⟨1751568168666694644401233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2335424224888926192534977 1751568168666694644401233)
                ·
                  refine ⟨1313676126500020983300925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1751568168666694644401233 1313676126500020983300925)
                  ·
                    refine ⟨492628547437507868737847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1313676126500020983300925 492628547437507868737847)
                    ·
                      rfl

theorem cell22_1439086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_1439086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439086 prefixEnd_1439086 := by exact prefixLift 1439086
  have htrace : WordTrace (prefixWord ++ tailWord_1439086) baseStart_1439086 baseEnd_1439086 := by
    simpa [prefixWord, tailWord_1439086, baseEnd_1439086] using wordTrace_append hprefix tailTrace_1439086
  have hstable : (prefixWord ++ tailWord_1439086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439086).length < 2 ^ (prefixWord ++ tailWord_1439086).sum := by decide
  have hdescent : baseEnd_1439086 < baseStart_1439086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439097 : List Nat := [1, 2, 1, 3, 2, 1, 4, 4, 1, 3]
def baseStart_1439097 : Nat := 118140960795 + 1439097 * 2 ^ 59
def prefixEnd_1439097 : Nat := 4983230072969 + 3 ^ 40 * 1439097 * 2
def baseEnd_1439097 : Nat := 492632312962307506712813

theorem tailTrace_1439097 : CollatzResearch.WordTrace tailWord_1439097 prefixEnd_1439097 492632312962307506712813 := by
  unfold tailWord_1439097
  simp only [CollatzResearch.WordTrace]
  refine ⟨52488179667404822045307545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34992119778269881363538363 52488179667404822045307545)
  ·
    refine ⟨39366134750553616533980659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52488179667404822045307545 39366134750553616533980659)
    ·
      refine ⟨59049202125830424800970989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39366134750553616533980659 59049202125830424800970989)
      ·
        refine ⟨22143450797186409300364121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59049202125830424800970989 22143450797186409300364121)
        ·
          refine ⟨16607588097889806975273091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22143450797186409300364121 16607588097889806975273091)
          ·
            refine ⟨24911382146834710462909637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16607588097889806975273091 24911382146834710462909637)
            ·
              refine ⟨4670884152531508211795557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24911382146834710462909637 4670884152531508211795557)
              ·
                refine ⟨875790778599657789711667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4670884152531508211795557 875790778599657789711667)
                ·
                  refine ⟨1313686167899486684567501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875790778599657789711667 1313686167899486684567501)
                  ·
                    refine ⟨492632312962307506712813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1313686167899486684567501 492632312962307506712813)
                    ·
                      rfl

theorem cell22_1439097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 1, 3].length) (baseStart_1439097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439097 prefixEnd_1439097 := by exact prefixLift 1439097
  have htrace : WordTrace (prefixWord ++ tailWord_1439097) baseStart_1439097 baseEnd_1439097 := by
    simpa [prefixWord, tailWord_1439097, baseEnd_1439097] using wordTrace_append hprefix tailTrace_1439097
  have hstable : (prefixWord ++ tailWord_1439097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439097).length < 2 ^ (prefixWord ++ tailWord_1439097).sum := by decide
  have hdescent : baseEnd_1439097 < baseStart_1439097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439155 : List Nat := [1, 1, 1, 2, 3, 1, 1, 8, 4]
def baseStart_1439155 : Nat := 118140960795 + 1439155 * 2 ^ 59
def prefixEnd_1439155 : Nat := 4983230072969 + 3 ^ 40 * 1439155 * 2
def baseEnd_1439155 : Nat := 164217389182538229587545

theorem tailTrace_1439155 : CollatzResearch.WordTrace tailWord_1439155 prefixEnd_1439155 164217389182538229587545 := by
  unfold tailWord_1439155
  simp only [CollatzResearch.WordTrace]
  refine ⟨52490295101194697950918919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34993530067463131967279279 52490295101194697950918919)
  ·
    refine ⟨78735442651792046926378379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52490295101194697950918919 78735442651792046926378379)
    ·
      refine ⟨118103163977688070389567569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78735442651792046926378379 118103163977688070389567569)
      ·
        refine ⟨88577372983266052792175677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118103163977688070389567569 88577372983266052792175677)
        ·
          refine ⟨33216514868724769797065879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88577372983266052792175677 33216514868724769797065879)
          ·
            refine ⟨49824772303087154695598819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33216514868724769797065879 49824772303087154695598819)
            ·
              refine ⟨74737158454630732043398229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49824772303087154695598819 74737158454630732043398229)
              ·
                refine ⟨875826075640203891133573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 74737158454630732043398229 875826075640203891133573)
                ·
                  refine ⟨164217389182538229587545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 875826075640203891133573 164217389182538229587545)
                  ·
                    rfl

theorem cell22_1439155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 4].length) (baseStart_1439155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439155 prefixEnd_1439155 := by exact prefixLift 1439155
  have htrace : WordTrace (prefixWord ++ tailWord_1439155) baseStart_1439155 baseEnd_1439155 := by
    simpa [prefixWord, tailWord_1439155, baseEnd_1439155] using wordTrace_append hprefix tailTrace_1439155
  have hstable : (prefixWord ++ tailWord_1439155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439155).length < 2 ^ (prefixWord ++ tailWord_1439155).sum := by decide
  have hdescent : baseEnd_1439155 < baseStart_1439155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439168 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 3, 6]
def baseStart_1439168 : Nat := 118140960795 + 1439168 * 2 ^ 59
def prefixEnd_1439168 : Nat := 4983230072969 + 3 ^ 40 * 1439168 * 2
def baseEnd_1439168 : Nat := 492656617713286988187595

theorem tailTrace_1439168 : CollatzResearch.WordTrace tailWord_1439168 prefixEnd_1439168 492656617713286988187595 := by
  unfold tailWord_1439168
  simp only [CollatzResearch.WordTrace]
  refine ⟨26245384625073800585571079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34993846166765067447428105 26245384625073800585571079)
  ·
    refine ⟨39368076937610700878356619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26245384625073800585571079 39368076937610700878356619)
    ·
      refine ⟨59052115406416051317534929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39368076937610700878356619 59052115406416051317534929)
      ·
        refine ⟨44289086554812038488151197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59052115406416051317534929 44289086554812038488151197)
        ·
          refine ⟨16608407458054514433056699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44289086554812038488151197 16608407458054514433056699)
          ·
            refine ⟨24912611187081771649585049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16608407458054514433056699 24912611187081771649585049)
            ·
              refine ⟨18684458390311328737188787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24912611187081771649585049 18684458390311328737188787)
              ·
                refine ⟨28026687585466993105783181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18684458390311328737188787 28026687585466993105783181)
                ·
                  refine ⟨10510007844550122414668693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28026687585466993105783181 10510007844550122414668693)
                  ·
                    refine ⟨492656617713286988187595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10510007844550122414668693 492656617713286988187595)
                    ·
                      rfl

theorem cell22_1439168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_1439168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439168 prefixEnd_1439168 := by exact prefixLift 1439168
  have htrace : WordTrace (prefixWord ++ tailWord_1439168) baseStart_1439168 baseEnd_1439168 := by
    simpa [prefixWord, tailWord_1439168, baseEnd_1439168] using wordTrace_append hprefix tailTrace_1439168
  have hstable : (prefixWord ++ tailWord_1439168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439168).length < 2 ^ (prefixWord ++ tailWord_1439168).sum := by decide
  have hdescent : baseEnd_1439168 < baseStart_1439168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439183 : List Nat := [1, 1, 2, 1, 1, 4, 4, 8]
def baseStart_1439183 : Nat := 118140960795 + 1439183 * 2 ^ 59
def prefixEnd_1439183 : Nat := 4983230072969 + 3 ^ 40 * 1439183 * 2
def baseEnd_1439183 : Nat := 54740194724425772118061

theorem tailTrace_1439183 : CollatzResearch.WordTrace tailWord_1439183 prefixEnd_1439183 54740194724425772118061 := by
  unfold tailWord_1439183
  simp only [CollatzResearch.WordTrace]
  refine ⟨52491316345093258732938203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34994210896728839155292135 52491316345093258732938203)
  ·
    refine ⟨78736974517639888099407305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52491316345093258732938203 78736974517639888099407305)
    ·
      refine ⟨59052730888229916074555479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78736974517639888099407305 59052730888229916074555479)
      ·
        refine ⟨88579096332344874111833219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59052730888229916074555479 88579096332344874111833219)
        ·
          refine ⟨132868644498517311167749829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88579096332344874111833219 132868644498517311167749829)
          ·
            refine ⟨24912870843471995843953093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132868644498517311167749829 24912870843471995843953093)
            ·
              refine ⟨4671163283150999220741205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24912870843471995843953093 4671163283150999220741205)
              ·
                refine ⟨54740194724425772118061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4671163283150999220741205 54740194724425772118061)
                ·
                  rfl

theorem cell22_1439183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 8].length) (baseStart_1439183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439183 prefixEnd_1439183 := by exact prefixLift 1439183
  have htrace : WordTrace (prefixWord ++ tailWord_1439183) baseStart_1439183 baseEnd_1439183 := by
    simpa [prefixWord, tailWord_1439183, baseEnd_1439183] using wordTrace_append hprefix tailTrace_1439183
  have hstable : (prefixWord ++ tailWord_1439183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439183).length < 2 ^ (prefixWord ++ tailWord_1439183).sum := by decide
  have hdescent : baseEnd_1439183 < baseStart_1439183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439234 : List Nat := [3, 4, 1, 2, 1, 2, 3, 6]
def baseStart_1439234 : Nat := 118140960795 + 1439234 * 2 ^ 59
def prefixEnd_1439234 : Nat := 4983230072969 + 3 ^ 40 * 1439234 * 2
def baseEnd_1439234 : Nat := 54742134540231646226377

theorem tailTrace_1439234 : CollatzResearch.WordTrace tailWord_1439234 prefixEnd_1439234 54742134540231646226377 := by
  unfold tailWord_1439234
  simp only [CollatzResearch.WordTrace]
  refine ⟨13123294116977123610761189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34995450978605662962029837 13123294116977123610761189)
  ·
    refine ⟨2460617646933210677017723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13123294116977123610761189 2460617646933210677017723)
    ·
      refine ⟨3690926470399816015526585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2460617646933210677017723 3690926470399816015526585)
      ·
        refine ⟨2768194852799862011644939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3690926470399816015526585 2768194852799862011644939)
        ·
          refine ⟨4152292279199793017467409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2768194852799862011644939 4152292279199793017467409)
          ·
            refine ⟨3114219209399844763100557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4152292279199793017467409 3114219209399844763100557)
            ·
              refine ⟨1167832203524941786162709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3114219209399844763100557 1167832203524941786162709)
              ·
                refine ⟨54742134540231646226377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1167832203524941786162709 54742134540231646226377)
                ·
                  rfl

theorem cell22_1439234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 6].length) (baseStart_1439234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439234 prefixEnd_1439234 := by exact prefixLift 1439234
  have htrace : WordTrace (prefixWord ++ tailWord_1439234) baseStart_1439234 baseEnd_1439234 := by
    simpa [prefixWord, tailWord_1439234, baseEnd_1439234] using wordTrace_append hprefix tailTrace_1439234
  have hstable : (prefixWord ++ tailWord_1439234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439234).length < 2 ^ (prefixWord ++ tailWord_1439234).sum := by decide
  have hdescent : baseEnd_1439234 < baseStart_1439234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439236 : List Nat := [2, 3, 2, 3, 3, 1, 1, 1, 2, 4]
def baseStart_1439236 : Nat := 118140960795 + 1439236 * 2 ^ 59
def prefixEnd_1439236 : Nat := 4983230072969 + 3 ^ 40 * 1439236 * 2
def baseEnd_1439236 : Nat := 492679895502957477487387

theorem tailTrace_1439236 : CollatzResearch.WordTrace tailWord_1439236 prefixEnd_1439236 492679895502957477487387 := by
  unfold tailWord_1439236
  simp only [CollatzResearch.WordTrace]
  refine ⟨26246624706950624392308781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34995499609267499189745041 26246624706950624392308781)
  ·
    refine ⟨9842484265106484147115793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26246624706950624392308781 9842484265106484147115793)
    ·
      refine ⟨7381863198829863110336845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9842484265106484147115793 7381863198829863110336845)
      ·
        refine ⟨2768198699561198666376317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7381863198829863110336845 2768198699561198666376317)
        ·
          refine ⟨1038074512335449499891119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2768198699561198666376317 1038074512335449499891119)
          ·
            refine ⟨1557111768503174249836679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038074512335449499891119 1557111768503174249836679)
            ·
              refine ⟨2335667652754761374755019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1557111768503174249836679 2335667652754761374755019)
              ·
                refine ⟨3503501479132142062132529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2335667652754761374755019 3503501479132142062132529)
                ·
                  refine ⟨2627626109349106546599397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3503501479132142062132529 2627626109349106546599397)
                  ·
                    refine ⟨492679895502957477487387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2627626109349106546599397 492679895502957477487387)
                    ·
                      rfl

theorem cell22_1439236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_1439236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439236 prefixEnd_1439236 := by exact prefixLift 1439236
  have htrace : WordTrace (prefixWord ++ tailWord_1439236) baseStart_1439236 baseEnd_1439236 := by
    simpa [prefixWord, tailWord_1439236, baseEnd_1439236] using wordTrace_append hprefix tailTrace_1439236
  have hstable : (prefixWord ++ tailWord_1439236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439236).length < 2 ^ (prefixWord ++ tailWord_1439236).sum := by decide
  have hdescent : baseEnd_1439236 < baseStart_1439236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439249 : List Nat := [1, 2, 2, 1, 1, 2, 6, 3, 1, 3]
def baseStart_1439249 : Nat := 118140960795 + 1439249 * 2 ^ 59
def prefixEnd_1439249 : Nat := 4983230072969 + 3 ^ 40 * 1439249 * 2
def baseEnd_1439249 : Nat := 492684345668629776912347

theorem tailTrace_1439249 : CollatzResearch.WordTrace tailWord_1439249 prefixEnd_1439249 492684345668629776912347 := by
  unfold tailWord_1439249
  simp only [CollatzResearch.WordTrace]
  refine ⟨52493723562854152004840801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34995815708569434669893867 52493723562854152004840801)
  ·
    refine ⟨39370292672140614003630601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52493723562854152004840801 39370292672140614003630601)
    ·
      refine ⟨29527719504105460502722951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39370292672140614003630601 29527719504105460502722951)
      ·
        refine ⟨44291579256158190754084427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29527719504105460502722951 44291579256158190754084427)
        ·
          refine ⟨66437368884237286131126641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44291579256158190754084427 66437368884237286131126641)
          ·
            refine ⟨49828026663177964598344981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66437368884237286131126641 49828026663177964598344981)
            ·
              refine ⟨2335688749836467090547421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49828026663177964598344981 2335688749836467090547421)
              ·
                refine ⟨875883281188675158955283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2335688749836467090547421 875883281188675158955283)
                ·
                  refine ⟨1313824921783012738432925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875883281188675158955283 1313824921783012738432925)
                  ·
                    refine ⟨492684345668629776912347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1313824921783012738432925 492684345668629776912347)
                    ·
                      rfl

theorem cell22_1439249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 1, 3].length) (baseStart_1439249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439249 prefixEnd_1439249 := by exact prefixLift 1439249
  have htrace : WordTrace (prefixWord ++ tailWord_1439249) baseStart_1439249 baseEnd_1439249 := by
    simpa [prefixWord, tailWord_1439249, baseEnd_1439249] using wordTrace_append hprefix tailTrace_1439249
  have hstable : (prefixWord ++ tailWord_1439249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439249).length < 2 ^ (prefixWord ++ tailWord_1439249).sum := by decide
  have hdescent : baseEnd_1439249 < baseStart_1439249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439260 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 4, 5]
def baseStart_1439260 : Nat := 118140960795 + 1439260 * 2 ^ 59
def prefixEnd_1439260 : Nat := 4983230072969 + 3 ^ 40 * 1439260 * 2
def baseEnd_1439260 : Nat := 492688111193429414887313

theorem tailTrace_1439260 : CollatzResearch.WordTrace tailWord_1439260 prefixEnd_1439260 492688111193429414887313 := by
  unfold tailWord_1439260
  simp only [CollatzResearch.WordTrace]
  refine ⟨26247062382907150441745617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34996083177209533922327489 26247062382907150441745617)
  ·
    refine ⟨19685296787180362831309213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26247062382907150441745617 19685296787180362831309213)
    ·
      refine ⟨7381986295192636061740955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19685296787180362831309213 7381986295192636061740955)
      ·
        refine ⟨11072979442788954092611433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7381986295192636061740955 11072979442788954092611433)
        ·
          refine ⟨8304734582091715569458575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11072979442788954092611433 8304734582091715569458575)
          ·
            refine ⟨12457101873137573354187863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8304734582091715569458575 12457101873137573354187863)
            ·
              refine ⟨18685652809706360031281795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12457101873137573354187863 18685652809706360031281795)
              ·
                refine ⟨28028479214559540046922693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18685652809706360031281795 28028479214559540046922693)
                ·
                  refine ⟨5255339852729913758798005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28028479214559540046922693 5255339852729913758798005)
                  ·
                    refine ⟨492688111193429414887313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5255339852729913758798005 492688111193429414887313)
                    ·
                      rfl

theorem cell22_1439260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_1439260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439260 prefixEnd_1439260 := by exact prefixLift 1439260
  have htrace : WordTrace (prefixWord ++ tailWord_1439260) baseStart_1439260 baseEnd_1439260 := by
    simpa [prefixWord, tailWord_1439260, baseEnd_1439260] using wordTrace_append hprefix tailTrace_1439260
  have hstable : (prefixWord ++ tailWord_1439260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439260).length < 2 ^ (prefixWord ++ tailWord_1439260).sum := by decide
  have hdescent : baseEnd_1439260 < baseStart_1439260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439290 : List Nat := [3, 1, 1, 1, 3, 2, 1, 4, 6]
def baseStart_1439290 : Nat := 118140960795 + 1439290 * 2 ^ 59
def prefixEnd_1439290 : Nat := 4983230072969 + 3 ^ 40 * 1439290 * 2
def baseEnd_1439290 : Nat := 164232793602173112212407

theorem tailTrace_1439290 : CollatzResearch.WordTrace tailWord_1439290 prefixEnd_1439290 164232793602173112212407 := by
  unfold tailWord_1439290
  simp only [CollatzResearch.WordTrace]
  refine ⟨13123804738926404001770831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34996812637137077338055549 13123804738926404001770831)
  ·
    refine ⟨19685707108389606002656247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13123804738926404001770831 19685707108389606002656247)
    ·
      refine ⟨29528560662584409003984371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19685707108389606002656247 29528560662584409003984371)
      ·
        refine ⟨44292840993876613505976557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29528560662584409003984371 44292840993876613505976557)
        ·
          refine ⟨16609815372703730064741209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44292840993876613505976557 16609815372703730064741209)
          ·
            refine ⟨12457361529527797548555907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16609815372703730064741209 12457361529527797548555907)
            ·
              refine ⟨18686042294291696322833861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12457361529527797548555907 18686042294291696322833861)
              ·
                refine ⟨3503632930179693060531349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18686042294291696322833861 3503632930179693060531349)
                ·
                  refine ⟨164232793602173112212407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3503632930179693060531349 164232793602173112212407)
                  ·
                    rfl

theorem cell22_1439290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_1439290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439290 prefixEnd_1439290 := by exact prefixLift 1439290
  have htrace : WordTrace (prefixWord ++ tailWord_1439290) baseStart_1439290 baseEnd_1439290 := by
    simpa [prefixWord, tailWord_1439290, baseEnd_1439290] using wordTrace_append hprefix tailTrace_1439290
  have hstable : (prefixWord ++ tailWord_1439290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439290).length < 2 ^ (prefixWord ++ tailWord_1439290).sum := by decide
  have hdescent : baseEnd_1439290 < baseStart_1439290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439305 : List Nat := [1, 2, 1, 1, 2, 2, 1, 6, 1, 5]
def baseStart_1439305 : Nat := 118140960795 + 1439305 * 2 ^ 59
def prefixEnd_1439305 : Nat := 4983230072969 + 3 ^ 40 * 1439305 * 2
def baseEnd_1439305 : Nat := 492703515613064297512175

theorem tailTrace_1439305 : CollatzResearch.WordTrace tailWord_1439305 prefixEnd_1439305 492703515613064297512175 := by
  unfold tailWord_1439305
  simp only [CollatzResearch.WordTrace]
  refine ⟨52495766050651273568879369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34997177367100849045919579 52495766050651273568879369)
  ·
    refine ⟨39371824537988455176659527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52495766050651273568879369 39371824537988455176659527)
    ·
      refine ⟨59057736806982682764989291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39371824537988455176659527 59057736806982682764989291)
      ·
        refine ⟨88586605210474024147483937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59057736806982682764989291 88586605210474024147483937)
        ·
          refine ⟨66439953907855518110612953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88586605210474024147483937 66439953907855518110612953)
          ·
            refine ⟨49829965430891638582959715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66439953907855518110612953 49829965430891638582959715)
            ·
              refine ⟨74744948146337457874439573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49829965430891638582959715 74744948146337457874439573)
              ·
                refine ⟨3503669444359568337864355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74744948146337457874439573 3503669444359568337864355)
                ·
                  refine ⟨5255504166539352506796533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3503669444359568337864355 5255504166539352506796533)
                  ·
                    refine ⟨492703515613064297512175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5255504166539352506796533 492703515613064297512175)
                    ·
                      rfl

theorem cell22_1439305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_1439305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439305 prefixEnd_1439305 := by exact prefixLift 1439305
  have htrace : WordTrace (prefixWord ++ tailWord_1439305) baseStart_1439305 baseEnd_1439305 := by
    simpa [prefixWord, tailWord_1439305, baseEnd_1439305] using wordTrace_append hprefix tailTrace_1439305
  have hstable : (prefixWord ++ tailWord_1439305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439305).length < 2 ^ (prefixWord ++ tailWord_1439305).sum := by decide
  have hdescent : baseEnd_1439305 < baseStart_1439305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439324 : List Nat := [2, 2, 4, 1, 2, 3, 1, 1, 6]
def baseStart_1439324 : Nat := 118140960795 + 1439324 * 2 ^ 59
def prefixEnd_1439324 : Nat := 4983230072969 + 3 ^ 40 * 1439324 * 2
def baseEnd_1439324 : Nat := 164236673233784860429039

theorem tailTrace_1439324 : CollatzResearch.WordTrace tailWord_1439324 prefixEnd_1439324 164236673233784860429039 := by
  unfold tailWord_1439324
  simp only [CollatzResearch.WordTrace]
  refine ⟨26248229518791219906910513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34997639358388293209214017 26248229518791219906910513)
  ·
    refine ⟨19686172139093414930182885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26248229518791219906910513 19686172139093414930182885)
    ·
      refine ⟨3691157276080015299409291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19686172139093414930182885 3691157276080015299409291)
      ·
        refine ⟨5536735914120022949113937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3691157276080015299409291 5536735914120022949113937)
        ·
          refine ⟨4152551935590017211835453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5536735914120022949113937 4152551935590017211835453)
          ·
            refine ⟨1557206975846256454438295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4152551935590017211835453 1557206975846256454438295)
            ·
              refine ⟨2335810463769384681657443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1557206975846256454438295 2335810463769384681657443)
              ·
                refine ⟨3503715695654077022486165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2335810463769384681657443 3503715695654077022486165)
                ·
                  refine ⟨164236673233784860429039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3503715695654077022486165 164236673233784860429039)
                  ·
                    rfl

theorem cell22_1439324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_1439324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439324 prefixEnd_1439324 := by exact prefixLift 1439324
  have htrace : WordTrace (prefixWord ++ tailWord_1439324) baseStart_1439324 baseEnd_1439324 := by
    simpa [prefixWord, tailWord_1439324, baseEnd_1439324] using wordTrace_append hprefix tailTrace_1439324
  have hstable : (prefixWord ++ tailWord_1439324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439324).length < 2 ^ (prefixWord ++ tailWord_1439324).sum := by decide
  have hdescent : baseEnd_1439324 < baseStart_1439324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439335 : List Nat := [1, 1, 5, 1, 1, 1, 3, 9]
def baseStart_1439335 : Nat := 118140960795 + 1439335 * 2 ^ 59
def prefixEnd_1439335 : Nat := 4983230072969 + 3 ^ 40 * 1439335 * 2
def baseEnd_1439335 : Nat := 54745976136239357695787

theorem tailTrace_1439335 : CollatzResearch.WordTrace tailWord_1439335 prefixEnd_1439335 54745976136239357695787 := by
  unfold tailWord_1439335
  simp only [CollatzResearch.WordTrace]
  refine ⟨52496860240542588692471459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34997906827028392461647639 52496860240542588692471459)
  ·
    refine ⟨78745290360813883038707189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52496860240542588692471459 78745290360813883038707189)
    ·
      refine ⟨7382370971326301534878799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78745290360813883038707189 7382370971326301534878799)
      ·
        refine ⟨11073556456989452302318199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7382370971326301534878799 11073556456989452302318199)
        ·
          refine ⟨16610334685484178453477299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11073556456989452302318199 16610334685484178453477299)
          ·
            refine ⟨24915502028226267680215949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16610334685484178453477299 24915502028226267680215949)
            ·
              refine ⟨9343313260584850380080981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24915502028226267680215949 9343313260584850380080981)
              ·
                refine ⟨54745976136239357695787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9343313260584850380080981 54745976136239357695787)
                ·
                  rfl

theorem cell22_1439335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 9].length) (baseStart_1439335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439335 prefixEnd_1439335 := by exact prefixLift 1439335
  have htrace : WordTrace (prefixWord ++ tailWord_1439335) baseStart_1439335 baseEnd_1439335 := by
    simpa [prefixWord, tailWord_1439335, baseEnd_1439335] using wordTrace_append hprefix tailTrace_1439335
  have hstable : (prefixWord ++ tailWord_1439335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439335).length < 2 ^ (prefixWord ++ tailWord_1439335).sum := by decide
  have hdescent : baseEnd_1439335 < baseStart_1439335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439397 : List Nat := [1, 3, 1, 2, 1, 2, 4, 3, 5]
def baseStart_1439397 : Nat := 118140960795 + 1439397 * 2 ^ 59
def prefixEnd_1439397 : Nat := 4983230072969 + 3 ^ 40 * 1439397 * 2
def baseEnd_1439397 : Nat := 164245003031068908070631

theorem tailTrace_1439397 : CollatzResearch.WordTrace tailWord_1439397 prefixEnd_1439397 164245003031068908070631 := by
  unfold tailWord_1439397
  simp only [CollatzResearch.WordTrace]
  refine ⟨52499121566317973281228445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34999414377545315520818963 52499121566317973281228445)
  ·
    refine ⟨19687170587369239980460667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52499121566317973281228445 19687170587369239980460667)
    ·
      refine ⟨29530755881053859970691001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19687170587369239980460667 29530755881053859970691001)
      ·
        refine ⟨22148066910790394978018251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29530755881053859970691001 22148066910790394978018251)
        ·
          refine ⟨33222100366185592467027377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22148066910790394978018251 33222100366185592467027377)
          ·
            refine ⟨24916575274639194350270533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33222100366185592467027377 24916575274639194350270533)
            ·
              refine ⟨4671857863994848940675725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24916575274639194350270533 4671857863994848940675725)
              ·
                refine ⟨1751946698998068352753397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4671857863994848940675725 1751946698998068352753397)
                ·
                  refine ⟨164245003031068908070631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1751946698998068352753397 164245003031068908070631)
                  ·
                    rfl

theorem cell22_1439397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_1439397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439397 prefixEnd_1439397 := by exact prefixLift 1439397
  have htrace : WordTrace (prefixWord ++ tailWord_1439397) baseStart_1439397 baseEnd_1439397 := by
    simpa [prefixWord, tailWord_1439397, baseEnd_1439397] using wordTrace_append hprefix tailTrace_1439397
  have hstable : (prefixWord ++ tailWord_1439397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439397).length < 2 ^ (prefixWord ++ tailWord_1439397).sum := by decide
  have hdescent : baseEnd_1439397 < baseStart_1439397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439474 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 6, 3]
def baseStart_1439474 : Nat := 118140960795 + 1439474 * 2 ^ 59
def prefixEnd_1439474 : Nat := 4983230072969 + 3 ^ 40 * 1439474 * 2
def baseEnd_1439474 : Nat := 492761367766804190036657

theorem tailTrace_1439474 : CollatzResearch.WordTrace tailWord_1439474 prefixEnd_1439474 492761367766804190036657 := by
  unfold tailWord_1439474
  simp only [CollatzResearch.WordTrace]
  refine ⟨13125482496759753857945369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35001286658026010287854317 13125482496759753857945369)
  ·
    refine ⟨9844111872569815393459027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13125482496759753857945369 9844111872569815393459027)
    ·
      refine ⟨14766167808854723090188541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9844111872569815393459027 14766167808854723090188541)
      ·
        refine ⟨5537312928320521158820703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14766167808854723090188541 5537312928320521158820703)
        ·
          refine ⟨8305969392480781738231055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5537312928320521158820703 8305969392480781738231055)
          ·
            refine ⟨12458954088721172607346583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8305969392480781738231055 12458954088721172607346583)
            ·
              refine ⟨18688431133081758911019875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12458954088721172607346583 18688431133081758911019875)
              ·
                refine ⟨28032646699622638366529813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18688431133081758911019875 28032646699622638366529813)
                ·
                  refine ⟨1314030314044811173431085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28032646699622638366529813 1314030314044811173431085)
                  ·
                    refine ⟨492761367766804190036657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1314030314044811173431085 492761367766804190036657)
                    ·
                      rfl

theorem cell22_1439474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_1439474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439474 prefixEnd_1439474 := by exact prefixLift 1439474
  have htrace : WordTrace (prefixWord ++ tailWord_1439474) baseStart_1439474 baseEnd_1439474 := by
    simpa [prefixWord, tailWord_1439474, baseEnd_1439474] using wordTrace_append hprefix tailTrace_1439474
  have hstable : (prefixWord ++ tailWord_1439474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439474).length < 2 ^ (prefixWord ++ tailWord_1439474).sum := by decide
  have hdescent : baseEnd_1439474 < baseStart_1439474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439519 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 5, 3]
def baseStart_1439519 : Nat := 118140960795 + 1439519 * 2 ^ 59
def prefixEnd_1439519 : Nat := 4983230072969 + 3 ^ 40 * 1439519 * 2
def baseEnd_1439519 : Nat := 492776772186439072661519

theorem tailTrace_1439519 : CollatzResearch.WordTrace tailWord_1439519 prefixEnd_1439519 492776772186439072661519 := by
  unfold tailWord_1439519
  simp only [CollatzResearch.WordTrace]
  refine ⟨52503571271875988117169611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35002380847917325411446407 52503571271875988117169611)
  ·
    refine ⟨78755356907813982175754417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52503571271875988117169611 78755356907813982175754417)
    ·
      refine ⟨59066517680860486631815813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78755356907813982175754417 59066517680860486631815813)
      ·
        refine ⟨11074972065161341243465465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59066517680860486631815813 11074972065161341243465465)
        ·
          refine ⟨8306229048871005932599099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11074972065161341243465465 8306229048871005932599099)
          ·
            refine ⟨12459343573306508898898649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8306229048871005932599099 12459343573306508898898649)
            ·
              refine ⟨9344507679979881674173987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12459343573306508898898649 9344507679979881674173987)
              ·
                refine ⟨14016761519969822511260981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9344507679979881674173987 14016761519969822511260981)
                ·
                  refine ⟨1314071392497170860430717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14016761519969822511260981 1314071392497170860430717)
                  ·
                    refine ⟨492776772186439072661519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1314071392497170860430717 492776772186439072661519)
                    ·
                      rfl

theorem cell22_1439519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 3].length) (baseStart_1439519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439519 prefixEnd_1439519 := by exact prefixLift 1439519
  have htrace : WordTrace (prefixWord ++ tailWord_1439519) baseStart_1439519 baseEnd_1439519 := by
    simpa [prefixWord, tailWord_1439519, baseEnd_1439519] using wordTrace_append hprefix tailTrace_1439519
  have hstable : (prefixWord ++ tailWord_1439519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439519).length < 2 ^ (prefixWord ++ tailWord_1439519).sum := by decide
  have hdescent : baseEnd_1439519 < baseStart_1439519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439596 : List Nat := [2, 2, 1, 1, 4, 3, 1, 3, 1, 4]
def baseStart_1439596 : Nat := 118140960795 + 1439596 * 2 ^ 59
def prefixEnd_1439596 : Nat := 4983230072969 + 3 ^ 40 * 1439596 * 2
def baseEnd_1439596 : Nat := 492803130860036538486283

theorem tailTrace_1439596 : CollatzResearch.WordTrace tailWord_1439596 prefixEnd_1439596 492803130860036538486283 := by
  unfold tailWord_1439596
  simp only [CollatzResearch.WordTrace]
  refine ⟨26253189846298515133861321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35004253128398020178481761 26253189846298515133861321)
  ·
    refine ⟨19689892384723886350395991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26253189846298515133861321 19689892384723886350395991)
    ·
      refine ⟨29534838577085829525593987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19689892384723886350395991 29534838577085829525593987)
      ·
        refine ⟨44302257865628744288390981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29534838577085829525593987 44302257865628744288390981)
        ·
          refine ⟨8306673349805389554073309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44302257865628744288390981 8306673349805389554073309)
          ·
            refine ⟨3115002506177021082777491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8306673349805389554073309 3115002506177021082777491)
            ·
              refine ⟨4672503759265531624166237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3115002506177021082777491 4672503759265531624166237)
              ·
                refine ⟨1752188909724574359062339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4672503759265531624166237 1752188909724574359062339)
                ·
                  refine ⟨2628283364586861538593509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752188909724574359062339 2628283364586861538593509)
                  ·
                    refine ⟨492803130860036538486283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2628283364586861538593509 492803130860036538486283)
                    ·
                      rfl

theorem cell22_1439596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_1439596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439596 prefixEnd_1439596 := by exact prefixLift 1439596
  have htrace : WordTrace (prefixWord ++ tailWord_1439596) baseStart_1439596 baseEnd_1439596 := by
    simpa [prefixWord, tailWord_1439596, baseEnd_1439596] using wordTrace_append hprefix tailTrace_1439596
  have hstable : (prefixWord ++ tailWord_1439596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439596).length < 2 ^ (prefixWord ++ tailWord_1439596).sum := by decide
  have hdescent : baseEnd_1439596 < baseStart_1439596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439630 : List Nat := [4, 1, 1, 5, 1, 1, 2, 2, 1, 4]
def baseStart_1439630 : Nat := 118140960795 + 1439630 * 2 ^ 59
def prefixEnd_1439630 : Nat := 4983230072969 + 3 ^ 40 * 1439630 * 2
def baseEnd_1439630 : Nat := 492814769754871783136179

theorem tailTrace_1439630 : CollatzResearch.WordTrace tailWord_1439630 prefixEnd_1439630 492814769754871783136179 := by
  unfold tailWord_1439630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6563452471809231759307543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35005079849649236049640229 6563452471809231759307543)
  ·
    refine ⟨9845178707713847638961315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6563452471809231759307543 9845178707713847638961315)
    ·
      refine ⟨14767768061570771458441973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9845178707713847638961315 14767768061570771458441973)
      ·
        refine ⟨1384478255772259824228935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14767768061570771458441973 1384478255772259824228935)
        ·
          refine ⟨2076717383658389736343403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1384478255772259824228935 2076717383658389736343403)
          ·
            refine ⟨3115076075487584604515105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2076717383658389736343403 3115076075487584604515105)
            ·
              refine ⟨2336307056615688453386329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3115076075487584604515105 2336307056615688453386329)
              ·
                refine ⟨1752230292461766340039747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2336307056615688453386329 1752230292461766340039747)
                ·
                  refine ⟨2628345438692649510059621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752230292461766340039747 2628345438692649510059621)
                  ·
                    refine ⟨492814769754871783136179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2628345438692649510059621 492814769754871783136179)
                    ·
                      rfl

theorem cell22_1439630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_1439630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439630 prefixEnd_1439630 := by exact prefixLift 1439630
  have htrace : WordTrace (prefixWord ++ tailWord_1439630) baseStart_1439630 baseEnd_1439630 := by
    simpa [prefixWord, tailWord_1439630, baseEnd_1439630] using wordTrace_append hprefix tailTrace_1439630
  have hstable : (prefixWord ++ tailWord_1439630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439630).length < 2 ^ (prefixWord ++ tailWord_1439630).sum := by decide
  have hdescent : baseEnd_1439630 < baseStart_1439630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439639 : List Nat := [1, 1, 3, 3, 1, 4, 1, 8]
def baseStart_1439639 : Nat := 118140960795 + 1439639 * 2 ^ 59
def prefixEnd_1439639 : Nat := 4983230072969 + 3 ^ 40 * 1439639 * 2
def baseEnd_1439639 : Nat := 54757538959866528851239

theorem tailTrace_1439639 : CollatzResearch.WordTrace tailWord_1439639 prefixEnd_1439639 54757538959866528851239 := by
  unfold tailWord_1439639
  simp only [CollatzResearch.WordTrace]
  refine ⟨52507948031441248611537971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35005298687627499074358647 52507948031441248611537971)
  ·
    refine ⟨78761922047161872917306957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52507948031441248611537971 78761922047161872917306957)
    ·
      refine ⟨29535720767685702343990109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78761922047161872917306957 29535720767685702343990109)
      ·
        refine ⟨11075895287882138378996291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29535720767685702343990109 11075895287882138378996291)
        ·
          refine ⟨16613842931823207568494437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11075895287882138378996291 16613842931823207568494437)
          ·
            refine ⟨3115095549716851419092707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16613842931823207568494437 3115095549716851419092707)
            ·
              refine ⟨4672643324575277128639061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3115095549716851419092707 4672643324575277128639061)
              ·
                refine ⟨54757538959866528851239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4672643324575277128639061 54757538959866528851239)
                ·
                  rfl

theorem cell22_1439639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 8].length) (baseStart_1439639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439639 prefixEnd_1439639 := by exact prefixLift 1439639
  have htrace : WordTrace (prefixWord ++ tailWord_1439639) baseStart_1439639 baseEnd_1439639 := by
    simpa [prefixWord, tailWord_1439639, baseEnd_1439639] using wordTrace_append hprefix tailTrace_1439639
  have hstable : (prefixWord ++ tailWord_1439639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439639).length < 2 ^ (prefixWord ++ tailWord_1439639).sum := by decide
  have hdescent : baseEnd_1439639 < baseStart_1439639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439662 : List Nat := [4, 1, 5, 1, 1, 2, 1, 1, 6]
def baseStart_1439662 : Nat := 118140960795 + 1439662 * 2 ^ 59
def prefixEnd_1439662 : Nat := 4983230072969 + 3 ^ 40 * 1439662 * 2
def baseEnd_1439662 : Nat := 164275241336278122112027

theorem tailTrace_1439662 : CollatzResearch.WordTrace tailWord_1439662 prefixEnd_1439662 164275241336278122112027 := by
  unfold tailWord_1439662
  simp only [CollatzResearch.WordTrace]
  refine ⟨6563598363794740442453155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35005857940238615693083493 6563598363794740442453155)
  ·
    refine ⟨9845397545692110663679733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6563598363794740442453155 9845397545692110663679733)
    ·
      refine ⟨923006019908635374719975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9845397545692110663679733 923006019908635374719975)
      ·
        refine ⟨1384509029862953062079963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 923006019908635374719975 1384509029862953062079963)
        ·
          refine ⟨2076763544794429593119945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1384509029862953062079963 2076763544794429593119945)
          ·
            refine ⟨1557572658595822194839959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2076763544794429593119945 1557572658595822194839959)
            ·
              refine ⟨2336358987893733292259939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1557572658595822194839959 2336358987893733292259939)
              ·
                refine ⟨3504538481840599938389909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2336358987893733292259939 3504538481840599938389909)
                ·
                  refine ⟨164275241336278122112027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3504538481840599938389909 164275241336278122112027)
                  ·
                    rfl

theorem cell22_1439662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_1439662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439662 prefixEnd_1439662 := by exact prefixLift 1439662
  have htrace : WordTrace (prefixWord ++ tailWord_1439662) baseStart_1439662 baseEnd_1439662 := by
    simpa [prefixWord, tailWord_1439662, baseEnd_1439662] using wordTrace_append hprefix tailTrace_1439662
  have hstable : (prefixWord ++ tailWord_1439662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439662).length < 2 ^ (prefixWord ++ tailWord_1439662).sum := by decide
  have hdescent : baseEnd_1439662 < baseStart_1439662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439778 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_1439778 : Nat := 118140960795 + 1439778 * 2 ^ 59
def prefixEnd_1439778 : Nat := 4983230072969 + 3 ^ 40 * 1439778 * 2
def baseEnd_1439778 : Nat := 492865433179448730435725

theorem tailTrace_1439778 : CollatzResearch.WordTrace tailWord_1439778 prefixEnd_1439778 492865433179448730435725 := by
  unfold tailWord_1439778
  simp only [CollatzResearch.WordTrace]
  refine ⟨13128254444484418837711997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35008678518625116900565325 13128254444484418837711997)
  ·
    refine ⟨4923095416681657064141999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13128254444484418837711997 4923095416681657064141999)
    ·
      refine ⟨7384643125022485596212999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4923095416681657064141999 7384643125022485596212999)
      ·
        refine ⟨11076964687533728394319499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7384643125022485596212999 11076964687533728394319499)
        ·
          refine ⟨16615447031300592591479249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11076964687533728394319499 16615447031300592591479249)
          ·
            refine ⟨12461585273475444443609437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16615447031300592591479249 12461585273475444443609437)
            ·
              refine ⟨4673094477553291666353539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12461585273475444443609437 4673094477553291666353539)
              ·
                refine ⟨7009641716329937499530309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4673094477553291666353539 7009641716329937499530309)
                ·
                  refine ⟨1314307821811863281161933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7009641716329937499530309 1314307821811863281161933)
                  ·
                    refine ⟨492865433179448730435725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1314307821811863281161933 492865433179448730435725)
                    ·
                      rfl

theorem cell22_1439778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_1439778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439778 prefixEnd_1439778 := by exact prefixLift 1439778
  have htrace : WordTrace (prefixWord ++ tailWord_1439778) baseStart_1439778 baseEnd_1439778 := by
    simpa [prefixWord, tailWord_1439778, baseEnd_1439778] using wordTrace_append hprefix tailTrace_1439778
  have hstable : (prefixWord ++ tailWord_1439778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439778).length < 2 ^ (prefixWord ++ tailWord_1439778).sum := by decide
  have hdescent : baseEnd_1439778 < baseStart_1439778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439808 : List Nat := [2, 1, 1, 2, 2, 6, 2, 6]
def baseStart_1439808 : Nat := 118140960795 + 1439808 * 2 ^ 59
def prefixEnd_1439808 : Nat := 4983230072969 + 3 ^ 40 * 1439808 * 2
def baseEnd_1439808 : Nat := 54763966976948739131737

theorem tailTrace_1439808 : CollatzResearch.WordTrace tailWord_1439808 prefixEnd_1439808 54763966976948739131737 := by
  unfold tailWord_1439808
  simp only [CollatzResearch.WordTrace]
  refine ⟨26257055983914495237220039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35009407978552660316293385 26257055983914495237220039)
  ·
    refine ⟨39385583975871742855830059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26257055983914495237220039 39385583975871742855830059)
    ·
      refine ⟨59078375963807614283745089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39385583975871742855830059 59078375963807614283745089)
      ·
        refine ⟨44308781972855710712808817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59078375963807614283745089 44308781972855710712808817)
        ·
          refine ⟨33231586479641783034606613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44308781972855710712808817 33231586479641783034606613)
          ·
            refine ⟨1557730616233208579747185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33231586479641783034606613 1557730616233208579747185)
            ·
              refine ⟨1168297962174906434810389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1557730616233208579747185 1168297962174906434810389)
              ·
                refine ⟨54763966976948739131737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1168297962174906434810389 54763966976948739131737)
                ·
                  rfl

theorem cell22_1439808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 6].length) (baseStart_1439808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439808 prefixEnd_1439808 := by exact prefixLift 1439808
  have htrace : WordTrace (prefixWord ++ tailWord_1439808) baseStart_1439808 baseEnd_1439808 := by
    simpa [prefixWord, tailWord_1439808, baseEnd_1439808] using wordTrace_append hprefix tailTrace_1439808
  have hstable : (prefixWord ++ tailWord_1439808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439808).length < 2 ^ (prefixWord ++ tailWord_1439808).sum := by decide
  have hdescent : baseEnd_1439808 < baseStart_1439808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439840 : List Nat := [2, 1, 1, 3, 2, 5, 1, 1, 3, 3]
def baseStart_1439840 : Nat := 118140960795 + 1439840 * 2 ^ 59
def prefixEnd_1439840 : Nat := 4983230072969 + 3 ^ 40 * 1439840 * 2
def baseEnd_1439840 : Nat := 492886657046501235385535

theorem tailTrace_1439840 : CollatzResearch.WordTrace tailWord_1439840 prefixEnd_1439840 492886657046501235385535 := by
  unfold tailWord_1439840
  simp only [CollatzResearch.WordTrace]
  refine ⟨26257639551856529969802487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35010186069142039959736649 26257639551856529969802487)
  ·
    refine ⟨39386459327784794954703731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26257639551856529969802487 39386459327784794954703731)
    ·
      refine ⟨59079688991677192432055597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39386459327784794954703731 59079688991677192432055597)
      ·
        refine ⟨22154883371878947162020849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59079688991677192432055597 22154883371878947162020849)
        ·
          refine ⟨16616162528909210371515637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22154883371878947162020849 16616162528909210371515637)
          ·
            refine ⟨1557765237085238472329591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16616162528909210371515637 1557765237085238472329591)
            ·
              refine ⟨2336647855627857708494387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1557765237085238472329591 2336647855627857708494387)
              ·
                refine ⟨3504971783441786562741581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2336647855627857708494387 3504971783441786562741581)
                ·
                  refine ⟨1314364418790669961028093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3504971783441786562741581 1314364418790669961028093)
                  ·
                    refine ⟨492886657046501235385535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1314364418790669961028093 492886657046501235385535)
                    ·
                      rfl

theorem cell22_1439840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 3, 3].length) (baseStart_1439840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439840 prefixEnd_1439840 := by exact prefixLift 1439840
  have htrace : WordTrace (prefixWord ++ tailWord_1439840) baseStart_1439840 baseEnd_1439840 := by
    simpa [prefixWord, tailWord_1439840, baseEnd_1439840] using wordTrace_append hprefix tailTrace_1439840
  have hstable : (prefixWord ++ tailWord_1439840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439840).length < 2 ^ (prefixWord ++ tailWord_1439840).sum := by decide
  have hdescent : baseEnd_1439840 < baseStart_1439840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439853 : List Nat := [1, 5, 1, 1, 2, 1, 3, 3, 5]
def baseStart_1439853 : Nat := 118140960795 + 1439853 * 2 ^ 59
def prefixEnd_1439853 : Nat := 4983230072969 + 3 ^ 40 * 1439853 * 2
def baseEnd_1439853 : Nat := 164297035737391178270165

theorem tailTrace_1439853 : CollatzResearch.WordTrace tailWord_1439853 prefixEnd_1439853 164297035737391178270165 := by
  unfold tailWord_1439853
  simp only [CollatzResearch.WordTrace]
  refine ⟨52515753252665963159828213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35010502168443975439885475 52515753252665963159828213)
  ·
    refine ⟨4923351867437434046233895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52515753252665963159828213 4923351867437434046233895)
    ·
      refine ⟨7385027801156151069350843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4923351867437434046233895 7385027801156151069350843)
      ·
        refine ⟨11077541701734226604026265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7385027801156151069350843 11077541701734226604026265)
        ·
          refine ⟨8308156276300669953019699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11077541701734226604026265 8308156276300669953019699)
          ·
            refine ⟨12462234414451004929529549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8308156276300669953019699 12462234414451004929529549)
            ·
              refine ⟨4673337905419126848573581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12462234414451004929529549 4673337905419126848573581)
              ·
                refine ⟨1752501714532172568215093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4673337905419126848573581 1752501714532172568215093)
                ·
                  refine ⟨164297035737391178270165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1752501714532172568215093 164297035737391178270165)
                  ·
                    rfl

theorem cell22_1439853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_1439853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439853 prefixEnd_1439853 := by exact prefixLift 1439853
  have htrace : WordTrace (prefixWord ++ tailWord_1439853) baseStart_1439853 baseEnd_1439853 := by
    simpa [prefixWord, tailWord_1439853, baseEnd_1439853] using wordTrace_append hprefix tailTrace_1439853
  have hstable : (prefixWord ++ tailWord_1439853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439853).length < 2 ^ (prefixWord ++ tailWord_1439853).sum := by decide
  have hdescent : baseEnd_1439853 < baseStart_1439853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439932 : List Nat := [2, 2, 2, 3, 3, 1, 2, 3, 4]
def baseStart_1439932 : Nat := 118140960795 + 1439932 * 2 ^ 59
def prefixEnd_1439932 : Nat := 4983230072969 + 3 ^ 40 * 1439932 * 2
def baseEnd_1439932 : Nat := 164306050175547887361751

theorem tailTrace_1439932 : CollatzResearch.WordTrace tailWord_1439932 prefixEnd_1439932 164306050175547887361751 := by
  unfold tailWord_1439932
  simp only [CollatzResearch.WordTrace]
  refine ⟨26259317309689879825977025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35012423079586506434636033 26259317309689879825977025)
  ·
    refine ⟨19694487982267409869482769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26259317309689879825977025 19694487982267409869482769)
    ·
      refine ⟨14770865986700557402112077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19694487982267409869482769 14770865986700557402112077)
      ·
        refine ⟨5539074745012709025792029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14770865986700557402112077 5539074745012709025792029)
        ·
          refine ⟨2077153029379765884672011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5539074745012709025792029 2077153029379765884672011)
          ·
            refine ⟨3115729544069648827008017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2077153029379765884672011 3115729544069648827008017)
            ·
              refine ⟨2336797158052236620256013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3115729544069648827008017 2336797158052236620256013)
              ·
                refine ⟨876298934269588732596005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2336797158052236620256013 876298934269588732596005)
                ·
                  refine ⟨164306050175547887361751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 876298934269588732596005 164306050175547887361751)
                  ·
                    rfl

theorem cell22_1439932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_1439932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439932 prefixEnd_1439932 := by exact prefixLift 1439932
  have htrace : WordTrace (prefixWord ++ tailWord_1439932) baseStart_1439932 baseEnd_1439932 := by
    simpa [prefixWord, tailWord_1439932, baseEnd_1439932] using wordTrace_append hprefix tailTrace_1439932
  have hstable : (prefixWord ++ tailWord_1439932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439932).length < 2 ^ (prefixWord ++ tailWord_1439932).sum := by decide
  have hdescent : baseEnd_1439932 < baseStart_1439932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439934 : List Nat := [4, 2, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_1439934 : Nat := 118140960795 + 1439934 * 2 ^ 59
def prefixEnd_1439934 : Nat := 4983230072969 + 3 ^ 40 * 1439934 * 2
def baseEnd_1439934 : Nat := 492918835167516323535247

theorem tailTrace_1439934 : CollatzResearch.WordTrace tailWord_1439934 prefixEnd_1439934 492918835167516323535247 := by
  unfold tailWord_1439934
  simp only [CollatzResearch.WordTrace]
  refine ⟨6564838445671564249190857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35012471710248342662351237 6564838445671564249190857)
  ·
    refine ⟨4923628834253673186893143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6564838445671564249190857 4923628834253673186893143)
    ·
      refine ⟨7385443251380509780339715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4923628834253673186893143 7385443251380509780339715)
      ·
        refine ⟨11078164877070764670509573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7385443251380509780339715 11078164877070764670509573)
        ·
          refine ⟨2077155914450768375720545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11078164877070764670509573 2077155914450768375720545)
          ·
            refine ⟨1557866935838076281790409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2077155914450768375720545 1557866935838076281790409)
            ·
              refine ⟨1168400201878557211342807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1557866935838076281790409 1168400201878557211342807)
              ·
                refine ⟨1752600302817835817014211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168400201878557211342807 1752600302817835817014211)
                ·
                  refine ⟨2628900454226753725521317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752600302817835817014211 2628900454226753725521317)
                  ·
                    refine ⟨492918835167516323535247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2628900454226753725521317 492918835167516323535247)
                    ·
                      rfl

theorem cell22_1439934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_1439934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439934 prefixEnd_1439934 := by exact prefixLift 1439934
  have htrace : WordTrace (prefixWord ++ tailWord_1439934) baseStart_1439934 baseEnd_1439934 := by
    simpa [prefixWord, tailWord_1439934, baseEnd_1439934] using wordTrace_append hprefix tailTrace_1439934
  have hstable : (prefixWord ++ tailWord_1439934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439934).length < 2 ^ (prefixWord ++ tailWord_1439934).sum := by decide
  have hdescent : baseEnd_1439934 < baseStart_1439934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439964 : List Nat := [2, 2, 5, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1439964 : Nat := 118140960795 + 1439964 * 2 ^ 59
def prefixEnd_1439964 : Nat := 4983230072969 + 3 ^ 40 * 1439964 * 2
def baseEnd_1439964 : Nat := 492929104780606245285155

theorem tailTrace_1439964 : CollatzResearch.WordTrace tailWord_1439964 prefixEnd_1439964 492929104780606245285155 := by
  unfold tailWord_1439964
  simp only [CollatzResearch.WordTrace]
  refine ⟨26259900877631914558559473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35013201170175886078079297 26259900877631914558559473)
  ·
    refine ⟨19694925658223935918919605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26259900877631914558559473 19694925658223935918919605)
    ·
      refine ⟨1846399280458493992398713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19694925658223935918919605 1846399280458493992398713)
      ·
        refine ⟨1384799460343870494299035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1846399280458493992398713 1384799460343870494299035)
        ·
          refine ⟨2077199190515805741448553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1384799460343870494299035 2077199190515805741448553)
          ·
            refine ⟨1557899392886854306086415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2077199190515805741448553 1557899392886854306086415)
            ·
              refine ⟨2336849089330281459129623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1557899392886854306086415 2336849089330281459129623)
              ·
                refine ⟨3505273633995422188694435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2336849089330281459129623 3505273633995422188694435)
                ·
                  refine ⟨5257910450993133283041653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3505273633995422188694435 5257910450993133283041653)
                  ·
                    refine ⟨492929104780606245285155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5257910450993133283041653 492929104780606245285155)
                    ·
                      rfl

theorem cell22_1439964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1439964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1439964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1439964 prefixEnd_1439964 := by exact prefixLift 1439964
  have htrace : WordTrace (prefixWord ++ tailWord_1439964) baseStart_1439964 baseEnd_1439964 := by
    simpa [prefixWord, tailWord_1439964, baseEnd_1439964] using wordTrace_append hprefix tailTrace_1439964
  have hstable : (prefixWord ++ tailWord_1439964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439964).length < 2 ^ (prefixWord ++ tailWord_1439964).sum := by decide
  have hdescent : baseEnd_1439964 < baseStart_1439964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440009 : List Nat := [1, 2, 1, 1, 3, 5, 3, 2, 1, 3]
def baseStart_1440009 : Nat := 118140960795 + 1440009 * 2 ^ 59
def prefixEnd_1440009 : Nat := 4983230072969 + 3 ^ 40 * 1440009 * 2
def baseEnd_1440009 : Nat := 492944509200241127910017

theorem tailTrace_1440009 : CollatzResearch.WordTrace tailWord_1440009 prefixEnd_1440009 492944509200241127910017 := by
  unfold tailWord_1440009
  simp only [CollatzResearch.WordTrace]
  refine ⟨52521443040100801802507081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35014295360067201201671387 52521443040100801802507081)
  ·
    refine ⟨39391082280075601351880311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52521443040100801802507081 39391082280075601351880311)
    ·
      refine ⟨59086623420113402027820467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39391082280075601351880311 59086623420113402027820467)
      ·
        refine ⟨88629935130170103041730701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59086623420113402027820467 88629935130170103041730701)
        ·
          refine ⟨33236225673813788640649013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88629935130170103041730701 33236225673813788640649013)
          ·
            refine ⟨3115896156920042685060845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33236225673813788640649013 3115896156920042685060845)
            ·
              refine ⟨1168461058845016006897817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3115896156920042685060845 1168461058845016006897817)
              ·
                refine ⟨876345794133762005173363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1168461058845016006897817 876345794133762005173363)
                ·
                  refine ⟨1314518691200643007760045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876345794133762005173363 1314518691200643007760045)
                  ·
                    refine ⟨492944509200241127910017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1314518691200643007760045 492944509200241127910017)
                    ·
                      rfl

theorem cell22_1440009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 1, 3].length) (baseStart_1440009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440009 prefixEnd_1440009 := by exact prefixLift 1440009
  have htrace : WordTrace (prefixWord ++ tailWord_1440009) baseStart_1440009 baseEnd_1440009 := by
    simpa [prefixWord, tailWord_1440009, baseEnd_1440009] using wordTrace_append hprefix tailTrace_1440009
  have hstable : (prefixWord ++ tailWord_1440009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440009).length < 2 ^ (prefixWord ++ tailWord_1440009).sum := by decide
  have hdescent : baseEnd_1440009 < baseStart_1440009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440033 : List Nat := [1, 2, 3, 2, 1, 1, 2, 4, 6]
def baseStart_1440033 : Nat := 118140960795 + 1440033 * 2 ^ 59
def prefixEnd_1440033 : Nat := 4983230072969 + 3 ^ 40 * 1440033 * 2
def baseEnd_1440033 : Nat := 164317574963571021769981

theorem tailTrace_1440033 : CollatzResearch.WordTrace tailWord_1440033 prefixEnd_1440033 164317574963571021769981 := by
  unfold tailWord_1440033
  simp only [CollatzResearch.WordTrace]
  refine ⟨52522318392013853901380753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35014878928009235934253835 52522318392013853901380753)
  ·
    refine ⟨39391738794010390426035565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52522318392013853901380753 39391738794010390426035565)
    ·
      refine ⟨14771902047753896409763337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39391738794010390426035565 14771902047753896409763337)
      ·
        refine ⟨11078926535815422307322503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14771902047753896409763337 11078926535815422307322503)
        ·
          refine ⟨16618389803723133460983755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11078926535815422307322503 16618389803723133460983755)
          ·
            refine ⟨24927584705584700191475633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16618389803723133460983755 24927584705584700191475633)
            ·
              refine ⟨18695688529188525143606725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24927584705584700191475633 18695688529188525143606725)
              ·
                refine ⟨3505441599222848464426261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18695688529188525143606725 3505441599222848464426261)
                ·
                  refine ⟨164317574963571021769981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3505441599222848464426261 164317574963571021769981)
                  ·
                    rfl

theorem cell22_1440033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 6].length) (baseStart_1440033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440033 prefixEnd_1440033 := by exact prefixLift 1440033
  have htrace : WordTrace (prefixWord ++ tailWord_1440033) baseStart_1440033 baseEnd_1440033 := by
    simpa [prefixWord, tailWord_1440033, baseEnd_1440033] using wordTrace_append hprefix tailTrace_1440033
  have hstable : (prefixWord ++ tailWord_1440033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440033).length < 2 ^ (prefixWord ++ tailWord_1440033).sum := by decide
  have hdescent : baseEnd_1440033 < baseStart_1440033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440067 : List Nat := [1, 1, 1, 3, 1, 3, 6, 2, 4]
def baseStart_1440067 : Nat := 118140960795 + 1440067 * 2 ^ 59
def prefixEnd_1440067 : Nat := 4983230072969 + 3 ^ 40 * 1440067 * 2
def baseEnd_1440067 : Nat := 164321454595182769986613

theorem tailTrace_1440067 : CollatzResearch.WordTrace tailWord_1440067 prefixEnd_1440067 164321454595182769986613 := by
  unfold tailWord_1440067
  simp only [CollatzResearch.WordTrace]
  refine ⟨52523558473890677708118455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35015705649260451805412303 52523558473890677708118455)
  ·
    refine ⟨78785337710836016562177683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52523558473890677708118455 78785337710836016562177683)
    ·
      refine ⟨118178006566254024843266525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78785337710836016562177683 118178006566254024843266525)
      ·
        refine ⟨44316752462345259316224947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118178006566254024843266525 44316752462345259316224947)
        ·
          refine ⟨66475128693517888974337421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44316752462345259316224947 66475128693517888974337421)
          ·
            refine ⟨24928173260069208365376533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66475128693517888974337421 24928173260069208365376533)
            ·
              refine ⟨1168508121565744142127025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24928173260069208365376533 1168508121565744142127025)
              ·
                refine ⟨876381091174308106595269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1168508121565744142127025 876381091174308106595269)
                ·
                  refine ⟨164321454595182769986613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 876381091174308106595269 164321454595182769986613)
                  ·
                    rfl

theorem cell22_1440067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 4].length) (baseStart_1440067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440067 prefixEnd_1440067 := by exact prefixLift 1440067
  have htrace : WordTrace (prefixWord ++ tailWord_1440067) baseStart_1440067 baseEnd_1440067 := by
    simpa [prefixWord, tailWord_1440067, baseEnd_1440067] using wordTrace_append hprefix tailTrace_1440067
  have hstable : (prefixWord ++ tailWord_1440067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440067).length < 2 ^ (prefixWord ++ tailWord_1440067).sum := by decide
  have hdescent : baseEnd_1440067 < baseStart_1440067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440078 : List Nat := [4, 1, 1, 1, 1, 1, 2, 11]
def baseStart_1440078 : Nat := 118140960795 + 1440078 * 2 ^ 59
def prefixEnd_1440078 : Nat := 4983230072969 + 3 ^ 40 * 1440078 * 2
def baseEnd_1440078 : Nat := 54774236590038660881645

theorem tailTrace_1440078 : CollatzResearch.WordTrace tailWord_1440078 prefixEnd_1440078 54774236590038660881645 := by
  unfold tailWord_1440078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6565494959606353323346111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35015973117900551057845925 6565494959606353323346111)
  ·
    refine ⟨9848242439409529985019167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6565494959606353323346111 9848242439409529985019167)
    ·
      refine ⟨14772363659114294977528751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9848242439409529985019167 14772363659114294977528751)
      ·
        refine ⟨22158545488671442466293127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14772363659114294977528751 22158545488671442466293127)
        ·
          refine ⟨33237818233007163699439691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22158545488671442466293127 33237818233007163699439691)
          ·
            refine ⟨49856727349510745549159537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33237818233007163699439691 49856727349510745549159537)
            ·
              refine ⟨37392545512133059161869653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49856727349510745549159537 37392545512133059161869653)
              ·
                refine ⟨54774236590038660881645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 37392545512133059161869653 54774236590038660881645)
                ·
                  rfl

theorem cell22_1440078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_1440078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440078 prefixEnd_1440078 := by exact prefixLift 1440078
  have htrace : WordTrace (prefixWord ++ tailWord_1440078) baseStart_1440078 baseEnd_1440078 := by
    simpa [prefixWord, tailWord_1440078, baseEnd_1440078] using wordTrace_append hprefix tailTrace_1440078
  have hstable : (prefixWord ++ tailWord_1440078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440078).length < 2 ^ (prefixWord ++ tailWord_1440078).sum := by decide
  have hdescent : baseEnd_1440078 < baseStart_1440078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440082 : List Nat := [3, 2, 2, 1, 1, 1, 4, 3, 2, 3]
def baseStart_1440082 : Nat := 118140960795 + 1440082 * 2 ^ 59
def prefixEnd_1440082 : Nat := 4983230072969 + 3 ^ 40 * 1440082 * 2
def baseEnd_1440082 : Nat := 492969498592093270834793

theorem tailTrace_1440082 : CollatzResearch.WordTrace tailWord_1440082 prefixEnd_1440082 492969498592093270834793 := by
  unfold tailWord_1440082
  simp only [CollatzResearch.WordTrace]
  refine ⟨13131026392209083817478625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35016070379224223513276333 13131026392209083817478625)
  ·
    refine ⟨9848269794156812863108969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13131026392209083817478625 9848269794156812863108969)
    ·
      refine ⟨7386202345617609647331727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9848269794156812863108969 7386202345617609647331727)
      ·
        refine ⟨11079303518426414470997591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7386202345617609647331727 11079303518426414470997591)
        ·
          refine ⟨16618955277639621706496387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11079303518426414470997591 16618955277639621706496387)
          ·
            refine ⟨24928432916459432559744581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16618955277639621706496387 24928432916459432559744581)
            ·
              refine ⟨4674081171836143604952109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24928432916459432559744581 4674081171836143604952109)
              ·
                refine ⟨1752780439438553851857041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4674081171836143604952109 1752780439438553851857041)
                ·
                  refine ⟨1314585329578915388892781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1752780439438553851857041 1314585329578915388892781)
                  ·
                    refine ⟨492969498592093270834793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1314585329578915388892781 492969498592093270834793)
                    ·
                      rfl

theorem cell22_1440082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_1440082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440082 prefixEnd_1440082 := by exact prefixLift 1440082
  have htrace : WordTrace (prefixWord ++ tailWord_1440082) baseStart_1440082 baseEnd_1440082 := by
    simpa [prefixWord, tailWord_1440082, baseEnd_1440082] using wordTrace_append hprefix tailTrace_1440082
  have hstable : (prefixWord ++ tailWord_1440082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440082).length < 2 ^ (prefixWord ++ tailWord_1440082).sum := by decide
  have hdescent : baseEnd_1440082 < baseStart_1440082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440232 : List Nat := [2, 1, 4, 1, 1, 3, 2, 2, 2, 4]
def baseStart_1440232 : Nat := 118140960795 + 1440232 * 2 ^ 59
def prefixEnd_1440232 : Nat := 4983230072969 + 3 ^ 40 * 1440232 * 2
def baseEnd_1440232 : Nat := 493020846657542879584333

theorem tailTrace_1440232 : CollatzResearch.WordTrace tailWord_1440232 prefixEnd_1440232 493020846657542879584333 := by
  unfold tailWord_1440232
  simp only [CollatzResearch.WordTrace]
  refine ⟨26264788259146455443937475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35019717678861940591916633 26264788259146455443937475)
  ·
    refine ⟨39397182388719683165906213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26264788259146455443937475 39397182388719683165906213)
    ·
      refine ⟨7386971697884940593607415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39397182388719683165906213 7386971697884940593607415)
      ·
        refine ⟨11080457546827410890411123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7386971697884940593607415 11080457546827410890411123)
        ·
          refine ⟨16620686320241116335616685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11080457546827410890411123 16620686320241116335616685)
          ·
            refine ⟨6232757370090418625856257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16620686320241116335616685 6232757370090418625856257)
            ·
              refine ⟨4674568027567813969392193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6232757370090418625856257 4674568027567813969392193)
              ·
                refine ⟨3505926020675860477044145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4674568027567813969392193 3505926020675860477044145)
                ·
                  refine ⟨2629444515506895357783109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3505926020675860477044145 2629444515506895357783109)
                  ·
                    refine ⟨493020846657542879584333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2629444515506895357783109 493020846657542879584333)
                    ·
                      rfl

theorem cell22_1440232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_1440232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440232 prefixEnd_1440232 := by exact prefixLift 1440232
  have htrace : WordTrace (prefixWord ++ tailWord_1440232) baseStart_1440232 baseEnd_1440232 := by
    simpa [prefixWord, tailWord_1440232, baseEnd_1440232] using wordTrace_append hprefix tailTrace_1440232
  have hstable : (prefixWord ++ tailWord_1440232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440232).length < 2 ^ (prefixWord ++ tailWord_1440232).sum := by decide
  have hdescent : baseEnd_1440232 < baseStart_1440232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440234 : List Nat := [3, 1, 3, 1, 3, 1, 1, 4, 2, 3]
def baseStart_1440234 : Nat := 118140960795 + 1440234 * 2 ^ 59
def prefixEnd_1440234 : Nat := 4983230072969 + 3 ^ 40 * 1440234 * 2
def baseEnd_1440234 : Nat := 493021531298415541034327

theorem tailTrace_1440234 : CollatzResearch.WordTrace tailWord_1440234 prefixEnd_1440234 493021531298415541034327 := by
  unfold tailWord_1440234
  simp only [CollatzResearch.WordTrace]
  refine ⟨13132412366071416307361939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35019766309523776819631837 13132412366071416307361939)
  ·
    refine ⟨19698618549107124461042909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13132412366071416307361939 19698618549107124461042909)
    ·
      refine ⟨7386981955915171672891091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19698618549107124461042909 7386981955915171672891091)
      ·
        refine ⟨11080472933872757509336637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7386981955915171672891091 11080472933872757509336637)
        ·
          refine ⟨4155177350202284066001239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11080472933872757509336637 4155177350202284066001239)
          ·
            refine ⟨6232766025303426099001859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4155177350202284066001239 6232766025303426099001859)
            ·
              refine ⟨9349149037955139148502789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6232766025303426099001859 9349149037955139148502789)
              ·
                refine ⟨1752965444616588590344273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9349149037955139148502789 1752965444616588590344273)
                ·
                  refine ⟨1314724083462441442758205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1752965444616588590344273 1314724083462441442758205)
                  ·
                    refine ⟨493021531298415541034327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1314724083462441442758205 493021531298415541034327)
                    ·
                      rfl

theorem cell22_1440234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_1440234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440234 prefixEnd_1440234 := by exact prefixLift 1440234
  have htrace : WordTrace (prefixWord ++ tailWord_1440234) baseStart_1440234 baseEnd_1440234 := by
    simpa [prefixWord, tailWord_1440234, baseEnd_1440234] using wordTrace_append hprefix tailTrace_1440234
  have hstable : (prefixWord ++ tailWord_1440234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440234).length < 2 ^ (prefixWord ++ tailWord_1440234).sum := by decide
  have hdescent : baseEnd_1440234 < baseStart_1440234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440275 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 7]
def baseStart_1440275 : Nat := 118140960795 + 1440275 * 2 ^ 59
def prefixEnd_1440275 : Nat := 4983230072969 + 3 ^ 40 * 1440275 * 2
def baseEnd_1440275 : Nat := 164345188812101700253067

theorem tailTrace_1440275 : CollatzResearch.WordTrace tailWord_1440275 prefixEnd_1440275 164345188812101700253067 := by
  unfold tailWord_1440275
  simp only [CollatzResearch.WordTrace]
  refine ⟨52531144857137129231690279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35020763238091419487793519 52531144857137129231690279)
  ·
    refine ⟨78796717285705693847535419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52531144857137129231690279 78796717285705693847535419)
    ·
      refine ⟨118195075928558540771303129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78796717285705693847535419 118195075928558540771303129)
      ·
        refine ⟨88646306946418905578477347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118195075928558540771303129 88646306946418905578477347)
        ·
          refine ⟨132969460419628358367716021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88646306946418905578477347 132969460419628358367716021)
          ·
            refine ⟨12465886914340158596973377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132969460419628358367716021 12465886914340158596973377)
            ·
              refine ⟨9349415185755118947730033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12465886914340158596973377 9349415185755118947730033)
              ·
                refine ⟨7012061389316339210797525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9349415185755118947730033 7012061389316339210797525)
                ·
                  refine ⟨164345188812101700253067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7012061389316339210797525 164345188812101700253067)
                  ·
                    rfl

theorem cell22_1440275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 7].length) (baseStart_1440275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440275 prefixEnd_1440275 := by exact prefixLift 1440275
  have htrace : WordTrace (prefixWord ++ tailWord_1440275) baseStart_1440275 baseEnd_1440275 := by
    simpa [prefixWord, tailWord_1440275, baseEnd_1440275] using wordTrace_append hprefix tailTrace_1440275
  have hstable : (prefixWord ++ tailWord_1440275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440275).length < 2 ^ (prefixWord ++ tailWord_1440275).sum := by decide
  have hdescent : baseEnd_1440275 < baseStart_1440275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440296 : List Nat := [2, 1, 5, 2, 1, 2, 2, 1, 3, 3]
def baseStart_1440296 : Nat := 118140960795 + 1440296 * 2 ^ 59
def prefixEnd_1440296 : Nat := 4983230072969 + 3 ^ 40 * 1440296 * 2
def baseEnd_1440296 : Nat := 493042755165468045984137

theorem tailTrace_1440296 : CollatzResearch.WordTrace tailWord_1440296 prefixEnd_1440296 493042755165468045984137 := by
  unfold tailWord_1440296
  simp only [CollatzResearch.WordTrace]
  refine ⟨26265955395030524909102371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35021273860040699878803161 26265955395030524909102371)
  ·
    refine ⟨39398933092545787363653557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26265955395030524909102371 39398933092545787363653557)
    ·
      refine ⟨3693649977426167565342521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39398933092545787363653557 3693649977426167565342521)
      ·
        refine ⟨2770237483069625674006891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3693649977426167565342521 2770237483069625674006891)
        ·
          refine ⟨4155356224604438511010337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2770237483069625674006891 4155356224604438511010337)
          ·
            refine ⟨3116517168453328883257753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4155356224604438511010337 3116517168453328883257753)
            ·
              refine ⟨2337387876339996662443315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3116517168453328883257753 2337387876339996662443315)
              ·
                refine ⟨3506081814509994993664973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2337387876339996662443315 3506081814509994993664973)
                ·
                  refine ⟨1314780680441248122624365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3506081814509994993664973 1314780680441248122624365)
                  ·
                    refine ⟨493042755165468045984137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1314780680441248122624365 493042755165468045984137)
                    ·
                      rfl

theorem cell22_1440296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_1440296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440296 prefixEnd_1440296 := by exact prefixLift 1440296
  have htrace : WordTrace (prefixWord ++ tailWord_1440296) baseStart_1440296 baseEnd_1440296 := by
    simpa [prefixWord, tailWord_1440296, baseEnd_1440296] using wordTrace_append hprefix tailTrace_1440296
  have hstable : (prefixWord ++ tailWord_1440296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440296).length < 2 ^ (prefixWord ++ tailWord_1440296).sum := by decide
  have hdescent : baseEnd_1440296 < baseStart_1440296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440309 : List Nat := [1, 3, 3, 1, 1, 2, 5, 1, 5]
def baseStart_1440309 : Nat := 118140960795 + 1440309 * 2 ^ 59
def prefixEnd_1440309 : Nat := 4983230072969 + 3 ^ 40 * 1440309 * 2
def baseEnd_1440309 : Nat := 164349068443713448469699

theorem tailTrace_1440309 : CollatzResearch.WordTrace tailWord_1440309 prefixEnd_1440309 164349068443713448469699 := by
  unfold tailWord_1440309
  simp only [CollatzResearch.WordTrace]
  refine ⟨52532384939013953038427981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35021589959342635358951987 52532384939013953038427981)
  ·
    refine ⟨19699644352130232389410493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52532384939013953038427981 19699644352130232389410493)
    ·
      refine ⟨7387366632048837146028935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19699644352130232389410493 7387366632048837146028935)
      ·
        refine ⟨11081049948073255719043403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7387366632048837146028935 11081049948073255719043403)
        ·
          refine ⟨16621574922109883578565105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11081049948073255719043403 16621574922109883578565105)
          ·
            refine ⟨12466181191582412683923829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16621574922109883578565105 12466181191582412683923829)
            ·
              refine ⟨1168704486710851189117859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12466181191582412683923829 1168704486710851189117859)
              ·
                refine ⟨1753056730066276783676789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168704486710851189117859 1753056730066276783676789)
                ·
                  refine ⟨164349068443713448469699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1753056730066276783676789 164349068443713448469699)
                  ·
                    rfl

theorem cell22_1440309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_1440309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440309 prefixEnd_1440309 := by exact prefixLift 1440309
  have htrace : WordTrace (prefixWord ++ tailWord_1440309) baseStart_1440309 baseEnd_1440309 := by
    simpa [prefixWord, tailWord_1440309, baseEnd_1440309] using wordTrace_append hprefix tailTrace_1440309
  have hstable : (prefixWord ++ tailWord_1440309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440309).length < 2 ^ (prefixWord ++ tailWord_1440309).sum := by decide
  have hdescent : baseEnd_1440309 < baseStart_1440309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440373 : List Nat := [1, 3, 4, 2, 2, 2, 1, 2, 1, 4]
def baseStart_1440373 : Nat := 118140960795 + 1440373 * 2 ^ 59
def prefixEnd_1440373 : Nat := 4983230072969 + 3 ^ 40 * 1440373 * 2
def baseEnd_1440373 : Nat := 493069113839065511808901

theorem tailTrace_1440373 : CollatzResearch.WordTrace tailWord_1440373 prefixEnd_1440373 493069113839065511808901 := by
  unfold tailWord_1440373
  simp only [CollatzResearch.WordTrace]
  refine ⟨52534719210782091968757773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35023146140521394645838515 52534719210782091968757773)
  ·
    refine ⟨19700519704043284488284165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52534719210782091968757773 19700519704043284488284165)
    ·
      refine ⟨3693847444508115841553281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19700519704043284488284165 3693847444508115841553281)
      ·
        refine ⟨2770385583381086881164961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3693847444508115841553281 2770385583381086881164961)
        ·
          refine ⟨2077789187535815160873721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2770385583381086881164961 2077789187535815160873721)
          ·
            refine ⟨1558341890651861370655291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2077789187535815160873721 1558341890651861370655291)
            ·
              refine ⟨2337512835977792055982937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1558341890651861370655291 2337512835977792055982937)
              ·
                refine ⟨1753134626983344041987203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2337512835977792055982937 1753134626983344041987203)
                ·
                  refine ⟨2629701940475016062980805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753134626983344041987203 2629701940475016062980805)
                  ·
                    refine ⟨493069113839065511808901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2629701940475016062980805 493069113839065511808901)
                    ·
                      rfl

theorem cell22_1440373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_1440373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440373 prefixEnd_1440373 := by exact prefixLift 1440373
  have htrace : WordTrace (prefixWord ++ tailWord_1440373) baseStart_1440373 baseEnd_1440373 := by
    simpa [prefixWord, tailWord_1440373, baseEnd_1440373] using wordTrace_append hprefix tailTrace_1440373
  have hstable : (prefixWord ++ tailWord_1440373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440373).length < 2 ^ (prefixWord ++ tailWord_1440373).sum := by decide
  have hdescent : baseEnd_1440373 < baseStart_1440373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440384 : List Nat := [2, 1, 1, 2, 1, 6, 2, 1, 2, 4]
def baseStart_1440384 : Nat := 118140960795 + 1440384 * 2 ^ 59
def prefixEnd_1440384 : Nat := 4983230072969 + 3 ^ 40 * 1440384 * 2
def baseEnd_1440384 : Nat := 493072879363865149783867

theorem tailTrace_1440384 : CollatzResearch.WordTrace tailWord_1440384 prefixEnd_1440384 493072879363865149783867 := by
  unfold tailWord_1440384
  simp only [CollatzResearch.WordTrace]
  refine ⟨26267560206871120423704103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35023413609161493898272137 26267560206871120423704103)
  ·
    refine ⟨39401340310306680635556155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26267560206871120423704103 39401340310306680635556155)
    ·
      refine ⟨59102010465460020953334233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39401340310306680635556155 59102010465460020953334233)
      ·
        refine ⟨44326507849095015715000675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59102010465460020953334233 44326507849095015715000675)
        ·
          refine ⟨66489761773642523572501013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44326507849095015715000675 66489761773642523572501013)
          ·
            refine ⟨3116707583139493292460985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66489761773642523572501013 3116707583139493292460985)
            ·
              refine ⟨2337530687354619969345739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3116707583139493292460985 2337530687354619969345739)
              ·
                refine ⟨3506296031031929954018609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2337530687354619969345739 3506296031031929954018609)
                ·
                  refine ⟨2629722023273947465513957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3506296031031929954018609 2629722023273947465513957)
                  ·
                    refine ⟨493072879363865149783867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2629722023273947465513957 493072879363865149783867)
                    ·
                      rfl

theorem cell22_1440384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 2, 4].length) (baseStart_1440384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440384 prefixEnd_1440384 := by exact prefixLift 1440384
  have htrace : WordTrace (prefixWord ++ tailWord_1440384) baseStart_1440384 baseEnd_1440384 := by
    simpa [prefixWord, tailWord_1440384, baseEnd_1440384] using wordTrace_append hprefix tailTrace_1440384
  have hstable : (prefixWord ++ tailWord_1440384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440384).length < 2 ^ (prefixWord ++ tailWord_1440384).sum := by decide
  have hdescent : baseEnd_1440384 < baseStart_1440384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440416 : List Nat := [2, 1, 1, 4, 5, 1, 1, 7]
def baseStart_1440416 : Nat := 118140960795 + 1440416 * 2 ^ 59
def prefixEnd_1440416 : Nat := 4983230072969 + 3 ^ 40 * 1440416 * 2
def baseEnd_1440416 : Nat := 54787092624203081442641

theorem tailTrace_1440416 : CollatzResearch.WordTrace tailWord_1440416 prefixEnd_1440416 54787092624203081442641 := by
  unfold tailWord_1440416
  simp only [CollatzResearch.WordTrace]
  refine ⟨26268143774813155156286551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35024191699750873541715401 26268143774813155156286551)
  ·
    refine ⟨39402215662219732734429827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26268143774813155156286551 39402215662219732734429827)
    ·
      refine ⟨59103323493329599101644741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39402215662219732734429827 59103323493329599101644741)
      ·
        refine ⟨11081873154999299831558389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59103323493329599101644741 11081873154999299831558389)
        ·
          refine ⟨1038925608281184359208599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11081873154999299831558389 1038925608281184359208599)
          ·
            refine ⟨1558388412421776538812899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038925608281184359208599 1558388412421776538812899)
            ·
              refine ⟨2337582618632664808219349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1558388412421776538812899 2337582618632664808219349)
              ·
                refine ⟨54787092624203081442641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2337582618632664808219349 54787092624203081442641)
                ·
                  rfl

theorem cell22_1440416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 7].length) (baseStart_1440416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440416 prefixEnd_1440416 := by exact prefixLift 1440416
  have htrace : WordTrace (prefixWord ++ tailWord_1440416) baseStart_1440416 baseEnd_1440416 := by
    simpa [prefixWord, tailWord_1440416, baseEnd_1440416] using wordTrace_append hprefix tailTrace_1440416
  have hstable : (prefixWord ++ tailWord_1440416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440416).length < 2 ^ (prefixWord ++ tailWord_1440416).sum := by decide
  have hdescent : baseEnd_1440416 < baseStart_1440416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440442 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 1, 7]
def baseStart_1440442 : Nat := 118140960795 + 1440442 * 2 ^ 59
def prefixEnd_1440442 : Nat := 4983230072969 + 3 ^ 40 * 1440442 * 2
def baseEnd_1440442 : Nat := 493092733949172331833689

theorem tailTrace_1440442 : CollatzResearch.WordTrace tailWord_1440442 prefixEnd_1440442 493092733949172331833689 := by
  unfold tailWord_1440442
  simp only [CollatzResearch.WordTrace]
  refine ⟨13134308961883029188254895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35024823898354744502013053 13134308961883029188254895)
  ·
    refine ⟨19701463442824543782382343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13134308961883029188254895 19701463442824543782382343)
    ·
      refine ⟨29552195164236815673573515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19701463442824543782382343 29552195164236815673573515)
      ·
        refine ⟨44328292746355223510360273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29552195164236815673573515 44328292746355223510360273)
        ·
          refine ⟨33246219559766417632770205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44328292746355223510360273 33246219559766417632770205)
          ·
            refine ⟨12467332334912406612288827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33246219559766417632770205 12467332334912406612288827)
            ·
              refine ⟨18700998502368609918433241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12467332334912406612288827 18700998502368609918433241)
              ·
                refine ⟨14025748876776457438824931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18700998502368609918433241 14025748876776457438824931)
                ·
                  refine ⟨21038623315164686158237397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14025748876776457438824931 21038623315164686158237397)
                  ·
                    refine ⟨493092733949172331833689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21038623315164686158237397 493092733949172331833689)
                    ·
                      rfl

theorem cell22_1440442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_1440442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440442 prefixEnd_1440442 := by exact prefixLift 1440442
  have htrace : WordTrace (prefixWord ++ tailWord_1440442) baseStart_1440442 baseEnd_1440442 := by
    simpa [prefixWord, tailWord_1440442, baseEnd_1440442] using wordTrace_append hprefix tailTrace_1440442
  have hstable : (prefixWord ++ tailWord_1440442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440442).length < 2 ^ (prefixWord ++ tailWord_1440442).sum := by decide
  have hdescent : baseEnd_1440442 < baseStart_1440442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440448 : List Nat := [2, 1, 1, 2, 4, 3, 2, 3, 1, 3]
def baseStart_1440448 : Nat := 118140960795 + 1440448 * 2 ^ 59
def prefixEnd_1440448 : Nat := 4983230072969 + 3 ^ 40 * 1440448 * 2
def baseEnd_1440448 : Nat := 493094787871790316183671

theorem tailTrace_1440448 : CollatzResearch.WordTrace tailWord_1440448 prefixEnd_1440448 493094787871790316183671 := by
  unfold tailWord_1440448
  simp only [CollatzResearch.WordTrace]
  refine ⟨26268727342755189888868999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35024969790340253185158665 26268727342755189888868999)
  ·
    refine ⟨39403091014132784833303499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26268727342755189888868999 39403091014132784833303499)
    ·
      refine ⟨59104636521199177249955249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39403091014132784833303499 59104636521199177249955249)
      ·
        refine ⟨44328477390899382937466437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59104636521199177249955249 44328477390899382937466437)
        ·
          refine ⟨8311589510793634300774957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44328477390899382937466437 8311589510793634300774957)
          ·
            refine ⟨3116846066547612862790609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8311589510793634300774957 3116846066547612862790609)
            ·
              refine ⟨2337634549910709647092957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3116846066547612862790609 2337634549910709647092957)
              ·
                refine ⟨876612956216516117659859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2337634549910709647092957 876612956216516117659859)
                ·
                  refine ⟨1314919434324774176489789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876612956216516117659859 1314919434324774176489789)
                  ·
                    refine ⟨493094787871790316183671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1314919434324774176489789 493094787871790316183671)
                    ·
                      rfl

theorem cell22_1440448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 1, 3].length) (baseStart_1440448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440448 prefixEnd_1440448 := by exact prefixLift 1440448
  have htrace : WordTrace (prefixWord ++ tailWord_1440448) baseStart_1440448 baseEnd_1440448 := by
    simpa [prefixWord, tailWord_1440448, baseEnd_1440448] using wordTrace_append hprefix tailTrace_1440448
  have hstable : (prefixWord ++ tailWord_1440448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440448).length < 2 ^ (prefixWord ++ tailWord_1440448).sum := by decide
  have hdescent : baseEnd_1440448 < baseStart_1440448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440454 : List Nat := [6, 1, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_1440454 : Nat := 118140960795 + 1440454 * 2 ^ 59
def prefixEnd_1440454 : Nat := 4983230072969 + 3 ^ 40 * 1440454 * 2
def baseEnd_1440454 : Nat := 493096841794408300533653

theorem tailTrace_1440454 : CollatzResearch.WordTrace tailWord_1440454 prefixEnd_1440454 493096841794408300533653 := by
  unfold tailWord_1440454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1641802297609020087576763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35025115682325761868304277 1641802297609020087576763)
  ·
    refine ⟨2462703446413530131365145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1641802297609020087576763 2462703446413530131365145)
    ·
      refine ⟨1847027584810147598523859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2462703446413530131365145 1847027584810147598523859)
      ·
        refine ⟨2770541377215221397785789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1847027584810147598523859 2770541377215221397785789)
        ·
          refine ⟨1038953016455708024169671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2770541377215221397785789 1038953016455708024169671)
          ·
            refine ⟨1558429524683562036254507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038953016455708024169671 1558429524683562036254507)
            ·
              refine ⟨2337644287025343054381761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1558429524683562036254507 2337644287025343054381761)
              ·
                refine ⟨1753233215269007290786321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2337644287025343054381761 1753233215269007290786321)
                ·
                  refine ⟨1314924911451755468089741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1753233215269007290786321 1314924911451755468089741)
                  ·
                    refine ⟨493096841794408300533653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1314924911451755468089741 493096841794408300533653)
                    ·
                      rfl

theorem cell22_1440454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_1440454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440454 prefixEnd_1440454 := by exact prefixLift 1440454
  have htrace : WordTrace (prefixWord ++ tailWord_1440454) baseStart_1440454 baseEnd_1440454 := by
    simpa [prefixWord, tailWord_1440454, baseEnd_1440454] using wordTrace_append hprefix tailTrace_1440454
  have hstable : (prefixWord ++ tailWord_1440454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440454).length < 2 ^ (prefixWord ++ tailWord_1440454).sum := by decide
  have hdescent : baseEnd_1440454 < baseStart_1440454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440476 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 2, 5]
def baseStart_1440476 : Nat := 118140960795 + 1440476 * 2 ^ 59
def prefixEnd_1440476 : Nat := 4983230072969 + 3 ^ 40 * 1440476 * 2
def baseEnd_1440476 : Nat := 493104372844007576483585

theorem tailTrace_1440476 : CollatzResearch.WordTrace tailWord_1440476 prefixEnd_1440476 493104372844007576483585 := by
  unfold tailWord_1440476
  simp only [CollatzResearch.WordTrace]
  refine ⟨26269237964704470279878641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35025650619605960373171521 26269237964704470279878641)
  ·
    refine ⟨19701928473528352709908981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26269237964704470279878641 19701928473528352709908981)
    ·
      refine ⟨1847055794393283066553967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19701928473528352709908981 1847055794393283066553967)
      ·
        refine ⟨2770583691589924599830951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1847055794393283066553967 2770583691589924599830951)
        ·
          refine ⟨4155875537384886899746427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2770583691589924599830951 4155875537384886899746427)
          ·
            refine ⟨6233813306077330349619641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4155875537384886899746427 6233813306077330349619641)
            ·
              refine ⟨4675359979557997762214731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6233813306077330349619641 4675359979557997762214731)
              ·
                refine ⟨7013039969336996643322097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4675359979557997762214731 7013039969336996643322097)
                ·
                  refine ⟨5259779977002747482491573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7013039969336996643322097 5259779977002747482491573)
                  ·
                    refine ⟨493104372844007576483585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5259779977002747482491573 493104372844007576483585)
                    ·
                      rfl

theorem cell22_1440476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_1440476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440476 prefixEnd_1440476 := by exact prefixLift 1440476
  have htrace : WordTrace (prefixWord ++ tailWord_1440476) baseStart_1440476 baseEnd_1440476 := by
    simpa [prefixWord, tailWord_1440476, baseEnd_1440476] using wordTrace_append hprefix tailTrace_1440476
  have hstable : (prefixWord ++ tailWord_1440476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440476).length < 2 ^ (prefixWord ++ tailWord_1440476).sum := by decide
  have hdescent : baseEnd_1440476 < baseStart_1440476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440504 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 6, 3]
def baseStart_1440504 : Nat := 118140960795 + 1440504 * 2 ^ 59
def prefixEnd_1440504 : Nat := 4983230072969 + 3 ^ 40 * 1440504 * 2
def baseEnd_1440504 : Nat := 493113957816224836783499

theorem tailTrace_1440504 : CollatzResearch.WordTrace tailWord_1440504 prefixEnd_1440504 493113957816224836783499 := by
  unfold tailWord_1440504
  simp only [CollatzResearch.WordTrace]
  refine ⟨26269748586653750670888283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35026331448871667561184377 26269748586653750670888283)
  ·
    refine ⟨39404622879980626006332425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26269748586653750670888283 39404622879980626006332425)
    ·
      refine ⟨29553467159985469504749319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39404622879980626006332425 29553467159985469504749319)
      ·
        refine ⟨44330200739978204257123979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29553467159985469504749319 44330200739978204257123979)
        ·
          refine ⟨66495301109967306385685969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44330200739978204257123979 66495301109967306385685969)
          ·
            refine ⟨49871475832475479789264477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66495301109967306385685969 49871475832475479789264477)
            ·
              refine ⟨18701803437178304920974179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49871475832475479789264477 18701803437178304920974179)
              ·
                refine ⟨28052705155767457381461269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18701803437178304920974179 28052705155767457381461269)
                ·
                  refine ⟨1314970554176599564755997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28052705155767457381461269 1314970554176599564755997)
                  ·
                    refine ⟨493113957816224836783499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1314970554176599564755997 493113957816224836783499)
                    ·
                      rfl

theorem cell22_1440504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_1440504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440504 prefixEnd_1440504 := by exact prefixLift 1440504
  have htrace : WordTrace (prefixWord ++ tailWord_1440504) baseStart_1440504 baseEnd_1440504 := by
    simpa [prefixWord, tailWord_1440504, baseEnd_1440504] using wordTrace_append hprefix tailTrace_1440504
  have hstable : (prefixWord ++ tailWord_1440504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440504).length < 2 ^ (prefixWord ++ tailWord_1440504).sum := by decide
  have hdescent : baseEnd_1440504 < baseStart_1440504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440506 : List Nat := [3, 1, 1, 1, 1, 3, 5, 3, 4]
def baseStart_1440506 : Nat := 118140960795 + 1440506 * 2 ^ 59
def prefixEnd_1440506 : Nat := 4983230072969 + 3 ^ 40 * 1440506 * 2
def baseEnd_1440506 : Nat := 164371547485699166077831

theorem tailTrace_1440506 : CollatzResearch.WordTrace tailWord_1440506 prefixEnd_1440506 164371547485699166077831 := by
  unfold tailWord_1440506
  simp only [CollatzResearch.WordTrace]
  refine ⟨13134892529825063920837343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35026380079533503788899581 13134892529825063920837343)
  ·
    refine ⟨19702338794737595881256015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13134892529825063920837343 19702338794737595881256015)
    ·
      refine ⟨29553508192106393821884023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19702338794737595881256015 29553508192106393821884023)
      ·
        refine ⟨44330262288159590732826035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29553508192106393821884023 44330262288159590732826035)
        ·
          refine ⟨66495393432239386099239053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44330262288159590732826035 66495393432239386099239053)
          ·
            refine ⟨24935772537089769787214645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66495393432239386099239053 24935772537089769787214645)
            ·
              refine ⟨2337728675352165917551373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24935772537089769787214645 2337728675352165917551373)
              ·
                refine ⟨876648253257062219081765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2337728675352165917551373 876648253257062219081765)
                ·
                  refine ⟨164371547485699166077831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 876648253257062219081765 164371547485699166077831)
                  ·
                    rfl

theorem cell22_1440506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_1440506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440506 prefixEnd_1440506 := by exact prefixLift 1440506
  have htrace : WordTrace (prefixWord ++ tailWord_1440506) baseStart_1440506 baseEnd_1440506 := by
    simpa [prefixWord, tailWord_1440506, baseEnd_1440506] using wordTrace_append hprefix tailTrace_1440506
  have hstable : (prefixWord ++ tailWord_1440506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440506).length < 2 ^ (prefixWord ++ tailWord_1440506).sum := by decide
  have hdescent : baseEnd_1440506 < baseStart_1440506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440630 : List Nat := [5, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_1440630 : Nat := 118140960795 + 1440630 * 2 ^ 59
def prefixEnd_1440630 : Nat := 4983230072969 + 3 ^ 40 * 1440630 * 2
def baseEnd_1440630 : Nat := 164385696730400836044371

theorem tailTrace_1440630 : CollatzResearch.WordTrace tailWord_1440630 prefixEnd_1440630 164385696730400836044371 := by
  unfold tailWord_1440630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3284005798178189053803959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35029395180567349907242229 3284005798178189053803959)
  ·
    refine ⟨4926008697267283580705939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3284005798178189053803959 4926008697267283580705939)
    ·
      refine ⟨7389013045900925371058909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4926008697267283580705939 7389013045900925371058909)
      ·
        refine ⟨2770879892212847014147091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7389013045900925371058909 2770879892212847014147091)
        ·
          refine ⟨4156319838319270521220637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2770879892212847014147091 4156319838319270521220637)
          ·
            refine ⟨1558619939369726445457739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4156319838319270521220637 1558619939369726445457739)
            ·
              refine ⟨2337929909054589668186609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1558619939369726445457739 2337929909054589668186609)
              ·
                refine ⟨1753447431790942251139957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2337929909054589668186609 1753447431790942251139957)
                ·
                  refine ⟨164385696730400836044371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1753447431790942251139957 164385696730400836044371)
                  ·
                    rfl

theorem cell22_1440630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_1440630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440630 prefixEnd_1440630 := by exact prefixLift 1440630
  have htrace : WordTrace (prefixWord ++ tailWord_1440630) baseStart_1440630 baseEnd_1440630 := by
    simpa [prefixWord, tailWord_1440630, baseEnd_1440630] using wordTrace_append hprefix tailTrace_1440630
  have hstable : (prefixWord ++ tailWord_1440630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440630).length < 2 ^ (prefixWord ++ tailWord_1440630).sum := by decide
  have hdescent : baseEnd_1440630 < baseStart_1440630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440639 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 3, 5]
def baseStart_1440639 : Nat := 118140960795 + 1440639 * 2 ^ 59
def prefixEnd_1440639 : Nat := 4983230072969 + 3 ^ 40 * 1440639 * 2
def baseEnd_1440639 : Nat := 493160171075129484658085

theorem tailTrace_1440639 : CollatzResearch.WordTrace tailWord_1440639 prefixEnd_1440639 493160171075129484658085 := by
  unfold tailWord_1440639
  simp only [CollatzResearch.WordTrace]
  refine ⟨52544421027818419397940971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35029614018545612931960647 52544421027818419397940971)
  ·
    refine ⟨78816631541727629096911457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52544421027818419397940971 78816631541727629096911457)
    ·
      refine ⟨59112473656295721822683593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78816631541727629096911457 59112473656295721822683593)
      ·
        refine ⟨44334355242221791367012695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59112473656295721822683593 44334355242221791367012695)
        ·
          refine ⟨66501532863332687050519043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44334355242221791367012695 66501532863332687050519043)
          ·
            refine ⟨99752299294999030575778565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66501532863332687050519043 99752299294999030575778565)
            ·
              refine ⟨18703556117812318232958481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99752299294999030575778565 18703556117812318232958481)
              ·
                refine ⟨14027667088359238674718861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18703556117812318232958481 14027667088359238674718861)
                ·
                  refine ⟨5260375158134714503019573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14027667088359238674718861 5260375158134714503019573)
                  ·
                    refine ⟨493160171075129484658085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5260375158134714503019573 493160171075129484658085)
                    ·
                      rfl

theorem cell22_1440639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_1440639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440639 prefixEnd_1440639 := by exact prefixLift 1440639
  have htrace : WordTrace (prefixWord ++ tailWord_1440639) baseStart_1440639 baseEnd_1440639 := by
    simpa [prefixWord, tailWord_1440639, baseEnd_1440639] using wordTrace_append hprefix tailTrace_1440639
  have hstable : (prefixWord ++ tailWord_1440639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440639).length < 2 ^ (prefixWord ++ tailWord_1440639).sum := by decide
  have hdescent : baseEnd_1440639 < baseStart_1440639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440671 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 1, 6]
def baseStart_1440671 : Nat := 118140960795 + 1440671 * 2 ^ 59
def prefixEnd_1440671 : Nat := 4983230072969 + 3 ^ 40 * 1440671 * 2
def baseEnd_1440671 : Nat := 493171125329092067857987

theorem tailTrace_1440671 : CollatzResearch.WordTrace tailWord_1440671 prefixEnd_1440671 493171125329092067857987 := by
  unfold tailWord_1440671
  simp only [CollatzResearch.WordTrace]
  refine ⟨52545588163702488863105867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35030392109134992575403911 52545588163702488863105867)
  ·
    refine ⟨78818382245553733294658801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52545588163702488863105867 78818382245553733294658801)
    ·
      refine ⟨59113786684165299970994101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78818382245553733294658801 59113786684165299970994101)
      ·
        refine ⟨5541917501640496872280697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59113786684165299970994101 5541917501640496872280697)
        ·
          refine ⟨4156438126230372654210523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5541917501640496872280697 4156438126230372654210523)
          ·
            refine ⟨6234657189345558981315785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4156438126230372654210523 6234657189345558981315785)
            ·
              refine ⟨4675992892009169235986839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6234657189345558981315785 4675992892009169235986839)
              ·
                refine ⟨7013989338013753853980259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4675992892009169235986839 7013989338013753853980259)
                ·
                  refine ⟨10520984007020630780970389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7013989338013753853980259 10520984007020630780970389)
                  ·
                    refine ⟨493171125329092067857987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10520984007020630780970389 493171125329092067857987)
                    ·
                      rfl

theorem cell22_1440671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_1440671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440671 prefixEnd_1440671 := by exact prefixLift 1440671
  have htrace : WordTrace (prefixWord ++ tailWord_1440671) baseStart_1440671 baseEnd_1440671 := by
    simpa [prefixWord, tailWord_1440671, baseEnd_1440671] using wordTrace_append hprefix tailTrace_1440671
  have hstable : (prefixWord ++ tailWord_1440671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440671).length < 2 ^ (prefixWord ++ tailWord_1440671).sum := by decide
  have hdescent : baseEnd_1440671 < baseStart_1440671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440673 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 4, 3]
def baseStart_1440673 : Nat := 118140960795 + 1440673 * 2 ^ 59
def prefixEnd_1440673 : Nat := 4983230072969 + 3 ^ 40 * 1440673 * 2
def baseEnd_1440673 : Nat := 493171809969964729307981

theorem tailTrace_1440673 : CollatzResearch.WordTrace tailWord_1440673 prefixEnd_1440673 493171809969964729307981 := by
  unfold tailWord_1440673
  simp only [CollatzResearch.WordTrace]
  refine ⟨52545661109695243204678673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35030440739796828803119115 52545661109695243204678673)
  ·
    refine ⟨39409245832271432403509005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52545661109695243204678673 39409245832271432403509005)
    ·
      refine ⟨14778467187101787151315877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39409245832271432403509005 14778467187101787151315877)
      ·
        refine ⟨2770962597581585090871727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14778467187101787151315877 2770962597581585090871727)
        ·
          refine ⟨4156443896372377636307591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2770962597581585090871727 4156443896372377636307591)
          ·
            refine ⟨6234665844558566454461387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4156443896372377636307591 6234665844558566454461387)
            ·
              refine ⟨9351998766837849681692081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6234665844558566454461387 9351998766837849681692081)
              ·
                refine ⟨7013999075128387261269061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9351998766837849681692081 7013999075128387261269061)
                ·
                  refine ⟨1315124826586572611487949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7013999075128387261269061 1315124826586572611487949)
                  ·
                    refine ⟨493171809969964729307981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1315124826586572611487949 493171809969964729307981)
                    ·
                      rfl

theorem cell22_1440673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_1440673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440673 prefixEnd_1440673 := by exact prefixLift 1440673
  have htrace : WordTrace (prefixWord ++ tailWord_1440673) baseStart_1440673 baseEnd_1440673 := by
    simpa [prefixWord, tailWord_1440673, baseEnd_1440673] using wordTrace_append hprefix tailTrace_1440673
  have hstable : (prefixWord ++ tailWord_1440673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440673).length < 2 ^ (prefixWord ++ tailWord_1440673).sum := by decide
  have hdescent : baseEnd_1440673 < baseStart_1440673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440684 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 1, 9]
def baseStart_1440684 : Nat := 118140960795 + 1440684 * 2 ^ 59
def prefixEnd_1440684 : Nat := 4983230072969 + 3 ^ 40 * 1440684 * 2
def baseEnd_1440684 : Nat := 493175575494764367282947

theorem tailTrace_1440684 : CollatzResearch.WordTrace tailWord_1440684 prefixEnd_1440684 493175575494764367282947 := by
  unfold tailWord_1440684
  simp only [CollatzResearch.WordTrace]
  refine ⟨26273031156327696041664553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35030708208436928055552737 26273031156327696041664553)
  ·
    refine ⟨19704773367245772031248415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26273031156327696041664553 19704773367245772031248415)
    ·
      refine ⟨29557160050868658046872623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19704773367245772031248415 29557160050868658046872623)
      ·
        refine ⟨44335740076302987070308935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29557160050868658046872623 44335740076302987070308935)
        ·
          refine ⟨66503610114454480605463403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44335740076302987070308935 66503610114454480605463403)
          ·
            refine ⟨99755415171681720908195105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66503610114454480605463403 99755415171681720908195105)
            ·
              refine ⟨74816561378761290681146329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99755415171681720908195105 74816561378761290681146329)
              ·
                refine ⟨56112421034070968010859747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74816561378761290681146329 56112421034070968010859747)
                ·
                  refine ⟨84168631551106452016289621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56112421034070968010859747 84168631551106452016289621)
                  ·
                    refine ⟨493175575494764367282947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 84168631551106452016289621 493175575494764367282947)
                    ·
                      rfl

theorem cell22_1440684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_1440684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440684 prefixEnd_1440684 := by exact prefixLift 1440684
  have htrace : WordTrace (prefixWord ++ tailWord_1440684) baseStart_1440684 baseEnd_1440684 := by
    simpa [prefixWord, tailWord_1440684, baseEnd_1440684] using wordTrace_append hprefix tailTrace_1440684
  have hstable : (prefixWord ++ tailWord_1440684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440684).length < 2 ^ (prefixWord ++ tailWord_1440684).sum := by decide
  have hdescent : baseEnd_1440684 < baseStart_1440684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440761 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 5, 4]
def baseStart_1440761 : Nat := 118140960795 + 1440761 * 2 ^ 59
def prefixEnd_1440761 : Nat := 4983230072969 + 3 ^ 40 * 1440761 * 2
def baseEnd_1440761 : Nat := 493201934168361833107711

theorem tailTrace_1440761 : CollatzResearch.WordTrace tailWord_1440761 prefixEnd_1440761 493201934168361833107711 := by
  unfold tailWord_1440761
  simp only [CollatzResearch.WordTrace]
  refine ⟨52548870733376434233882137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35032580488917622822588091 52548870733376434233882137)
  ·
    refine ⟨39411653050032325675411603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52548870733376434233882137 39411653050032325675411603)
    ·
      refine ⟨59117479575048488513117405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39411653050032325675411603 59117479575048488513117405)
      ·
        refine ⟨22169054840643183192419027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59117479575048488513117405 22169054840643183192419027)
        ·
          refine ⟨33253582260964774788628541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22169054840643183192419027 33253582260964774788628541)
          ·
            refine ⟨12470093347861790545735703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33253582260964774788628541 12470093347861790545735703)
            ·
              refine ⟨18705140021792685818603555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12470093347861790545735703 18705140021792685818603555)
              ·
                refine ⟨28057710032689028727905333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18705140021792685818603555 28057710032689028727905333)
                ·
                  refine ⟨2630410315564596443241125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28057710032689028727905333 2630410315564596443241125)
                  ·
                    refine ⟨493201934168361833107711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2630410315564596443241125 493201934168361833107711)
                    ·
                      rfl

theorem cell22_1440761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_1440761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440761 prefixEnd_1440761 := by exact prefixLift 1440761
  have htrace : WordTrace (prefixWord ++ tailWord_1440761) baseStart_1440761 baseEnd_1440761 := by
    simpa [prefixWord, tailWord_1440761, baseEnd_1440761] using wordTrace_append hprefix tailTrace_1440761
  have hstable : (prefixWord ++ tailWord_1440761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440761).length < 2 ^ (prefixWord ++ tailWord_1440761).sum := by decide
  have hdescent : baseEnd_1440761 < baseStart_1440761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440776 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 8]
def baseStart_1440776 : Nat := 118140960795 + 1440776 * 2 ^ 59
def prefixEnd_1440776 : Nat := 4983230072969 + 3 ^ 40 * 1440776 * 2
def baseEnd_1440776 : Nat := 164402356324968931327555

theorem tailTrace_1440776 : CollatzResearch.WordTrace tailWord_1440776 prefixEnd_1440776 164402356324968931327555 := by
  unfold tailWord_1440776
  simp only [CollatzResearch.WordTrace]
  refine ⟨26274708914161045897839091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35032945218881394530452121 26274708914161045897839091)
  ·
    refine ⟨39412063371241568846758637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26274708914161045897839091 39412063371241568846758637)
    ·
      refine ⟨14779523764215588317534489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39412063371241568846758637 14779523764215588317534489)
      ·
        refine ⟨11084642823161691238150867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14779523764215588317534489 11084642823161691238150867)
        ·
          refine ⟨16626964234742536857226301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11084642823161691238150867 16626964234742536857226301)
          ·
            refine ⟨6235111588028451321459863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16626964234742536857226301 6235111588028451321459863)
            ·
              refine ⟨9352667382042676982189795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6235111588028451321459863 9352667382042676982189795)
              ·
                refine ⟨14029001073064015473284693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9352667382042676982189795 14029001073064015473284693)
                ·
                  refine ⟨164402356324968931327555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14029001073064015473284693 164402356324968931327555)
                  ·
                    rfl

theorem cell22_1440776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 8].length) (baseStart_1440776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440776 prefixEnd_1440776 := by exact prefixLift 1440776
  have htrace : WordTrace (prefixWord ++ tailWord_1440776) baseStart_1440776 baseEnd_1440776 := by
    simpa [prefixWord, tailWord_1440776, baseEnd_1440776] using wordTrace_append hprefix tailTrace_1440776
  have hstable : (prefixWord ++ tailWord_1440776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440776).length < 2 ^ (prefixWord ++ tailWord_1440776).sum := by decide
  have hdescent : baseEnd_1440776 < baseStart_1440776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440778 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 3, 4]
def baseStart_1440778 : Nat := 118140960795 + 1440778 * 2 ^ 59
def prefixEnd_1440778 : Nat := 4983230072969 + 3 ^ 40 * 1440778 * 2
def baseEnd_1440778 : Nat := 493207753615779455432659

theorem tailTrace_1440778 : CollatzResearch.WordTrace tailWord_1440778 prefixEnd_1440778 493207753615779455432659 := by
  unfold tailWord_1440778
  simp only [CollatzResearch.WordTrace]
  refine ⟨13137372693578711534312747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35032993849543230758167325 13137372693578711534312747)
  ·
    refine ⟨19706059040368067301469121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13137372693578711534312747 19706059040368067301469121)
    ·
      refine ⟨14779544280276050476101841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19706059040368067301469121 14779544280276050476101841)
      ·
        refine ⟨11084658210207037857076381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14779544280276050476101841 11084658210207037857076381)
        ·
          refine ⟨4156746828827639196403643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11084658210207037857076381 4156746828827639196403643)
          ·
            refine ⟨6235120243241458794605465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4156746828827639196403643 6235120243241458794605465)
            ·
              refine ⟨4676340182431094095954099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6235120243241458794605465 4676340182431094095954099)
              ·
                refine ⟨7014510273646641143931149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4676340182431094095954099 7014510273646641143931149)
                ·
                  refine ⟨2630441352617490428974181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7014510273646641143931149 2630441352617490428974181)
                  ·
                    refine ⟨493207753615779455432659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2630441352617490428974181 493207753615779455432659)
                    ·
                      rfl

theorem cell22_1440778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_1440778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440778 prefixEnd_1440778 := by exact prefixLift 1440778
  have htrace : WordTrace (prefixWord ++ tailWord_1440778) baseStart_1440778 baseEnd_1440778 := by
    simpa [prefixWord, tailWord_1440778, baseEnd_1440778] using wordTrace_append hprefix tailTrace_1440778
  have hstable : (prefixWord ++ tailWord_1440778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440778).length < 2 ^ (prefixWord ++ tailWord_1440778).sum := by decide
  have hdescent : baseEnd_1440778 < baseStart_1440778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440793 : List Nat := [1, 2, 1, 2, 1, 1, 5, 5, 4]
def baseStart_1440793 : Nat := 118140960795 + 1440793 * 2 ^ 59
def prefixEnd_1440793 : Nat := 4983230072969 + 3 ^ 40 * 1440793 * 2
def baseEnd_1440793 : Nat := 164404296140774805435871

theorem tailTrace_1440793 : CollatzResearch.WordTrace tailWord_1440793 prefixEnd_1440793 164404296140774805435871 := by
  unfold tailWord_1440793
  simp only [CollatzResearch.WordTrace]
  refine ⟨52550037869260503699047033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35033358579507002466031355 52550037869260503699047033)
  ·
    refine ⟨39412528401945377774285275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52550037869260503699047033 39412528401945377774285275)
    ·
      refine ⟨59118792602918066661427913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39412528401945377774285275 59118792602918066661427913)
      ·
        refine ⟨44339094452188549996070935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59118792602918066661427913 44339094452188549996070935)
        ·
          refine ⟨66508641678282824994106403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44339094452188549996070935 66508641678282824994106403)
          ·
            refine ⟨99762962517424237491159605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66508641678282824994106403 99762962517424237491159605)
            ·
              refine ⟨9352777736008522264796213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99762962517424237491159605 9352777736008522264796213)
              ·
                refine ⟨876822912750798962324645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9352777736008522264796213 876822912750798962324645)
                ·
                  refine ⟨164404296140774805435871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 876822912750798962324645 164404296140774805435871)
                  ·
                    rfl

theorem cell22_1440793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 4].length) (baseStart_1440793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440793 prefixEnd_1440793 := by exact prefixLift 1440793
  have htrace : WordTrace (prefixWord ++ tailWord_1440793) baseStart_1440793 baseEnd_1440793 := by
    simpa [prefixWord, tailWord_1440793, baseEnd_1440793] using wordTrace_append hprefix tailTrace_1440793
  have hstable : (prefixWord ++ tailWord_1440793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440793).length < 2 ^ (prefixWord ++ tailWord_1440793).sum := by decide
  have hdescent : baseEnd_1440793 < baseStart_1440793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440810 : List Nat := [3, 1, 4, 1, 3, 1, 2, 1, 6]
def baseStart_1440810 : Nat := 118140960795 + 1440810 * 2 ^ 59
def prefixEnd_1440810 : Nat := 4983230072969 + 3 ^ 40 * 1440810 * 2
def baseEnd_1440810 : Nat := 164406235956580679544187

theorem tailTrace_1440810 : CollatzResearch.WordTrace tailWord_1440810 prefixEnd_1440810 164406235956580679544187 := by
  unfold tailWord_1440810
  simp only [CollatzResearch.WordTrace]
  refine ⟨13137664477549728900603971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35033771940132610401610589 13137664477549728900603971)
  ·
    refine ⟨19706496716324593350905957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13137664477549728900603971 19706496716324593350905957)
    ·
      refine ⟨3694968134310861253294867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19706496716324593350905957 3694968134310861253294867)
      ·
        refine ⟨5542452201466291879942301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3694968134310861253294867 5542452201466291879942301)
        ·
          refine ⟨2078419575549859454978363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5542452201466291879942301 2078419575549859454978363)
          ·
            refine ⟨3117629363324789182467545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2078419575549859454978363 3117629363324789182467545)
            ·
              refine ⟨2338222022493591886850659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3117629363324789182467545 2338222022493591886850659)
              ·
                refine ⟨3507333033740387830275989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2338222022493591886850659 3507333033740387830275989)
                ·
                  refine ⟨164406235956580679544187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3507333033740387830275989 164406235956580679544187)
                  ·
                    rfl

theorem cell22_1440810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_1440810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440810 prefixEnd_1440810 := by exact prefixLift 1440810
  have htrace : WordTrace (prefixWord ++ tailWord_1440810) baseStart_1440810 baseEnd_1440810 := by
    simpa [prefixWord, tailWord_1440810, baseEnd_1440810] using wordTrace_append hprefix tailTrace_1440810
  have hstable : (prefixWord ++ tailWord_1440810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440810).length < 2 ^ (prefixWord ++ tailWord_1440810).sum := by decide
  have hdescent : baseEnd_1440810 < baseStart_1440810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440821 : List Nat := [1, 3, 3, 1, 1, 1, 1, 11]
def baseStart_1440821 : Nat := 118140960795 + 1440821 * 2 ^ 59
def prefixEnd_1440821 : Nat := 4983230072969 + 3 ^ 40 * 1440821 * 2
def baseEnd_1440821 : Nat := 54802497043837964067503

theorem tailTrace_1440821 : CollatzResearch.WordTrace tailWord_1440821 prefixEnd_1440821 54802497043837964067503 := by
  unfold tailWord_1440821
  simp only [CollatzResearch.WordTrace]
  refine ⟨52551059113159064481066317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35034039408772709654044211 52551059113159064481066317)
  ·
    refine ⟨19706647167434649180399869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52551059113159064481066317 19706647167434649180399869)
    ·
      refine ⟨7389992687787993442649951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19706647167434649180399869 7389992687787993442649951)
      ·
        refine ⟨11084989031681990163974927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7389992687787993442649951 11084989031681990163974927)
        ·
          refine ⟨16627483547522985245962391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11084989031681990163974927 16627483547522985245962391)
          ·
            refine ⟨24941225321284477868943587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16627483547522985245962391 24941225321284477868943587)
            ·
              refine ⟨37411837981926716803415381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24941225321284477868943587 37411837981926716803415381)
              ·
                refine ⟨54802497043837964067503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 37411837981926716803415381 54802497043837964067503)
                ·
                  rfl

theorem cell22_1440821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 11].length) (baseStart_1440821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440821 prefixEnd_1440821 := by exact prefixLift 1440821
  have htrace : WordTrace (prefixWord ++ tailWord_1440821) baseStart_1440821 baseEnd_1440821 := by
    simpa [prefixWord, tailWord_1440821, baseEnd_1440821] using wordTrace_append hprefix tailTrace_1440821
  have hstable : (prefixWord ++ tailWord_1440821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440821).length < 2 ^ (prefixWord ++ tailWord_1440821).sum := by decide
  have hdescent : baseEnd_1440821 < baseStart_1440821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440825 : List Nat := [1, 2, 1, 5, 2, 3, 1, 1, 1, 5]
def baseStart_1440825 : Nat := 118140960795 + 1440825 * 2 ^ 59
def prefixEnd_1440825 : Nat := 4983230072969 + 3 ^ 40 * 1440825 * 2
def baseEnd_1440825 : Nat := 493223842676286999507515

theorem tailTrace_1440825 : CollatzResearch.WordTrace tailWord_1440825 prefixEnd_1440825 493223842676286999507515 := by
  unfold tailWord_1440825
  simp only [CollatzResearch.WordTrace]
  refine ⟨52551205005144573164211929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35034136670096382109474619 52551205005144573164211929)
  ·
    refine ⟨39413403753858429873158947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52551205005144573164211929 39413403753858429873158947)
    ·
      refine ⟨59120105630787644809738421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39413403753858429873158947 59120105630787644809738421)
      ·
        refine ⟨5542509902886341700912977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59120105630787644809738421 5542509902886341700912977)
        ·
          refine ⟨4156882427164756275684733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5542509902886341700912977 4156882427164756275684733)
          ·
            refine ⟨1558830910186783603381775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4156882427164756275684733 1558830910186783603381775)
            ·
              refine ⟨2338246365280175405072663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1558830910186783603381775 2338246365280175405072663)
              ·
                refine ⟨3507369547920263107608995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2338246365280175405072663 3507369547920263107608995)
                ·
                  refine ⟨5261054321880394661413493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507369547920263107608995 5261054321880394661413493)
                  ·
                    refine ⟨493223842676286999507515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5261054321880394661413493 493223842676286999507515)
                    ·
                      rfl

theorem cell22_1440825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 5].length) (baseStart_1440825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440825 prefixEnd_1440825 := by exact prefixLift 1440825
  have htrace : WordTrace (prefixWord ++ tailWord_1440825) baseStart_1440825 baseEnd_1440825 := by
    simpa [prefixWord, tailWord_1440825, baseEnd_1440825] using wordTrace_append hprefix tailTrace_1440825
  have hstable : (prefixWord ++ tailWord_1440825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440825).length < 2 ^ (prefixWord ++ tailWord_1440825).sum := by decide
  have hdescent : baseEnd_1440825 < baseStart_1440825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440928 : List Nat := [2, 1, 1, 4, 2, 1, 2, 3, 6]
def baseStart_1440928 : Nat := 118140960795 + 1440928 * 2 ^ 59
def prefixEnd_1440928 : Nat := 4983230072969 + 3 ^ 40 * 1440928 * 2
def baseEnd_1440928 : Nat := 164419700560409688060733

theorem tailTrace_1440928 : CollatzResearch.WordTrace tailWord_1440928 prefixEnd_1440928 164419700560409688060733 := by
  unfold tailWord_1440928
  simp only [CollatzResearch.WordTrace]
  refine ⟨26277480861885710877605719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35036641149180947836807625 26277480861885710877605719)
  ·
    refine ⟨39416221292828566316408579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26277480861885710877605719 39416221292828566316408579)
    ·
      refine ⟨59124331939242849474612869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39416221292828566316408579 59124331939242849474612869)
      ·
        refine ⟨11085812238608034276489913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59124331939242849474612869 11085812238608034276489913)
        ·
          refine ⟨8314359178956025707367435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11085812238608034276489913 8314359178956025707367435)
          ·
            refine ⟨12471538768434038561051153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8314359178956025707367435 12471538768434038561051153)
            ·
              refine ⟨9353654076325528920788365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12471538768434038561051153 9353654076325528920788365)
              ·
                refine ⟨3507620278622073345295637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9353654076325528920788365 3507620278622073345295637)
                ·
                  refine ⟨164419700560409688060733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3507620278622073345295637 164419700560409688060733)
                  ·
                    rfl

theorem cell22_1440928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 6].length) (baseStart_1440928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440928 prefixEnd_1440928 := by exact prefixLift 1440928
  have htrace : WordTrace (prefixWord ++ tailWord_1440928) baseStart_1440928 baseEnd_1440928 := by
    simpa [prefixWord, tailWord_1440928, baseEnd_1440928] using wordTrace_append hprefix tailTrace_1440928
  have hstable : (prefixWord ++ tailWord_1440928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440928).length < 2 ^ (prefixWord ++ tailWord_1440928).sum := by decide
  have hdescent : baseEnd_1440928 < baseStart_1440928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440943 : List Nat := [1, 1, 2, 1, 2, 3, 3, 3, 1, 5]
def baseStart_1440943 : Nat := 118140960795 + 1440943 * 2 ^ 59
def prefixEnd_1440943 : Nat := 4983230072969 + 3 ^ 40 * 1440943 * 2
def baseEnd_1440943 : Nat := 493264236487774025057153

theorem tailTrace_1440943 : CollatzResearch.WordTrace tailWord_1440943 prefixEnd_1440943 493264236487774025057153 := by
  unfold tailWord_1440943
  simp only [CollatzResearch.WordTrace]
  refine ⟨52555508818717079317007483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35037005879144719544671655 52555508818717079317007483)
  ·
    refine ⟨78833263228075618975511225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52555508818717079317007483 78833263228075618975511225)
    ·
      refine ⟨59124947421056714231633419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78833263228075618975511225 59124947421056714231633419)
      ·
        refine ⟨88687421131585071347450129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59124947421056714231633419 88687421131585071347450129)
        ·
          refine ⟨66515565848688803510587597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88687421131585071347450129 66515565848688803510587597)
          ·
            refine ⟨24943337193258301316470349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66515565848688803510587597 24943337193258301316470349)
            ·
              refine ⟨9353751447471862993676381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24943337193258301316470349 9353751447471862993676381)
              ·
                refine ⟨3507656792801948622628643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9353751447471862993676381 3507656792801948622628643)
                ·
                  refine ⟨5261485189202922933942965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507656792801948622628643 5261485189202922933942965)
                  ·
                    refine ⟨493264236487774025057153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5261485189202922933942965 493264236487774025057153)
                    ·
                      rfl

theorem cell22_1440943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_1440943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440943 prefixEnd_1440943 := by exact prefixLift 1440943
  have htrace : WordTrace (prefixWord ++ tailWord_1440943) baseStart_1440943 baseEnd_1440943 := by
    simpa [prefixWord, tailWord_1440943, baseEnd_1440943] using wordTrace_append hprefix tailTrace_1440943
  have hstable : (prefixWord ++ tailWord_1440943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440943).length < 2 ^ (prefixWord ++ tailWord_1440943).sum := by decide
  have hdescent : baseEnd_1440943 < baseStart_1440943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440945 : List Nat := [1, 2, 2, 5, 1, 2, 1, 2, 6]
def baseStart_1440945 : Nat := 118140960795 + 1440945 * 2 ^ 59
def prefixEnd_1440945 : Nat := 4983230072969 + 3 ^ 40 * 1440945 * 2
def baseEnd_1440945 : Nat := 164421640376215562169049

theorem tailTrace_1440945 : CollatzResearch.WordTrace tailWord_1440945 prefixEnd_1440945 164421640376215562169049 := by
  unfold tailWord_1440945
  simp only [CollatzResearch.WordTrace]
  refine ⟨52555581764709833658580289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35037054509806555772386859 52555581764709833658580289)
  ·
    refine ⟨39416686323532375243935217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52555581764709833658580289 39416686323532375243935217)
    ·
      refine ⟨29562514742649281432951413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39416686323532375243935217 29562514742649281432951413)
      ·
        refine ⟨2771485757123370134339195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29562514742649281432951413 2771485757123370134339195)
        ·
          refine ⟨4157228635685055201508793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2771485757123370134339195 4157228635685055201508793)
          ·
            refine ⟨3117921476763791401131595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4157228635685055201508793 3117921476763791401131595)
            ·
              refine ⟨4676882215145687101697393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3117921476763791401131595 4676882215145687101697393)
              ·
                refine ⟨3507661661359265326273045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4676882215145687101697393 3507661661359265326273045)
                ·
                  refine ⟨164421640376215562169049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3507661661359265326273045 164421640376215562169049)
                  ·
                    rfl

theorem cell22_1440945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 6].length) (baseStart_1440945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1440945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1440945 prefixEnd_1440945 := by exact prefixLift 1440945
  have htrace : WordTrace (prefixWord ++ tailWord_1440945) baseStart_1440945 baseEnd_1440945 := by
    simpa [prefixWord, tailWord_1440945, baseEnd_1440945] using wordTrace_append hprefix tailTrace_1440945
  have hstable : (prefixWord ++ tailWord_1440945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440945).length < 2 ^ (prefixWord ++ tailWord_1440945).sum := by decide
  have hdescent : baseEnd_1440945 < baseStart_1440945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441007 : List Nat := [1, 1, 2, 1, 7, 2, 2, 6]
def baseStart_1441007 : Nat := 118140960795 + 1441007 * 2 ^ 59
def prefixEnd_1441007 : Nat := 4983230072969 + 3 ^ 40 * 1441007 * 2
def baseEnd_1441007 : Nat := 54809571666188799050773

theorem tailTrace_1441007 : CollatzResearch.WordTrace tailWord_1441007 prefixEnd_1441007 54809571666188799050773 := by
  unfold tailWord_1441007
  simp only [CollatzResearch.WordTrace]
  refine ⟨52557843090485218247337275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35038562060323478831558183 52557843090485218247337275)
  ·
    refine ⟨78836764635727827371005913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52557843090485218247337275 78836764635727827371005913)
    ·
      refine ⟨59127573476795870528254435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78836764635727827371005913 59127573476795870528254435)
      ·
        refine ⟨88691360215193805792381653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59127573476795870528254435 88691360215193805792381653)
        ·
          refine ⟨2078703755043604823258945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 88691360215193805792381653 2078703755043604823258945)
          ·
            refine ⟨1559027816282703617444209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2078703755043604823258945 1559027816282703617444209)
            ·
              refine ⟨1169270862212027713083157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1559027816282703617444209 1169270862212027713083157)
              ·
                refine ⟨54809571666188799050773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1169270862212027713083157 54809571666188799050773)
                ·
                  rfl

theorem cell22_1441007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 6].length) (baseStart_1441007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441007 prefixEnd_1441007 := by exact prefixLift 1441007
  have htrace : WordTrace (prefixWord ++ tailWord_1441007) baseStart_1441007 baseEnd_1441007 := by
    simpa [prefixWord, tailWord_1441007, baseEnd_1441007] using wordTrace_append hprefix tailTrace_1441007
  have hstable : (prefixWord ++ tailWord_1441007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441007).length < 2 ^ (prefixWord ++ tailWord_1441007).sum := by decide
  have hdescent : baseEnd_1441007 < baseStart_1441007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441018 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 9]
def baseStart_1441018 : Nat := 118140960795 + 1441018 * 2 ^ 59
def prefixEnd_1441018 : Nat := 4983230072969 + 3 ^ 40 * 1441018 * 2
def baseEnd_1441018 : Nat := 164429970173499609810641

theorem tailTrace_1441018 : CollatzResearch.WordTrace tailWord_1441018 prefixEnd_1441018 164429970173499609810641 := by
  unfold tailWord_1441018
  simp only [CollatzResearch.WordTrace]
  refine ⟨13139561073361341781496927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35038829528963578083991805 13139561073361341781496927)
  ·
    refine ⟨19709341610042012672245391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13139561073361341781496927 19709341610042012672245391)
    ·
      refine ⟨29564012415063019008368087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19709341610042012672245391 29564012415063019008368087)
      ·
        refine ⟨44346018622594528512552131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29564012415063019008368087 44346018622594528512552131)
        ·
          refine ⟨66519027933891792768828197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44346018622594528512552131 66519027933891792768828197)
          ·
            refine ⟨12472317737604711144155287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66519027933891792768828197 12472317737604711144155287)
            ·
              refine ⟨18708476606407066716232931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12472317737604711144155287 18708476606407066716232931)
              ·
                refine ⟨28062714909610600074349397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18708476606407066716232931 28062714909610600074349397)
                ·
                  refine ⟨164429970173499609810641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28062714909610600074349397 164429970173499609810641)
                  ·
                    rfl

theorem cell22_1441018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_1441018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441018 prefixEnd_1441018 := by exact prefixLift 1441018
  have htrace : WordTrace (prefixWord ++ tailWord_1441018) baseStart_1441018 baseEnd_1441018 := by
    simpa [prefixWord, tailWord_1441018, baseEnd_1441018] using wordTrace_append hprefix tailTrace_1441018
  have hstable : (prefixWord ++ tailWord_1441018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441018).length < 2 ^ (prefixWord ++ tailWord_1441018).sum := by decide
  have hdescent : baseEnd_1441018 < baseStart_1441018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441052 : List Nat := [2, 2, 3, 1, 1, 1, 6, 1, 5]
def baseStart_1441052 : Nat := 118140960795 + 1441052 * 2 ^ 59
def prefixEnd_1441052 : Nat := 4983230072969 + 3 ^ 40 * 1441052 * 2
def baseEnd_1441052 : Nat := 164433849805111358027273

theorem tailTrace_1441052 : CollatzResearch.WordTrace tailWord_1441052 prefixEnd_1441052 164433849805111358027273 := by
  unfold tailWord_1441052
  simp only [CollatzResearch.WordTrace]
  refine ⟨26279742187661095466362705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35039656250214793955150273 26279742187661095466362705)
  ·
    refine ⟨19709806640745821599772029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26279742187661095466362705 19709806640745821599772029)
    ·
      refine ⟨7391177490279683099914511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19709806640745821599772029 7391177490279683099914511)
      ·
        refine ⟨11086766235419524649871767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7391177490279683099914511 11086766235419524649871767)
        ·
          refine ⟨16630149353129286974807651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11086766235419524649871767 16630149353129286974807651)
          ·
            refine ⟨24945224029693930462211477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16630149353129286974807651 24945224029693930462211477)
            ·
              refine ⟨1169307376391902990416163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24945224029693930462211477 1169307376391902990416163)
              ·
                refine ⟨1753961064587854485624245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1169307376391902990416163 1753961064587854485624245)
                ·
                  refine ⟨164433849805111358027273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1753961064587854485624245 164433849805111358027273)
                  ·
                    rfl

theorem cell22_1441052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_1441052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441052 prefixEnd_1441052 := by exact prefixLift 1441052
  have htrace : WordTrace (prefixWord ++ tailWord_1441052) baseStart_1441052 baseEnd_1441052 := by
    simpa [prefixWord, tailWord_1441052, baseEnd_1441052] using wordTrace_append hprefix tailTrace_1441052
  have hstable : (prefixWord ++ tailWord_1441052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441052).length < 2 ^ (prefixWord ++ tailWord_1441052).sum := by decide
  have hdescent : baseEnd_1441052 < baseStart_1441052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441112 : List Nat := [2, 1, 2, 2, 1, 1, 3, 5, 2, 3]
def baseStart_1441112 : Nat := 118140960795 + 1441112 * 2 ^ 59
def prefixEnd_1441112 : Nat := 4983230072969 + 3 ^ 40 * 1441112 * 2
def baseEnd_1441112 : Nat := 493322088641513917581635

theorem tailTrace_1441112 : CollatzResearch.WordTrace tailWord_1441112 prefixEnd_1441112 493322088641513917581635 := by
  unfold tailWord_1441112
  simp only [CollatzResearch.WordTrace]
  refine ⟨26280836377552410589954795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35041115170069880786606393 26280836377552410589954795)
  ·
    refine ⟨39421254566328615884932193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26280836377552410589954795 39421254566328615884932193)
    ·
      refine ⟨29565940924746461913699145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39421254566328615884932193 29565940924746461913699145)
      ·
        refine ⟨22174455693559846435274359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29565940924746461913699145 22174455693559846435274359)
        ·
          refine ⟨33261683540339769652911539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22174455693559846435274359 33261683540339769652911539)
          ·
            refine ⟨49892525310509654479367309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33261683540339769652911539 49892525310509654479367309)
            ·
              refine ⟨18709696991441120429762741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49892525310509654479367309 18709696991441120429762741)
              ·
                refine ⟨1754034092947605040290257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18709696991441120429762741 1754034092947605040290257)
                ·
                  refine ⟨1315525569710703780217693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1754034092947605040290257 1315525569710703780217693)
                  ·
                    refine ⟨493322088641513917581635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1315525569710703780217693 493322088641513917581635)
                    ·
                      rfl

theorem cell22_1441112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_1441112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441112 prefixEnd_1441112 := by exact prefixLift 1441112
  have htrace : WordTrace (prefixWord ++ tailWord_1441112) baseStart_1441112 baseEnd_1441112 := by
    simpa [prefixWord, tailWord_1441112, baseEnd_1441112] using wordTrace_append hprefix tailTrace_1441112
  have hstable : (prefixWord ++ tailWord_1441112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441112).length < 2 ^ (prefixWord ++ tailWord_1441112).sum := by decide
  have hdescent : baseEnd_1441112 < baseStart_1441112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441127 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 1, 6]
def baseStart_1441127 : Nat := 118140960795 + 1441127 * 2 ^ 59
def prefixEnd_1441127 : Nat := 4983230072969 + 3 ^ 40 * 1441127 * 2
def baseEnd_1441127 : Nat := 493327223448058878456589

theorem tailTrace_1441127 : CollatzResearch.WordTrace tailWord_1441127 prefixEnd_1441127 493327223448058878456589 := by
  unfold tailWord_1441127
  simp only [CollatzResearch.WordTrace]
  refine ⟨52562219850050478741705635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35041479900033652494470423 52562219850050478741705635)
  ·
    refine ⟨78843329775075718112558453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52562219850050478741705635 78843329775075718112558453)
    ·
      refine ⟨7391562166413348573052355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78843329775075718112558453 7391562166413348573052355)
      ·
        refine ⟨11087343249620022859578533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7391562166413348573052355 11087343249620022859578533)
        ·
          refine ⟨2078876859303754286170975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11087343249620022859578533 2078876859303754286170975)
          ·
            refine ⟨3118315288955631429256463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2078876859303754286170975 3118315288955631429256463)
            ·
              refine ⟨4677472933433447143884695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3118315288955631429256463 4677472933433447143884695)
              ·
                refine ⟨7016209400150170715827043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4677472933433447143884695 7016209400150170715827043)
                ·
                  refine ⟨10524314100225256073740565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7016209400150170715827043 10524314100225256073740565)
                  ·
                    refine ⟨493327223448058878456589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10524314100225256073740565 493327223448058878456589)
                    ·
                      rfl

theorem cell22_1441127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_1441127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441127 prefixEnd_1441127 := by exact prefixLift 1441127
  have htrace : WordTrace (prefixWord ++ tailWord_1441127) baseStart_1441127 baseEnd_1441127 := by
    simpa [prefixWord, tailWord_1441127, baseEnd_1441127] using wordTrace_append hprefix tailTrace_1441127
  have hstable : (prefixWord ++ tailWord_1441127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441127).length < 2 ^ (prefixWord ++ tailWord_1441127).sum := by decide
  have hdescent : baseEnd_1441127 < baseStart_1441127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441157 : List Nat := [1, 3, 1, 1, 3, 1, 3, 3, 3, 3]
def baseStart_1441157 : Nat := 118140960795 + 1441157 * 2 ^ 59
def prefixEnd_1441157 : Nat := 4983230072969 + 3 ^ 40 * 1441157 * 2
def baseEnd_1441157 : Nat := 493337493061148800206497

theorem tailTrace_1441157 : CollatzResearch.WordTrace tailWord_1441157 prefixEnd_1441157 493337493061148800206497 := by
  unfold tailWord_1441157
  simp only [CollatzResearch.WordTrace]
  refine ⟨52563314039941793865297725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35042209359961195910198483 52563314039941793865297725)
  ·
    refine ⟨19711242764978172699486647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52563314039941793865297725 19711242764978172699486647)
    ·
      refine ⟨29566864147467259049229971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19711242764978172699486647 29566864147467259049229971)
      ·
        refine ⟨44350296221200888573844957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29566864147467259049229971 44350296221200888573844957)
        ·
          refine ⟨16631361082950333215191859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44350296221200888573844957 16631361082950333215191859)
          ·
            refine ⟨24947041624425499822787789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16631361082950333215191859 24947041624425499822787789)
            ·
              refine ⟨9355140609159562433545421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24947041624425499822787789 9355140609159562433545421)
              ·
                refine ⟨3508177728434835912579533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9355140609159562433545421 3508177728434835912579533)
                ·
                  refine ⟨1315566648163063467217325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3508177728434835912579533 1315566648163063467217325)
                  ·
                    refine ⟨493337493061148800206497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1315566648163063467217325 493337493061148800206497)
                    ·
                      rfl

theorem cell22_1441157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_1441157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441157 prefixEnd_1441157 := by exact prefixLift 1441157
  have htrace : WordTrace (prefixWord ++ tailWord_1441157) baseStart_1441157 baseEnd_1441157 := by
    simpa [prefixWord, tailWord_1441157, baseEnd_1441157] using wordTrace_append hprefix tailTrace_1441157
  have hstable : (prefixWord ++ tailWord_1441157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441157).length < 2 ^ (prefixWord ++ tailWord_1441157).sum := by decide
  have hdescent : baseEnd_1441157 < baseStart_1441157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441176 : List Nat := [2, 1, 2, 5, 3, 1, 2, 6]
def baseStart_1441176 : Nat := 118140960795 + 1441176 * 2 ^ 59
def prefixEnd_1441176 : Nat := 4983230072969 + 3 ^ 40 * 1441176 * 2
def baseEnd_1441176 : Nat := 54815999683271009331271

theorem tailTrace_1441176 : CollatzResearch.WordTrace tailWord_1441176 prefixEnd_1441176 54815999683271009331271 := by
  unfold tailWord_1441176
  simp only [CollatzResearch.WordTrace]
  refine ⟨26282003513436480055119691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35042671351248640073492921 26282003513436480055119691)
  ·
    refine ⟨39423005270154720082679537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26282003513436480055119691 39423005270154720082679537)
    ·
      refine ⟨29567253952616040062009653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39423005270154720082679537 29567253952616040062009653)
      ·
        refine ⟨2771930058057753755813405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29567253952616040062009653 2771930058057753755813405)
        ·
          refine ⟨1039473771771657658430027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2771930058057753755813405 1039473771771657658430027)
          ·
            refine ⟨1559210657657486487645041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039473771771657658430027 1559210657657486487645041)
            ·
              refine ⟨1169407993243114865733781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1559210657657486487645041 1169407993243114865733781)
              ·
                refine ⟨54815999683271009331271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1169407993243114865733781 54815999683271009331271)
                ·
                  rfl

theorem cell22_1441176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 6].length) (baseStart_1441176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441176 prefixEnd_1441176 := by exact prefixLift 1441176
  have htrace : WordTrace (prefixWord ++ tailWord_1441176) baseStart_1441176 baseEnd_1441176 := by
    simpa [prefixWord, tailWord_1441176, baseEnd_1441176] using wordTrace_append hprefix tailTrace_1441176
  have hstable : (prefixWord ++ tailWord_1441176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441176).length < 2 ^ (prefixWord ++ tailWord_1441176).sum := by decide
  have hdescent : baseEnd_1441176 < baseStart_1441176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441247 : List Nat := [1, 1, 2, 3, 3, 1, 3, 2, 1, 5]
def baseStart_1441247 : Nat := 118140960795 + 1441247 * 2 ^ 59
def prefixEnd_1441247 : Nat := 4983230072969 + 3 ^ 40 * 1441247 * 2
def baseEnd_1441247 : Nat := 493368301900418565456221

theorem tailTrace_1441247 : CollatzResearch.WordTrace tailWord_1441247 prefixEnd_1441247 493368301900418565456221 := by
  unfold tailWord_1441247
  simp only [CollatzResearch.WordTrace]
  refine ⟨52566596609615739236073995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35044397739743826157382663 52566596609615739236073995)
  ·
    refine ⟨78849894914423608854110993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52566596609615739236073995 78849894914423608854110993)
    ·
      refine ⟨59137421185817706640583245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78849894914423608854110993 59137421185817706640583245)
      ·
        refine ⟨22176532944681639990218717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59137421185817706640583245 22176532944681639990218717)
        ·
          refine ⟨8316199854255614996332019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22176532944681639990218717 8316199854255614996332019)
          ·
            refine ⟨12474299781383422494498029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8316199854255614996332019 12474299781383422494498029)
            ·
              refine ⟨4677862418018783435436761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12474299781383422494498029 4677862418018783435436761)
              ·
                refine ⟨3508396813514087576577571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4677862418018783435436761 3508396813514087576577571)
                ·
                  refine ⟨5262595220271131364866357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3508396813514087576577571 5262595220271131364866357)
                  ·
                    refine ⟨493368301900418565456221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5262595220271131364866357 493368301900418565456221)
                    ·
                      rfl

theorem cell22_1441247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_1441247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441247 prefixEnd_1441247 := by exact prefixLift 1441247
  have htrace : WordTrace (prefixWord ++ tailWord_1441247) baseStart_1441247 baseEnd_1441247 := by
    simpa [prefixWord, tailWord_1441247, baseEnd_1441247] using wordTrace_append hprefix tailTrace_1441247
  have hstable : (prefixWord ++ tailWord_1441247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441247).length < 2 ^ (prefixWord ++ tailWord_1441247).sum := by decide
  have hdescent : baseEnd_1441247 < baseStart_1441247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441251 : List Nat := [1, 1, 1, 6, 2, 2, 3, 1, 1, 4]
def baseStart_1441251 : Nat := 118140960795 + 1441251 * 2 ^ 59
def prefixEnd_1441251 : Nat := 4983230072969 + 3 ^ 40 * 1441251 * 2
def baseEnd_1441251 : Nat := 493369671182163888356209

theorem tailTrace_1441251 : CollatzResearch.WordTrace tailWord_1441251 prefixEnd_1441251 493369671182163888356209 := by
  unfold tailWord_1441251
  simp only [CollatzResearch.WordTrace]
  refine ⟨52566742501601247919219607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35044495001067498612813071 52566742501601247919219607)
  ·
    refine ⟨78850113752401871878829411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52566742501601247919219607 78850113752401871878829411)
    ·
      refine ⟨118275170628602807818244117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78850113752401871878829411 118275170628602807818244117)
      ·
        refine ⟨5544148623215756616480193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 118275170628602807818244117 5544148623215756616480193)
        ·
          refine ⟨4158111467411817462360145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5544148623215756616480193 4158111467411817462360145)
          ·
            refine ⟨3118583600558863096770109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4158111467411817462360145 3118583600558863096770109)
            ·
              refine ⟨1169468850209573661288791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3118583600558863096770109 1169468850209573661288791)
              ·
                refine ⟨1754203275314360491933187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1169468850209573661288791 1754203275314360491933187)
                ·
                  refine ⟨2631304912971540737899781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1754203275314360491933187 2631304912971540737899781)
                  ·
                    refine ⟨493369671182163888356209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2631304912971540737899781 493369671182163888356209)
                    ·
                      rfl

theorem cell22_1441251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 1, 4].length) (baseStart_1441251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441251 prefixEnd_1441251 := by exact prefixLift 1441251
  have htrace : WordTrace (prefixWord ++ tailWord_1441251) baseStart_1441251 baseEnd_1441251 := by
    simpa [prefixWord, tailWord_1441251, baseEnd_1441251] using wordTrace_append hprefix tailTrace_1441251
  have hstable : (prefixWord ++ tailWord_1441251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441251).length < 2 ^ (prefixWord ++ tailWord_1441251).sum := by decide
  have hdescent : baseEnd_1441251 < baseStart_1441251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441264 : List Nat := [2, 1, 1, 1, 3, 4, 1, 4, 2, 3]
def baseStart_1441264 : Nat := 118140960795 + 1441264 * 2 ^ 59
def prefixEnd_1441264 : Nat := 4983230072969 + 3 ^ 40 * 1441264 * 2
def baseEnd_1441264 : Nat := 493374121347836187781169

theorem tailTrace_1441264 : CollatzResearch.WordTrace tailWord_1441264 prefixEnd_1441264 493374121347836187781169 := by
  unfold tailWord_1441264
  simp only [CollatzResearch.WordTrace]
  refine ⟨26283608325277075569721423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35044811100369434092961897 26283608325277075569721423)
  ·
    refine ⟨39425412487915613354582135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26283608325277075569721423 39425412487915613354582135)
    ·
      refine ⟨59138118731873420031873203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39425412487915613354582135 59138118731873420031873203)
      ·
        refine ⟨88707178097810130047809805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59138118731873420031873203 88707178097810130047809805)
        ·
          refine ⟨33265191786678798767928677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88707178097810130047809805 33265191786678798767928677)
          ·
            refine ⟨6237223460002274768986627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33265191786678798767928677 6237223460002274768986627)
            ·
              refine ⟨9355835190003412153479941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6237223460002274768986627 9355835190003412153479941)
              ·
                refine ⟨1754219098125639778777489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9355835190003412153479941 1754219098125639778777489)
                ·
                  refine ⟨1315664323594229834083117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1754219098125639778777489 1315664323594229834083117)
                  ·
                    refine ⟨493374121347836187781169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1315664323594229834083117 493374121347836187781169)
                    ·
                      rfl

theorem cell22_1441264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 2, 3].length) (baseStart_1441264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441264 prefixEnd_1441264 := by exact prefixLift 1441264
  have htrace : WordTrace (prefixWord ++ tailWord_1441264) baseStart_1441264 baseEnd_1441264 := by
    simpa [prefixWord, tailWord_1441264, baseEnd_1441264] using wordTrace_append hprefix tailTrace_1441264
  have hstable : (prefixWord ++ tailWord_1441264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441264).length < 2 ^ (prefixWord ++ tailWord_1441264).sum := by decide
  have hdescent : baseEnd_1441264 < baseStart_1441264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441266 : List Nat := [3, 2, 1, 4, 1, 2, 1, 4, 4]
def baseStart_1441266 : Nat := 118140960795 + 1441266 * 2 ^ 59
def prefixEnd_1441266 : Nat := 4983230072969 + 3 ^ 40 * 1441266 * 2
def baseEnd_1441266 : Nat := 164458268662902949743721

theorem tailTrace_1441266 : CollatzResearch.WordTrace tailWord_1441266 prefixEnd_1441266 164458268662902949743721 := by
  unfold tailWord_1441266
  simp only [CollatzResearch.WordTrace]
  refine ⟨13141822399136726370253913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35044859731031270320677101 13141822399136726370253913)
  ·
    refine ⟨9856366799352544777690435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13141822399136726370253913 9856366799352544777690435)
    ·
      refine ⟨14784550199028817166535653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9856366799352544777690435 14784550199028817166535653)
      ·
        refine ⟨2772103162317903218725435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14784550199028817166535653 2772103162317903218725435)
        ·
          refine ⟨4158154743476854828088153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2772103162317903218725435 4158154743476854828088153)
          ·
            refine ⟨3118616057607641121066115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4158154743476854828088153 3118616057607641121066115)
            ·
              refine ⟨4677924086411461681599173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3118616057607641121066115 4677924086411461681599173)
              ·
                refine ⟨877110766202149065299845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4677924086411461681599173 877110766202149065299845)
                ·
                  refine ⟨164458268662902949743721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 877110766202149065299845 164458268662902949743721)
                  ·
                    rfl

theorem cell22_1441266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_1441266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441266 prefixEnd_1441266 := by exact prefixLift 1441266
  have htrace : WordTrace (prefixWord ++ tailWord_1441266) baseStart_1441266 baseEnd_1441266 := by
    simpa [prefixWord, tailWord_1441266, baseEnd_1441266] using wordTrace_append hprefix tailTrace_1441266
  have hstable : (prefixWord ++ tailWord_1441266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441266).length < 2 ^ (prefixWord ++ tailWord_1441266).sum := by decide
  have hdescent : baseEnd_1441266 < baseStart_1441266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441277 : List Nat := [1, 4, 1, 1, 1, 4, 3, 7]
def baseStart_1441277 : Nat := 118140960795 + 1441277 * 2 ^ 59
def prefixEnd_1441277 : Nat := 4983230072969 + 3 ^ 40 * 1441277 * 2
def baseEnd_1441277 : Nat := 54819841279278720800681

theorem tailTrace_1441277 : CollatzResearch.WordTrace tailWord_1441277 prefixEnd_1441277 54819841279278720800681 := by
  unfold tailWord_1441277
  simp only [CollatzResearch.WordTrace]
  refine ⟨52567690799507054359666085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35045127199671369573110723 52567690799507054359666085)
  ·
    refine ⟨9856442024907572692437391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52567690799507054359666085 9856442024907572692437391)
    ·
      refine ⟨14784663037361359038656087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9856442024907572692437391 14784663037361359038656087)
      ·
        refine ⟨22176994556042038557984131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14784663037361359038656087 22176994556042038557984131)
        ·
          refine ⟨33265491834063057836976197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22176994556042038557984131 33265491834063057836976197)
          ·
            refine ⟨6237279718886823344433037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33265491834063057836976197 6237279718886823344433037)
            ·
              refine ⟨2338979894582558754162389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6237279718886823344433037 2338979894582558754162389)
              ·
                refine ⟨54819841279278720800681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2338979894582558754162389 54819841279278720800681)
                ·
                  rfl

theorem cell22_1441277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 7].length) (baseStart_1441277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441277 prefixEnd_1441277 := by exact prefixLift 1441277
  have htrace : WordTrace (prefixWord ++ tailWord_1441277) baseStart_1441277 baseEnd_1441277 := by
    simpa [prefixWord, tailWord_1441277, baseEnd_1441277] using wordTrace_append hprefix tailTrace_1441277
  have hstable : (prefixWord ++ tailWord_1441277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441277).length < 2 ^ (prefixWord ++ tailWord_1441277).sum := by decide
  have hdescent : baseEnd_1441277 < baseStart_1441277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441309 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 5, 3]
def baseStart_1441309 : Nat := 118140960795 + 1441309 * 2 ^ 59
def prefixEnd_1441309 : Nat := 4983230072969 + 3 ^ 40 * 1441309 * 2
def baseEnd_1441309 : Nat := 493389525767471070406031

theorem tailTrace_1441309 : CollatzResearch.WordTrace tailWord_1441309 prefixEnd_1441309 493389525767471070406031 := by
  unfold tailWord_1441309
  simp only [CollatzResearch.WordTrace]
  refine ⟨52568857935391123824830981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35045905290260749216553987 52568857935391123824830981)
  ·
    refine ⟨9856660862885835717155809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52568857935391123824830981 9856660862885835717155809)
    ·
      refine ⟨7392495647164376787866857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9856660862885835717155809 7392495647164376787866857)
      ·
        refine ⟨5544371735373282590900143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7392495647164376787866857 5544371735373282590900143)
        ·
          refine ⟨8316557603059923886350215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5544371735373282590900143 8316557603059923886350215)
          ·
            refine ⟨12474836404589885829525323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8316557603059923886350215 12474836404589885829525323)
            ·
              refine ⟨18712254606884828744287985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12474836404589885829525323 18712254606884828744287985)
              ·
                refine ⟨14034190955163621558215989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18712254606884828744287985 14034190955163621558215989)
                ·
                  refine ⟨1315705402046589521082749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14034190955163621558215989 1315705402046589521082749)
                  ·
                    refine ⟨493389525767471070406031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1315705402046589521082749 493389525767471070406031)
                    ·
                      rfl

theorem cell22_1441309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_1441309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441309 prefixEnd_1441309 := by exact prefixLift 1441309
  have htrace : WordTrace (prefixWord ++ tailWord_1441309) baseStart_1441309 baseEnd_1441309 := by
    simpa [prefixWord, tailWord_1441309, baseEnd_1441309] using wordTrace_append hprefix tailTrace_1441309
  have hstable : (prefixWord ++ tailWord_1441309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441309).length < 2 ^ (prefixWord ++ tailWord_1441309).sum := by decide
  have hdescent : baseEnd_1441309 < baseStart_1441309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441326 : List Nat := [4, 1, 3, 1, 2, 1, 1, 3, 3, 3]
def baseStart_1441326 : Nat := 118140960795 + 1441326 * 2 ^ 59
def prefixEnd_1441326 : Nat := 4983230072969 + 3 ^ 40 * 1441326 * 2
def baseEnd_1441326 : Nat := 493395345214888692730979

theorem tailTrace_1441326 : CollatzResearch.WordTrace tailWord_1441326 prefixEnd_1441326 493395345214888692730979 := by
  unfold tailWord_1441326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6571184747041191966024979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35046318650886357152133221 6571184747041191966024979)
  ·
    refine ⟨9856777120561787949037469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6571184747041191966024979 9856777120561787949037469)
    ·
      refine ⟨3696291420210670480889051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9856777120561787949037469 3696291420210670480889051)
      ·
        refine ⟨5544437130316005721333577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3696291420210670480889051 5544437130316005721333577)
        ·
          refine ⟨4158327847737004291000183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5544437130316005721333577 4158327847737004291000183)
          ·
            refine ⟨6237491771605506436500275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4158327847737004291000183 6237491771605506436500275)
            ·
              refine ⟨9356237657408259654750413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6237491771605506436500275 9356237657408259654750413)
              ·
                refine ⟨3508589121528097370531405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9356237657408259654750413 3508589121528097370531405)
                ·
                  refine ⟨1315720920573036513949277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3508589121528097370531405 1315720920573036513949277)
                  ·
                    refine ⟨493395345214888692730979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1315720920573036513949277 493395345214888692730979)
                    ·
                      rfl

theorem cell22_1441326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_1441326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441326 prefixEnd_1441326 := by exact prefixLift 1441326
  have htrace : WordTrace (prefixWord ++ tailWord_1441326) baseStart_1441326 baseEnd_1441326 := by
    simpa [prefixWord, tailWord_1441326, baseEnd_1441326] using wordTrace_append hprefix tailTrace_1441326
  have hstable : (prefixWord ++ tailWord_1441326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441326).length < 2 ^ (prefixWord ++ tailWord_1441326).sum := by decide
  have hdescent : baseEnd_1441326 < baseStart_1441326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441390 : List Nat := [4, 1, 2, 2, 4, 1, 2, 1, 5]
def baseStart_1441390 : Nat := 118140960795 + 1441390 * 2 ^ 59
def prefixEnd_1441390 : Nat := 4983230072969 + 3 ^ 40 * 1441390 * 2
def baseEnd_1441390 : Nat := 164472417907604619710261

theorem tailTrace_1441390 : CollatzResearch.WordTrace tailWord_1441390 prefixEnd_1441390 164472417907604619710261 := by
  unfold tailWord_1441390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6571476531012209332316203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35047874832065116439019749 6571476531012209332316203)
  ·
    refine ⟨9857214796518313998474305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6571476531012209332316203 9857214796518313998474305)
    ·
      refine ⟨7392911097388735498855729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9857214796518313998474305 7392911097388735498855729)
      ·
        refine ⟨5544683323041551624141797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7392911097388735498855729 5544683323041551624141797)
        ·
          refine ⟨1039628123070290929526587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5544683323041551624141797 1039628123070290929526587)
          ·
            refine ⟨1559442184605436394289881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039628123070290929526587 1559442184605436394289881)
            ·
              refine ⟨1169581638454077295717411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1559442184605436394289881 1169581638454077295717411)
              ·
                refine ⟨1754372457681115943576117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1169581638454077295717411 1754372457681115943576117)
                ·
                  refine ⟨164472417907604619710261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1754372457681115943576117 164472417907604619710261)
                  ·
                    rfl

theorem cell22_1441390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_1441390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441390 prefixEnd_1441390 := by exact prefixLift 1441390
  have htrace : WordTrace (prefixWord ++ tailWord_1441390) baseStart_1441390 baseEnd_1441390 := by
    simpa [prefixWord, tailWord_1441390, baseEnd_1441390] using wordTrace_append hprefix tailTrace_1441390
  have hstable : (prefixWord ++ tailWord_1441390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441390).length < 2 ^ (prefixWord ++ tailWord_1441390).sum := by decide
  have hdescent : baseEnd_1441390 < baseStart_1441390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441489 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 2, 5]
def baseStart_1441489 : Nat := 118140960795 + 1441489 * 2 ^ 59
def prefixEnd_1441489 : Nat := 4983230072969 + 3 ^ 40 * 1441489 * 2
def baseEnd_1441489 : Nat := 493451143446010600905479

theorem tailTrace_1441489 : CollatzResearch.WordTrace tailWord_1441489 prefixEnd_1441489 493451143446010600905479 := by
  unfold tailWord_1441489
  simp only [CollatzResearch.WordTrace]
  refine ⟨52575423074739014566383521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35050282049826009710922347 52575423074739014566383521)
  ·
    refine ⟨39431567306054260924787641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52575423074739014566383521 39431567306054260924787641)
    ·
      refine ⟨29573675479540695693590731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39431567306054260924787641 29573675479540695693590731)
      ·
        refine ⟨44360513219311043540386097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29573675479540695693590731 44360513219311043540386097)
        ·
          refine ⟨33270384914483282655289573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44360513219311043540386097 33270384914483282655289573)
          ·
            refine ⟨6238197171465615497866795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33270384914483282655289573 6238197171465615497866795)
            ·
              refine ⟨9357295757198423246800193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6238197171465615497866795 9357295757198423246800193)
              ·
                refine ⟨7017971817898817435100145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9357295757198423246800193 7017971817898817435100145)
                ·
                  refine ⟨5263478863424113076325109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7017971817898817435100145 5263478863424113076325109)
                  ·
                    refine ⟨493451143446010600905479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5263478863424113076325109 493451143446010600905479)
                    ·
                      rfl

theorem cell22_1441489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_1441489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441489 prefixEnd_1441489 := by exact prefixLift 1441489
  have htrace : WordTrace (prefixWord ++ tailWord_1441489) baseStart_1441489 baseEnd_1441489 := by
    simpa [prefixWord, tailWord_1441489, baseEnd_1441489] using wordTrace_append hprefix tailTrace_1441489
  have hstable : (prefixWord ++ tailWord_1441489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441489).length < 2 ^ (prefixWord ++ tailWord_1441489).sum := by decide
  have hdescent : baseEnd_1441489 < baseStart_1441489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441504 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 5, 4]
def baseStart_1441504 : Nat := 118140960795 + 1441504 * 2 ^ 59
def prefixEnd_1441504 : Nat := 4983230072969 + 3 ^ 40 * 1441504 * 2
def baseEnd_1441504 : Nat := 493456278252555561780433

theorem tailTrace_1441504 : CollatzResearch.WordTrace tailWord_1441504 prefixEnd_1441504 493456278252555561780433 := by
  unfold tailWord_1441504
  simp only [CollatzResearch.WordTrace]
  refine ⟨26287985084842336064089783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35050646779789781418786377 26287985084842336064089783)
  ·
    refine ⟨39431977627263504096134675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26287985084842336064089783 39431977627263504096134675)
    ·
      refine ⟨59147966440895256144202013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39431977627263504096134675 59147966440895256144202013)
      ·
        refine ⟨22180487415335721054075755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59147966440895256144202013 22180487415335721054075755)
        ·
          refine ⟨33270731123003581581113633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22180487415335721054075755 33270731123003581581113633)
          ·
            refine ⟨24953048342252686185835225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33270731123003581581113633 24953048342252686185835225)
            ·
              refine ⟨18714786256689514639376419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24953048342252686185835225 18714786256689514639376419)
              ·
                refine ⟨28072179385034271959064629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18714786256689514639376419 28072179385034271959064629)
                ·
                  refine ⟨2631766817346962996162309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28072179385034271959064629 2631766817346962996162309)
                  ·
                    refine ⟨493456278252555561780433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2631766817346962996162309 493456278252555561780433)
                    ·
                      rfl

theorem cell22_1441504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_1441504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441504 prefixEnd_1441504 := by exact prefixLift 1441504
  have htrace : WordTrace (prefixWord ++ tailWord_1441504) baseStart_1441504 baseEnd_1441504 := by
    simpa [prefixWord, tailWord_1441504, baseEnd_1441504] using wordTrace_append hprefix tailTrace_1441504
  have hstable : (prefixWord ++ tailWord_1441504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441504).length < 2 ^ (prefixWord ++ tailWord_1441504).sum := by decide
  have hdescent : baseEnd_1441504 < baseStart_1441504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441519 : List Nat := [1, 1, 2, 1, 5, 1, 1, 4, 6]
def baseStart_1441519 : Nat := 118140960795 + 1441519 * 2 ^ 59
def prefixEnd_1441519 : Nat := 4983230072969 + 3 ^ 40 * 1441519 * 2
def baseEnd_1441519 : Nat := 164487137686366840885129

theorem tailTrace_1441519 : CollatzResearch.WordTrace tailWord_1441519 prefixEnd_1441519 164487137686366840885129 := by
  unfold tailWord_1441519
  simp only [CollatzResearch.WordTrace]
  refine ⟨52576517264630329689975611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35051011509753553126650407 52576517264630329689975611)
  ·
    refine ⟨78864775896945494534963417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52576517264630329689975611 78864775896945494534963417)
    ·
      refine ⟨59148581922709120901222563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78864775896945494534963417 59148581922709120901222563)
      ·
        refine ⟨88722872884063681351833845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59148581922709120901222563 88722872884063681351833845)
        ·
          refine ⟨8317769332880970126734423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88722872884063681351833845 8317769332880970126734423)
          ·
            refine ⟨12476653999321455190101635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8317769332880970126734423 12476653999321455190101635)
            ·
              refine ⟨18714980998982182785152453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12476653999321455190101635 18714980998982182785152453)
              ·
                refine ⟨3509058937309159272216085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18714980998982182785152453 3509058937309159272216085)
                ·
                  refine ⟨164487137686366840885129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3509058937309159272216085 164487137686366840885129)
                  ·
                    rfl

theorem cell22_1441519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 6].length) (baseStart_1441519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441519 prefixEnd_1441519 := by exact prefixLift 1441519
  have htrace : WordTrace (prefixWord ++ tailWord_1441519) baseStart_1441519 baseEnd_1441519 := by
    simpa [prefixWord, tailWord_1441519, baseEnd_1441519] using wordTrace_append hprefix tailTrace_1441519
  have hstable : (prefixWord ++ tailWord_1441519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441519).length < 2 ^ (prefixWord ++ tailWord_1441519).sum := by decide
  have hdescent : baseEnd_1441519 < baseStart_1441519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441521 : List Nat := [1, 2, 2, 2, 2, 3, 1, 4, 1, 4]
def baseStart_1441521 : Nat := 118140960795 + 1441521 * 2 ^ 59
def prefixEnd_1441521 : Nat := 4983230072969 + 3 ^ 40 * 1441521 * 2
def baseEnd_1441521 : Nat := 493462097699973184105381

theorem tailTrace_1441521 : CollatzResearch.WordTrace tailWord_1441521 prefixEnd_1441521 493462097699973184105381 := by
  unfold tailWord_1441521
  simp only [CollatzResearch.WordTrace]
  refine ⟨52576590210623084031548417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35051060140415389354365611 52576590210623084031548417)
  ·
    refine ⟨39432442657967313023661313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52576590210623084031548417 39432442657967313023661313)
    ·
      refine ⟨29574331993475484767745985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39432442657967313023661313 29574331993475484767745985)
      ·
        refine ⟨22180748995106613575809489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29574331993475484767745985 22180748995106613575809489)
        ·
          refine ⟨16635561746329960181857117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22180748995106613575809489 16635561746329960181857117)
          ·
            refine ⟨6238335654873735068196419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16635561746329960181857117 6238335654873735068196419)
            ·
              refine ⟨9357503482310602602294629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6238335654873735068196419 9357503482310602602294629)
              ·
                refine ⟨1754531902933237987930243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9357503482310602602294629 1754531902933237987930243)
                ·
                  refine ⟨2631797854399856981895365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1754531902933237987930243 2631797854399856981895365)
                  ·
                    refine ⟨493462097699973184105381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2631797854399856981895365 493462097699973184105381)
                    ·
                      rfl

theorem cell22_1441521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_1441521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441521 prefixEnd_1441521 := by exact prefixLift 1441521
  have htrace : WordTrace (prefixWord ++ tailWord_1441521) baseStart_1441521 baseEnd_1441521 := by
    simpa [prefixWord, tailWord_1441521, baseEnd_1441521] using wordTrace_append hprefix tailTrace_1441521
  have hstable : (prefixWord ++ tailWord_1441521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441521).length < 2 ^ (prefixWord ++ tailWord_1441521).sum := by decide
  have hdescent : baseEnd_1441521 < baseStart_1441521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441538 : List Nat := [3, 4, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_1441538 : Nat := 118140960795 + 1441538 * 2 ^ 59
def prefixEnd_1441538 : Nat := 4983230072969 + 3 ^ 40 * 1441538 * 2
def baseEnd_1441538 : Nat := 493467917147390806430329

theorem tailTrace_1441538 : CollatzResearch.WordTrace tailWord_1441538 prefixEnd_1441538 493467917147390806430329 := by
  unfold tailWord_1441538
  simp only [CollatzResearch.WordTrace]
  refine ⟨13144302562890373983729317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35051473501040997289944845 13144302562890373983729317)
  ·
    refine ⟨2464556730541945121949247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13144302562890373983729317 2464556730541945121949247)
    ·
      refine ⟨3696835095812917682923871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2464556730541945121949247 3696835095812917682923871)
      ·
        refine ⟨5545252643719376524385807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3696835095812917682923871 5545252643719376524385807)
        ·
          refine ⟨8317878965579064786578711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5545252643719376524385807 8317878965579064786578711)
          ·
            refine ⟨12476818448368597179868067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8317878965579064786578711 12476818448368597179868067)
            ·
              refine ⟨18715227672552895769802101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12476818448368597179868067 18715227672552895769802101)
              ·
                refine ⟨1754552594301833978418947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18715227672552895769802101 1754552594301833978418947)
                ·
                  refine ⟨2631828891452750967628421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1754552594301833978418947 2631828891452750967628421)
                  ·
                    refine ⟨493467917147390806430329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2631828891452750967628421 493467917147390806430329)
                    ·
                      rfl

theorem cell22_1441538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_1441538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441538 prefixEnd_1441538 := by exact prefixLift 1441538
  have htrace : WordTrace (prefixWord ++ tailWord_1441538) baseStart_1441538 baseEnd_1441538 := by
    simpa [prefixWord, tailWord_1441538, baseEnd_1441538] using wordTrace_append hprefix tailTrace_1441538
  have hstable : (prefixWord ++ tailWord_1441538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441538).length < 2 ^ (prefixWord ++ tailWord_1441538).sum := by decide
  have hdescent : baseEnd_1441538 < baseStart_1441538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441568 : List Nat := [2, 1, 1, 5, 1, 1, 3, 3, 2, 3]
def baseStart_1441568 : Nat := 118140960795 + 1441568 * 2 ^ 59
def prefixEnd_1441568 : Nat := 4983230072969 + 3 ^ 40 * 1441568 * 2
def baseEnd_1441568 : Nat := 493478186760480728180237

theorem tailTrace_1441568 : CollatzResearch.WordTrace tailWord_1441568 prefixEnd_1441568 493478186760480728180237 := by
  unfold tailWord_1441568
  simp only [CollatzResearch.WordTrace]
  refine ⟨26289152220726405529254679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35052202960968540705672905 26289152220726405529254679)
  ·
    refine ⟨39433728331089608293882019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26289152220726405529254679 39433728331089608293882019)
    ·
      refine ⟨59150592496634412440823029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39433728331089608293882019 59150592496634412440823029)
      ·
        refine ⟨5545368046559476166327159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59150592496634412440823029 5545368046559476166327159)
        ·
          refine ⟨8318052069839214249490739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5545368046559476166327159 8318052069839214249490739)
          ·
            refine ⟨12477078104758821374236109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8318052069839214249490739 12477078104758821374236109)
            ·
              refine ⟨4678904289284558015338541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12477078104758821374236109 4678904289284558015338541)
              ·
                refine ⟨1754589108481709255751953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4678904289284558015338541 1754589108481709255751953)
                ·
                  refine ⟨1315941831361281941813965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1754589108481709255751953 1315941831361281941813965)
                  ·
                    refine ⟨493478186760480728180237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1315941831361281941813965 493478186760480728180237)
                    ·
                      rfl

theorem cell22_1441568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 2, 3].length) (baseStart_1441568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441568 prefixEnd_1441568 := by exact prefixLift 1441568
  have htrace : WordTrace (prefixWord ++ tailWord_1441568) baseStart_1441568 baseEnd_1441568 := by
    simpa [prefixWord, tailWord_1441568, baseEnd_1441568] using wordTrace_append hprefix tailTrace_1441568
  have hstable : (prefixWord ++ tailWord_1441568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441568).length < 2 ^ (prefixWord ++ tailWord_1441568).sum := by decide
  have hdescent : baseEnd_1441568 < baseStart_1441568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441626 : List Nat := [3, 1, 1, 2, 1, 3, 1, 5, 5]
def baseStart_1441626 : Nat := 118140960795 + 1441626 * 2 ^ 59
def prefixEnd_1441626 : Nat := 4983230072969 + 3 ^ 40 * 1441626 * 2
def baseEnd_1441626 : Nat := 164499347115262636743353

theorem tailTrace_1441626 : CollatzResearch.WordTrace tailWord_1441626 prefixEnd_1441626 164499347115262636743353 := by
  unfold tailWord_1441626
  simp only [CollatzResearch.WordTrace]
  refine ⟨13145104968810671741030183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35053613250161791309413821 13145104968810671741030183)
  ·
    refine ⟨19717657453216007611545275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13145104968810671741030183 19717657453216007611545275)
    ·
      refine ⟨29576486179824011417317913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19717657453216007611545275 29576486179824011417317913)
      ·
        refine ⟨22182364634868008562988435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29576486179824011417317913 22182364634868008562988435)
        ·
          refine ⟨33273546952302012844482653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22182364634868008562988435 33273546952302012844482653)
          ·
            refine ⟨12477580107113254816680995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33273546952302012844482653 12477580107113254816680995)
            ·
              refine ⟨18716370160669882225021493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12477580107113254816680995 18716370160669882225021493)
              ·
                refine ⟨1754659702562801458595765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18716370160669882225021493 1754659702562801458595765)
                ·
                  refine ⟨164499347115262636743353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1754659702562801458595765 164499347115262636743353)
                  ·
                    rfl

theorem cell22_1441626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_1441626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441626 prefixEnd_1441626 := by exact prefixLift 1441626
  have htrace : WordTrace (prefixWord ++ tailWord_1441626) baseStart_1441626 baseEnd_1441626 := by
    simpa [prefixWord, tailWord_1441626, baseEnd_1441626] using wordTrace_append hprefix tailTrace_1441626
  have hstable : (prefixWord ++ tailWord_1441626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441626).length < 2 ^ (prefixWord ++ tailWord_1441626).sum := by decide
  have hdescent : baseEnd_1441626 < baseStart_1441626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441690 : List Nat := [3, 1, 1, 4, 2, 2, 2, 2, 1, 4]
def baseStart_1441690 : Nat := 118140960795 + 1441690 * 2 ^ 59
def prefixEnd_1441690 : Nat := 4983230072969 + 3 ^ 40 * 1441690 * 2
def baseEnd_1441690 : Nat := 493519949853713076629863

theorem tailTrace_1441690 : CollatzResearch.WordTrace tailWord_1441690 prefixEnd_1441690 493519949853713076629863 := by
  unfold tailWord_1441690
  simp only [CollatzResearch.WordTrace]
  refine ⟨13145688536752706473612631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35055169431340550596300349 13145688536752706473612631)
  ·
    refine ⟨19718532805129059710418947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13145688536752706473612631 19718532805129059710418947)
    ·
      refine ⟨29577799207693589565628421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19718532805129059710418947 29577799207693589565628421)
      ·
        refine ⟨5545837351442548043555329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29577799207693589565628421 5545837351442548043555329)
        ·
          refine ⟨4159378013581911032666497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5545837351442548043555329 4159378013581911032666497)
          ·
            refine ⟨3119533510186433274499873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4159378013581911032666497 3119533510186433274499873)
            ·
              refine ⟨2339650132639824955874905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3119533510186433274499873 2339650132639824955874905)
              ·
                refine ⟨1754737599479868716906179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2339650132639824955874905 1754737599479868716906179)
                ·
                  refine ⟨2632106399219803075359269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1754737599479868716906179 2632106399219803075359269)
                  ·
                    refine ⟨493519949853713076629863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2632106399219803075359269 493519949853713076629863)
                    ·
                      rfl

theorem cell22_1441690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_1441690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441690 prefixEnd_1441690 := by exact prefixLift 1441690
  have htrace : WordTrace (prefixWord ++ tailWord_1441690) baseStart_1441690 baseEnd_1441690 := by
    simpa [prefixWord, tailWord_1441690, baseEnd_1441690] using wordTrace_append hprefix tailTrace_1441690
  have hstable : (prefixWord ++ tailWord_1441690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441690).length < 2 ^ (prefixWord ++ tailWord_1441690).sum := by decide
  have hdescent : baseEnd_1441690 < baseStart_1441690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441701 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 6, 4]
def baseStart_1441701 : Nat := 118140960795 + 1441701 * 2 ^ 59
def prefixEnd_1441701 : Nat := 4983230072969 + 3 ^ 40 * 1441701 * 2
def baseEnd_1441701 : Nat := 493523715378512714604829

theorem tailTrace_1441701 : CollatzResearch.WordTrace tailWord_1441701 prefixEnd_1441701 493523715378512714604829 := by
  unfold tailWord_1441701
  simp only [CollatzResearch.WordTrace]
  refine ⟨52583155349970974773100957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35055436899980649848733971 52583155349970974773100957)
  ·
    refine ⟨19718683256239115539912859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52583155349970974773100957 19718683256239115539912859)
    ·
      refine ⟨29578024884358673309869289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19718683256239115539912859 29578024884358673309869289)
      ·
        refine ⟨22183518663269004982401967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29578024884358673309869289 22183518663269004982401967)
        ·
          refine ⟨33275277994903507473602951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22183518663269004982401967 33275277994903507473602951)
          ·
            refine ⟨49912916992355261210404427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33275277994903507473602951 49912916992355261210404427)
            ·
              refine ⟨74869375488532891815606641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49912916992355261210404427 74869375488532891815606641)
              ·
                refine ⟨56152031616399668861704981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74869375488532891815606641 56152031616399668861704981)
                ·
                  refine ⟨2632126482018734477892421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56152031616399668861704981 2632126482018734477892421)
                  ·
                    refine ⟨493523715378512714604829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2632126482018734477892421 493523715378512714604829)
                    ·
                      rfl

theorem cell22_1441701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_1441701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441701 prefixEnd_1441701 := by exact prefixLift 1441701
  have htrace : WordTrace (prefixWord ++ tailWord_1441701) baseStart_1441701 baseEnd_1441701 := by
    simpa [prefixWord, tailWord_1441701, baseEnd_1441701] using wordTrace_append hprefix tailTrace_1441701
  have hstable : (prefixWord ++ tailWord_1441701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441701).length < 2 ^ (prefixWord ++ tailWord_1441701).sum := by decide
  have hdescent : baseEnd_1441701 < baseStart_1441701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441761 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 9]
def baseStart_1441761 : Nat := 118140960795 + 1441761 * 2 ^ 59
def prefixEnd_1441761 : Nat := 4983230072969 + 3 ^ 40 * 1441761 * 2
def baseEnd_1441761 : Nat := 164514751534897519368215

theorem tailTrace_1441761 : CollatzResearch.WordTrace tailWord_1441761 prefixEnd_1441761 164514751534897519368215 := by
  unfold tailWord_1441761
  simp only [CollatzResearch.WordTrace]
  refine ⟨52585343729753605020285137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35056895819835736680190091 52585343729753605020285137)
  ·
    refine ⟨39439007797315203765213853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52585343729753605020285137 39439007797315203765213853)
    ·
      refine ⟨14789627923993201411955195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39439007797315203765213853 14789627923993201411955195)
      ·
        refine ⟨22184441885989802117932793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14789627923993201411955195 22184441885989802117932793)
        ·
          refine ⟨16638331414492351588449595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22184441885989802117932793 16638331414492351588449595)
          ·
            refine ⟨24957497121738527382674393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16638331414492351588449595 24957497121738527382674393)
            ·
              refine ⟨18718122841303895537005795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24957497121738527382674393 18718122841303895537005795)
              ·
                refine ⟨28077184261955843305508693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18718122841303895537005795 28077184261955843305508693)
                ·
                  refine ⟨164514751534897519368215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28077184261955843305508693 164514751534897519368215)
                  ·
                    rfl

theorem cell22_1441761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 9].length) (baseStart_1441761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441761 prefixEnd_1441761 := by exact prefixLift 1441761
  have htrace : WordTrace (prefixWord ++ tailWord_1441761) baseStart_1441761 baseEnd_1441761 := by
    simpa [prefixWord, tailWord_1441761, baseEnd_1441761] using wordTrace_append hprefix tailTrace_1441761
  have hstable : (prefixWord ++ tailWord_1441761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441761).length < 2 ^ (prefixWord ++ tailWord_1441761).sum := by decide
  have hdescent : baseEnd_1441761 < baseStart_1441761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441793 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 2, 5]
def baseStart_1441793 : Nat := 118140960795 + 1441793 * 2 ^ 59
def prefixEnd_1441793 : Nat := 4983230072969 + 3 ^ 40 * 1441793 * 2
def baseEnd_1441793 : Nat := 493555208858655141304547

theorem tailTrace_1441793 : CollatzResearch.WordTrace tailWord_1441793 prefixEnd_1441793 493555208858655141304547 := by
  unfold tailWord_1441793
  simp only [CollatzResearch.WordTrace]
  refine ⟨52586510865637674485450033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35057673910425116323633355 52586510865637674485450033)
  ·
    refine ⟨39439883149228255864087525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52586510865637674485450033 39439883149228255864087525)
    ·
      refine ⟨7394978090480297974516411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39439883149228255864087525 7394978090480297974516411)
      ·
        refine ⟨11092467135720446961774617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7394978090480297974516411 11092467135720446961774617)
        ·
          refine ⟨8319350351790335221330963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11092467135720446961774617 8319350351790335221330963)
          ·
            refine ⟨12479025527685502831996445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8319350351790335221330963 12479025527685502831996445)
            ·
              refine ⟨4679634572882063561998667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12479025527685502831996445 4679634572882063561998667)
              ·
                refine ⟨7019451859323095342998001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4679634572882063561998667 7019451859323095342998001)
                ·
                  refine ⟨5264588894492321507248501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7019451859323095342998001 5264588894492321507248501)
                  ·
                    refine ⟨493555208858655141304547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5264588894492321507248501 493555208858655141304547)
                    ·
                      rfl

theorem cell22_1441793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_1441793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441793 prefixEnd_1441793 := by exact prefixLift 1441793
  have htrace : WordTrace (prefixWord ++ tailWord_1441793) baseStart_1441793 baseEnd_1441793 := by
    simpa [prefixWord, tailWord_1441793, baseEnd_1441793] using wordTrace_append hprefix tailTrace_1441793
  have hstable : (prefixWord ++ tailWord_1441793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441793).length < 2 ^ (prefixWord ++ tailWord_1441793).sum := by decide
  have hdescent : baseEnd_1441793 < baseStart_1441793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441840 : List Nat := [2, 1, 1, 1, 2, 5, 2, 4, 4]
def baseStart_1441840 : Nat := 118140960795 + 1441840 * 2 ^ 59
def prefixEnd_1441840 : Nat := 4983230072969 + 3 ^ 40 * 1441840 * 2
def baseEnd_1441840 : Nat := 164523765973054228459801

theorem tailTrace_1441840 : CollatzResearch.WordTrace tailWord_1441840 prefixEnd_1441840 164523765973054228459801 := by
  unfold tailWord_1441840
  simp only [CollatzResearch.WordTrace]
  refine ⟨26294112548233700756205487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35058816730978267674940649 26294112548233700756205487)
  ·
    refine ⟨39441168822350551134308231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26294112548233700756205487 39441168822350551134308231)
    ·
      refine ⟨59161753233525826701462347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39441168822350551134308231 59161753233525826701462347)
      ·
        refine ⟨88742629850288740052193521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59161753233525826701462347 88742629850288740052193521)
        ·
          refine ⟨66556972387716555039145141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88742629850288740052193521 66556972387716555039145141)
          ·
            refine ⟨6239716161348427034919857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66556972387716555039145141 6239716161348427034919857)
            ·
              refine ⟨4679787121011320276189893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6239716161348427034919857 4679787121011320276189893)
              ·
                refine ⟨877460085189622551785605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4679787121011320276189893 877460085189622551785605)
                ·
                  refine ⟨164523765973054228459801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 877460085189622551785605 164523765973054228459801)
                  ·
                    rfl

theorem cell22_1441840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 4].length) (baseStart_1441840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441840 prefixEnd_1441840 := by exact prefixLift 1441840
  have htrace : WordTrace (prefixWord ++ tailWord_1441840) baseStart_1441840 baseEnd_1441840 := by
    simpa [prefixWord, tailWord_1441840, baseEnd_1441840] using wordTrace_append hprefix tailTrace_1441840
  have hstable : (prefixWord ++ tailWord_1441840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441840).length < 2 ^ (prefixWord ++ tailWord_1441840).sum := by decide
  have hdescent : baseEnd_1441840 < baseStart_1441840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441853 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_1441853 : Nat := 118140960795 + 1441853 * 2 ^ 59
def prefixEnd_1441853 : Nat := 4983230072969 + 3 ^ 40 * 1441853 * 2
def baseEnd_1441853 : Nat := 493575748084834984804363

theorem tailTrace_1441853 : CollatzResearch.WordTrace tailWord_1441853 prefixEnd_1441853 493575748084834984804363 := by
  unfold tailWord_1441853
  simp only [CollatzResearch.WordTrace]
  refine ⟨52588699245420304732634213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35059132830280203155089475 52588699245420304732634213)
  ·
    refine ⟨9860381108516307137368915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52588699245420304732634213 9860381108516307137368915)
    ·
      refine ⟨14790571662774460706053373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9860381108516307137368915 14790571662774460706053373)
      ·
        refine ⟨5546464373540422764770015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14790571662774460706053373 5546464373540422764770015)
        ·
          refine ⟨8319696560310634147155023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5546464373540422764770015 8319696560310634147155023)
          ·
            refine ⟨12479544840465951220732535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8319696560310634147155023 12479544840465951220732535)
            ·
              refine ⟨18719317260698926831098803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12479544840465951220732535 18719317260698926831098803)
              ·
                refine ⟨28078975891048390246648205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18719317260698926831098803 28078975891048390246648205)
                ·
                  refine ⟨10529615959143146342493077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28078975891048390246648205 10529615959143146342493077)
                  ·
                    refine ⟨493575748084834984804363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10529615959143146342493077 493575748084834984804363)
                    ·
                      rfl

theorem cell22_1441853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_1441853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441853 prefixEnd_1441853 := by exact prefixLift 1441853
  have htrace : WordTrace (prefixWord ++ tailWord_1441853) baseStart_1441853 baseEnd_1441853 := by
    simpa [prefixWord, tailWord_1441853, baseEnd_1441853] using wordTrace_append hprefix tailTrace_1441853
  have hstable : (prefixWord ++ tailWord_1441853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441853).length < 2 ^ (prefixWord ++ tailWord_1441853).sum := by decide
  have hdescent : baseEnd_1441853 < baseStart_1441853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441855 : List Nat := [1, 1, 2, 2, 3, 1, 2, 5, 2, 3]
def baseStart_1441855 : Nat := 118140960795 + 1441855 * 2 ^ 59
def prefixEnd_1441855 : Nat := 4983230072969 + 3 ^ 40 * 1441855 * 2
def baseEnd_1441855 : Nat := 493576432725707646254357

theorem tailTrace_1441855 : CollatzResearch.WordTrace tailWord_1441855 prefixEnd_1441855 493576432725707646254357 := by
  unfold tailWord_1441855
  simp only [CollatzResearch.WordTrace]
  refine ⟨52588772191413059074207019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35059181460942039382804679 52588772191413059074207019)
  ·
    refine ⟨78883158287119588611310529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52588772191413059074207019 78883158287119588611310529)
    ·
      refine ⟨59162368715339691458482897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78883158287119588611310529 59162368715339691458482897)
      ·
        refine ⟨44371776536504768593862173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59162368715339691458482897 44371776536504768593862173)
        ·
          refine ⟨16639416201189288222698315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44371776536504768593862173 16639416201189288222698315)
          ·
            refine ⟨24959124301783932334047473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16639416201189288222698315 24959124301783932334047473)
            ·
              refine ⟨18719343226337949250535605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24959124301783932334047473 18719343226337949250535605)
              ·
                refine ⟨1754938427469182742237713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18719343226337949250535605 1754938427469182742237713)
                ·
                  refine ⟨1316203820601887056678285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1754938427469182742237713 1316203820601887056678285)
                  ·
                    refine ⟨493576432725707646254357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1316203820601887056678285 493576432725707646254357)
                    ·
                      rfl

theorem cell22_1441855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 3].length) (baseStart_1441855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441855 prefixEnd_1441855 := by exact prefixLift 1441855
  have htrace : WordTrace (prefixWord ++ tailWord_1441855) baseStart_1441855 baseEnd_1441855 := by
    simpa [prefixWord, tailWord_1441855, baseEnd_1441855] using wordTrace_append hprefix tailTrace_1441855
  have hstable : (prefixWord ++ tailWord_1441855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441855).length < 2 ^ (prefixWord ++ tailWord_1441855).sum := by decide
  have hdescent : baseEnd_1441855 < baseStart_1441855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441874 : List Nat := [3, 2, 2, 1, 4, 2, 1, 3, 4]
def baseStart_1441874 : Nat := 118140960795 + 1441874 * 2 ^ 59
def prefixEnd_1441874 : Nat := 4983230072969 + 3 ^ 40 * 1441874 * 2
def baseEnd_1441874 : Nat := 164527645604665976676433

theorem tailTrace_1441874 : CollatzResearch.WordTrace tailWord_1441874 prefixEnd_1441874 164527645604665976676433 := by
  unfold tailWord_1441874
  simp only [CollatzResearch.WordTrace]
  refine ⟨13147366294586056329787169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35059643452229483546099117 13147366294586056329787169)
  ·
    refine ⟨9860524720939542247340377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13147366294586056329787169 9860524720939542247340377)
    ·
      refine ⟨7395393540704656685505283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9860524720939542247340377 7395393540704656685505283)
      ·
        refine ⟨11093090311056985028257925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7395393540704656685505283 11093090311056985028257925)
        ·
          refine ⟨2079954433323184692798361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11093090311056985028257925 2079954433323184692798361)
          ·
            refine ⟨1559965824992388519598771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2079954433323184692798361 1559965824992388519598771)
            ·
              refine ⟨2339948737488582779398157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1559965824992388519598771 2339948737488582779398157)
              ·
                refine ⟨877480776558218542274309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2339948737488582779398157 877480776558218542274309)
                ·
                  refine ⟨164527645604665976676433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 877480776558218542274309 164527645604665976676433)
                  ·
                    rfl

theorem cell22_1441874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_1441874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441874 prefixEnd_1441874 := by exact prefixLift 1441874
  have htrace : WordTrace (prefixWord ++ tailWord_1441874) baseStart_1441874 baseEnd_1441874 := by
    simpa [prefixWord, tailWord_1441874, baseEnd_1441874] using wordTrace_append hprefix tailTrace_1441874
  have hstable : (prefixWord ++ tailWord_1441874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441874).length < 2 ^ (prefixWord ++ tailWord_1441874).sum := by decide
  have hdescent : baseEnd_1441874 < baseStart_1441874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441885 : List Nat := [1, 4, 4, 1, 1, 1, 10]
def baseStart_1441885 : Nat := 118140960795 + 1441885 * 2 ^ 59
def prefixEnd_1441885 : Nat := 4983230072969 + 3 ^ 40 * 1441885 * 2
def baseEnd_1441885 : Nat := 18280988975511021037195

theorem tailTrace_1441885 : CollatzResearch.WordTrace tailWord_1441885 prefixEnd_1441885 18280988975511021037195 := by
  unfold tailWord_1441885
  simp only [CollatzResearch.WordTrace]
  refine ⟨52589866381304374197799109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35059910920869582798532739 52589866381304374197799109)
  ·
    refine ⟨9860599946494570162087333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52589866381304374197799109 9860599946494570162087333)
    ·
      refine ⟨1848862489967731905391375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9860599946494570162087333 1848862489967731905391375)
      ·
        refine ⟨2773293734951597858087063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1848862489967731905391375 2773293734951597858087063)
        ·
          refine ⟨4159940602427396787130595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2773293734951597858087063 4159940602427396787130595)
          ·
            refine ⟨6239910903641095180695893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4159940602427396787130595 6239910903641095180695893)
            ·
              refine ⟨18280988975511021037195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6239910903641095180695893 18280988975511021037195)
              ·
                rfl

theorem cell22_1441885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 10].length) (baseStart_1441885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441885 prefixEnd_1441885 := by exact prefixLift 1441885
  have htrace : WordTrace (prefixWord ++ tailWord_1441885) baseStart_1441885 baseEnd_1441885 := by
    simpa [prefixWord, tailWord_1441885, baseEnd_1441885] using wordTrace_append hprefix tailTrace_1441885
  have hstable : (prefixWord ++ tailWord_1441885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441885).length < 2 ^ (prefixWord ++ tailWord_1441885).sum := by decide
  have hdescent : baseEnd_1441885 < baseStart_1441885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441942 : List Nat := [5, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_1441942 : Nat := 118140960795 + 1441942 * 2 ^ 59
def prefixEnd_1441942 : Nat := 4983230072969 + 3 ^ 40 * 1441942 * 2
def baseEnd_1441942 : Nat := 164535404867889473109697

theorem tailTrace_1441942 : CollatzResearch.WordTrace tailWord_1441942 prefixEnd_1441942 164535404867889473109697 := by
  unfold tailWord_1441942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3286996583881117058289005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35061296894731915288416053 3286996583881117058289005)
  ·
    refine ⟨1232623718955418896858377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3286996583881117058289005 1232623718955418896858377)
    ·
      refine ⟨924467789216564172643783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1232623718955418896858377 924467789216564172643783)
      ·
        refine ⟨1386701683824846258965675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 924467789216564172643783 1386701683824846258965675)
        ·
          refine ⟨2080052525737269388448513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1386701683824846258965675 2080052525737269388448513)
          ·
            refine ⟨1560039394302952041336385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2080052525737269388448513 1560039394302952041336385)
            ·
              refine ⟨1170029545727214031002289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1560039394302952041336385 1170029545727214031002289)
              ·
                refine ⟨877522159295410523251717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1170029545727214031002289 877522159295410523251717)
                ·
                  refine ⟨164535404867889473109697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 877522159295410523251717 164535404867889473109697)
                  ·
                    rfl

theorem cell22_1441942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_1441942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441942 prefixEnd_1441942 := by exact prefixLift 1441942
  have htrace : WordTrace (prefixWord ++ tailWord_1441942) baseStart_1441942 baseEnd_1441942 := by
    simpa [prefixWord, tailWord_1441942, baseEnd_1441942] using wordTrace_append hprefix tailTrace_1441942
  have hstable : (prefixWord ++ tailWord_1441942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441942).length < 2 ^ (prefixWord ++ tailWord_1441942).sum := by decide
  have hdescent : baseEnd_1441942 < baseStart_1441942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441951 : List Nat := [1, 1, 2, 6, 1, 1, 4, 2, 1, 3]
def baseStart_1441951 : Nat := 118140960795 + 1441951 * 2 ^ 59
def prefixEnd_1441951 : Nat := 4983230072969 + 3 ^ 40 * 1441951 * 2
def baseEnd_1441951 : Nat := 493609295487595395854063

theorem tailTrace_1441951 : CollatzResearch.WordTrace tailWord_1441951 prefixEnd_1441951 493609295487595395854063 := by
  unfold tailWord_1441951
  simp only [CollatzResearch.WordTrace]
  refine ⟨52592273599065267469701707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35061515732710178313134471 52592273599065267469701707)
  ·
    refine ⟨78888410398597901204552561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52592273599065267469701707 78888410398597901204552561)
    ·
      refine ⟨59166307798948425903414421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78888410398597901204552561 59166307798948425903414421)
      ·
        refine ⟨2773420678075707464222551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59166307798948425903414421 2773420678075707464222551)
        ·
          refine ⟨4160131017113561196333827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2773420678075707464222551 4160131017113561196333827)
          ·
            refine ⟨6240196525670341794500741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4160131017113561196333827 6240196525670341794500741)
            ·
              refine ⟨1170036848563189086468889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6240196525670341794500741 1170036848563189086468889)
              ·
                refine ⟨877527636422391814851667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1170036848563189086468889 877527636422391814851667)
                ·
                  refine ⟨1316291454633587722277501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 877527636422391814851667 1316291454633587722277501)
                  ·
                    refine ⟨493609295487595395854063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1316291454633587722277501 493609295487595395854063)
                    ·
                      rfl

theorem cell22_1441951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 1, 3].length) (baseStart_1441951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441951 prefixEnd_1441951 := by exact prefixLift 1441951
  have htrace : WordTrace (prefixWord ++ tailWord_1441951) baseStart_1441951 baseEnd_1441951 := by
    simpa [prefixWord, tailWord_1441951, baseEnd_1441951] using wordTrace_append hprefix tailTrace_1441951
  have hstable : (prefixWord ++ tailWord_1441951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441951).length < 2 ^ (prefixWord ++ tailWord_1441951).sum := by decide
  have hdescent : baseEnd_1441951 < baseStart_1441951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441975 : List Nat := [1, 1, 3, 1, 4, 3, 1, 2, 6]
def baseStart_1441975 : Nat := 118140960795 + 1441975 * 2 ^ 59
def prefixEnd_1441975 : Nat := 4983230072969 + 3 ^ 40 * 1441975 * 2
def baseEnd_1441975 : Nat := 164539170392689111084663

theorem tailTrace_1441975 : CollatzResearch.WordTrace tailWord_1441975 prefixEnd_1441975 164539170392689111084663 := by
  unfold tailWord_1441975
  simp only [CollatzResearch.WordTrace]
  refine ⟨52593148950978319568575379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35062099300652213045716919 52593148950978319568575379)
  ·
    refine ⟨78889723426467479352863069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52593148950978319568575379 78889723426467479352863069)
    ·
      refine ⟨29583646284925304757323651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78889723426467479352863069 29583646284925304757323651)
      ·
        refine ⟨44375469427387957135985477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29583646284925304757323651 44375469427387957135985477)
        ·
          refine ⟨8320400517635241962997277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44375469427387957135985477 8320400517635241962997277)
          ·
            refine ⟨3120150194113215736123979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8320400517635241962997277 3120150194113215736123979)
            ·
              refine ⟨4680225291169823604185969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3120150194113215736123979 4680225291169823604185969)
              ·
                refine ⟨3510168968377367703139477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4680225291169823604185969 3510168968377367703139477)
                ·
                  refine ⟨164539170392689111084663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3510168968377367703139477 164539170392689111084663)
                  ·
                    rfl

theorem cell22_1441975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 6].length) (baseStart_1441975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1441975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1441975 prefixEnd_1441975 := by exact prefixLift 1441975
  have htrace : WordTrace (prefixWord ++ tailWord_1441975) baseStart_1441975 baseEnd_1441975 := by
    simpa [prefixWord, tailWord_1441975, baseEnd_1441975] using wordTrace_append hprefix tailTrace_1441975
  have hstable : (prefixWord ++ tailWord_1441975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441975).length < 2 ^ (prefixWord ++ tailWord_1441975).sum := by decide
  have hdescent : baseEnd_1441975 < baseStart_1441975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442065 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 7]
def baseStart_1442065 : Nat := 118140960795 + 1442065 * 2 ^ 59
def prefixEnd_1442065 : Nat := 4983230072969 + 3 ^ 40 * 1442065 * 2
def baseEnd_1442065 : Nat := 164549440005779032834571

theorem tailTrace_1442065 : CollatzResearch.WordTrace tailWord_1442065 prefixEnd_1442065 164549440005779032834571 := by
  unfold tailWord_1442065
  simp only [CollatzResearch.WordTrace]
  refine ⟨52596431520652264939351649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35064287680434843292901099 52596431520652264939351649)
  ·
    refine ⟨39447323640489198704513737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52596431520652264939351649 39447323640489198704513737)
    ·
      refine ⟨29585492730366899028385303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39447323640489198704513737 29585492730366899028385303)
      ·
        refine ⟨44378239095550348542577955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29585492730366899028385303 44378239095550348542577955)
        ·
          refine ⟨66567358643325522813866933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44378239095550348542577955 66567358643325522813866933)
          ·
            refine ⟨6240689872811767763800025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66567358643325522813866933 6240689872811767763800025)
            ·
              refine ⟨4680517404608825822850019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6240689872811767763800025 4680517404608825822850019)
              ·
                refine ⟨7020776106913238734275029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680517404608825822850019 7020776106913238734275029)
                ·
                  refine ⟨164549440005779032834571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7020776106913238734275029 164549440005779032834571)
                  ·
                    rfl

theorem cell22_1442065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 7].length) (baseStart_1442065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442065 prefixEnd_1442065 := by exact prefixLift 1442065
  have htrace : WordTrace (prefixWord ++ tailWord_1442065) baseStart_1442065 baseEnd_1442065 := by
    simpa [prefixWord, tailWord_1442065, baseEnd_1442065] using wordTrace_append hprefix tailTrace_1442065
  have hstable : (prefixWord ++ tailWord_1442065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442065).length < 2 ^ (prefixWord ++ tailWord_1442065).sum := by decide
  have hdescent : baseEnd_1442065 < baseStart_1442065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442069 : List Nat := [1, 3, 2, 1, 2, 1, 2, 6, 1, 3]
def baseStart_1442069 : Nat := 118140960795 + 1442069 * 2 ^ 59
def prefixEnd_1442069 : Nat := 4983230072969 + 3 ^ 40 * 1442069 * 2
def baseEnd_1442069 : Nat := 493649689299082421403701

theorem tailTrace_1442069 : CollatzResearch.WordTrace tailWord_1442069 prefixEnd_1442069 493649689299082421403701 := by
  unfold tailWord_1442069
  simp only [CollatzResearch.WordTrace]
  refine ⟨52596577412637773622497261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35064384941758515748331507 52596577412637773622497261)
  ·
    refine ⟨19723716529739165108436473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52596577412637773622497261 19723716529739165108436473)
    ·
      refine ⟨14792787397304373831327355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19723716529739165108436473 14792787397304373831327355)
      ·
        refine ⟨22189181095956560746991033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14792787397304373831327355 22189181095956560746991033)
        ·
          refine ⟨16641885821967420560243275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22189181095956560746991033 16641885821967420560243275)
          ·
            refine ⟨24962828732951130840364913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16641885821967420560243275 24962828732951130840364913)
            ·
              refine ⟨18722121549713348130273685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24962828732951130840364913 18722121549713348130273685)
              ·
                refine ⟨877599447642813193606579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18722121549713348130273685 877599447642813193606579)
                ·
                  refine ⟨1316399171464219790409869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 877599447642813193606579 1316399171464219790409869)
                  ·
                    refine ⟨493649689299082421403701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1316399171464219790409869 493649689299082421403701)
                    ·
                      rfl

theorem cell22_1442069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_1442069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442069 prefixEnd_1442069 := by exact prefixLift 1442069
  have htrace : WordTrace (prefixWord ++ tailWord_1442069) baseStart_1442069 baseEnd_1442069 := by
    simpa [prefixWord, tailWord_1442069, baseEnd_1442069] using wordTrace_append hprefix tailTrace_1442069
  have hstable : (prefixWord ++ tailWord_1442069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442069).length < 2 ^ (prefixWord ++ tailWord_1442069).sum := by decide
  have hdescent : baseEnd_1442069 < baseStart_1442069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442116 : List Nat := [2, 3, 4, 1, 2, 1, 2, 2, 5]
def baseStart_1442116 : Nat := 118140960795 + 1442116 * 2 ^ 59
def prefixEnd_1442116 : Nat := 4983230072969 + 3 ^ 40 * 1442116 * 2
def baseEnd_1442116 : Nat := 164555259453196655159519

theorem tailTrace_1442116 : CollatzResearch.WordTrace tailWord_1442116 prefixEnd_1442116 164555259453196655159519 := by
  unfold tailWord_1442116
  simp only [CollatzResearch.WordTrace]
  refine ⟨26299145821733750324729101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35065527762311667099638801 26299145821733750324729101)
  ·
    refine ⟨9862179683150156371773413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26299145821733750324729101 9862179683150156371773413)
    ·
      refine ⟨1849158690590654319707515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9862179683150156371773413 1849158690590654319707515)
      ·
        refine ⟨2773738035885981479561273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1849158690590654319707515 2773738035885981479561273)
        ·
          refine ⟨2080303526914486109670955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2773738035885981479561273 2080303526914486109670955)
          ·
            refine ⟨3120455290371729164506433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080303526914486109670955 3120455290371729164506433)
            ·
              refine ⟨2340341467778796873379825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3120455290371729164506433 2340341467778796873379825)
              ·
                refine ⟨1755256100834097655034869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2340341467778796873379825 1755256100834097655034869)
                ·
                  refine ⟨164555259453196655159519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1755256100834097655034869 164555259453196655159519)
                  ·
                    rfl

theorem cell22_1442116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_1442116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442116 prefixEnd_1442116 := by exact prefixLift 1442116
  have htrace : WordTrace (prefixWord ++ tailWord_1442116) baseStart_1442116 baseEnd_1442116 := by
    simpa [prefixWord, tailWord_1442116, baseEnd_1442116] using wordTrace_append hprefix tailTrace_1442116
  have hstable : (prefixWord ++ tailWord_1442116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442116).length < 2 ^ (prefixWord ++ tailWord_1442116).sum := by decide
  have hdescent : baseEnd_1442116 < baseStart_1442116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442157 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_1442157 : Nat := 118140960795 + 1442157 * 2 ^ 59
def prefixEnd_1442157 : Nat := 4983230072969 + 3 ^ 40 * 1442157 * 2
def baseEnd_1442157 : Nat := 493679813497479525203431

theorem tailTrace_1442157 : CollatzResearch.WordTrace tailWord_1442157 prefixEnd_1442157 493679813497479525203431 := by
  unfold tailWord_1442157
  simp only [CollatzResearch.WordTrace]
  refine ⟨52599787036318964651700725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35066524690879309767800483 52599787036318964651700725)
  ·
    refine ⟨4931230034654902936096943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52599787036318964651700725 4931230034654902936096943)
    ·
      refine ⟨7396845051982354404145415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4931230034654902936096943 7396845051982354404145415)
      ·
        refine ⟨11095267577973531606218123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7396845051982354404145415 11095267577973531606218123)
        ·
          refine ⟨16642901366960297409327185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11095267577973531606218123 16642901366960297409327185)
          ·
            refine ⟨12482176025220223056995389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16642901366960297409327185 12482176025220223056995389)
            ·
              refine ⟨4680816009457583646373271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12482176025220223056995389 4680816009457583646373271)
              ·
                refine ⟨7021224014186375469559907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680816009457583646373271 7021224014186375469559907)
                ·
                  refine ⟨10531836021279563204339861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7021224014186375469559907 10531836021279563204339861)
                  ·
                    refine ⟨493679813497479525203431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10531836021279563204339861 493679813497479525203431)
                    ·
                      rfl

theorem cell22_1442157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_1442157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442157 prefixEnd_1442157 := by exact prefixLift 1442157
  have htrace : WordTrace (prefixWord ++ tailWord_1442157) baseStart_1442157 baseEnd_1442157 := by
    simpa [prefixWord, tailWord_1442157, baseEnd_1442157] using wordTrace_append hprefix tailTrace_1442157
  have hstable : (prefixWord ++ tailWord_1442157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442157).length < 2 ^ (prefixWord ++ tailWord_1442157).sum := by decide
  have hdescent : baseEnd_1442157 < baseStart_1442157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442206 : List Nat := [4, 3, 1, 2, 1, 1, 4, 6]
def baseStart_1442206 : Nat := 118140960795 + 1442206 * 2 ^ 59
def prefixEnd_1442206 : Nat := 4983230072969 + 3 ^ 40 * 1442206 * 2
def baseEnd_1442206 : Nat := 54855176355428858969809

theorem tailTrace_1442206 : CollatzResearch.WordTrace tailWord_1442206 prefixEnd_1442206 54855176355428858969809 := by
  unfold tailWord_1442206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6575196776642680752529309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35067716142094297346822981 6575196776642680752529309)
  ·
    refine ⟨2465698791241005282198491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6575196776642680752529309 2465698791241005282198491)
    ·
      refine ⟨3698548186861507923297737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2465698791241005282198491 3698548186861507923297737)
      ·
        refine ⟨2773911140146130942473303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3698548186861507923297737 2773911140146130942473303)
        ·
          refine ⟨4160866710219196413709955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2773911140146130942473303 4160866710219196413709955)
          ·
            refine ⟨6241300065328794620564933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4160866710219196413709955 6241300065328794620564933)
            ·
              refine ⟨1170243762249148991355925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6241300065328794620564933 1170243762249148991355925)
              ·
                refine ⟨54855176355428858969809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1170243762249148991355925 54855176355428858969809)
                ·
                  rfl

theorem cell22_1442206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_1442206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442206 prefixEnd_1442206 := by exact prefixLift 1442206
  have htrace : WordTrace (prefixWord ++ tailWord_1442206) baseStart_1442206 baseEnd_1442206 := by
    simpa [prefixWord, tailWord_1442206, baseEnd_1442206] using wordTrace_append hprefix tailTrace_1442206
  have hstable : (prefixWord ++ tailWord_1442206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442206).length < 2 ^ (prefixWord ++ tailWord_1442206).sum := by decide
  have hdescent : baseEnd_1442206 < baseStart_1442206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442294 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_1442294 : Nat := 118140960795 + 1442294 * 2 ^ 59
def prefixEnd_1442294 : Nat := 4983230072969 + 3 ^ 40 * 1442294 * 2
def baseEnd_1442294 : Nat := 493726711397256834528011

theorem tailTrace_1442294 : CollatzResearch.WordTrace tailWord_1442294 prefixEnd_1442294 493726711397256834528011 := by
  unfold tailWord_1442294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3287798989801414815589871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35069855891215091366291957 3287798989801414815589871)
  ·
    refine ⟨4931698484702122223384807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3287798989801414815589871 4931698484702122223384807)
    ·
      refine ⟨7397547727053183335077211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4931698484702122223384807 7397547727053183335077211)
      ·
        refine ⟨11096321590579775002615817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7397547727053183335077211 11096321590579775002615817)
        ·
          refine ⟨8322241192934831251961863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11096321590579775002615817 8322241192934831251961863)
          ·
            refine ⟨12483361789402246877942795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8322241192934831251961863 12483361789402246877942795)
            ·
              refine ⟨18725042684103370316914193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12483361789402246877942795 18725042684103370316914193)
              ·
                refine ⟨14043782013077527737685645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18725042684103370316914193 14043782013077527737685645)
                ·
                  refine ⟨5266418254904072901632117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14043782013077527737685645 5266418254904072901632117)
                  ·
                    refine ⟨493726711397256834528011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5266418254904072901632117 493726711397256834528011)
                    ·
                      rfl

theorem cell22_1442294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_1442294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442294 prefixEnd_1442294 := by exact prefixLift 1442294
  have htrace : WordTrace (prefixWord ++ tailWord_1442294) baseStart_1442294 baseEnd_1442294 := by
    simpa [prefixWord, tailWord_1442294, baseEnd_1442294] using wordTrace_append hprefix tailTrace_1442294
  have hstable : (prefixWord ++ tailWord_1442294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442294).length < 2 ^ (prefixWord ++ tailWord_1442294).sum := by decide
  have hdescent : baseEnd_1442294 < baseStart_1442294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442311 : List Nat := [1, 1, 4, 3, 3, 1, 2, 1, 1, 5]
def baseStart_1442311 : Nat := 118140960795 + 1442311 * 2 ^ 59
def prefixEnd_1442311 : Nat := 4983230072969 + 3 ^ 40 * 1442311 * 2
def baseEnd_1442311 : Nat := 493732530844674456852959

theorem tailTrace_1442311 : CollatzResearch.WordTrace tailWord_1442311 prefixEnd_1442311 493732530844674456852959 := by
  unfold tailWord_1442311
  simp only [CollatzResearch.WordTrace]
  refine ⟨52605403877761048952806787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35070269251840699301871191 52605403877761048952806787)
  ·
    refine ⟨78908105816641573429210181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52605403877761048952806787 78908105816641573429210181)
    ·
      refine ⟨14795269840620295017976909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78908105816641573429210181 14795269840620295017976909)
      ·
        refine ⟨5548226190232610631741341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14795269840620295017976909 5548226190232610631741341)
        ·
          refine ⟨2080584821337228986903003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5548226190232610631741341 2080584821337228986903003)
          ·
            refine ⟨3120877232005843480354505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080584821337228986903003 3120877232005843480354505)
            ·
              refine ⟨2340657924004382610265879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3120877232005843480354505 2340657924004382610265879)
              ·
                refine ⟨3510986886006573915398819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2340657924004382610265879 3510986886006573915398819)
                ·
                  refine ⟨5266480329009860873098229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3510986886006573915398819 5266480329009860873098229)
                  ·
                    refine ⟨493732530844674456852959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5266480329009860873098229 493732530844674456852959)
                    ·
                      rfl

theorem cell22_1442311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_1442311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442311 prefixEnd_1442311 := by exact prefixLift 1442311
  have htrace : WordTrace (prefixWord ++ tailWord_1442311) baseStart_1442311 baseEnd_1442311 := by
    simpa [prefixWord, tailWord_1442311, baseEnd_1442311] using wordTrace_append hprefix tailTrace_1442311
  have hstable : (prefixWord ++ tailWord_1442311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442311).length < 2 ^ (prefixWord ++ tailWord_1442311).sum := by decide
  have hdescent : baseEnd_1442311 < baseStart_1442311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442446 : List Nat := [4, 1, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_1442446 : Nat := 118140960795 + 1442446 * 2 ^ 59
def prefixEnd_1442446 : Nat := 4983230072969 + 3 ^ 40 * 1442446 * 2
def baseEnd_1442446 : Nat := 493778744103579104727545

theorem tailTrace_1442446 : CollatzResearch.WordTrace tailWord_1442446 prefixEnd_1442446 493778744103579104727545 := by
  unfold tailWord_1442446
  simp only [CollatzResearch.WordTrace]
  refine ⟨6576290966533995876121399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35073551821514644672647461 6576290966533995876121399)
  ·
    refine ⟨9864436449800993814182099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6576290966533995876121399 9864436449800993814182099)
    ·
      refine ⟨14796654674701490721273149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9864436449800993814182099 14796654674701490721273149)
      ·
        refine ⟨5548745503013059020477431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14796654674701490721273149 5548745503013059020477431)
        ·
          refine ⟨8323118254519588530716147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5548745503013059020477431 8323118254519588530716147)
          ·
            refine ⟨12484677381779382796074221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8323118254519588530716147 12484677381779382796074221)
            ·
              refine ⟨4681754018167268548527833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12484677381779382796074221 4681754018167268548527833)
              ·
                refine ⟨3511315513625451411395875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4681754018167268548527833 3511315513625451411395875)
                ·
                  refine ⟨5266973270438177117093813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3511315513625451411395875 5266973270438177117093813)
                  ·
                    refine ⟨493778744103579104727545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5266973270438177117093813 493778744103579104727545)
                    ·
                      rfl

theorem cell22_1442446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_1442446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442446 prefixEnd_1442446 := by exact prefixLift 1442446
  have htrace : WordTrace (prefixWord ++ tailWord_1442446) baseStart_1442446 baseEnd_1442446 := by
    simpa [prefixWord, tailWord_1442446, baseEnd_1442446] using wordTrace_append hprefix tailTrace_1442446
  have hstable : (prefixWord ++ tailWord_1442446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442446).length < 2 ^ (prefixWord ++ tailWord_1442446).sum := by decide
  have hdescent : baseEnd_1442446 < baseStart_1442446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442450 : List Nat := [3, 2, 3, 1, 2, 2, 3, 1, 1, 4]
def baseStart_1442450 : Nat := 118140960795 + 1442450 * 2 ^ 59
def prefixEnd_1442450 : Nat := 4983230072969 + 3 ^ 40 * 1442450 * 2
def baseEnd_1442450 : Nat := 493780113385324427627533

theorem tailTrace_1442450 : CollatzResearch.WordTrace tailWord_1442450 prefixEnd_1442450 493780113385324427627533 := by
  unfold tailWord_1442450
  simp only [CollatzResearch.WordTrace]
  refine ⟨13152618406064368923029201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35073649082838317128077869 13152618406064368923029201)
  ·
    refine ⟨9864463804548276692271901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13152618406064368923029201 9864463804548276692271901)
    ·
      refine ⟨3699173926705603759601963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9864463804548276692271901 3699173926705603759601963)
      ·
        refine ⟨5548760890058405639402945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3699173926705603759601963 5548760890058405639402945)
        ·
          refine ⟨4161570667543804229552209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5548760890058405639402945 4161570667543804229552209)
          ·
            refine ⟨3121178000657853172164157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4161570667543804229552209 3121178000657853172164157)
            ·
              refine ⟨1170441750246694939561559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3121178000657853172164157 1170441750246694939561559)
              ·
                refine ⟨1755662625370042409342339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1170441750246694939561559 1755662625370042409342339)
                ·
                  refine ⟨2633493938055063614013509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1755662625370042409342339 2633493938055063614013509)
                  ·
                    refine ⟨493780113385324427627533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2633493938055063614013509 493780113385324427627533)
                    ·
                      rfl

theorem cell22_1442450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_1442450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442450 prefixEnd_1442450 := by exact prefixLift 1442450
  have htrace : WordTrace (prefixWord ++ tailWord_1442450) baseStart_1442450 baseEnd_1442450 := by
    simpa [prefixWord, tailWord_1442450, baseEnd_1442450] using wordTrace_append hprefix tailTrace_1442450
  have hstable : (prefixWord ++ tailWord_1442450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442450).length < 2 ^ (prefixWord ++ tailWord_1442450).sum := by decide
  have hdescent : baseEnd_1442450 < baseStart_1442450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442461 : List Nat := [1, 4, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_1442461 : Nat := 118140960795 + 1442461 * 2 ^ 59
def prefixEnd_1442461 : Nat := 4983230072969 + 3 ^ 40 * 1442461 * 2
def baseEnd_1442461 : Nat := 493783878910124065602499

theorem tailTrace_1442461 : CollatzResearch.WordTrace tailWord_1442461 prefixEnd_1442461 493783878910124065602499 := by
  unfold tailWord_1442461
  simp only [CollatzResearch.WordTrace]
  refine ⟨52610874827217624570767237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35073916551478416380511491 52610874827217624570767237)
  ·
    refine ⟨9864539030103304607018857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52610874827217624570767237 9864539030103304607018857)
    ·
      refine ⟨7398404272577478455264143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9864539030103304607018857 7398404272577478455264143)
      ·
        refine ⟨11097606408866217682896215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7398404272577478455264143 11097606408866217682896215)
        ·
          refine ⟨16646409613299326524344323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11097606408866217682896215 16646409613299326524344323)
          ·
            refine ⟨24969614419948989786516485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16646409613299326524344323 24969614419948989786516485)
            ·
              refine ⟨4681802703740435584971841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24969614419948989786516485 4681802703740435584971841)
              ·
                refine ⟨3511352027805326688728881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4681802703740435584971841 3511352027805326688728881)
                ·
                  refine ⟨2633514020853995016546661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3511352027805326688728881 2633514020853995016546661)
                  ·
                    refine ⟨493783878910124065602499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2633514020853995016546661 493783878910124065602499)
                    ·
                      rfl

theorem cell22_1442461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_1442461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442461 prefixEnd_1442461 := by exact prefixLift 1442461
  have htrace : WordTrace (prefixWord ++ tailWord_1442461) baseStart_1442461 baseEnd_1442461 := by
    simpa [prefixWord, tailWord_1442461, baseEnd_1442461] using wordTrace_append hprefix tailTrace_1442461
  have hstable : (prefixWord ++ tailWord_1442461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442461).length < 2 ^ (prefixWord ++ tailWord_1442461).sum := by decide
  have hdescent : baseEnd_1442461 < baseStart_1442461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442489 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 4, 6]
def baseStart_1442489 : Nat := 118140960795 + 1442489 * 2 ^ 59
def prefixEnd_1442489 : Nat := 4983230072969 + 3 ^ 40 * 1442489 * 2
def baseEnd_1442489 : Nat := 493793463882341325902413

theorem tailTrace_1442489 : CollatzResearch.WordTrace tailWord_1442489 prefixEnd_1442489 493793463882341325902413 := by
  unfold tailWord_1442489
  simp only [CollatzResearch.WordTrace]
  refine ⟨52611896071116185352786521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35074597380744123568524347 52611896071116185352786521)
  ·
    refine ⟨39458922053337139014589891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52611896071116185352786521 39458922053337139014589891)
    ·
      refine ⟨59188383080005708521884837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39458922053337139014589891 59188383080005708521884837)
      ·
        refine ⟨11097821827501070347853407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59188383080005708521884837 11097821827501070347853407)
        ·
          refine ⟨16646732741251605521780111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11097821827501070347853407 16646732741251605521780111)
          ·
            refine ⟨24970099111877408282670167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16646732741251605521780111 24970099111877408282670167)
            ·
              refine ⟨37455148667816112424005251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24970099111877408282670167 37455148667816112424005251)
              ·
                refine ⟨56182723001724168636007877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37455148667816112424005251 56182723001724168636007877)
                ·
                  refine ⟨10534260562823281619251477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56182723001724168636007877 10534260562823281619251477)
                  ·
                    refine ⟨493793463882341325902413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10534260562823281619251477 493793463882341325902413)
                    ·
                      rfl

theorem cell22_1442489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_1442489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442489 prefixEnd_1442489 := by exact prefixLift 1442489
  have htrace : WordTrace (prefixWord ++ tailWord_1442489) baseStart_1442489 baseEnd_1442489 := by
    simpa [prefixWord, tailWord_1442489, baseEnd_1442489] using wordTrace_append hprefix tailTrace_1442489
  have hstable : (prefixWord ++ tailWord_1442489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442489).length < 2 ^ (prefixWord ++ tailWord_1442489).sum := by decide
  have hdescent : baseEnd_1442489 < baseStart_1442489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442568 : List Nat := [2, 1, 3, 2, 2, 2, 2, 3, 1, 4]
def baseStart_1442568 : Nat := 118140960795 + 1442568 * 2 ^ 59
def prefixEnd_1442568 : Nat := 4983230072969 + 3 ^ 40 * 1442568 * 2
def baseEnd_1442568 : Nat := 493820507196811453177171

theorem tailTrace_1442568 : CollatzResearch.WordTrace tailWord_1442568 prefixEnd_1442568 493820507196811453177171 := by
  unfold tailWord_1442568
  simp only [CollatzResearch.WordTrace]
  refine ⟨26307388718914990922456179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35076518291886654563274905 26307388718914990922456179)
  ·
    refine ⟨39461083078372486383684269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26307388718914990922456179 39461083078372486383684269)
    ·
      refine ⟨14797906154389682393881601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39461083078372486383684269 14797906154389682393881601)
      ·
        refine ⟨11098429615792261795411201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14797906154389682393881601 11098429615792261795411201)
        ·
          refine ⟨8323822211844196346558401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11098429615792261795411201 8323822211844196346558401)
          ·
            refine ⟨6242866658883147259918801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8323822211844196346558401 6242866658883147259918801)
            ·
              refine ⟨4682149994162360444939101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6242866658883147259918801 4682149994162360444939101)
              ·
                refine ⟨1755806247810885166852163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4682149994162360444939101 1755806247810885166852163)
                ·
                  refine ⟨2633709371716327750278245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1755806247810885166852163 2633709371716327750278245)
                  ·
                    refine ⟨493820507196811453177171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2633709371716327750278245 493820507196811453177171)
                    ·
                      rfl

theorem cell22_1442568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_1442568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442568 prefixEnd_1442568 := by exact prefixLift 1442568
  have htrace : WordTrace (prefixWord ++ tailWord_1442568) baseStart_1442568 baseEnd_1442568 := by
    simpa [prefixWord, tailWord_1442568, baseEnd_1442568] using wordTrace_append hprefix tailTrace_1442568
  have hstable : (prefixWord ++ tailWord_1442568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442568).length < 2 ^ (prefixWord ++ tailWord_1442568).sum := by decide
  have hdescent : baseEnd_1442568 < baseStart_1442568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442589 : List Nat := [1, 4, 2, 4, 2, 1, 2, 1, 5]
def baseStart_1442589 : Nat := 118140960795 + 1442589 * 2 ^ 59
def prefixEnd_1442589 : Nat := 4983230072969 + 3 ^ 40 * 1442589 * 2
def baseEnd_1442589 : Nat := 164609231975324799467369

theorem tailTrace_1442589 : CollatzResearch.WordTrace tailWord_1442589 prefixEnd_1442589 164609231975324799467369 := by
  unfold tailWord_1442589
  simp only [CollatzResearch.WordTrace]
  refine ⟨52615543370753902431426821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35077028913835934954284547 52615543370753902431426821)
  ·
    refine ⟨9865414382016356705892529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52615543370753902431426821 9865414382016356705892529)
    ·
      refine ⟨7399060786512267529419397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9865414382016356705892529 7399060786512267529419397)
      ·
        refine ⟨1387323897471050161766137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7399060786512267529419397 1387323897471050161766137)
        ·
          refine ⟨1040492923103287621324603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1387323897471050161766137 1040492923103287621324603)
          ·
            refine ⟨1560739384654931431986905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040492923103287621324603 1560739384654931431986905)
            ·
              refine ⟨1170554538491198573990179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1560739384654931431986905 1170554538491198573990179)
              ·
                refine ⟨1755831807736797860985269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1170554538491198573990179 1755831807736797860985269)
                ·
                  refine ⟨164609231975324799467369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1755831807736797860985269 164609231975324799467369)
                  ·
                    rfl

theorem cell22_1442589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_1442589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442589 prefixEnd_1442589 := by exact prefixLift 1442589
  have htrace : WordTrace (prefixWord ++ tailWord_1442589) baseStart_1442589 baseEnd_1442589 := by
    simpa [prefixWord, tailWord_1442589, baseEnd_1442589] using wordTrace_append hprefix tailTrace_1442589
  have hstable : (prefixWord ++ tailWord_1442589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442589).length < 2 ^ (prefixWord ++ tailWord_1442589).sum := by decide
  have hdescent : baseEnd_1442589 < baseStart_1442589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442611 : List Nat := [1, 1, 1, 2, 6, 1, 2, 8]
def baseStart_1442611 : Nat := 118140960795 + 1442611 * 2 ^ 59
def prefixEnd_1442611 : Nat := 4983230072969 + 3 ^ 40 * 1442611 * 2
def baseEnd_1442611 : Nat := 54870580775063741594671

theorem tailTrace_1442611 : CollatzResearch.WordTrace tailWord_1442611 prefixEnd_1442611 54870580775063741594671 := by
  unfold tailWord_1442611
  simp only [CollatzResearch.WordTrace]
  refine ⟨52616345776674200188727687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35077563851116133459151791 52616345776674200188727687)
  ·
    refine ⟨78924518665011300283091531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52616345776674200188727687 78924518665011300283091531)
    ·
      refine ⟨118386777997516950424637297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78924518665011300283091531 118386777997516950424637297)
      ·
        refine ⟨88790083498137712818477973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118386777997516950424637297 88790083498137712818477973)
        ·
          refine ⟨4162035163975205288366155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88790083498137712818477973 4162035163975205288366155)
          ·
            refine ⟨6243052745962807932549233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162035163975205288366155 6243052745962807932549233)
            ·
              refine ⟨4682289559472105949411925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6243052745962807932549233 4682289559472105949411925)
              ·
                refine ⟨54870580775063741594671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4682289559472105949411925 54870580775063741594671)
                ·
                  rfl

theorem cell22_1442611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 8].length) (baseStart_1442611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442611 prefixEnd_1442611 := by exact prefixLift 1442611
  have htrace : WordTrace (prefixWord ++ tailWord_1442611) baseStart_1442611 baseEnd_1442611 := by
    simpa [prefixWord, tailWord_1442611, baseEnd_1442611] using wordTrace_append hprefix tailTrace_1442611
  have hstable : (prefixWord ++ tailWord_1442611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442611).length < 2 ^ (prefixWord ++ tailWord_1442611).sum := by decide
  have hdescent : baseEnd_1442611 < baseStart_1442611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442613 : List Nat := [1, 3, 3, 1, 3, 1, 1, 3, 2, 4]
def baseStart_1442613 : Nat := 118140960795 + 1442613 * 2 ^ 59
def prefixEnd_1442613 : Nat := 4983230072969 + 3 ^ 40 * 1442613 * 2
def baseEnd_1442613 : Nat := 493835911616446335802033

theorem tailTrace_1442613 : CollatzResearch.WordTrace tailWord_1442613 prefixEnd_1442613 493835911616446335802033 := by
  unfold tailWord_1442613
  simp only [CollatzResearch.WordTrace]
  refine ⟨52616418722666954530300493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35077612481777969686866995 52616418722666954530300493)
  ·
    refine ⟨19731157021000107948862685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52616418722666954530300493 19731157021000107948862685)
    ·
      refine ⟨7399183882875040480823507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19731157021000107948862685 7399183882875040480823507)
      ·
        refine ⟨11098775824312560721235261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7399183882875040480823507 11098775824312560721235261)
        ·
          refine ⟨4162040934117210270463223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11098775824312560721235261 4162040934117210270463223)
          ·
            refine ⟨6243061401175815405694835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162040934117210270463223 6243061401175815405694835)
            ·
              refine ⟨9364592101763723108542253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6243061401175815405694835 9364592101763723108542253)
              ·
                refine ⟨3511722038161396165703345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9364592101763723108542253 3511722038161396165703345)
                ·
                  refine ⟨2633791528621047124277509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3511722038161396165703345 2633791528621047124277509)
                  ·
                    refine ⟨493835911616446335802033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2633791528621047124277509 493835911616446335802033)
                    ·
                      rfl

theorem cell22_1442613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_1442613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442613 prefixEnd_1442613 := by exact prefixLift 1442613
  have htrace : WordTrace (prefixWord ++ tailWord_1442613) baseStart_1442613 baseEnd_1442613 := by
    simpa [prefixWord, tailWord_1442613, baseEnd_1442613] using wordTrace_append hprefix tailTrace_1442613
  have hstable : (prefixWord ++ tailWord_1442613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442613).length < 2 ^ (prefixWord ++ tailWord_1442613).sum := by decide
  have hdescent : baseEnd_1442613 < baseStart_1442613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442628 : List Nat := [2, 3, 4, 2, 11]
def baseStart_1442628 : Nat := 118140960795 + 1442628 * 2 ^ 59
def prefixEnd_1442628 : Nat := 4983230072969 + 3 ^ 40 * 1442628 * 2
def baseEnd_1442628 : Nat := 2032267680753050603609

theorem tailTrace_1442628 : CollatzResearch.WordTrace tailWord_1442628 prefixEnd_1442628 2032267680753050603609 := by
  unfold tailWord_1442628
  simp only [CollatzResearch.WordTrace]
  refine ⟨26308482908806306046048269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35077977211741741394731025 26308482908806306046048269)
  ·
    refine ⟨9865681090802364767268101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26308482908806306046048269 9865681090802364767268101)
    ·
      refine ⟨1849815204525443393862769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9865681090802364767268101 1849815204525443393862769)
      ·
        refine ⟨1387361403394082545397077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1849815204525443393862769 1387361403394082545397077)
        ·
          refine ⟨2032267680753050603609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1387361403394082545397077 2032267680753050603609)
          ·
            rfl

theorem cell22_1442628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 11].length) (baseStart_1442628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442628 prefixEnd_1442628 := by exact prefixLift 1442628
  have htrace : WordTrace (prefixWord ++ tailWord_1442628) baseStart_1442628 baseEnd_1442628 := by
    simpa [prefixWord, tailWord_1442628, baseEnd_1442628] using wordTrace_append hprefix tailTrace_1442628
  have hstable : (prefixWord ++ tailWord_1442628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442628).length < 2 ^ (prefixWord ++ tailWord_1442628).sum := by decide
  have hdescent : baseEnd_1442628 < baseStart_1442628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442660 : List Nat := [2, 3, 1, 1, 4, 2, 1, 2, 3, 3]
def baseStart_1442660 : Nat := 118140960795 + 1442660 * 2 ^ 59
def prefixEnd_1442660 : Nat := 4983230072969 + 3 ^ 40 * 1442660 * 2
def baseEnd_1442660 : Nat := 493852000676953879876889

theorem tailTrace_1442660 : CollatzResearch.WordTrace tailWord_1442660 prefixEnd_1442660 493852000676953879876889 := by
  unfold tailWord_1442660
  simp only [CollatzResearch.WordTrace]
  refine ⟨26309066476748340778630717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35078755302331121038174289 26309066476748340778630717)
  ·
    refine ⟨9865899928780627791986519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26309066476748340778630717 9865899928780627791986519)
    ·
      refine ⟨14798849893170941687979779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9865899928780627791986519 14798849893170941687979779)
      ·
        refine ⟨22198274839756412531969669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14798849893170941687979779 22198274839756412531969669)
        ·
          refine ⟨4162176532454327349744313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22198274839756412531969669 4162176532454327349744313)
          ·
            refine ⟨3121632399340745512308235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4162176532454327349744313 3121632399340745512308235)
            ·
              refine ⟨4682448599011118268462353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3121632399340745512308235 4682448599011118268462353)
              ·
                refine ⟨3511836449258338701346765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4682448599011118268462353 3511836449258338701346765)
                ·
                  refine ⟨1316938668471877013005037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3511836449258338701346765 1316938668471877013005037)
                  ·
                    refine ⟨493852000676953879876889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1316938668471877013005037 493852000676953879876889)
                    ·
                      rfl

theorem cell22_1442660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_1442660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442660 prefixEnd_1442660 := by exact prefixLift 1442660
  have htrace : WordTrace (prefixWord ++ tailWord_1442660) baseStart_1442660 baseEnd_1442660 := by
    simpa [prefixWord, tailWord_1442660, baseEnd_1442660] using wordTrace_append hprefix tailTrace_1442660
  have hstable : (prefixWord ++ tailWord_1442660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442660).length < 2 ^ (prefixWord ++ tailWord_1442660).sum := by decide
  have hdescent : baseEnd_1442660 < baseStart_1442660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442677 : List Nat := [1, 3, 4, 1, 1, 2, 1, 5, 1, 3]
def baseStart_1442677 : Nat := 118140960795 + 1442677 * 2 ^ 59
def prefixEnd_1442677 : Nat := 4983230072969 + 3 ^ 40 * 1442677 * 2
def baseEnd_1442677 : Nat := 493857820124371502201837

theorem tailTrace_1442677 : CollatzResearch.WordTrace tailWord_1442677 prefixEnd_1442677 493857820124371502201837 := by
  unfold tailWord_1442677
  simp only [CollatzResearch.WordTrace]
  refine ⟨52618752994435093460630285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35079168662956728973753523 52618752994435093460630285)
  ·
    refine ⟨19732032372913160047736357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52618752994435093460630285 19732032372913160047736357)
    ·
      refine ⟨3699756069921217508950567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19732032372913160047736357 3699756069921217508950567)
      ·
        refine ⟨5549634104881826263425851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3699756069921217508950567 5549634104881826263425851)
        ·
          refine ⟨8324451157322739395138777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5549634104881826263425851 8324451157322739395138777)
          ·
            refine ⟨6243338367992054546354083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8324451157322739395138777 6243338367992054546354083)
            ·
              refine ⟨9365007551988081819531125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6243338367992054546354083 9365007551988081819531125)
              ·
                refine ⟨877969457998882670581043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9365007551988081819531125 877969457998882670581043)
                ·
                  refine ⟨1316954186998324005871565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 877969457998882670581043 1316954186998324005871565)
                  ·
                    refine ⟨493857820124371502201837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1316954186998324005871565 493857820124371502201837)
                    ·
                      rfl

theorem cell22_1442677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_1442677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442677 prefixEnd_1442677 := by exact prefixLift 1442677
  have htrace : WordTrace (prefixWord ++ tailWord_1442677) baseStart_1442677 baseEnd_1442677 := by
    simpa [prefixWord, tailWord_1442677, baseEnd_1442677] using wordTrace_append hprefix tailTrace_1442677
  have hstable : (prefixWord ++ tailWord_1442677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442677).length < 2 ^ (prefixWord ++ tailWord_1442677).sum := by decide
  have hdescent : baseEnd_1442677 < baseStart_1442677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442750 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_1442750 : Nat := 118140960795 + 1442750 * 2 ^ 59
def prefixEnd_1442750 : Nat := 4983230072969 + 3 ^ 40 * 1442750 * 2
def baseEnd_1442750 : Nat := 493882809516223645126613

theorem tailTrace_1442750 : CollatzResearch.WordTrace tailWord_1442750 prefixEnd_1442750 493882809516223645126613 := by
  unfold tailWord_1442750
  simp only [CollatzResearch.WordTrace]
  refine ⟨6577676940396328366004713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35080943682113751285358469 6577676940396328366004713)
  ·
    refine ⟨4933257705297246274503535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6577676940396328366004713 4933257705297246274503535)
    ·
      refine ⟨7399886557945869411755303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4933257705297246274503535 7399886557945869411755303)
      ·
        refine ⟨11099829836918804117632955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7399886557945869411755303 11099829836918804117632955)
        ·
          refine ⟨16649744755378206176449433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11099829836918804117632955 16649744755378206176449433)
          ·
            refine ⟨12487308566533654632337075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16649744755378206176449433 12487308566533654632337075)
            ·
              refine ⟨18730962849800481948505613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12487308566533654632337075 18730962849800481948505613)
              ·
                refine ⟨7024111068675180730689605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18730962849800481948505613 7024111068675180730689605)
                ·
                  refine ⟨1317020825376596387004301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7024111068675180730689605 1317020825376596387004301)
                  ·
                    refine ⟨493882809516223645126613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1317020825376596387004301 493882809516223645126613)
                    ·
                      rfl

theorem cell22_1442750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_1442750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442750 prefixEnd_1442750 := by exact prefixLift 1442750
  have htrace : WordTrace (prefixWord ++ tailWord_1442750) baseStart_1442750 baseEnd_1442750 := by
    simpa [prefixWord, tailWord_1442750, baseEnd_1442750] using wordTrace_append hprefix tailTrace_1442750
  have hstable : (prefixWord ++ tailWord_1442750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442750).length < 2 ^ (prefixWord ++ tailWord_1442750).sum := by decide
  have hdescent : baseEnd_1442750 < baseStart_1442750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442752 : List Nat := [2, 1, 1, 2, 3, 4, 3, 2, 4]
def baseStart_1442752 : Nat := 118140960795 + 1442752 * 2 ^ 59
def prefixEnd_1442752 : Nat := 4983230072969 + 3 ^ 40 * 1442752 * 2
def baseEnd_1442752 : Nat := 164627831385698768858869

theorem tailTrace_1442752 : CollatzResearch.WordTrace tailWord_1442752 prefixEnd_1442752 164627831385698768858869 := by
  unfold tailWord_1442752
  simp only [CollatzResearch.WordTrace]
  refine ⟨26310744234581690634805255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35080992312775587513073673 26310744234581690634805255)
  ·
    refine ⟨39466116351872535952207883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26310744234581690634805255 39466116351872535952207883)
    ·
      refine ⟨59199174527808803928311825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39466116351872535952207883 59199174527808803928311825)
      ·
        refine ⟨44399380895856602946233869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59199174527808803928311825 44399380895856602946233869)
        ·
          refine ⟨16649767835946226104837701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44399380895856602946233869 16649767835946226104837701)
          ·
            refine ⟨3121831469239917394657069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16649767835946226104837701 3121831469239917394657069)
            ·
              refine ⟨1170686800964969022996401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3121831469239917394657069 1170686800964969022996401)
              ·
                refine ⟨878015100723726767247301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1170686800964969022996401 878015100723726767247301)
                ·
                  refine ⟨164627831385698768858869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 878015100723726767247301 164627831385698768858869)
                  ·
                    rfl

theorem cell22_1442752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 4].length) (baseStart_1442752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442752 prefixEnd_1442752 := by exact prefixLift 1442752
  have htrace : WordTrace (prefixWord ++ tailWord_1442752) baseStart_1442752 baseEnd_1442752 := by
    simpa [prefixWord, tailWord_1442752, baseEnd_1442752] using wordTrace_append hprefix tailTrace_1442752
  have hstable : (prefixWord ++ tailWord_1442752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442752).length < 2 ^ (prefixWord ++ tailWord_1442752).sum := by decide
  have hdescent : baseEnd_1442752 < baseStart_1442752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442763 : List Nat := [1, 1, 1, 1, 3, 6, 2, 7]
def baseStart_1442763 : Nat := 118140960795 + 1442763 * 2 ^ 59
def prefixEnd_1442763 : Nat := 4983230072969 + 3 ^ 40 * 1442763 * 2
def baseEnd_1442763 : Nat := 54876362186877327172397

theorem tailTrace_1442763 : CollatzResearch.WordTrace tailWord_1442763 prefixEnd_1442763 54876362186877327172397 := by
  unfold tailWord_1442763
  simp only [CollatzResearch.WordTrace]
  refine ⟨52621889672123530148260943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35081259781415686765507295 52621889672123530148260943)
  ·
    refine ⟨78932834508185295222391415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52621889672123530148260943 78932834508185295222391415)
    ·
      refine ⟨118399251762277942833587123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78932834508185295222391415 118399251762277942833587123)
      ·
        refine ⟨177598877643416914250380685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118399251762277942833587123 177598877643416914250380685)
        ·
          refine ⟨66599579116281342843892757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177598877643416914250380685 66599579116281342843892757)
          ·
            refine ⟨3121855271075687945807473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66599579116281342843892757 3121855271075687945807473)
            ·
              refine ⟨2341391453306765959355605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3121855271075687945807473 2341391453306765959355605)
              ·
                refine ⟨54876362186877327172397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2341391453306765959355605 54876362186877327172397)
                ·
                  rfl

theorem cell22_1442763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 7].length) (baseStart_1442763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442763 prefixEnd_1442763 := by exact prefixLift 1442763
  have htrace : WordTrace (prefixWord ++ tailWord_1442763) baseStart_1442763 baseEnd_1442763 := by
    simpa [prefixWord, tailWord_1442763, baseEnd_1442763] using wordTrace_append hprefix tailTrace_1442763
  have hstable : (prefixWord ++ tailWord_1442763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442763).length < 2 ^ (prefixWord ++ tailWord_1442763).sum := by decide
  have hdescent : baseEnd_1442763 < baseStart_1442763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442767 : List Nat := [1, 1, 2, 1, 1, 6, 4, 1, 2, 3]
def baseStart_1442767 : Nat := 118140960795 + 1442767 * 2 ^ 59
def prefixEnd_1442767 : Nat := 4983230072969 + 3 ^ 40 * 1442767 * 2
def baseEnd_1442767 : Nat := 493888628963641267451561

theorem tailTrace_1442767 : CollatzResearch.WordTrace tailWord_1442767 prefixEnd_1442767 493888628963641267451561 := by
  unfold tailWord_1442767
  simp only [CollatzResearch.WordTrace]
  refine ⟨52622035564109038831406555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35081357042739359220937703 52622035564109038831406555)
  ·
    refine ⟨78933053346163558247109833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52622035564109038831406555 78933053346163558247109833)
    ·
      refine ⟨59199790009622668685332375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78933053346163558247109833 59199790009622668685332375)
      ·
        refine ⟨88799685014434003027998563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59199790009622668685332375 88799685014434003027998563)
        ·
          refine ⟨133199527521651004541997845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88799685014434003027998563 133199527521651004541997845)
          ·
            refine ⟨6243727852577390837906149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 133199527521651004541997845 6243727852577390837906149)
            ·
              refine ⟨1170698972358260782107403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6243727852577390837906149 1170698972358260782107403)
              ·
                refine ⟨1756048458537391173161105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1170698972358260782107403 1756048458537391173161105)
                ·
                  refine ⟨1317036343903043379870829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1756048458537391173161105 1317036343903043379870829)
                  ·
                    refine ⟨493888628963641267451561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1317036343903043379870829 493888628963641267451561)
                    ·
                      rfl

theorem cell22_1442767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 2, 3].length) (baseStart_1442767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442767 prefixEnd_1442767 := by exact prefixLift 1442767
  have htrace : WordTrace (prefixWord ++ tailWord_1442767) baseStart_1442767 baseEnd_1442767 := by
    simpa [prefixWord, tailWord_1442767, baseEnd_1442767] using wordTrace_append hprefix tailTrace_1442767
  have hstable : (prefixWord ++ tailWord_1442767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442767).length < 2 ^ (prefixWord ++ tailWord_1442767).sum := by decide
  have hdescent : baseEnd_1442767 < baseStart_1442767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442814 : List Nat := [4, 2, 2, 2, 3, 1, 1, 7]
def baseStart_1442814 : Nat := 118140960795 + 1442814 * 2 ^ 59
def prefixEnd_1442814 : Nat := 4983230072969 + 3 ^ 40 * 1442814 * 2
def baseEnd_1442814 : Nat := 54878302002683201280713

theorem tailTrace_1442814 : CollatzResearch.WordTrace tailWord_1442814 prefixEnd_1442814 54878302002683201280713 := by
  unfold tailWord_1442814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6577968724367345732295937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35082499863292510572244997 6577968724367345732295937)
  ·
    refine ⟨4933476543275509299221953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6577968724367345732295937 4933476543275509299221953)
    ·
      refine ⟨3700107407456631974416465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4933476543275509299221953 3700107407456631974416465)
      ·
        refine ⟨2775080555592473980812349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3700107407456631974416465 2775080555592473980812349)
        ·
          refine ⟨1040655208347177742804631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2775080555592473980812349 1040655208347177742804631)
          ·
            refine ⟨1560982812520766614206947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040655208347177742804631 1560982812520766614206947)
            ·
              refine ⟨2341474218781149921310421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1560982812520766614206947 2341474218781149921310421)
              ·
                refine ⟨54878302002683201280713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2341474218781149921310421 54878302002683201280713)
                ·
                  rfl

theorem cell22_1442814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_1442814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442814 prefixEnd_1442814 := by exact prefixLift 1442814
  have htrace : WordTrace (prefixWord ++ tailWord_1442814) baseStart_1442814 baseEnd_1442814 := by
    simpa [prefixWord, tailWord_1442814, baseEnd_1442814] using wordTrace_append hprefix tailTrace_1442814
  have hstable : (prefixWord ++ tailWord_1442814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442814).length < 2 ^ (prefixWord ++ tailWord_1442814).sum := by decide
  have hdescent : baseEnd_1442814 < baseStart_1442814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442853 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 8]
def baseStart_1442853 : Nat := 118140960795 + 1442853 * 2 ^ 59
def prefixEnd_1442853 : Nat := 4983230072969 + 3 ^ 40 * 1442853 * 2
def baseEnd_1442853 : Nat := 164639356173721903267099

theorem tailTrace_1442853 : CollatzResearch.WordTrace tailWord_1442853 prefixEnd_1442853 164639356173721903267099 := by
  unfold tailWord_1442853
  simp only [CollatzResearch.WordTrace]
  refine ⟨52625172241797475519037213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35083448161198317012691475 52625172241797475519037213)
  ·
    refine ⟨19734439590674053319638955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52625172241797475519037213 19734439590674053319638955)
    ·
      refine ⟨29601659386011079979458433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19734439590674053319638955 29601659386011079979458433)
      ·
        refine ⟨22201244539508309984593825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29601659386011079979458433 22201244539508309984593825)
        ·
          refine ⟨16650933404631232488445369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22201244539508309984593825 16650933404631232488445369)
          ·
            refine ⟨12488200053473424366334027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16650933404631232488445369 12488200053473424366334027)
            ·
              refine ⟨18732300080210136549501041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12488200053473424366334027 18732300080210136549501041)
              ·
                refine ⟨14049225060157602412125781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18732300080210136549501041 14049225060157602412125781)
                ·
                  refine ⟨164639356173721903267099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14049225060157602412125781 164639356173721903267099)
                  ·
                    rfl

theorem cell22_1442853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_1442853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442853 prefixEnd_1442853 := by exact prefixLift 1442853
  have htrace : WordTrace (prefixWord ++ tailWord_1442853) baseStart_1442853 baseEnd_1442853 := by
    simpa [prefixWord, tailWord_1442853, baseEnd_1442853] using wordTrace_append hprefix tailTrace_1442853
  have hstable : (prefixWord ++ tailWord_1442853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442853).length < 2 ^ (prefixWord ++ tailWord_1442853).sum := by decide
  have hdescent : baseEnd_1442853 < baseStart_1442853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442883 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 3, 6]
def baseStart_1442883 : Nat := 118140960795 + 1442883 * 2 ^ 59
def prefixEnd_1442883 : Nat := 4983230072969 + 3 ^ 40 * 1442883 * 2
def baseEnd_1442883 : Nat := 493928338134255631551205

theorem tailTrace_1442883 : CollatzResearch.WordTrace tailWord_1442883 prefixEnd_1442883 493928338134255631551205 := by
  unfold tailWord_1442883
  simp only [CollatzResearch.WordTrace]
  refine ⟨52626266431688790642629303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35084177621125860428419535 52626266431688790642629303)
  ·
    refine ⟨78939399647533185963943955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52626266431688790642629303 78939399647533185963943955)
    ·
      refine ⟨118409099471299778945915933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78939399647533185963943955 118409099471299778945915933)
      ·
        refine ⟨44403412301737417104718475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118409099471299778945915933 44403412301737417104718475)
        ·
          refine ⟨66605118452606125657077713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44403412301737417104718475 66605118452606125657077713)
          ·
            refine ⟨49953838839454594242808285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66605118452606125657077713 49953838839454594242808285)
            ·
              refine ⟨18732689564795472841053107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49953838839454594242808285 18732689564795472841053107)
              ·
                refine ⟨28099034347193209261579661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18732689564795472841053107 28099034347193209261579661)
                ·
                  refine ⟨10537137880197453473092373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28099034347193209261579661 10537137880197453473092373)
                  ·
                    refine ⟨493928338134255631551205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10537137880197453473092373 493928338134255631551205)
                    ·
                      rfl

theorem cell22_1442883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 6].length) (baseStart_1442883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442883 prefixEnd_1442883 := by exact prefixLift 1442883
  have htrace : WordTrace (prefixWord ++ tailWord_1442883) baseStart_1442883 baseEnd_1442883 := by
    simpa [prefixWord, tailWord_1442883, baseEnd_1442883] using wordTrace_append hprefix tailTrace_1442883
  have hstable : (prefixWord ++ tailWord_1442883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442883).length < 2 ^ (prefixWord ++ tailWord_1442883).sum := by decide
  have hdescent : baseEnd_1442883 < baseStart_1442883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442885 : List Nat := [1, 3, 1, 1, 1, 3, 5, 1, 1, 5]
def baseStart_1442885 : Nat := 118140960795 + 1442885 * 2 ^ 59
def prefixEnd_1442885 : Nat := 4983230072969 + 3 ^ 40 * 1442885 * 2
def baseEnd_1442885 : Nat := 493929022775128293001199

theorem tailTrace_1442885 : CollatzResearch.WordTrace tailWord_1442885 prefixEnd_1442885 493929022775128293001199 := by
  unfold tailWord_1442885
  simp only [CollatzResearch.WordTrace]
  refine ⟨52626339377681544984202109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35084226251787696656134739 52626339377681544984202109)
  ·
    refine ⟨19734877266630579369075791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52626339377681544984202109 19734877266630579369075791)
    ·
      refine ⟨29602315899945869053613687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19734877266630579369075791 29602315899945869053613687)
      ·
        refine ⟨44403473849918803580420531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29602315899945869053613687 44403473849918803580420531)
        ·
          refine ⟨66605210774878205370630797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44403473849918803580420531 66605210774878205370630797)
          ·
            refine ⟨24976954040579327013986549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66605210774878205370630797 24976954040579327013986549)
            ·
              refine ⟨2341589441304311907561239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24976954040579327013986549 2341589441304311907561239)
              ·
                refine ⟨3512384161956467861341859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2341589441304311907561239 3512384161956467861341859)
                ·
                  refine ⟨5268576242934701792012789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3512384161956467861341859 5268576242934701792012789)
                  ·
                    refine ⟨493929022775128293001199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5268576242934701792012789 493929022775128293001199)
                    ·
                      rfl

theorem cell22_1442885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_1442885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442885 prefixEnd_1442885 := by exact prefixLift 1442885
  have htrace : WordTrace (prefixWord ++ tailWord_1442885) baseStart_1442885 baseEnd_1442885 := by
    simpa [prefixWord, tailWord_1442885, baseEnd_1442885] using wordTrace_append hprefix tailTrace_1442885
  have hstable : (prefixWord ++ tailWord_1442885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442885).length < 2 ^ (prefixWord ++ tailWord_1442885).sum := by decide
  have hdescent : baseEnd_1442885 < baseStart_1442885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442900 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_1442900 : Nat := 118140960795 + 1442900 * 2 ^ 59
def prefixEnd_1442900 : Nat := 4983230072969 + 3 ^ 40 * 1442900 * 2
def baseEnd_1442900 : Nat := 493934157581673253876153

theorem tailTrace_1442900 : CollatzResearch.WordTrace tailWord_1442900 prefixEnd_1442900 493934157581673253876153 := by
  unfold tailWord_1442900
  simp only [CollatzResearch.WordTrace]
  refine ⟨26313443236313601272999077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35084590981751468363998769 26313443236313601272999077)
  ·
    refine ⟨4933770606808800238687327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26313443236313601272999077 4933770606808800238687327)
    ·
      refine ⟨7400655910213200358030991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4933770606808800238687327 7400655910213200358030991)
      ·
        refine ⟨11100983865319800537046487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7400655910213200358030991 11100983865319800537046487)
        ·
          refine ⟨16651475797979700805569731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11100983865319800537046487 16651475797979700805569731)
          ·
            refine ⟨24977213696969551208354597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16651475797979700805569731 24977213696969551208354597)
            ·
              refine ⟨4683227568181790851566487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24977213696969551208354597 4683227568181790851566487)
              ·
                refine ⟨7024841352272686277349731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4683227568181790851566487 7024841352272686277349731)
                ·
                  refine ⟨10537262028409029416024597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7024841352272686277349731 10537262028409029416024597)
                  ·
                    refine ⟨493934157581673253876153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10537262028409029416024597 493934157581673253876153)
                    ·
                      rfl

theorem cell22_1442900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_1442900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442900 prefixEnd_1442900 := by exact prefixLift 1442900
  have htrace : WordTrace (prefixWord ++ tailWord_1442900) baseStart_1442900 baseEnd_1442900 := by
    simpa [prefixWord, tailWord_1442900, baseEnd_1442900] using wordTrace_append hprefix tailTrace_1442900
  have hstable : (prefixWord ++ tailWord_1442900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442900).length < 2 ^ (prefixWord ++ tailWord_1442900).sum := by decide
  have hdescent : baseEnd_1442900 < baseStart_1442900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442977 : List Nat := [1, 2, 3, 3, 1, 1, 4, 2, 5]
def baseStart_1442977 : Nat := 118140960795 + 1442977 * 2 ^ 59
def prefixEnd_1442977 : Nat := 4983230072969 + 3 ^ 40 * 1442977 * 2
def baseEnd_1442977 : Nat := 164653505418423573233639

theorem tailTrace_1442977 : CollatzResearch.WordTrace tailWord_1442977 prefixEnd_1442977 164653505418423573233639 := by
  unfold tailWord_1442977
  simp only [CollatzResearch.WordTrace]
  refine ⟨52629694893348244696551185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35086463262232163131034123 52629694893348244696551185)
  ·
    refine ⟨39472271170011183522413389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52629694893348244696551185 39472271170011183522413389)
    ·
      refine ⟨14802101688754193820905021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39472271170011183522413389 14802101688754193820905021)
      ·
        refine ⟨5550788133282822682839383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14802101688754193820905021 5550788133282822682839383)
        ·
          refine ⟨8326182199924234024259075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5550788133282822682839383 8326182199924234024259075)
          ·
            refine ⟨12489273299886351036388613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8326182199924234024259075 12489273299886351036388613)
            ·
              refine ⟨2341738743728690819322865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12489273299886351036388613 2341738743728690819322865)
              ·
                refine ⟨1756304057796518114492149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2341738743728690819322865 1756304057796518114492149)
                ·
                  refine ⟨164653505418423573233639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1756304057796518114492149 164653505418423573233639)
                  ·
                    rfl

theorem cell22_1442977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 5].length) (baseStart_1442977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442977 prefixEnd_1442977 := by exact prefixLift 1442977
  have htrace : WordTrace (prefixWord ++ tailWord_1442977) baseStart_1442977 baseEnd_1442977 := by
    simpa [prefixWord, tailWord_1442977, baseEnd_1442977] using wordTrace_append hprefix tailTrace_1442977
  have hstable : (prefixWord ++ tailWord_1442977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442977).length < 2 ^ (prefixWord ++ tailWord_1442977).sum := by decide
  have hdescent : baseEnd_1442977 < baseStart_1442977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442981 : List Nat := [1, 3, 1, 2, 1, 4, 4, 2, 1, 3]
def baseStart_1442981 : Nat := 118140960795 + 1442981 * 2 ^ 59
def prefixEnd_1442981 : Nat := 4983230072969 + 3 ^ 40 * 1442981 * 2
def baseEnd_1442981 : Nat := 493961885537016042600905

theorem tailTrace_1442981 : CollatzResearch.WordTrace tailWord_1442981 prefixEnd_1442981 493961885537016042600905 := by
  unfold tailWord_1442981
  simp only [CollatzResearch.WordTrace]
  refine ⟨52629840785333753379696797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35086560523555835586464531 52629840785333753379696797)
  ·
    refine ⟨19736190294500157517386299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52629840785333753379696797 19736190294500157517386299)
    ·
      refine ⟨29604285441750236276079449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19736190294500157517386299 29604285441750236276079449)
      ·
        refine ⟨22203214081312677207059587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29604285441750236276079449 22203214081312677207059587)
        ·
          refine ⟨33304821121969015810589381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22203214081312677207059587 33304821121969015810589381)
          ·
            refine ⟨6244653960369190464485509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33304821121969015810589381 6244653960369190464485509)
            ·
              refine ⟨1170872617569223212091033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6244653960369190464485509 1170872617569223212091033)
              ·
                refine ⟨878154463176917409068275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1170872617569223212091033 878154463176917409068275)
                ·
                  refine ⟨1317231694765376113602413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 878154463176917409068275 1317231694765376113602413)
                  ·
                    refine ⟨493961885537016042600905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1317231694765376113602413 493961885537016042600905)
                    ·
                      rfl

theorem cell22_1442981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 1, 3].length) (baseStart_1442981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442981 prefixEnd_1442981 := by exact prefixLift 1442981
  have htrace : WordTrace (prefixWord ++ tailWord_1442981) baseStart_1442981 baseEnd_1442981 := by
    simpa [prefixWord, tailWord_1442981, baseEnd_1442981] using wordTrace_append hprefix tailTrace_1442981
  have hstable : (prefixWord ++ tailWord_1442981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442981).length < 2 ^ (prefixWord ++ tailWord_1442981).sum := by decide
  have hdescent : baseEnd_1442981 < baseStart_1442981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442998 : List Nat := [5, 1, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_1442998 : Nat := 118140960795 + 1442998 * 2 ^ 59
def prefixEnd_1442998 : Nat := 4983230072969 + 3 ^ 40 * 1442998 * 2
def baseEnd_1442998 : Nat := 493967704984433664925853

theorem tailTrace_1442998 : CollatzResearch.WordTrace tailWord_1442998 prefixEnd_1442998 493967704984433664925853 := by
  unfold tailWord_1442998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3289403801642010330191603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35086973884181443522043765 3289403801642010330191603)
  ·
    refine ⟨4934105702463015495287405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3289403801642010330191603 4934105702463015495287405)
    ·
      refine ⟨1850289638423630810732777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4934105702463015495287405 1850289638423630810732777)
      ·
        refine ⟨1387717228817723108049583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1850289638423630810732777 1387717228817723108049583)
        ·
          refine ⟨2081575843226584662074375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1387717228817723108049583 2081575843226584662074375)
          ·
            refine ⟨3122363764839876993111563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2081575843226584662074375 3122363764839876993111563)
            ·
              refine ⟨4683545647259815489667345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3122363764839876993111563 4683545647259815489667345)
              ·
                refine ⟨3512659235444861617250509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4683545647259815489667345 3512659235444861617250509)
                ·
                  refine ⟨1317247213291823106468941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3512659235444861617250509 1317247213291823106468941)
                  ·
                    refine ⟨493967704984433664925853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1317247213291823106468941 493967704984433664925853)
                    ·
                      rfl

theorem cell22_1442998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_1442998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442998 prefixEnd_1442998 := by exact prefixLift 1442998
  have htrace : WordTrace (prefixWord ++ tailWord_1442998) baseStart_1442998 baseEnd_1442998 := by
    simpa [prefixWord, tailWord_1442998, baseEnd_1442998] using wordTrace_append hprefix tailTrace_1442998
  have hstable : (prefixWord ++ tailWord_1442998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442998).length < 2 ^ (prefixWord ++ tailWord_1442998).sum := by decide
  have hdescent : baseEnd_1442998 < baseStart_1442998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443005 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 8]
def baseStart_1443005 : Nat := 118140960795 + 1443005 * 2 ^ 59
def prefixEnd_1443005 : Nat := 4983230072969 + 3 ^ 40 * 1443005 * 2
def baseEnd_1443005 : Nat := 164656700409162660000277

theorem tailTrace_1443005 : CollatzResearch.WordTrace tailWord_1443005 prefixEnd_1443005 164656700409162660000277 := by
  unfold tailWord_1443005
  simp only [CollatzResearch.WordTrace]
  refine ⟨52630716137246805478570469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35087144091497870319046979 52630716137246805478570469)
  ·
    refine ⟨9868259275733776027231963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52630716137246805478570469 9868259275733776027231963)
    ·
      refine ⟨14802388913600664040847945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9868259275733776027231963 14802388913600664040847945)
      ·
        refine ⟨11101791685200498030635959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14802388913600664040847945 11101791685200498030635959)
        ·
          refine ⟨16652687527800747045953939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11101791685200498030635959 16652687527800747045953939)
          ·
            refine ⟨24979031291701120568930909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16652687527800747045953939 24979031291701120568930909)
            ·
              refine ⟨9367136734387920213349091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24979031291701120568930909 9367136734387920213349091)
              ·
                refine ⟨14050705101581880320023637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9367136734387920213349091 14050705101581880320023637)
                ·
                  refine ⟨164656700409162660000277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14050705101581880320023637 164656700409162660000277)
                  ·
                    rfl

theorem cell22_1443005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_1443005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443005 prefixEnd_1443005 := by exact prefixLift 1443005
  have htrace : WordTrace (prefixWord ++ tailWord_1443005) baseStart_1443005 baseEnd_1443005 := by
    simpa [prefixWord, tailWord_1443005, baseEnd_1443005] using wordTrace_append hprefix tailTrace_1443005
  have hstable : (prefixWord ++ tailWord_1443005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443005).length < 2 ^ (prefixWord ++ tailWord_1443005).sum := by decide
  have hdescent : baseEnd_1443005 < baseStart_1443005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443028 : List Nat := [2, 4, 1, 4, 2, 1, 1, 2, 5]
def baseStart_1443028 : Nat := 118140960795 + 1443028 * 2 ^ 59
def prefixEnd_1443028 : Nat := 4983230072969 + 3 ^ 40 * 1443028 * 2
def baseEnd_1443028 : Nat := 164659324865841195558587

theorem tailTrace_1443028 : CollatzResearch.WordTrace tailWord_1443028 prefixEnd_1443028 164659324865841195558587 := by
  unfold tailWord_1443028
  simp only [CollatzResearch.WordTrace]
  refine ⟨26315777508081740203328869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35087703344108986937771825 26315777508081740203328869)
  ·
    refine ⟨4934208282765326288124163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26315777508081740203328869 4934208282765326288124163)
    ·
      refine ⟨7401312424147989432186245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4934208282765326288124163 7401312424147989432186245)
      ·
        refine ⟨1387746079527748018534921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7401312424147989432186245 1387746079527748018534921)
        ·
          refine ⟨1040809559645811013901191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1387746079527748018534921 1040809559645811013901191)
          ·
            refine ⟨1561214339468716520851787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040809559645811013901191 1561214339468716520851787)
            ·
              refine ⟨2341821509203074781277681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561214339468716520851787 2341821509203074781277681)
              ·
                refine ⟨1756366131902306085958261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2341821509203074781277681 1756366131902306085958261)
                ·
                  refine ⟨164659324865841195558587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1756366131902306085958261 164659324865841195558587)
                  ·
                    rfl

theorem cell22_1443028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_1443028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443028 prefixEnd_1443028 := by exact prefixLift 1443028
  have htrace : WordTrace (prefixWord ++ tailWord_1443028) baseStart_1443028 baseEnd_1443028 := by
    simpa [prefixWord, tailWord_1443028, baseEnd_1443028] using wordTrace_append hprefix tailTrace_1443028
  have hstable : (prefixWord ++ tailWord_1443028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443028).length < 2 ^ (prefixWord ++ tailWord_1443028).sum := by decide
  have hdescent : baseEnd_1443028 < baseStart_1443028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443054 : List Nat := [4, 1, 2, 1, 1, 1, 2, 5, 2, 3]
def baseStart_1443054 : Nat := 118140960795 + 1443054 * 2 ^ 59
def prefixEnd_1443054 : Nat := 4983230072969 + 3 ^ 40 * 1443054 * 2
def baseEnd_1443054 : Nat := 493986874928868185525681

theorem tailTrace_1443054 : CollatzResearch.WordTrace tailWord_1443054 prefixEnd_1443054 493986874928868185525681 := by
  unfold tailWord_1443054
  simp only [CollatzResearch.WordTrace]
  refine ⟨6579062914258660855888027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35088335542712857898069477 6579062914258660855888027)
  ·
    refine ⟨9868594371387991283832041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6579062914258660855888027 9868594371387991283832041)
    ·
      refine ⟨7401445778540993462874031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9868594371387991283832041 7401445778540993462874031)
      ·
        refine ⟨11102168667811490194311047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7401445778540993462874031 11102168667811490194311047)
        ·
          refine ⟨16653253001717235291466571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11102168667811490194311047 16653253001717235291466571)
          ·
            refine ⟨24979879502575852937199857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16653253001717235291466571 24979879502575852937199857)
            ·
              refine ⟨18734909626931889702899893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24979879502575852937199857 18734909626931889702899893)
              ·
                refine ⟨1756397777524864659646865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18734909626931889702899893 1756397777524864659646865)
                ·
                  refine ⟨1317298333143648494735149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1756397777524864659646865 1317298333143648494735149)
                  ·
                    refine ⟨493986874928868185525681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1317298333143648494735149 493986874928868185525681)
                    ·
                      rfl

theorem cell22_1443054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_1443054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443054 prefixEnd_1443054 := by exact prefixLift 1443054
  have htrace : WordTrace (prefixWord ++ tailWord_1443054) baseStart_1443054 baseEnd_1443054 := by
    simpa [prefixWord, tailWord_1443054, baseEnd_1443054] using wordTrace_append hprefix tailTrace_1443054
  have hstable : (prefixWord ++ tailWord_1443054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443054).length < 2 ^ (prefixWord ++ tailWord_1443054).sum := by decide
  have hdescent : baseEnd_1443054 < baseStart_1443054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443065 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 2, 7]
def baseStart_1443065 : Nat := 118140960795 + 1443065 * 2 ^ 59
def prefixEnd_1443065 : Nat := 4983230072969 + 3 ^ 40 * 1443065 * 2
def baseEnd_1443065 : Nat := 493990640453667823500647

theorem tailTrace_1443065 : CollatzResearch.WordTrace tailWord_1443065 prefixEnd_1443065 493990640453667823500647 := by
  unfold tailWord_1443065
  simp only [CollatzResearch.WordTrace]
  refine ⟨52632904517029435725754649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35088603011352957150503099 52632904517029435725754649)
  ·
    refine ⟨39474678387772076794315987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52632904517029435725754649 39474678387772076794315987)
    ·
      refine ⟨59212017581658115191473981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39474678387772076794315987 59212017581658115191473981)
      ·
        refine ⟨22204506593121793196802743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59212017581658115191473981 22204506593121793196802743)
        ·
          refine ⟨33306759889682689795204115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22204506593121793196802743 33306759889682689795204115)
          ·
            refine ⟨49960139834524034692806173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33306759889682689795204115 49960139834524034692806173)
            ·
              refine ⟨18735052437946513009802315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49960139834524034692806173 18735052437946513009802315)
              ·
                refine ⟨28102578656919769514703473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18735052437946513009802315 28102578656919769514703473)
                ·
                  refine ⟨21076933992689827136027605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28102578656919769514703473 21076933992689827136027605)
                  ·
                    refine ⟨493990640453667823500647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21076933992689827136027605 493990640453667823500647)
                    ·
                      rfl

theorem cell22_1443065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_1443065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443065 prefixEnd_1443065 := by exact prefixLift 1443065
  have htrace : WordTrace (prefixWord ++ tailWord_1443065) baseStart_1443065 baseEnd_1443065 := by
    simpa [prefixWord, tailWord_1443065, baseEnd_1443065] using wordTrace_append hprefix tailTrace_1443065
  have hstable : (prefixWord ++ tailWord_1443065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443065).length < 2 ^ (prefixWord ++ tailWord_1443065).sum := by decide
  have hdescent : baseEnd_1443065 < baseStart_1443065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443090 : List Nat := [3, 2, 4, 2, 1, 1, 3, 2, 4]
def baseStart_1443090 : Nat := 118140960795 + 1443090 * 2 ^ 59
def prefixEnd_1443090 : Nat := 4983230072969 + 3 ^ 40 * 1443090 * 2
def baseEnd_1443090 : Nat := 164666399488192030541857

theorem tailTrace_1443090 : CollatzResearch.WordTrace tailWord_1443090 prefixEnd_1443090 164666399488192030541857 := by
  unfold tailWord_1443090
  simp only [CollatzResearch.WordTrace]
  refine ⟨13158454085484716248853681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35089210894625909996943149 13158454085484716248853681)
  ·
    refine ⟨9868840564113537186640261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13158454085484716248853681 9868840564113537186640261)
    ·
      refine ⟨1850407605771288222495049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9868840564113537186640261 1850407605771288222495049)
      ·
        refine ⟨1387805704328466166871287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1850407605771288222495049 1387805704328466166871287)
        ·
          refine ⟨2081708556492699250306931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1387805704328466166871287 2081708556492699250306931)
          ·
            refine ⟨3122562834739048875460397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2081708556492699250306931 3122562834739048875460397)
            ·
              refine ⟨1170961063027143328297649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3122562834739048875460397 1170961063027143328297649)
              ·
                refine ⟨878220797270357496223237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1170961063027143328297649 878220797270357496223237)
                ·
                  refine ⟨164666399488192030541857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 878220797270357496223237 164666399488192030541857)
                  ·
                    rfl

theorem cell22_1443090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_1443090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443090 prefixEnd_1443090 := by exact prefixLift 1443090
  have htrace : WordTrace (prefixWord ++ tailWord_1443090) baseStart_1443090 baseEnd_1443090 := by
    simpa [prefixWord, tailWord_1443090, baseEnd_1443090] using wordTrace_append hprefix tailTrace_1443090
  have hstable : (prefixWord ++ tailWord_1443090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443090).length < 2 ^ (prefixWord ++ tailWord_1443090).sum := by decide
  have hdescent : baseEnd_1443090 < baseStart_1443090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443268 : List Nat := [2, 3, 3, 2, 1, 1, 3, 1, 3, 3]
def baseStart_1443268 : Nat := 118140960795 + 1443268 * 2 ^ 59
def prefixEnd_1443268 : Nat := 4983230072969 + 3 ^ 40 * 1443268 * 2
def baseEnd_1443268 : Nat := 494060131502242960675025

theorem tailTrace_1443268 : CollatzResearch.WordTrace tailWord_1443268 prefixEnd_1443268 494060131502242960675025 := by
  unfold tailWord_1443268
  simp only [CollatzResearch.WordTrace]
  refine ⟨26320154267647000697697229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35093539023529334263596305 26320154267647000697697229)
  ·
    refine ⟨9870057850367625261636461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26320154267647000697697229 9870057850367625261636461)
    ·
      refine ⟨3701271693887859473113673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9870057850367625261636461 3701271693887859473113673)
      ·
        refine ⟨2775953770415894604835255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3701271693887859473113673 2775953770415894604835255)
        ·
          refine ⟨4163930655623841907252883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2775953770415894604835255 4163930655623841907252883)
          ·
            refine ⟨6245895983435762860879325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4163930655623841907252883 6245895983435762860879325)
            ·
              refine ⟨2342210993788411072829747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6245895983435762860879325 2342210993788411072829747)
              ·
                refine ⟨3513316490682616609244621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342210993788411072829747 3513316490682616609244621)
                ·
                  refine ⟨1317493684005981228466733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3513316490682616609244621 1317493684005981228466733)
                  ·
                    refine ⟨494060131502242960675025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1317493684005981228466733 494060131502242960675025)
                    ·
                      rfl

theorem cell22_1443268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_1443268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443268 prefixEnd_1443268 := by exact prefixLift 1443268
  have htrace : WordTrace (prefixWord ++ tailWord_1443268) baseStart_1443268 baseEnd_1443268 := by
    simpa [prefixWord, tailWord_1443268, baseEnd_1443268] using wordTrace_append hprefix tailTrace_1443268
  have hstable : (prefixWord ++ tailWord_1443268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443268).length < 2 ^ (prefixWord ++ tailWord_1443268).sum := by decide
  have hdescent : baseEnd_1443268 < baseStart_1443268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443405 : List Nat := [1, 6, 1, 1, 3, 2, 2, 6]
def baseStart_1443405 : Nat := 118140960795 + 1443405 * 2 ^ 59
def prefixEnd_1443405 : Nat := 4983230072969 + 3 ^ 40 * 1443405 * 2
def baseEnd_1443405 : Nat := 54900781044668918888845

theorem tailTrace_1443405 : CollatzResearch.WordTrace tailWord_1443405 prefixEnd_1443405 54900781044668918888845 := by
  unfold tailWord_1443405
  simp only [CollatzResearch.WordTrace]
  refine ⟨52645305335797673793131669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35096870223865115862087779 52645305335797673793131669)
  ·
    refine ⟨2467748687615515959053047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52645305335797673793131669 2467748687615515959053047)
    ·
      refine ⟨3701623031423273938579571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2467748687615515959053047 3701623031423273938579571)
      ·
        refine ⟨5552434547134910907869357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3701623031423273938579571 5552434547134910907869357)
        ·
          refine ⟨2082162955175591590451009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5552434547134910907869357 2082162955175591590451009)
          ·
            refine ⟨1561622216381693692838257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2082162955175591590451009 1561622216381693692838257)
            ·
              refine ⟨1171216662286270269628693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1561622216381693692838257 1171216662286270269628693)
              ·
                refine ⟨54900781044668918888845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1171216662286270269628693 54900781044668918888845)
                ·
                  rfl

theorem cell22_1443405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 6].length) (baseStart_1443405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443405 prefixEnd_1443405 := by exact prefixLift 1443405
  have htrace : WordTrace (prefixWord ++ tailWord_1443405) baseStart_1443405 baseEnd_1443405 := by
    simpa [prefixWord, tailWord_1443405, baseEnd_1443405] using wordTrace_append hprefix tailTrace_1443405
  have hstable : (prefixWord ++ tailWord_1443405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443405).length < 2 ^ (prefixWord ++ tailWord_1443405).sum := by decide
  have hdescent : baseEnd_1443405 < baseStart_1443405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443437 : List Nat := [1, 5, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_1443437 : Nat := 118140960795 + 1443437 * 2 ^ 59
def prefixEnd_1443437 : Nat := 4983230072969 + 3 ^ 40 * 1443437 * 2
def baseEnd_1443437 : Nat := 494117983655982853199507

theorem tailTrace_1443437 : CollatzResearch.WordTrace tailWord_1443437 prefixEnd_1443437 494117983655982853199507 := by
  unfold tailWord_1443437
  simp only [CollatzResearch.WordTrace]
  refine ⟨52646472471681743258296565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35097648314454495505531043 52646472471681743258296565)
  ·
    refine ⟨4935606794220163430465303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52646472471681743258296565 4935606794220163430465303)
    ·
      refine ⟨7403410191330245145697955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4935606794220163430465303 7403410191330245145697955)
      ·
        refine ⟨11105115286995367718546933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7403410191330245145697955 11105115286995367718546933)
        ·
          refine ⟨1041104558155815723613775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11105115286995367718546933 1041104558155815723613775)
          ·
            refine ⟨1561656837233723585420663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041104558155815723613775 1561656837233723585420663)
            ·
              refine ⟨2342485255850585378130995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561656837233723585420663 2342485255850585378130995)
              ·
                refine ⟨3513727883775878067196493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342485255850585378130995 3513727883775878067196493)
                ·
                  refine ⟨1317647956415954275198685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3513727883775878067196493 1317647956415954275198685)
                  ·
                    refine ⟨494117983655982853199507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1317647956415954275198685 494117983655982853199507)
                    ·
                      rfl

theorem cell22_1443437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_1443437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443437 prefixEnd_1443437 := by exact prefixLift 1443437
  have htrace : WordTrace (prefixWord ++ tailWord_1443437) baseStart_1443437 baseEnd_1443437 := by
    simpa [prefixWord, tailWord_1443437, baseEnd_1443437] using wordTrace_append hprefix tailTrace_1443437
  have hstable : (prefixWord ++ tailWord_1443437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443437).length < 2 ^ (prefixWord ++ tailWord_1443437).sum := by decide
  have hdescent : baseEnd_1443437 < baseStart_1443437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443463 : List Nat := [1, 1, 4, 2, 1, 3, 3, 2, 1, 4]
def baseStart_1443463 : Nat := 118140960795 + 1443463 * 2 ^ 59
def prefixEnd_1443463 : Nat := 4983230072969 + 3 ^ 40 * 1443463 * 2
def baseEnd_1443463 : Nat := 494126883987327452049427

theorem tailTrace_1443463 : CollatzResearch.WordTrace tailWord_1443463 prefixEnd_1443463 494126883987327452049427 := by
  unfold tailWord_1443463
  simp only [CollatzResearch.WordTrace]
  refine ⟨52647420769587549698743043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35098280513058366465828695 52647420769587549698743043)
  ·
    refine ⟨78971131154381324548114565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52647420769587549698743043 78971131154381324548114565)
    ·
      refine ⟨14807087091446498352771481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78971131154381324548114565 14807087091446498352771481)
      ·
        refine ⟨11105315318584873764578611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14807087091446498352771481 11105315318584873764578611)
        ·
          refine ⟨16657972977877310646867917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11105315318584873764578611 16657972977877310646867917)
          ·
            refine ⟨6246739866703991492575469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16657972977877310646867917 6246739866703991492575469)
            ·
              refine ⟨2342527450013996809715801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6246739866703991492575469 2342527450013996809715801)
              ·
                refine ⟨1756895587510497607286851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2342527450013996809715801 1756895587510497607286851)
                ·
                  refine ⟨2635343381265746410930277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1756895587510497607286851 2635343381265746410930277)
                  ·
                    refine ⟨494126883987327452049427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2635343381265746410930277 494126883987327452049427)
                    ·
                      rfl

theorem cell22_1443463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_1443463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443463 prefixEnd_1443463 := by exact prefixLift 1443463
  have htrace : WordTrace (prefixWord ++ tailWord_1443463) baseStart_1443463 baseEnd_1443463 := by
    simpa [prefixWord, tailWord_1443463, baseEnd_1443463] using wordTrace_append hprefix tailTrace_1443463
  have hstable : (prefixWord ++ tailWord_1443463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443463).length < 2 ^ (prefixWord ++ tailWord_1443463).sum := by decide
  have hdescent : baseEnd_1443463 < baseStart_1443463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443480 : List Nat := [2, 1, 2, 4, 1, 3, 3, 1, 1, 4]
def baseStart_1443480 : Nat := 118140960795 + 1443480 * 2 ^ 59
def prefixEnd_1443480 : Nat := 4983230072969 + 3 ^ 40 * 1443480 * 2
def baseEnd_1443480 : Nat := 494132703434745074374375

theorem tailTrace_1443480 : CollatzResearch.WordTrace tailWord_1443480 prefixEnd_1443480 494132703434745074374375 := by
  unfold tailWord_1443480
  simp only [CollatzResearch.WordTrace]
  refine ⟨26324020405262980801055947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35098693873683974401407929 26324020405262980801055947)
  ·
    refine ⟨39486030607894471201583921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26324020405262980801055947 39486030607894471201583921)
    ·
      refine ⟨29614522955920853401187941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39486030607894471201583921 29614522955920853401187941)
      ·
        refine ⟨5552723054235160012722739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29614522955920853401187941 5552723054235160012722739)
        ·
          refine ⟨8329084581352740019084109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5552723054235160012722739 8329084581352740019084109)
          ·
            refine ⟨3123406718007277507156541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8329084581352740019084109 3123406718007277507156541)
            ·
              refine ⟨1171277519252729065183703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3123406718007277507156541 1171277519252729065183703)
              ·
                refine ⟨1756916278879093597775555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1171277519252729065183703 1756916278879093597775555)
                ·
                  refine ⟨2635374418318640396663333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1756916278879093597775555 2635374418318640396663333)
                  ·
                    refine ⟨494132703434745074374375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2635374418318640396663333 494132703434745074374375)
                    ·
                      rfl

theorem cell22_1443480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 1, 4].length) (baseStart_1443480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443480 prefixEnd_1443480 := by exact prefixLift 1443480
  have htrace : WordTrace (prefixWord ++ tailWord_1443480) baseStart_1443480 baseEnd_1443480 := by
    simpa [prefixWord, tailWord_1443480, baseEnd_1443480] using wordTrace_append hprefix tailTrace_1443480
  have hstable : (prefixWord ++ tailWord_1443480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443480).length < 2 ^ (prefixWord ++ tailWord_1443480).sum := by decide
  have hdescent : baseEnd_1443480 < baseStart_1443480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443491 : List Nat := [1, 1, 1, 4, 1, 1, 3, 4, 2, 4]
def baseStart_1443491 : Nat := 118140960795 + 1443491 * 2 ^ 59
def prefixEnd_1443491 : Nat := 4983230072969 + 3 ^ 40 * 1443491 * 2
def baseEnd_1443491 : Nat := 494136468959544712349341

theorem tailTrace_1443491 : CollatzResearch.WordTrace tailWord_1443491 prefixEnd_1443491 494136468959544712349341 := by
  unfold tailWord_1443491
  simp only [CollatzResearch.WordTrace]
  refine ⟨52648442013486110480762327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35098961342324073653841551 52648442013486110480762327)
  ·
    refine ⟨78972663020229165721143491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52648442013486110480762327 78972663020229165721143491)
    ·
      refine ⟨118458994530343748581715237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78972663020229165721143491 118458994530343748581715237)
      ·
        refine ⟨22211061474439452859071607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118458994530343748581715237 22211061474439452859071607)
        ·
          refine ⟨33316592211659179288607411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22211061474439452859071607 33316592211659179288607411)
          ·
            refine ⟨49974888317488768932911117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33316592211659179288607411 49974888317488768932911117)
            ·
              refine ⟨18740583119058288349841669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49974888317488768932911117 18740583119058288349841669)
              ·
                refine ⟨3513859334823429065595313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18740583119058288349841669 3513859334823429065595313)
                ·
                  refine ⟨2635394501117571799196485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3513859334823429065595313 2635394501117571799196485)
                  ·
                    refine ⟨494136468959544712349341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2635394501117571799196485 494136468959544712349341)
                    ·
                      rfl

theorem cell22_1443491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 4].length) (baseStart_1443491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443491 prefixEnd_1443491 := by exact prefixLift 1443491
  have htrace : WordTrace (prefixWord ++ tailWord_1443491) baseStart_1443491 baseEnd_1443491 := by
    simpa [prefixWord, tailWord_1443491, baseEnd_1443491] using wordTrace_append hprefix tailTrace_1443491
  have hstable : (prefixWord ++ tailWord_1443491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443491).length < 2 ^ (prefixWord ++ tailWord_1443491).sum := by decide
  have hdescent : baseEnd_1443491 < baseStart_1443491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443493 : List Nat := [1, 3, 1, 2, 1, 2, 3, 4, 2, 3]
def baseStart_1443493 : Nat := 118140960795 + 1443493 * 2 ^ 59
def prefixEnd_1443493 : Nat := 4983230072969 + 3 ^ 40 * 1443493 * 2
def baseEnd_1443493 : Nat := 494137153600417373799335

theorem tailTrace_1443493 : CollatzResearch.WordTrace tailWord_1443493 prefixEnd_1443493 494137153600417373799335 := by
  unfold tailWord_1443493
  simp only [CollatzResearch.WordTrace]
  refine ⟨52648514959478864822335133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35099009972985909881556755 52648514959478864822335133)
  ·
    refine ⟨19743193109804574308375675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52648514959478864822335133 19743193109804574308375675)
    ·
      refine ⟨29614789664706861462563513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19743193109804574308375675 29614789664706861462563513)
      ·
        refine ⟨22211092248530146096922635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29614789664706861462563513 22211092248530146096922635)
        ·
          refine ⟨33316638372795219145383953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22211092248530146096922635 33316638372795219145383953)
          ·
            refine ⟨24987478779596414359037965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33316638372795219145383953 24987478779596414359037965)
            ·
              refine ⟨9370304542348655384639237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24987478779596414359037965 9370304542348655384639237)
              ·
                refine ⟨1756932101690372884619857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9370304542348655384639237 1756932101690372884619857)
                ·
                  refine ⟨1317699076267779663464893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1756932101690372884619857 1317699076267779663464893)
                  ·
                    refine ⟨494137153600417373799335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1317699076267779663464893 494137153600417373799335)
                    ·
                      rfl

theorem cell22_1443493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_1443493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443493 prefixEnd_1443493 := by exact prefixLift 1443493
  have htrace : WordTrace (prefixWord ++ tailWord_1443493) baseStart_1443493 baseEnd_1443493 := by
    simpa [prefixWord, tailWord_1443493, baseEnd_1443493] using wordTrace_append hprefix tailTrace_1443493
  have hstable : (prefixWord ++ tailWord_1443493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443493).length < 2 ^ (prefixWord ++ tailWord_1443493).sum := by decide
  have hdescent : baseEnd_1443493 < baseStart_1443493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443506 : List Nat := [3, 2, 1, 1, 1, 2, 5, 7]
def baseStart_1443506 : Nat := 118140960795 + 1443506 * 2 ^ 59
def prefixEnd_1443506 : Nat := 4983230072969 + 3 ^ 40 * 1443506 * 2
def baseEnd_1443506 : Nat := 54904622640676630358255

theorem tailTrace_1443506 : CollatzResearch.WordTrace tailWord_1443506 prefixEnd_1443506 54904622640676630358255 := by
  unfold tailWord_1443506
  simp only [CollatzResearch.WordTrace]
  refine ⟨13162247277107942010639593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35099326072287845361705581 13162247277107942010639593)
  ·
    refine ⟨9871685457830956507979695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13162247277107942010639593 9871685457830956507979695)
    ·
      refine ⟨14807528186746434761969543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9871685457830956507979695 14807528186746434761969543)
      ·
        refine ⟨22211292280119652142954315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14807528186746434761969543 22211292280119652142954315)
        ·
          refine ⟨33316938420179478214431473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22211292280119652142954315 33316938420179478214431473)
          ·
            refine ⟨24987703815134608660823605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33316938420179478214431473 24987703815134608660823605)
            ·
              refine ⟨2342597232668869561952213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24987703815134608660823605 2342597232668869561952213)
              ·
                refine ⟨54904622640676630358255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2342597232668869561952213 54904622640676630358255)
                ·
                  rfl

theorem cell22_1443506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 7].length) (baseStart_1443506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443506 prefixEnd_1443506 := by exact prefixLift 1443506
  have htrace : WordTrace (prefixWord ++ tailWord_1443506) baseStart_1443506 baseEnd_1443506 := by
    simpa [prefixWord, tailWord_1443506, baseEnd_1443506] using wordTrace_append hprefix tailTrace_1443506
  have hstable : (prefixWord ++ tailWord_1443506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443506).length < 2 ^ (prefixWord ++ tailWord_1443506).sum := by decide
  have hdescent : baseEnd_1443506 < baseStart_1443506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443510 : List Nat := [5, 1, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_1443510 : Nat := 118140960795 + 1443510 * 2 ^ 59
def prefixEnd_1443510 : Nat := 4983230072969 + 3 ^ 40 * 1443510 * 2
def baseEnd_1443510 : Nat := 494142973047834996124283

theorem tailTrace_1443510 : CollatzResearch.WordTrace tailWord_1443510 prefixEnd_1443510 494142973047834996124283 := by
  unfold tailWord_1443510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3290570937526079795356499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35099423333611517817135989 3290570937526079795356499)
  ·
    refine ⟨4935856406289119693034749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3290570937526079795356499 4935856406289119693034749)
    ·
      refine ⟨1850946152358419884888031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4935856406289119693034749 1850946152358419884888031)
      ·
        refine ⟨2776419228537629827332047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1850946152358419884888031 2776419228537629827332047)
        ·
          refine ⟨4164628842806444740998071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2776419228537629827332047 4164628842806444740998071)
          ·
            refine ⟨6246943264209667111497107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4164628842806444740998071 6246943264209667111497107)
            ·
              refine ⟨9370414896314500667245661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6246943264209667111497107 9370414896314500667245661)
              ·
                refine ⟨3513905586117937750217123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9370414896314500667245661 3513905586117937750217123)
                ·
                  refine ⟨5270858379176906625325685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3513905586117937750217123 5270858379176906625325685)
                  ·
                    refine ⟨494142973047834996124283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5270858379176906625325685 494142973047834996124283)
                    ·
                      rfl

theorem cell22_1443510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_1443510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443510 prefixEnd_1443510 := by exact prefixLift 1443510
  have htrace : WordTrace (prefixWord ++ tailWord_1443510) baseStart_1443510 baseEnd_1443510 := by
    simpa [prefixWord, tailWord_1443510, baseEnd_1443510] using wordTrace_append hprefix tailTrace_1443510
  have hstable : (prefixWord ++ tailWord_1443510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443510).length < 2 ^ (prefixWord ++ tailWord_1443510).sum := by decide
  have hdescent : baseEnd_1443510 < baseStart_1443510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443551 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 7]
def baseStart_1443551 : Nat := 118140960795 + 1443551 * 2 ^ 59
def prefixEnd_1443551 : Nat := 4983230072969 + 3 ^ 40 * 1443551 * 2
def baseEnd_1443551 : Nat := 164719002728574851949719

theorem tailTrace_1443551 : CollatzResearch.WordTrace tailWord_1443551 prefixEnd_1443551 164719002728574851949719 := by
  unfold tailWord_1443551
  simp only [CollatzResearch.WordTrace]
  refine ⟨52650630393268740727946507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35100420262179160485297671 52650630393268740727946507)
  ·
    refine ⟨78975945589903111091919761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52650630393268740727946507 78975945589903111091919761)
    ·
      refine ⟨59231959192427333318939821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78975945589903111091919761 59231959192427333318939821)
      ·
        refine ⟨22211984697160249994602433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59231959192427333318939821 22211984697160249994602433)
        ·
          refine ⟨16658988522870187495951825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22211984697160249994602433 16658988522870187495951825)
          ·
            refine ⟨12494241392152640621963869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16658988522870187495951825 12494241392152640621963869)
            ·
              refine ⟨4685340522057240233236451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12494241392152640621963869 4685340522057240233236451)
              ·
                refine ⟨7028010783085860349854677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4685340522057240233236451 7028010783085860349854677)
                ·
                  refine ⟨164719002728574851949719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7028010783085860349854677 164719002728574851949719)
                  ·
                    rfl

theorem cell22_1443551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 7].length) (baseStart_1443551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443551 prefixEnd_1443551 := by exact prefixLift 1443551
  have htrace : WordTrace (prefixWord ++ tailWord_1443551) baseStart_1443551 baseEnd_1443551 := by
    simpa [prefixWord, tailWord_1443551, baseEnd_1443551] using wordTrace_append hprefix tailTrace_1443551
  have hstable : (prefixWord ++ tailWord_1443551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443551).length < 2 ^ (prefixWord ++ tailWord_1443551).sum := by decide
  have hdescent : baseEnd_1443551 < baseStart_1443551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443596 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 8]
def baseStart_1443596 : Nat := 118140960795 + 1443596 * 2 ^ 59
def prefixEnd_1443596 : Nat := 4983230072969 + 3 ^ 40 * 1443596 * 2
def baseEnd_1443596 : Nat := 164724137535119812824673

theorem tailTrace_1443596 : CollatzResearch.WordTrace tailWord_1443596 prefixEnd_1443596 164724137535119812824673 := by
  unfold tailWord_1443596
  simp only [CollatzResearch.WordTrace]
  refine ⟨26326135839052856706667321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35101514452070475608889761 26326135839052856706667321)
  ·
    refine ⟨19744601879289642530000491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26326135839052856706667321 19744601879289642530000491)
    ·
      refine ⟨29616902818934463795000737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19744601879289642530000491 29616902818934463795000737)
      ·
        refine ⟨22212677114200847846250553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29616902818934463795000737 22212677114200847846250553)
        ·
          refine ⟨16659507835650635884687915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22212677114200847846250553 16659507835650635884687915)
          ·
            refine ⟨24989261753475953827031873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16659507835650635884687915 24989261753475953827031873)
            ·
              refine ⟨18741946315106965370273905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24989261753475953827031873 18741946315106965370273905)
              ·
                refine ⟨14056459736330224027705429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18741946315106965370273905 14056459736330224027705429)
                ·
                  refine ⟨164724137535119812824673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14056459736330224027705429 164724137535119812824673)
                  ·
                    rfl

theorem cell22_1443596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_1443596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443596 prefixEnd_1443596 := by exact prefixLift 1443596
  have htrace : WordTrace (prefixWord ++ tailWord_1443596) baseStart_1443596 baseEnd_1443596 := by
    simpa [prefixWord, tailWord_1443596, baseEnd_1443596] using wordTrace_append hprefix tailTrace_1443596
  have hstable : (prefixWord ++ tailWord_1443596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443596).length < 2 ^ (prefixWord ++ tailWord_1443596).sum := by decide
  have hdescent : baseEnd_1443596 < baseStart_1443596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443611 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 3, 5]
def baseStart_1443611 : Nat := 118140960795 + 1443611 * 2 ^ 59
def prefixEnd_1443611 : Nat := 4983230072969 + 3 ^ 40 * 1443611 * 2
def baseEnd_1443611 : Nat := 494177547411904399348973

theorem tailTrace_1443611 : CollatzResearch.WordTrace tailWord_1443611 prefixEnd_1443611 494177547411904399348973 := by
  unfold tailWord_1443611
  simp only [CollatzResearch.WordTrace]
  refine ⟨52652818773051370975130687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35101879182034247316753791 52652818773051370975130687)
  ·
    refine ⟨78979228159577056462696031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52652818773051370975130687 78979228159577056462696031)
    ·
      refine ⟨118468842239365584694044047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78979228159577056462696031 118468842239365584694044047)
      ·
        refine ⟨177703263359048377041066071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118468842239365584694044047 177703263359048377041066071)
        ·
          refine ⟨266554895038572565561599107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177703263359048377041066071 266554895038572565561599107)
          ·
            refine ⟨399832342557858848342398661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266554895038572565561599107 399832342557858848342398661)
            ·
              refine ⟨74968564229598534064199749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 399832342557858848342398661 74968564229598534064199749)
              ·
                refine ⟨14056605793049725137037453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74968564229598534064199749 14056605793049725137037453)
                ·
                  refine ⟨5271227172393646926389045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14056605793049725137037453 5271227172393646926389045)
                  ·
                    refine ⟨494177547411904399348973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5271227172393646926389045 494177547411904399348973)
                    ·
                      rfl

theorem cell22_1443611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 5].length) (baseStart_1443611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443611 prefixEnd_1443611 := by exact prefixLift 1443611
  have htrace : WordTrace (prefixWord ++ tailWord_1443611) baseStart_1443611 baseEnd_1443611 := by
    simpa [prefixWord, tailWord_1443611, baseEnd_1443611] using wordTrace_append hprefix tailTrace_1443611
  have hstable : (prefixWord ++ tailWord_1443611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443611).length < 2 ^ (prefixWord ++ tailWord_1443611).sum := by decide
  have hdescent : baseEnd_1443611 < baseStart_1443611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443645 : List Nat := [1, 4, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_1443645 : Nat := 118140960795 + 1443645 * 2 ^ 59
def prefixEnd_1443645 : Nat := 4983230072969 + 3 ^ 40 * 1443645 * 2
def baseEnd_1443645 : Nat := 494189186306739643998869

theorem tailTrace_1443645 : CollatzResearch.WordTrace tailWord_1443645 prefixEnd_1443645 494189186306739643998869 := by
  unfold tailWord_1443645
  simp only [CollatzResearch.WordTrace]
  refine ⟨52654058854928194781868389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35102705903285463187912259 52654058854928194781868389)
  ·
    refine ⟨9872636035299036521600323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52654058854928194781868389 9872636035299036521600323)
    ·
      refine ⟨14808954052948554782400485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9872636035299036521600323 14808954052948554782400485)
      ·
        refine ⟨2776678884927854021700091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14808954052948554782400485 2776678884927854021700091)
        ·
          refine ⟨4165018327391781032550137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2776678884927854021700091 4165018327391781032550137)
          ·
            refine ⟨3123763745543835774412603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4165018327391781032550137 3123763745543835774412603)
            ·
              refine ⟨4685645618315753661618905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3123763745543835774412603 4685645618315753661618905)
              ·
                refine ⟨3514234213736815246214179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4685645618315753661618905 3514234213736815246214179)
                ·
                  refine ⟨5271351320605222869321269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514234213736815246214179 5271351320605222869321269)
                  ·
                    refine ⟨494189186306739643998869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5271351320605222869321269 494189186306739643998869)
                    ·
                      rfl

theorem cell22_1443645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_1443645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443645 prefixEnd_1443645 := by exact prefixLift 1443645
  have htrace : WordTrace (prefixWord ++ tailWord_1443645) baseStart_1443645 baseEnd_1443645 := by
    simpa [prefixWord, tailWord_1443645, baseEnd_1443645] using wordTrace_append hprefix tailTrace_1443645
  have hstable : (prefixWord ++ tailWord_1443645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443645).length < 2 ^ (prefixWord ++ tailWord_1443645).sum := by decide
  have hdescent : baseEnd_1443645 < baseStart_1443645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443688 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 2, 6]
def baseStart_1443688 : Nat := 118140960795 + 1443688 * 2 ^ 59
def prefixEnd_1443688 : Nat := 4983230072969 + 3 ^ 40 * 1443688 * 2
def baseEnd_1443688 : Nat := 494203906085501865173737

theorem tailTrace_1443688 : CollatzResearch.WordTrace tailWord_1443688 prefixEnd_1443688 494203906085501865173737 := by
  unfold tailWord_1443688
  simp only [CollatzResearch.WordTrace]
  refine ⟨26327813596886206562841859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35103751462514942083789145 26327813596886206562841859)
  ·
    refine ⟨39491720395329309844262789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26327813596886206562841859 39491720395329309844262789)
    ·
      refine ⟨7404697574124245595799273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39491720395329309844262789 7404697574124245595799273)
      ·
        refine ⟨5553523180593184196849455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7404697574124245595799273 5553523180593184196849455)
        ·
          refine ⟨8330284770889776295274183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5553523180593184196849455 8330284770889776295274183)
          ·
            refine ⟨12495427156334664442911275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8330284770889776295274183 12495427156334664442911275)
            ·
              refine ⟨18743140734501996664366913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12495427156334664442911275 18743140734501996664366913)
              ·
                refine ⟨14057355550876497498275185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18743140734501996664366913 14057355550876497498275185)
                ·
                  refine ⟨10543016663157373123706389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14057355550876497498275185 10543016663157373123706389)
                  ·
                    refine ⟨494203906085501865173737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10543016663157373123706389 494203906085501865173737)
                    ·
                      rfl

theorem cell22_1443688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_1443688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443688 prefixEnd_1443688 := by exact prefixLift 1443688
  have htrace : WordTrace (prefixWord ++ tailWord_1443688) baseStart_1443688 baseEnd_1443688 := by
    simpa [prefixWord, tailWord_1443688, baseEnd_1443688] using wordTrace_append hprefix tailTrace_1443688
  have hstable : (prefixWord ++ tailWord_1443688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443688).length < 2 ^ (prefixWord ++ tailWord_1443688).sum := by decide
  have hdescent : baseEnd_1443688 < baseStart_1443688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443720 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 7]
def baseStart_1443720 : Nat := 118140960795 + 1443720 * 2 ^ 59
def prefixEnd_1443720 : Nat := 4983230072969 + 3 ^ 40 * 1443720 * 2
def baseEnd_1443720 : Nat := 164738286779821482791213

theorem tailTrace_1443720 : CollatzResearch.WordTrace tailWord_1443720 prefixEnd_1443720 164738286779821482791213 := by
  unfold tailWord_1443720
  simp only [CollatzResearch.WordTrace]
  refine ⟨26328397164828241295424307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35104529553104321727232409 26328397164828241295424307)
  ·
    refine ⟨39492595747242361943136461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26328397164828241295424307 39492595747242361943136461)
    ·
      refine ⟨14809723405215885728676173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39492595747242361943136461 14809723405215885728676173)
      ·
        refine ⟨5553646276955957148253565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14809723405215885728676173 5553646276955957148253565)
        ·
          refine ⟨2082617353858483930595087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5553646276955957148253565 2082617353858483930595087)
          ·
            refine ⟨3123926030787725895892631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082617353858483930595087 3123926030787725895892631)
            ·
              refine ⟨4685889046181588843838947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3123926030787725895892631 4685889046181588843838947)
              ·
                refine ⟨7028833569272383265758421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4685889046181588843838947 7028833569272383265758421)
                ·
                  refine ⟨164738286779821482791213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7028833569272383265758421 164738286779821482791213)
                  ·
                    rfl

theorem cell22_1443720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 7].length) (baseStart_1443720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443720 prefixEnd_1443720 := by exact prefixLift 1443720
  have htrace : WordTrace (prefixWord ++ tailWord_1443720) baseStart_1443720 baseEnd_1443720 := by
    simpa [prefixWord, tailWord_1443720, baseEnd_1443720] using wordTrace_append hprefix tailTrace_1443720
  have hstable : (prefixWord ++ tailWord_1443720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443720).length < 2 ^ (prefixWord ++ tailWord_1443720).sum := by decide
  have hdescent : baseEnd_1443720 < baseStart_1443720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443763 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 3, 5]
def baseStart_1443763 : Nat := 118140960795 + 1443763 * 2 ^ 59
def prefixEnd_1443763 : Nat := 4983230072969 + 3 ^ 40 * 1443763 * 2
def baseEnd_1443763 : Nat := 494229580118226669548507

theorem tailTrace_1443763 : CollatzResearch.WordTrace tailWord_1443763 prefixEnd_1443763 494229580118226669548507 := by
  unfold tailWord_1443763
  simp only [CollatzResearch.WordTrace]
  refine ⟨52658362668500700934663943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35105575112333800623109295 52658362668500700934663943)
  ·
    refine ⟨78987544002751051401995915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52658362668500700934663943 78987544002751051401995915)
    ·
      refine ⟨118481316004126577102993873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78987544002751051401995915 118481316004126577102993873)
      ·
        refine ⟨88860987003094932827245405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118481316004126577102993873 88860987003094932827245405)
        ·
          refine ⟨33322870126160599810217027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88860987003094932827245405 33322870126160599810217027)
          ·
            refine ⟨49984305189240899715325541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33322870126160599810217027 49984305189240899715325541)
            ·
              refine ⟨9372057222982668696623539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49984305189240899715325541 9372057222982668696623539)
              ·
                refine ⟨14058085834474003044935309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9372057222982668696623539 14058085834474003044935309)
                ·
                  refine ⟨5271782187927751141850741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14058085834474003044935309 5271782187927751141850741)
                  ·
                    refine ⟨494229580118226669548507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5271782187927751141850741 494229580118226669548507)
                    ·
                      rfl

theorem cell22_1443763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 5].length) (baseStart_1443763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443763 prefixEnd_1443763 := by exact prefixLift 1443763
  have htrace : WordTrace (prefixWord ++ tailWord_1443763) baseStart_1443763 baseEnd_1443763 := by
    simpa [prefixWord, tailWord_1443763, baseEnd_1443763] using wordTrace_append hprefix tailTrace_1443763
  have hstable : (prefixWord ++ tailWord_1443763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443763).length < 2 ^ (prefixWord ++ tailWord_1443763).sum := by decide
  have hdescent : baseEnd_1443763 < baseStart_1443763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443808 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 2, 7]
def baseStart_1443808 : Nat := 118140960795 + 1443808 * 2 ^ 59
def prefixEnd_1443808 : Nat := 4983230072969 + 3 ^ 40 * 1443808 * 2
def baseEnd_1443808 : Nat := 494244984537861552173369

theorem tailTrace_1443808 : CollatzResearch.WordTrace tailWord_1443808 prefixEnd_1443808 494244984537861552173369 := by
  unfold tailWord_1443808
  simp only [CollatzResearch.WordTrace]
  refine ⟨26330001976668836810026039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35106669302225115746701385 26330001976668836810026039)
  ·
    refine ⟨39495002965003255215039059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26330001976668836810026039 39495002965003255215039059)
    ·
      refine ⟨59242504447504882822558589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39495002965003255215039059 59242504447504882822558589)
      ·
        refine ⟨22215939167814331058459471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59242504447504882822558589 22215939167814331058459471)
        ·
          refine ⟨33323908751721496587689207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22215939167814331058459471 33323908751721496587689207)
          ·
            refine ⟨49985863127582244881533811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33323908751721496587689207 49985863127582244881533811)
            ·
              refine ⟨74978794691373367322300717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49985863127582244881533811 74978794691373367322300717)
              ·
                refine ⟨28117048009265012745862769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74978794691373367322300717 28117048009265012745862769)
                ·
                  refine ⟨21087786006948759559397077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28117048009265012745862769 21087786006948759559397077)
                  ·
                    refine ⟨494244984537861552173369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21087786006948759559397077 494244984537861552173369)
                    ·
                      rfl

theorem cell22_1443808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_1443808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443808 prefixEnd_1443808 := by exact prefixLift 1443808
  have htrace : WordTrace (prefixWord ++ tailWord_1443808) baseStart_1443808 baseEnd_1443808 := by
    simpa [prefixWord, tailWord_1443808, baseEnd_1443808] using wordTrace_append hprefix tailTrace_1443808
  have hstable : (prefixWord ++ tailWord_1443808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443808).length < 2 ^ (prefixWord ++ tailWord_1443808).sum := by decide
  have hdescent : baseEnd_1443808 < baseStart_1443808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443844 : List Nat := [2, 3, 2, 4, 1, 2, 1, 7]
def baseStart_1443844 : Nat := 118140960795 + 1443844 * 2 ^ 59
def prefixEnd_1443844 : Nat := 4983230072969 + 3 ^ 40 * 1443844 * 2
def baseEnd_1443844 : Nat := 54917478674841050919251

theorem tailTrace_1443844 : CollatzResearch.WordTrace tailWord_1443844 prefixEnd_1443844 54917478674841050919251 := by
  unfold tailWord_1443844
  simp only [CollatzResearch.WordTrace]
  refine ⟨26330658490603625884181293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35107544654138167845575057 26330658490603625884181293)
  ·
    refine ⟨9873996933976359706567985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26330658490603625884181293 9873996933976359706567985)
    ·
      refine ⟨7405497700482269779925989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9873996933976359706567985 7405497700482269779925989)
      ·
        refine ⟨1388530818840425583736123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7405497700482269779925989 1388530818840425583736123)
        ·
          refine ⟨2082796228260638375604185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1388530818840425583736123 2082796228260638375604185)
          ·
            refine ⟨1562097171195478781703139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2082796228260638375604185 1562097171195478781703139)
            ·
              refine ⟨2343145756793218172554709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1562097171195478781703139 2343145756793218172554709)
              ·
                refine ⟨54917478674841050919251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2343145756793218172554709 54917478674841050919251)
                ·
                  rfl

theorem cell22_1443844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 7].length) (baseStart_1443844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443844 prefixEnd_1443844 := by exact prefixLift 1443844
  have htrace : WordTrace (prefixWord ++ tailWord_1443844) baseStart_1443844 baseEnd_1443844 := by
    simpa [prefixWord, tailWord_1443844, baseEnd_1443844] using wordTrace_append hprefix tailTrace_1443844
  have hstable : (prefixWord ++ tailWord_1443844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443844).length < 2 ^ (prefixWord ++ tailWord_1443844).sum := by decide
  have hdescent : baseEnd_1443844 < baseStart_1443844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443917 : List Nat := [1, 6, 1, 1, 1, 1, 1, 4, 6]
def baseStart_1443917 : Nat := 118140960795 + 1443917 * 2 ^ 59
def prefixEnd_1443917 : Nat := 4983230072969 + 3 ^ 40 * 1443917 * 2
def baseEnd_1443917 : Nat := 164760765821807200399345

theorem tailTrace_1443917 : CollatzResearch.WordTrace tailWord_1443917 prefixEnd_1443917 164760765821807200399345 := by
  unfold tailWord_1443917
  simp only [CollatzResearch.WordTrace]
  refine ⟨52663979509942785235770005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35109319673295190157180003 52663979509942785235770005)
  ·
    refine ⟨2468624039528568057926719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52663979509942785235770005 2468624039528568057926719)
    ·
      refine ⟨3702936059292852086890079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2468624039528568057926719 3702936059292852086890079)
      ·
        refine ⟨5554404088939278130335119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3702936059292852086890079 5554404088939278130335119)
        ·
          refine ⟨8331606133408917195502679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5554404088939278130335119 8331606133408917195502679)
          ·
            refine ⟨12497409200113375793254019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8331606133408917195502679 12497409200113375793254019)
            ·
              refine ⟨18746113800170063689881029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12497409200113375793254019 18746113800170063689881029)
              ·
                refine ⟨3514896337531886941852693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18746113800170063689881029 3514896337531886941852693)
                ·
                  refine ⟨164760765821807200399345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3514896337531886941852693 164760765821807200399345)
                  ·
                    rfl

theorem cell22_1443917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_1443917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443917 prefixEnd_1443917 := by exact prefixLift 1443917
  have htrace : WordTrace (prefixWord ++ tailWord_1443917) baseStart_1443917 baseEnd_1443917 := by
    simpa [prefixWord, tailWord_1443917, baseEnd_1443917] using wordTrace_append hprefix tailTrace_1443917
  have hstable : (prefixWord ++ tailWord_1443917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443917).length < 2 ^ (prefixWord ++ tailWord_1443917).sum := by decide
  have hdescent : baseEnd_1443917 < baseStart_1443917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443930 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 1, 6]
def baseStart_1443930 : Nat := 118140960795 + 1443930 * 2 ^ 59
def prefixEnd_1443930 : Nat := 4983230072969 + 3 ^ 40 * 1443930 * 2
def baseEnd_1443930 : Nat := 494286747631093900622995

theorem tailTrace_1443930 : CollatzResearch.WordTrace tailWord_1443930 prefixEnd_1443930 494286747631093900622995 := by
  unfold tailWord_1443930
  simp only [CollatzResearch.WordTrace]
  refine ⟨13166113414723922113998311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35109635772597125637328829 13166113414723922113998311)
  ·
    refine ⟨19749170122085883170997467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13166113414723922113998311 19749170122085883170997467)
    ·
      refine ⟨29623755183128824756496201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19749170122085883170997467 29623755183128824756496201)
      ·
        refine ⟨22217816387346618567372151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29623755183128824756496201 22217816387346618567372151)
        ·
          refine ⟨33326724581019927851058227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22217816387346618567372151 33326724581019927851058227)
          ·
            refine ⟨49990086871529891776587341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33326724581019927851058227 49990086871529891776587341)
            ·
              refine ⟨18746282576823709416220253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49990086871529891776587341 18746282576823709416220253)
              ·
                refine ⟨7029855966308891031082595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18746282576823709416220253 7029855966308891031082595)
                ·
                  refine ⟨10544783949463336546623893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7029855966308891031082595 10544783949463336546623893)
                  ·
                    refine ⟨494286747631093900622995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10544783949463336546623893 494286747631093900622995)
                    ·
                      rfl

theorem cell22_1443930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_1443930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443930 prefixEnd_1443930 := by exact prefixLift 1443930
  have htrace : WordTrace (prefixWord ++ tailWord_1443930) baseStart_1443930 baseEnd_1443930 := by
    simpa [prefixWord, tailWord_1443930, baseEnd_1443930] using wordTrace_append hprefix tailTrace_1443930
  have hstable : (prefixWord ++ tailWord_1443930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443930).length < 2 ^ (prefixWord ++ tailWord_1443930).sum := by decide
  have hdescent : baseEnd_1443930 < baseStart_1443930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443949 : List Nat := [1, 5, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_1443949 : Nat := 118140960795 + 1443949 * 2 ^ 59
def prefixEnd_1443949 : Nat := 4983230072969 + 3 ^ 40 * 1443949 * 2
def baseEnd_1443949 : Nat := 494293251719384184397937

theorem tailTrace_1443949 : CollatzResearch.WordTrace tailWord_1443949 prefixEnd_1443949 494293251719384184397937 := by
  unfold tailWord_1443949
  simp only [CollatzResearch.WordTrace]
  refine ⟨52665146645826854700934901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35110097763884569800623267 52665146645826854700934901)
  ·
    refine ⟨4937357498046267628212647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52665146645826854700934901 4937357498046267628212647)
    ·
      refine ⟨7406036247069401442318971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4937357498046267628212647 7406036247069401442318971)
      ·
        refine ⟨11109054370604102163478457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7406036247069401442318971 11109054370604102163478457)
        ·
          refine ⟨8331790777953076622608843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11109054370604102163478457 8331790777953076622608843)
          ·
            refine ⟨12497686166929614933913265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8331790777953076622608843 12497686166929614933913265)
            ·
              refine ⟨9373264625197211200434949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12497686166929614933913265 9373264625197211200434949)
              ·
                refine ⟨1757487117224477100081553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9373264625197211200434949 1757487117224477100081553)
                ·
                  refine ⟨1318115337918357825061165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1757487117224477100081553 1318115337918357825061165)
                  ·
                    refine ⟨494293251719384184397937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1318115337918357825061165 494293251719384184397937)
                    ·
                      rfl

theorem cell22_1443949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_1443949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443949 prefixEnd_1443949 := by exact prefixLift 1443949
  have htrace : WordTrace (prefixWord ++ tailWord_1443949) baseStart_1443949 baseEnd_1443949 := by
    simpa [prefixWord, tailWord_1443949, baseEnd_1443949] using wordTrace_append hprefix tailTrace_1443949
  have hstable : (prefixWord ++ tailWord_1443949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443949).length < 2 ^ (prefixWord ++ tailWord_1443949).sum := by decide
  have hdescent : baseEnd_1443949 < baseStart_1443949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443977 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 5, 3]
def baseStart_1443977 : Nat := 118140960795 + 1443977 * 2 ^ 59
def prefixEnd_1443977 : Nat := 4983230072969 + 3 ^ 40 * 1443977 * 2
def baseEnd_1443977 : Nat := 494302836691601444697851

theorem tailTrace_1443977 : CollatzResearch.WordTrace tailWord_1443977 prefixEnd_1443977 494302836691601444697851 := by
  unfold tailWord_1443977
  simp only [CollatzResearch.WordTrace]
  refine ⟨52666167889725415482954185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35110778593150276988636123 52666167889725415482954185)
  ·
    refine ⟨39499625917294061612215639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52666167889725415482954185 39499625917294061612215639)
    ·
      refine ⟨59249438875941092418323459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39499625917294061612215639 59249438875941092418323459)
      ·
        refine ⟨88874158313911638627485189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59249438875941092418323459 88874158313911638627485189)
        ·
          refine ⟨16663904683858432242653473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88874158313911638627485189 16663904683858432242653473)
          ·
            refine ⟨12497928512893824181990105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16663904683858432242653473 12497928512893824181990105)
            ·
              refine ⟨9373446384670368136492579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12497928512893824181990105 9373446384670368136492579)
              ·
                refine ⟨14060169577005552204738869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9373446384670368136492579 14060169577005552204738869)
                ·
                  refine ⟨1318140897844270519194269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14060169577005552204738869 1318140897844270519194269)
                  ·
                    refine ⟨494302836691601444697851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1318140897844270519194269 494302836691601444697851)
                    ·
                      rfl

theorem cell22_1443977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 3].length) (baseStart_1443977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1443977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1443977 prefixEnd_1443977 := by exact prefixLift 1443977
  have htrace : WordTrace (prefixWord ++ tailWord_1443977) baseStart_1443977 baseEnd_1443977 := by
    simpa [prefixWord, tailWord_1443977, baseEnd_1443977] using wordTrace_append hprefix tailTrace_1443977
  have hstable : (prefixWord ++ tailWord_1443977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443977).length < 2 ^ (prefixWord ++ tailWord_1443977).sum := by decide
  have hdescent : baseEnd_1443977 < baseStart_1443977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444037 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 3, 4]
def baseStart_1444037 : Nat := 118140960795 + 1444037 * 2 ^ 59
def prefixEnd_1444037 : Nat := 4983230072969 + 3 ^ 40 * 1444037 * 2
def baseEnd_1444037 : Nat := 494323375917781288197667

theorem tailTrace_1444037 : CollatzResearch.WordTrace tailWord_1444037 prefixEnd_1444037 494323375917781288197667 := by
  unfold tailWord_1444037
  simp only [CollatzResearch.WordTrace]
  refine ⟨52668356269508045730138365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35112237513005363820092243 52668356269508045730138365)
  ·
    refine ⟨19750633601065517148801887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52668356269508045730138365 19750633601065517148801887)
    ·
      refine ⟨29625950401598275723202831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19750633601065517148801887 29625950401598275723202831)
      ·
        refine ⟨44438925602397413584804247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29625950401598275723202831 44438925602397413584804247)
        ·
          refine ⟨66658388403596120377206371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44438925602397413584804247 66658388403596120377206371)
          ·
            refine ⟨99987582605394180565809557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66658388403596120377206371 99987582605394180565809557)
            ·
              refine ⟨4686917934627852214022323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99987582605394180565809557 4686917934627852214022323)
              ·
                refine ⟨7030376901941778321033485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4686917934627852214022323 7030376901941778321033485)
                ·
                  refine ⟨2636391338228166870387557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7030376901941778321033485 2636391338228166870387557)
                  ·
                    refine ⟨494323375917781288197667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2636391338228166870387557 494323375917781288197667)
                    ·
                      rfl

theorem cell22_1444037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_1444037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444037 prefixEnd_1444037 := by exact prefixLift 1444037
  have htrace : WordTrace (prefixWord ++ tailWord_1444037) baseStart_1444037 baseEnd_1444037 := by
    simpa [prefixWord, tailWord_1444037, baseEnd_1444037] using wordTrace_append hprefix tailTrace_1444037
  have hstable : (prefixWord ++ tailWord_1444037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444037).length < 2 ^ (prefixWord ++ tailWord_1444037).sum := by decide
  have hdescent : baseEnd_1444037 < baseStart_1444037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444069 : List Nat := [1, 3, 1, 4, 2, 2, 2, 1, 6]
def baseStart_1444069 : Nat := 118140960795 + 1444069 * 2 ^ 59
def prefixEnd_1444069 : Nat := 4983230072969 + 3 ^ 40 * 1444069 * 2
def baseEnd_1444069 : Nat := 164778110057247957132523

theorem tailTrace_1444069 : CollatzResearch.WordTrace tailWord_1444069 prefixEnd_1444069 164778110057247957132523 := by
  unfold tailWord_1444069
  simp only [CollatzResearch.WordTrace]
  refine ⟨52669523405392115195303261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35113015603594743463535507 52669523405392115195303261)
  ·
    refine ⟨19751071277022043198238723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52669523405392115195303261 19751071277022043198238723)
    ·
      refine ⟨29626606915533064797358085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19751071277022043198238723 29626606915533064797358085)
      ·
        refine ⟨5554988796662449649504641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29626606915533064797358085 5554988796662449649504641)
        ·
          refine ⟨4166241597496837237128481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5554988796662449649504641 4166241597496837237128481)
          ·
            refine ⟨3124681198122627927846361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4166241597496837237128481 3124681198122627927846361)
            ·
              refine ⟨2343510898591970945884771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3124681198122627927846361 2343510898591970945884771)
              ·
                refine ⟨3515266347887956418827157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2343510898591970945884771 3515266347887956418827157)
                ·
                  refine ⟨164778110057247957132523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3515266347887956418827157 164778110057247957132523)
                  ·
                    rfl

theorem cell22_1444069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_1444069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444069 prefixEnd_1444069 := by exact prefixLift 1444069
  have htrace : WordTrace (prefixWord ++ tailWord_1444069) baseStart_1444069 baseEnd_1444069 := by
    simpa [prefixWord, tailWord_1444069, baseEnd_1444069] using wordTrace_append hprefix tailTrace_1444069
  have hstable : (prefixWord ++ tailWord_1444069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444069).length < 2 ^ (prefixWord ++ tailWord_1444069).sum := by decide
  have hdescent : baseEnd_1444069 < baseStart_1444069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444097 : List Nat := [1, 2, 4, 1, 1, 2, 3, 8]
def baseStart_1444097 : Nat := 118140960795 + 1444097 * 2 ^ 59
def prefixEnd_1444097 : Nat := 4983230072969 + 3 ^ 40 * 1444097 * 2
def baseEnd_1444097 : Nat := 54927101682662347966387

theorem tailTrace_1444097 : CollatzResearch.WordTrace tailWord_1444097 prefixEnd_1444097 54927101682662347966387 := by
  unfold tailWord_1444097
  simp only [CollatzResearch.WordTrace]
  refine ⟨52670544649290675977322545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35113696432860450651548363 52670544649290675977322545)
  ·
    refine ⟨39502908486968006982991909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52670544649290675977322545 39502908486968006982991909)
    ·
      refine ⟨7406795341306501309310983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39502908486968006982991909 7406795341306501309310983)
      ·
        refine ⟨11110193011959751963966475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7406795341306501309310983 11110193011959751963966475)
        ·
          refine ⟨16665289517939627945949713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11110193011959751963966475 16665289517939627945949713)
          ·
            refine ⟨12498967138454720959462285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16665289517939627945949713 12498967138454720959462285)
            ·
              refine ⟨4687112676920520359798357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12498967138454720959462285 4687112676920520359798357)
              ·
                refine ⟨54927101682662347966387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4687112676920520359798357 54927101682662347966387)
                ·
                  rfl

theorem cell22_1444097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 8].length) (baseStart_1444097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444097 prefixEnd_1444097 := by exact prefixLift 1444097
  have htrace : WordTrace (prefixWord ++ tailWord_1444097) baseStart_1444097 baseEnd_1444097 := by
    simpa [prefixWord, tailWord_1444097, baseEnd_1444097] using wordTrace_append hprefix tailTrace_1444097
  have hstable : (prefixWord ++ tailWord_1444097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444097).length < 2 ^ (prefixWord ++ tailWord_1444097).sum := by decide
  have hdescent : baseEnd_1444097 < baseStart_1444097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444180 : List Nat := [2, 4, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_1444180 : Nat := 118140960795 + 1444180 * 2 ^ 59
def prefixEnd_1444180 : Nat := 4983230072969 + 3 ^ 40 * 1444180 * 2
def baseEnd_1444180 : Nat := 494372327740176581872229

theorem tailTrace_1444180 : CollatzResearch.WordTrace tailWord_1444180 prefixEnd_1444180 494372327740176581872229 := by
  unfold tailWord_1444180
  simp only [CollatzResearch.WordTrace]
  refine ⟨26336785953994990576296997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35115714605326654101729329 26336785953994990576296997)
  ·
    refine ⟨4938147366374060733055687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26336785953994990576296997 4938147366374060733055687)
    ·
      refine ⟨7407221049561091099583531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4938147366374060733055687 7407221049561091099583531)
      ·
        refine ⟨11110831574341636649375297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7407221049561091099583531 11110831574341636649375297)
        ·
          refine ⟨8333123680756227487031473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11110831574341636649375297 8333123680756227487031473)
          ·
            refine ⟨6249842760567170615273605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8333123680756227487031473 6249842760567170615273605)
            ·
              refine ⟨1171845517606344490363801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6249842760567170615273605 1171845517606344490363801)
              ·
                refine ⟨878884138204758367772851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1171845517606344490363801 878884138204758367772851)
                ·
                  refine ⟨1318326207307137551659277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 878884138204758367772851 1318326207307137551659277)
                  ·
                    refine ⟨494372327740176581872229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1318326207307137551659277 494372327740176581872229)
                    ·
                      rfl

theorem cell22_1444180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_1444180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444180 prefixEnd_1444180 := by exact prefixLift 1444180
  have htrace : WordTrace (prefixWord ++ tailWord_1444180) baseStart_1444180 baseEnd_1444180 := by
    simpa [prefixWord, tailWord_1444180, baseEnd_1444180] using wordTrace_append hprefix tailTrace_1444180
  have hstable : (prefixWord ++ tailWord_1444180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444180).length < 2 ^ (prefixWord ++ tailWord_1444180).sum := by decide
  have hdescent : baseEnd_1444180 < baseStart_1444180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444219 : List Nat := [1, 1, 1, 1, 1, 7, 2, 2, 1, 5]
def baseStart_1444219 : Nat := 118140960795 + 1444219 * 2 ^ 59
def prefixEnd_1444219 : Nat := 4983230072969 + 3 ^ 40 * 1444219 * 2
def baseEnd_1444219 : Nat := 494385678237193480147109

theorem tailTrace_1444219 : CollatzResearch.WordTrace tailWord_1444219 prefixEnd_1444219 494385678237193480147109 := by
  unfold tailWord_1444219
  simp only [CollatzResearch.WordTrace]
  refine ⟨52674994354848690813263711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35116662903232460542175807 52674994354848690813263711)
  ·
    refine ⟨79012491532273036219895567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52674994354848690813263711 79012491532273036219895567)
    ·
      refine ⟨118518737298409554329843351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79012491532273036219895567 118518737298409554329843351)
      ·
        refine ⟨177778105947614331494765027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118518737298409554329843351 177778105947614331494765027)
        ·
          refine ⟨266667158921421497242147541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177778105947614331494765027 266667158921421497242147541)
          ·
            refine ⟨6250011537220816341612833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 266667158921421497242147541 6250011537220816341612833)
            ·
              refine ⟨4687508652915612256209625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6250011537220816341612833 4687508652915612256209625)
              ·
                refine ⟨3515631489686709192157219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4687508652915612256209625 3515631489686709192157219)
                ·
                  refine ⟨5273447234530063788235829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3515631489686709192157219 5273447234530063788235829)
                  ·
                    refine ⟨494385678237193480147109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5273447234530063788235829 494385678237193480147109)
                    ·
                      rfl

theorem cell22_1444219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 5].length) (baseStart_1444219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444219 prefixEnd_1444219 := by exact prefixLift 1444219
  have htrace : WordTrace (prefixWord ++ tailWord_1444219) baseStart_1444219 baseEnd_1444219 := by
    simpa [prefixWord, tailWord_1444219, baseEnd_1444219] using wordTrace_append hprefix tailTrace_1444219
  have hstable : (prefixWord ++ tailWord_1444219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444219).length < 2 ^ (prefixWord ++ tailWord_1444219).sum := by decide
  have hdescent : baseEnd_1444219 < baseStart_1444219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444221 : List Nat := [1, 4, 1, 1, 2, 3, 1, 5, 4]
def baseStart_1444221 : Nat := 118140960795 + 1444221 * 2 ^ 59
def prefixEnd_1444221 : Nat := 4983230072969 + 3 ^ 40 * 1444221 * 2
def baseEnd_1444221 : Nat := 164795454292688713865701

theorem tailTrace_1444221 : CollatzResearch.WordTrace tailWord_1444221 prefixEnd_1444221 164795454292688713865701 := by
  unfold tailWord_1444221
  simp only [CollatzResearch.WordTrace]
  refine ⟨52675067300841445154836517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35116711533894296769891011 52675067300841445154836517)
  ·
    refine ⟨9876575118907770966531847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52675067300841445154836517 9876575118907770966531847)
    ·
      refine ⟨14814862678361656449797771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9876575118907770966531847 14814862678361656449797771)
      ·
        refine ⟨22222294017542484674696657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14814862678361656449797771 22222294017542484674696657)
        ·
          refine ⟨16666720513156863506022493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22222294017542484674696657 16666720513156863506022493)
          ·
            refine ⟨6250020192433823814758435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16666720513156863506022493 6250020192433823814758435)
            ·
              refine ⟨9375030288650735722137653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6250020192433823814758435 9375030288650735722137653)
              ·
                refine ⟨878909089561006473950405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9375030288650735722137653 878909089561006473950405)
                ·
                  refine ⟨164795454292688713865701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 878909089561006473950405 164795454292688713865701)
                  ·
                    rfl

theorem cell22_1444221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_1444221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444221 prefixEnd_1444221 := by exact prefixLift 1444221
  have htrace : WordTrace (prefixWord ++ tailWord_1444221) baseStart_1444221 baseEnd_1444221 := by
    simpa [prefixWord, tailWord_1444221, baseEnd_1444221] using wordTrace_append hprefix tailTrace_1444221
  have hstable : (prefixWord ++ tailWord_1444221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444221).length < 2 ^ (prefixWord ++ tailWord_1444221).sum := by decide
  have hdescent : baseEnd_1444221 < baseStart_1444221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444236 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 4, 3]
def baseStart_1444236 : Nat := 118140960795 + 1444236 * 2 ^ 59
def prefixEnd_1444236 : Nat := 4983230072969 + 3 ^ 40 * 1444236 * 2
def baseEnd_1444236 : Nat := 494391497684611102472057

theorem tailTrace_1444236 : CollatzResearch.WordTrace tailWord_1444236 prefixEnd_1444236 494391497684611102472057 := by
  unfold tailWord_1444236
  simp only [CollatzResearch.WordTrace]
  refine ⟨26337807197893551358316281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35117076263858068477755041 26337807197893551358316281)
  ·
    refine ⟨19753355398420163518737211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26337807197893551358316281 19753355398420163518737211)
    ·
      refine ⟨29630033097630245278105817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19753355398420163518737211 29630033097630245278105817)
      ·
        refine ⟨22222524823222683958579363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29630033097630245278105817 22222524823222683958579363)
        ·
          refine ⟨33333787234834025937869045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22222524823222683958579363 33333787234834025937869045)
          ·
            refine ⟨3125042553265689931675223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33333787234834025937869045 3125042553265689931675223)
            ·
              refine ⟨4687563829898534897512835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3125042553265689931675223 4687563829898534897512835)
              ·
                refine ⟨7031345744847802346269253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4687563829898534897512835 7031345744847802346269253)
                ·
                  refine ⟨1318377327158962939925485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7031345744847802346269253 1318377327158962939925485)
                  ·
                    refine ⟨494391497684611102472057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1318377327158962939925485 494391497684611102472057)
                    ·
                      rfl

theorem cell22_1444236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_1444236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444236 prefixEnd_1444236 := by exact prefixLift 1444236
  have htrace : WordTrace (prefixWord ++ tailWord_1444236) baseStart_1444236 baseEnd_1444236 := by
    simpa [prefixWord, tailWord_1444236, baseEnd_1444236] using wordTrace_append hprefix tailTrace_1444236
  have hstable : (prefixWord ++ tailWord_1444236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444236).length < 2 ^ (prefixWord ++ tailWord_1444236).sum := by decide
  have hdescent : baseEnd_1444236 < baseStart_1444236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444238 : List Nat := [4, 1, 1, 4, 1, 1, 2, 4, 4]
def baseStart_1444238 : Nat := 118140960795 + 1444238 * 2 ^ 59
def prefixEnd_1444238 : Nat := 4983230072969 + 3 ^ 40 * 1444238 * 2
def baseEnd_1444238 : Nat := 164797394108494587974017

theorem tailTrace_1444238 : CollatzResearch.WordTrace tailWord_1444238 prefixEnd_1444238 164797394108494587974017 := by
  unfold tailWord_1444238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6584460917722482132275671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35117124894519904705470245 6584460917722482132275671)
  ·
    refine ⟨9876691376583723198413507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6584460917722482132275671 9876691376583723198413507)
    ·
      refine ⟨14815037064875584797620261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9876691376583723198413507 14815037064875584797620261)
      ·
        refine ⟨2777819449664172149553799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14815037064875584797620261 2777819449664172149553799)
        ·
          refine ⟨4166729174496258224330699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2777819449664172149553799 4166729174496258224330699)
          ·
            refine ⟨6250093761744387336496049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4166729174496258224330699 6250093761744387336496049)
            ·
              refine ⟨4687570321308290502372037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6250093761744387336496049 4687570321308290502372037)
              ·
                refine ⟨878919435245304469194757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4687570321308290502372037 878919435245304469194757)
                ·
                  refine ⟨164797394108494587974017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 878919435245304469194757 164797394108494587974017)
                  ·
                    rfl

theorem cell22_1444238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_1444238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444238 prefixEnd_1444238 := by exact prefixLift 1444238
  have htrace : WordTrace (prefixWord ++ tailWord_1444238) baseStart_1444238 baseEnd_1444238 := by
    simpa [prefixWord, tailWord_1444238, baseEnd_1444238] using wordTrace_append hprefix tailTrace_1444238
  have hstable : (prefixWord ++ tailWord_1444238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444238).length < 2 ^ (prefixWord ++ tailWord_1444238).sum := by decide
  have hdescent : baseEnd_1444238 < baseStart_1444238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444253 : List Nat := [1, 4, 2, 1, 4, 2, 1, 1, 1, 5]
def baseStart_1444253 : Nat := 118140960795 + 1444253 * 2 ^ 59
def prefixEnd_1444253 : Nat := 4983230072969 + 3 ^ 40 * 1444253 * 2
def baseEnd_1444253 : Nat := 494397317132028724797005

theorem tailTrace_1444253 : CollatzResearch.WordTrace tailWord_1444253 prefixEnd_1444253 494397317132028724797005 := by
  unfold tailWord_1444253
  simp only [CollatzResearch.WordTrace]
  refine ⟨52676234436725514620001413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35117489624483676413334275 52676234436725514620001413)
  ·
    refine ⟨9876793956886033991250265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52676234436725514620001413 9876793956886033991250265)
    ·
      refine ⟨7407595467664525493437699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9876793956886033991250265 7407595467664525493437699)
      ·
        refine ⟨11111393201496788240156549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7407595467664525493437699 11111393201496788240156549)
        ·
          refine ⟨2083386225280647795029353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11111393201496788240156549 2083386225280647795029353)
          ·
            refine ⟨1562539668960485846272015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2083386225280647795029353 1562539668960485846272015)
            ·
              refine ⟨2343809503440728769408023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1562539668960485846272015 2343809503440728769408023)
              ·
                refine ⟨3515714255161093154112035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2343809503440728769408023 3515714255161093154112035)
                ·
                  refine ⟨5273571382741639731168053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3515714255161093154112035 5273571382741639731168053)
                  ·
                    refine ⟨494397317132028724797005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5273571382741639731168053 494397317132028724797005)
                    ·
                      rfl

theorem cell22_1444253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_1444253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444253 prefixEnd_1444253 := by exact prefixLift 1444253
  have htrace : WordTrace (prefixWord ++ tailWord_1444253) baseStart_1444253 baseEnd_1444253 := by
    simpa [prefixWord, tailWord_1444253, baseEnd_1444253] using wordTrace_append hprefix tailTrace_1444253
  have hstable : (prefixWord ++ tailWord_1444253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444253).length < 2 ^ (prefixWord ++ tailWord_1444253).sum := by decide
  have hdescent : baseEnd_1444253 < baseStart_1444253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444289 : List Nat := [1, 2, 7, 1, 1, 1, 3, 2, 4]
def baseStart_1444289 : Nat := 118140960795 + 1444289 * 2 ^ 59
def prefixEnd_1444289 : Nat := 4983230072969 + 3 ^ 40 * 1444289 * 2
def baseEnd_1444289 : Nat := 164803213555912210298965

theorem tailTrace_1444289 : CollatzResearch.WordTrace tailWord_1444289 prefixEnd_1444289 164803213555912210298965 := by
  unfold tailWord_1444289
  simp only [CollatzResearch.WordTrace]
  refine ⟨52677547464595092768311921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35118364976396728512207947 52677547464595092768311921)
  ·
    refine ⟨39508160598446319576233941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52677547464595092768311921 39508160598446319576233941)
    ·
      refine ⟨925972514026085615067983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 39508160598446319576233941 925972514026085615067983)
      ·
        refine ⟨1388958771039128422601975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 925972514026085615067983 1388958771039128422601975)
        ·
          refine ⟨2083438156558692633902963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1388958771039128422601975 2083438156558692633902963)
          ·
            refine ⟨3125157234838038950854445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2083438156558692633902963 3125157234838038950854445)
            ·
              refine ⟨1171933963064264606570417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3125157234838038950854445 1171933963064264606570417)
              ·
                refine ⟨878950472298198454927813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1171933963064264606570417 878950472298198454927813)
                ·
                  refine ⟨164803213555912210298965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 878950472298198454927813 164803213555912210298965)
                  ·
                    rfl

theorem cell22_1444289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 4].length) (baseStart_1444289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444289 prefixEnd_1444289 := by exact prefixLift 1444289
  have htrace : WordTrace (prefixWord ++ tailWord_1444289) baseStart_1444289 baseEnd_1444289 := by
    simpa [prefixWord, tailWord_1444289, baseEnd_1444289] using wordTrace_append hprefix tailTrace_1444289
  have hstable : (prefixWord ++ tailWord_1444289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444289).length < 2 ^ (prefixWord ++ tailWord_1444289).sum := by decide
  have hdescent : baseEnd_1444289 < baseStart_1444289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444371 : List Nat := [1, 1, 1, 2, 1, 5, 4, 1, 1, 5]
def baseStart_1444371 : Nat := 118140960795 + 1444371 * 2 ^ 59
def prefixEnd_1444371 : Nat := 4983230072969 + 3 ^ 40 * 1444371 * 2
def baseEnd_1444371 : Nat := 494437710943515750346643

theorem tailTrace_1444371 : CollatzResearch.WordTrace tailWord_1444371 prefixEnd_1444371 494437710943515750346643 := by
  unfold tailWord_1444371
  simp only [CollatzResearch.WordTrace]
  refine ⟨52680538250298020772796967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35120358833532013848531311 52680538250298020772796967)
  ·
    refine ⟨79020807375447031159195451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52680538250298020772796967 79020807375447031159195451)
    ·
      refine ⟨118531211063170546738793177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79020807375447031159195451 118531211063170546738793177)
      ·
        refine ⟨88898408297377910054094883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118531211063170546738793177 88898408297377910054094883)
        ·
          refine ⟨133347612446066865081142325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88898408297377910054094883 133347612446066865081142325)
          ·
            refine ⟨12501338666818768601357093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133347612446066865081142325 12501338666818768601357093)
            ·
              refine ⟨2344001000028519112754455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12501338666818768601357093 2344001000028519112754455)
              ·
                refine ⟨3516001500042778669131683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2344001000028519112754455 3516001500042778669131683)
                ·
                  refine ⟨5274002250064168003697525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3516001500042778669131683 5274002250064168003697525)
                  ·
                    refine ⟨494437710943515750346643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5274002250064168003697525 494437710943515750346643)
                    ·
                      rfl

theorem cell22_1444371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 5].length) (baseStart_1444371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444371 prefixEnd_1444371 := by exact prefixLift 1444371
  have htrace : WordTrace (prefixWord ++ tailWord_1444371) baseStart_1444371 baseEnd_1444371 := by
    simpa [prefixWord, tailWord_1444371, baseEnd_1444371] using wordTrace_append hprefix tailTrace_1444371
  have hstable : (prefixWord ++ tailWord_1444371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444371).length < 2 ^ (prefixWord ++ tailWord_1444371).sum := by decide
  have hdescent : baseEnd_1444371 < baseStart_1444371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444392 : List Nat := [2, 1, 5, 2, 1, 3, 2, 1, 1, 4]
def baseStart_1444392 : Nat := 118140960795 + 1444392 * 2 ^ 59
def prefixEnd_1444392 : Nat := 4983230072969 + 3 ^ 40 * 1444392 * 2
def baseEnd_1444392 : Nat := 494444899672678695571579

theorem tailTrace_1444392 : CollatzResearch.WordTrace tailWord_1444392 prefixEnd_1444392 494444899672678695571579 := by
  unfold tailWord_1444392
  simp only [CollatzResearch.WordTrace]
  refine ⟨26340652091610970679655715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35120869455481294239540953 26340652091610970679655715)
  ·
    refine ⟨39510978137416456019483573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26340652091610970679655715 39510978137416456019483573)
    ·
      refine ⟨3704154200382792751826585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39510978137416456019483573 3704154200382792751826585)
      ·
        refine ⟨2778115650287094563869939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3704154200382792751826585 2778115650287094563869939)
        ·
          refine ⟨4167173475430641845804909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2778115650287094563869939 4167173475430641845804909)
          ·
            refine ⟨1562690053286490692176841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4167173475430641845804909 1562690053286490692176841)
            ·
              refine ⟨1172017539964868019132631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1562690053286490692176841 1172017539964868019132631)
              ·
                refine ⟨1758026309947302028698947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1172017539964868019132631 1758026309947302028698947)
                ·
                  refine ⟨2637039464920953043048421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758026309947302028698947 2637039464920953043048421)
                  ·
                    refine ⟨494444899672678695571579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2637039464920953043048421 494444899672678695571579)
                    ·
                      rfl

theorem cell22_1444392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_1444392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444392 prefixEnd_1444392 := by exact prefixLift 1444392
  have htrace : WordTrace (prefixWord ++ tailWord_1444392) baseStart_1444392 baseEnd_1444392 := by
    simpa [prefixWord, tailWord_1444392, baseEnd_1444392] using wordTrace_append hprefix tailTrace_1444392
  have hstable : (prefixWord ++ tailWord_1444392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444392).length < 2 ^ (prefixWord ++ tailWord_1444392).sum := by decide
  have hdescent : baseEnd_1444392 < baseStart_1444392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444399 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 3, 9]
def baseStart_1444399 : Nat := 118140960795 + 1444399 * 2 ^ 59
def prefixEnd_1444399 : Nat := 4983230072969 + 3 ^ 40 * 1444399 * 2
def baseEnd_1444399 : Nat := 494447295915733010646557

theorem tailTrace_1444399 : CollatzResearch.WordTrace tailWord_1444399 prefixEnd_1444399 494447295915733010646557 := by
  unfold tailWord_1444399
  simp only [CollatzResearch.WordTrace]
  refine ⟨52681559494196581554816251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35121039662797721036544167 52681559494196581554816251)
  ·
    refine ⟨79022339241294872332224377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52681559494196581554816251 79022339241294872332224377)
    ·
      refine ⟨59266754430971154249168283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79022339241294872332224377 59266754430971154249168283)
      ·
        refine ⟨88900131646456731373752425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59266754430971154249168283 88900131646456731373752425)
        ·
          refine ⟨66675098734842548530314319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88900131646456731373752425 66675098734842548530314319)
          ·
            refine ⟨100012648102263822795471479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66675098734842548530314319 100012648102263822795471479)
            ·
              refine ⟨150018972153395734193207219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100012648102263822795471479 150018972153395734193207219)
              ·
                refine ⟨225028458230093601289810829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150018972153395734193207219 225028458230093601289810829)
                ·
                  refine ⟨84385671836285100483679061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225028458230093601289810829 84385671836285100483679061)
                  ·
                    refine ⟨494447295915733010646557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 84385671836285100483679061 494447295915733010646557)
                    ·
                      rfl

theorem cell22_1444399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_1444399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444399 prefixEnd_1444399 := by exact prefixLift 1444399
  have htrace : WordTrace (prefixWord ++ tailWord_1444399) baseStart_1444399 baseEnd_1444399 := by
    simpa [prefixWord, tailWord_1444399, baseEnd_1444399] using wordTrace_append hprefix tailTrace_1444399
  have hstable : (prefixWord ++ tailWord_1444399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444399).length < 2 ^ (prefixWord ++ tailWord_1444399).sum := by decide
  have hdescent : baseEnd_1444399 < baseStart_1444399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444422 : List Nat := [6, 1, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_1444422 : Nat := 118140960795 + 1444422 * 2 ^ 59
def prefixEnd_1444422 : Nat := 4983230072969 + 3 ^ 40 * 1444422 * 2
def baseEnd_1444422 : Nat := 494455169285768617321487

theorem tailTrace_1444422 : CollatzResearch.WordTrace tailWord_1444422 prefixEnd_1444422 494455169285768617321487 := by
  unfold tailWord_1444422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1646324949159789265090735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35121598915408837655269013 1646324949159789265090735)
  ·
    refine ⟨2469487423739683897636103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1646324949159789265090735 2469487423739683897636103)
    ·
      refine ⟨3704231135609525846454155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2469487423739683897636103 3704231135609525846454155)
      ·
        refine ⟨5556346703414288769681233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3704231135609525846454155 5556346703414288769681233)
        ·
          refine ⟨4167260027560716577260925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5556346703414288769681233 4167260027560716577260925)
          ·
            refine ⟨1562722510335268716472847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4167260027560716577260925 1562722510335268716472847)
            ·
              refine ⟨2344083765502903074709271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1562722510335268716472847 2344083765502903074709271)
              ·
                refine ⟨3516125648254354612063907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2344083765502903074709271 3516125648254354612063907)
                ·
                  refine ⟨5274188472381531918095861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3516125648254354612063907 5274188472381531918095861)
                  ·
                    refine ⟨494455169285768617321487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5274188472381531918095861 494455169285768617321487)
                    ·
                      rfl

theorem cell22_1444422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_1444422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444422 prefixEnd_1444422 := by exact prefixLift 1444422
  have htrace : WordTrace (prefixWord ++ tailWord_1444422) baseStart_1444422 baseEnd_1444422 := by
    simpa [prefixWord, tailWord_1444422, baseEnd_1444422] using wordTrace_append hprefix tailTrace_1444422
  have hstable : (prefixWord ++ tailWord_1444422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444422).length < 2 ^ (prefixWord ++ tailWord_1444422).sum := by decide
  have hdescent : baseEnd_1444422 < baseStart_1444422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444433 : List Nat := [1, 2, 2, 1, 3, 3, 2, 2, 3, 3]
def baseStart_1444433 : Nat := 118140960795 + 1444433 * 2 ^ 59
def prefixEnd_1444433 : Nat := 4983230072969 + 3 ^ 40 * 1444433 * 2
def baseEnd_1444433 : Nat := 494458934810568255296453

theorem tailTrace_1444433 : CollatzResearch.WordTrace tailWord_1444433 prefixEnd_1444433 494458934810568255296453 := by
  unfold tailWord_1444433
  simp only [CollatzResearch.WordTrace]
  refine ⟨52682799576073405361553953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35121866384048936907702635 52682799576073405361553953)
  ·
    refine ⟨39512099682055054021165465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52682799576073405361553953 39512099682055054021165465)
    ·
      refine ⟨29634074761541290515874099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39512099682055054021165465 29634074761541290515874099)
      ·
        refine ⟨44451112142311935773811149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29634074761541290515874099 44451112142311935773811149)
        ·
          refine ⟨16669167053366975915179181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44451112142311935773811149 16669167053366975915179181)
          ·
            refine ⟨6250937645012615968192193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16669167053366975915179181 6250937645012615968192193)
            ·
              refine ⟨4688203233759461976144145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6250937645012615968192193 4688203233759461976144145)
              ·
                refine ⟨3516152425319596482108109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4688203233759461976144145 3516152425319596482108109)
                ·
                  refine ⟨1318557159494848680790541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3516152425319596482108109 1318557159494848680790541)
                  ·
                    refine ⟨494458934810568255296453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1318557159494848680790541 494458934810568255296453)
                    ·
                      rfl

theorem cell22_1444433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_1444433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444433 prefixEnd_1444433 := by exact prefixLift 1444433
  have htrace : WordTrace (prefixWord ++ tailWord_1444433) baseStart_1444433 baseEnd_1444433 := by
    simpa [prefixWord, tailWord_1444433, baseEnd_1444433] using wordTrace_append hprefix tailTrace_1444433
  have hstable : (prefixWord ++ tailWord_1444433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444433).length < 2 ^ (prefixWord ++ tailWord_1444433).sum := by decide
  have hdescent : baseEnd_1444433 < baseStart_1444433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444480 : List Nat := [2, 1, 1, 2, 1, 7, 2, 1, 5]
def baseStart_1444480 : Nat := 118140960795 + 1444480 * 2 ^ 59
def prefixEnd_1444480 : Nat := 4983230072969 + 3 ^ 40 * 1444480 * 2
def baseEnd_1444480 : Nat := 164825007957025266457103

theorem tailTrace_1444480 : CollatzResearch.WordTrace tailWord_1444480 prefixEnd_1444480 164825007957025266457103 := by
  unfold tailWord_1444480
  simp only [CollatzResearch.WordTrace]
  refine ⟨26342256903451566194257447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35123009204602088259009929 26342256903451566194257447)
  ·
    refine ⟨39513385355177349291386171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26342256903451566194257447 39513385355177349291386171)
    ·
      refine ⟨59270078032766023937079257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39513385355177349291386171 59270078032766023937079257)
      ·
        refine ⟨44452558524574517952809443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59270078032766023937079257 44452558524574517952809443)
        ·
          refine ⟨66678837786861776929214165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44452558524574517952809443 66678837786861776929214165)
          ·
            refine ⟨1562785260629572896778457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 66678837786861776929214165 1562785260629572896778457)
            ·
              refine ⟨1172088945472179672583843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1562785260629572896778457 1172088945472179672583843)
              ·
                refine ⟨1758133418208269508875765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1172088945472179672583843 1758133418208269508875765)
                ·
                  refine ⟨164825007957025266457103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1758133418208269508875765 164825007957025266457103)
                  ·
                    rfl

theorem cell22_1444480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 5].length) (baseStart_1444480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444480 prefixEnd_1444480 := by exact prefixLift 1444480
  have htrace : WordTrace (prefixWord ++ tailWord_1444480) baseStart_1444480 baseEnd_1444480 := by
    simpa [prefixWord, tailWord_1444480, baseEnd_1444480] using wordTrace_append hprefix tailTrace_1444480
  have hstable : (prefixWord ++ tailWord_1444480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444480).length < 2 ^ (prefixWord ++ tailWord_1444480).sum := by decide
  have hdescent : baseEnd_1444480 < baseStart_1444480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444540 : List Nat := [2, 2, 2, 3, 1, 1, 1, 5, 2, 3]
def baseStart_1444540 : Nat := 118140960795 + 1444540 * 2 ^ 59
def prefixEnd_1444540 : Nat := 4983230072969 + 3 ^ 40 * 1444540 * 2
def baseEnd_1444540 : Nat := 494495563097255642871125

theorem tailTrace_1444540 : CollatzResearch.WordTrace tailWord_1444540 prefixEnd_1444540 494495563097255642871125 := by
  unfold tailWord_1444540
  simp only [CollatzResearch.WordTrace]
  refine ⟨26343351093342881317849537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35124468124457175090466049 26343351093342881317849537)
  ·
    refine ⟨19757513320007160988387153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26343351093342881317849537 19757513320007160988387153)
    ·
      refine ⟨14818134990005370741290365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19757513320007160988387153 14818134990005370741290365)
      ·
        refine ⟨5556800621252014027983887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14818134990005370741290365 5556800621252014027983887)
        ·
          refine ⟨8335200931878021041975831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5556800621252014027983887 8335200931878021041975831)
          ·
            refine ⟨12502801397817031562963747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8335200931878021041975831 12502801397817031562963747)
            ·
              refine ⟨18754202096725547344445621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12502801397817031562963747 18754202096725547344445621)
              ·
                refine ⟨1758206446568020063541777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18754202096725547344445621 1758206446568020063541777)
                ·
                  refine ⟨1318654834926015047656333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1758206446568020063541777 1318654834926015047656333)
                  ·
                    refine ⟨494495563097255642871125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1318654834926015047656333 494495563097255642871125)
                    ·
                      rfl

theorem cell22_1444540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_1444540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444540 prefixEnd_1444540 := by exact prefixLift 1444540
  have htrace : WordTrace (prefixWord ++ tailWord_1444540) baseStart_1444540 baseEnd_1444540 := by
    simpa [prefixWord, tailWord_1444540, baseEnd_1444540] using wordTrace_append hprefix tailTrace_1444540
  have hstable : (prefixWord ++ tailWord_1444540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444540).length < 2 ^ (prefixWord ++ tailWord_1444540).sum := by decide
  have hdescent : baseEnd_1444540 < baseStart_1444540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444551 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 1, 9]
def baseStart_1444551 : Nat := 118140960795 + 1444551 * 2 ^ 59
def prefixEnd_1444551 : Nat := 4983230072969 + 3 ^ 40 * 1444551 * 2
def baseEnd_1444551 : Nat := 494499328622055280846091

theorem tailTrace_1444551 : CollatzResearch.WordTrace tailWord_1444551 prefixEnd_1444551 494499328622055280846091 := by
  unfold tailWord_1444551
  simp only [CollatzResearch.WordTrace]
  refine ⟨52687103389645911514349507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35124735593097274342899671 52687103389645911514349507)
  ·
    refine ⟨79030655084468867271524261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52687103389645911514349507 79030655084468867271524261)
    ·
      refine ⟨14818247828337912613410799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79030655084468867271524261 14818247828337912613410799)
      ·
        refine ⟨22227371742506868920116199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14818247828337912613410799 22227371742506868920116199)
        ·
          refine ⟨33341057613760303380174299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22227371742506868920116199 33341057613760303380174299)
          ·
            refine ⟨50011586420640455070261449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33341057613760303380174299 50011586420640455070261449)
            ·
              refine ⟨37508689815480341302696087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50011586420640455070261449 37508689815480341302696087)
              ·
                refine ⟨56263034723220511954044131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37508689815480341302696087 56263034723220511954044131)
                ·
                  refine ⟨84394552084830767931066197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56263034723220511954044131 84394552084830767931066197)
                  ·
                    refine ⟨494499328622055280846091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 84394552084830767931066197 494499328622055280846091)
                    ·
                      rfl

theorem cell22_1444551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_1444551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444551 prefixEnd_1444551 := by exact prefixLift 1444551
  have htrace : WordTrace (prefixWord ++ tailWord_1444551) baseStart_1444551 baseEnd_1444551 := by
    simpa [prefixWord, tailWord_1444551, baseEnd_1444551] using wordTrace_append hprefix tailTrace_1444551
  have hstable : (prefixWord ++ tailWord_1444551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444551).length < 2 ^ (prefixWord ++ tailWord_1444551).sum := by decide
  have hdescent : baseEnd_1444551 < baseStart_1444551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444690 : List Nat := [3, 2, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_1444690 : Nat := 118140960795 + 1444690 * 2 ^ 59
def prefixEnd_1444690 : Nat := 4983230072969 + 3 ^ 40 * 1444690 * 2
def baseEnd_1444690 : Nat := 494546911162705251620665

theorem tailTrace_1444690 : CollatzResearch.WordTrace tailWord_1444690 prefixEnd_1444690 494546911162705251620665 := by
  unfold tailWord_1444690
  simp only [CollatzResearch.WordTrace]
  refine ⟨13173043284035584563414881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35128115424094892169106349 13173043284035584563414881)
  ·
    refine ⟨9879782463026688422561161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13173043284035584563414881 9879782463026688422561161)
    ·
      refine ⟨7409836847270016316920871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9879782463026688422561161 7409836847270016316920871)
      ·
        refine ⟨11114755270905024475381307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7409836847270016316920871 11114755270905024475381307)
        ·
          refine ⟨16672132906357536713071961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11114755270905024475381307 16672132906357536713071961)
          ·
            refine ⟨12504099679768152534803971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16672132906357536713071961 12504099679768152534803971)
            ·
              refine ⟨18756149519652228802205957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12504099679768152534803971 18756149519652228802205957)
              ·
                refine ⟨3516778034934792900413617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18756149519652228802205957 3516778034934792900413617)
                ·
                  refine ⟨2637583526201094675310213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3516778034934792900413617 2637583526201094675310213)
                  ·
                    refine ⟨494546911162705251620665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2637583526201094675310213 494546911162705251620665)
                    ·
                      rfl

theorem cell22_1444690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_1444690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444690 prefixEnd_1444690 := by exact prefixLift 1444690
  have htrace : WordTrace (prefixWord ++ tailWord_1444690) baseStart_1444690 baseEnd_1444690 := by
    simpa [prefixWord, tailWord_1444690, baseEnd_1444690] using wordTrace_append hprefix tailTrace_1444690
  have hstable : (prefixWord ++ tailWord_1444690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444690).length < 2 ^ (prefixWord ++ tailWord_1444690).sum := by decide
  have hdescent : baseEnd_1444690 < baseStart_1444690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444720 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 5, 3]
def baseStart_1444720 : Nat := 118140960795 + 1444720 * 2 ^ 59
def prefixEnd_1444720 : Nat := 4983230072969 + 3 ^ 40 * 1444720 * 2
def baseEnd_1444720 : Nat := 494557180775795173370573

theorem tailTrace_1444720 : CollatzResearch.WordTrace tailWord_1444720 prefixEnd_1444720 494557180775795173370573 := by
  unfold tailWord_1444720
  simp only [CollatzResearch.WordTrace]
  refine ⟨26346633663016826688625807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35128844884022435584834409 26346633663016826688625807)
  ·
    refine ⟨39519950494525240032938711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26346633663016826688625807 39519950494525240032938711)
    ·
      refine ⟨59279925741787860049408067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39519950494525240032938711 59279925741787860049408067)
      ·
        refine ⟨88919888612681790074112101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59279925741787860049408067 88919888612681790074112101)
        ·
          refine ⟨16672479114877835638896019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88919888612681790074112101 16672479114877835638896019)
          ·
            refine ⟨25008718672316753458344029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16672479114877835638896019 25008718672316753458344029)
            ·
              refine ⟨9378269502118782546879011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25008718672316753458344029 9378269502118782546879011)
              ·
                refine ⟨14067404253178173820318517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9378269502118782546879011 14067404253178173820318517)
                ·
                  refine ⟨1318819148735453795654861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14067404253178173820318517 1318819148735453795654861)
                  ·
                    refine ⟨494557180775795173370573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1318819148735453795654861 494557180775795173370573)
                    ·
                      rfl

theorem cell22_1444720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 5, 3].length) (baseStart_1444720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444720 prefixEnd_1444720 := by exact prefixLift 1444720
  have htrace : WordTrace (prefixWord ++ tailWord_1444720) baseStart_1444720 baseEnd_1444720 := by
    simpa [prefixWord, tailWord_1444720, baseEnd_1444720] using wordTrace_append hprefix tailTrace_1444720
  have hstable : (prefixWord ++ tailWord_1444720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444720).length < 2 ^ (prefixWord ++ tailWord_1444720).sum := by decide
  have hdescent : baseEnd_1444720 < baseStart_1444720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444765 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_1444765 : Nat := 118140960795 + 1444765 * 2 ^ 59
def prefixEnd_1444765 : Nat := 4983230072969 + 3 ^ 40 * 1444765 * 2
def baseEnd_1444765 : Nat := 494572585195430055995435

theorem tailTrace_1444765 : CollatzResearch.WordTrace tailWord_1444765 prefixEnd_1444765 494572585195430055995435 := by
  unfold tailWord_1444765
  simp only [CollatzResearch.WordTrace]
  refine ⟨52694908610870626062639749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35129939073913750708426499 52694908610870626062639749)
  ·
    refine ⟨9880295364538242386744953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52694908610870626062639749 9880295364538242386744953)
    ·
      refine ⟨7410221523403681790058715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9880295364538242386744953 7410221523403681790058715)
      ·
        refine ⟨11115332285105522685088073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7410221523403681790058715 11115332285105522685088073)
        ·
          refine ⟨8336499213829142013816055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11115332285105522685088073 8336499213829142013816055)
          ·
            refine ⟨12504748820743713020724083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8336499213829142013816055 12504748820743713020724083)
            ·
              refine ⟨18757123231115569531086125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12504748820743713020724083 18757123231115569531086125)
              ·
                refine ⟨7033921211668338574157297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18757123231115569531086125 7033921211668338574157297)
                ·
                  refine ⟨5275440908751253930617973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7033921211668338574157297 5275440908751253930617973)
                  ·
                    refine ⟨494572585195430055995435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5275440908751253930617973 494572585195430055995435)
                    ·
                      rfl

theorem cell22_1444765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_1444765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444765 prefixEnd_1444765 := by exact prefixLift 1444765
  have htrace : WordTrace (prefixWord ++ tailWord_1444765) baseStart_1444765 baseEnd_1444765 := by
    simpa [prefixWord, tailWord_1444765, baseEnd_1444765] using wordTrace_append hprefix tailTrace_1444765
  have hstable : (prefixWord ++ tailWord_1444765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444765).length < 2 ^ (prefixWord ++ tailWord_1444765).sum := by decide
  have hdescent : baseEnd_1444765 < baseStart_1444765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444788 : List Nat := [2, 5, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_1444788 : Nat := 118140960795 + 1444788 * 2 ^ 59
def prefixEnd_1444788 : Nat := 4983230072969 + 3 ^ 40 * 1444788 * 2
def baseEnd_1444788 : Nat := 494580458565465662670365

theorem tailTrace_1444788 : CollatzResearch.WordTrace tailWord_1444788 prefixEnd_1444788 494580458565465662670365 := by
  unfold tailWord_1444788
  simp only [CollatzResearch.WordTrace]
  refine ⟨26347873744893650495363509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35130498326524867327151345 26347873744893650495363509)
  ·
    refine ⟨2470113163583779733940329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26347873744893650495363509 2470113163583779733940329)
    ·
      refine ⟨1852584872687834800455247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2470113163583779733940329 1852584872687834800455247)
      ·
        refine ⟨2778877309031752200682871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1852584872687834800455247 2778877309031752200682871)
        ·
          refine ⟨4168315963547628301024307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2778877309031752200682871 4168315963547628301024307)
          ·
            refine ⟨6252473945321442451536461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4168315963547628301024307 6252473945321442451536461)
            ·
              refine ⟨2344677729495540919326173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6252473945321442451536461 2344677729495540919326173)
              ·
                refine ⟨879254148560827844747315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2344677729495540919326173 879254148560827844747315)
                ·
                  refine ⟨1318881222841241767120973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 879254148560827844747315 1318881222841241767120973)
                  ·
                    refine ⟨494580458565465662670365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1318881222841241767120973 494580458565465662670365)
                    ·
                      rfl

theorem cell22_1444788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_1444788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444788 prefixEnd_1444788 := by exact prefixLift 1444788
  have htrace : WordTrace (prefixWord ++ tailWord_1444788) baseStart_1444788 baseEnd_1444788 := by
    simpa [prefixWord, tailWord_1444788, baseEnd_1444788] using wordTrace_append hprefix tailTrace_1444788
  have hstable : (prefixWord ++ tailWord_1444788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444788).length < 2 ^ (prefixWord ++ tailWord_1444788).sum := by decide
  have hdescent : baseEnd_1444788 < baseStart_1444788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444831 : List Nat := [1, 1, 2, 3, 6, 1, 1, 2, 1, 4]
def baseStart_1444831 : Nat := 118140960795 + 1444831 * 2 ^ 59
def prefixEnd_1444831 : Nat := 4983230072969 + 3 ^ 40 * 1444831 * 2
def baseEnd_1444831 : Nat := 494595178344227883845233

theorem tailTrace_1444831 : CollatzResearch.WordTrace tailWord_1444831 prefixEnd_1444831 494595178344227883845233 := by
  unfold tailWord_1444831
  simp only [CollatzResearch.WordTrace]
  refine ⟨52697315828631519334542347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35131543885754346223028231 52697315828631519334542347)
  ·
    refine ⟨79045973742947279001813521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52697315828631519334542347 79045973742947279001813521)
    ·
      refine ⟨59284480307210459251360141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79045973742947279001813521 59284480307210459251360141)
      ·
        refine ⟨22231680115203922219260053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59284480307210459251360141 22231680115203922219260053)
        ·
          refine ⟨1042110005400183854027815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22231680115203922219260053 1042110005400183854027815)
          ·
            refine ⟨1563165008100275781041723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042110005400183854027815 1563165008100275781041723)
            ·
              refine ⟨2344747512150413671562585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563165008100275781041723 2344747512150413671562585)
              ·
                refine ⟨1758560634112810253671939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2344747512150413671562585 1758560634112810253671939)
                ·
                  refine ⟨2637840951169215380507909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758560634112810253671939 2637840951169215380507909)
                  ·
                    refine ⟨494595178344227883845233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2637840951169215380507909 494595178344227883845233)
                    ·
                      rfl

theorem cell22_1444831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 1, 4].length) (baseStart_1444831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444831 prefixEnd_1444831 := by exact prefixLift 1444831
  have htrace : WordTrace (prefixWord ++ tailWord_1444831) baseStart_1444831 baseEnd_1444831 := by
    simpa [prefixWord, tailWord_1444831, baseEnd_1444831] using wordTrace_append hprefix tailTrace_1444831
  have hstable : (prefixWord ++ tailWord_1444831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444831).length < 2 ^ (prefixWord ++ tailWord_1444831).sum := by decide
  have hdescent : baseEnd_1444831 < baseStart_1444831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444840 : List Nat := [2, 1, 4, 1, 1, 1, 4, 8]
def baseStart_1444840 : Nat := 118140960795 + 1444840 * 2 ^ 59
def prefixEnd_1444840 : Nat := 4983230072969 + 3 ^ 40 * 1444840 * 2
def baseEnd_1444840 : Nat := 54955362136461651152245

theorem tailTrace_1444840 : CollatzResearch.WordTrace tailWord_1444840 prefixEnd_1444840 54955362136461651152245 := by
  unfold tailWord_1444840
  simp only [CollatzResearch.WordTrace]
  refine ⟨26348822042799456935809987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35131762723732609247746649 26348822042799456935809987)
  ·
    refine ⟨39523233064199185403714981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26348822042799456935809987 39523233064199185403714981)
    ·
      refine ⟨7410606199537347263196559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39523233064199185403714981 7410606199537347263196559)
      ·
        refine ⟨11115909299306020894794839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7410606199537347263196559 11115909299306020894794839)
        ·
          refine ⟨16673863948959031342192259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11115909299306020894794839 16673863948959031342192259)
          ·
            refine ⟨25010795923438547013288389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16673863948959031342192259 25010795923438547013288389)
            ·
              refine ⟨4689524235644727564991573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25010795923438547013288389 4689524235644727564991573)
              ·
                refine ⟨54955362136461651152245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4689524235644727564991573 54955362136461651152245)
                ·
                  rfl

theorem cell22_1444840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 8].length) (baseStart_1444840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444840 prefixEnd_1444840 := by exact prefixLift 1444840
  have htrace : WordTrace (prefixWord ++ tailWord_1444840) baseStart_1444840 baseEnd_1444840 := by
    simpa [prefixWord, tailWord_1444840, baseEnd_1444840] using wordTrace_append hprefix tailTrace_1444840
  have hstable : (prefixWord ++ tailWord_1444840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444840).length < 2 ^ (prefixWord ++ tailWord_1444840).sum := by decide
  have hdescent : baseEnd_1444840 < baseStart_1444840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444842 : List Nat := [3, 1, 3, 1, 2, 2, 1, 3, 2, 4]
def baseStart_1444842 : Nat := 118140960795 + 1444842 * 2 ^ 59
def prefixEnd_1444842 : Nat := 4983230072969 + 3 ^ 40 * 1444842 * 2
def baseEnd_1444842 : Nat := 494598943869027521820199

theorem tailTrace_1444842 : CollatzResearch.WordTrace tailWord_1444842 prefixEnd_1444842 494598943869027521820199 := by
  unfold tailWord_1444842
  simp only [CollatzResearch.WordTrace]
  refine ⟨13174429257897917053298195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35131811354394445475461853 13174429257897917053298195)
  ·
    refine ⟨19761643886846875579947293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13174429257897917053298195 19761643886846875579947293)
    ·
      refine ⟨7410616457567578342480235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19761643886846875579947293 7410616457567578342480235)
      ·
        refine ⟨11115924686351367513720353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7410616457567578342480235 11115924686351367513720353)
        ·
          refine ⟨8336943514763525635290265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11115924686351367513720353 8336943514763525635290265)
          ·
            refine ⟨6252707636072644226467699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8336943514763525635290265 6252707636072644226467699)
            ·
              refine ⟨9379061454108966339701549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6252707636072644226467699 9379061454108966339701549)
              ·
                refine ⟨3517148045290862377388081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9379061454108966339701549 3517148045290862377388081)
                ·
                  refine ⟨2637861033968146783041061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3517148045290862377388081 2637861033968146783041061)
                  ·
                    refine ⟨494598943869027521820199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2637861033968146783041061 494598943869027521820199)
                    ·
                      rfl

theorem cell22_1444842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_1444842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444842 prefixEnd_1444842 := by exact prefixLift 1444842
  have htrace : WordTrace (prefixWord ++ tailWord_1444842) baseStart_1444842 baseEnd_1444842 := by
    simpa [prefixWord, tailWord_1444842, baseEnd_1444842] using wordTrace_append hprefix tailTrace_1444842
  have hstable : (prefixWord ++ tailWord_1444842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444842).length < 2 ^ (prefixWord ++ tailWord_1444842).sum := by decide
  have hdescent : baseEnd_1444842 < baseStart_1444842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444949 : List Nat := [1, 3, 2, 2, 1, 2, 4, 2, 1, 4]
def baseStart_1444949 : Nat := 118140960795 + 1444949 * 2 ^ 59
def prefixEnd_1444949 : Nat := 4983230072969 + 3 ^ 40 * 1444949 * 2
def baseEnd_1444949 : Nat := 494635572155714909394871

theorem tailTrace_1444949 : CollatzResearch.WordTrace tailWord_1444949 prefixEnd_1444949 494635572155714909394871 := by
  unfold tailWord_1444949
  simp only [CollatzResearch.WordTrace]
  refine ⟨52701619642204025487337901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35134413094802683658225267 52701619642204025487337901)
  ·
    refine ⟨19763107365826509557751713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52701619642204025487337901 19763107365826509557751713)
    ·
      refine ⟨14822330524369882168313785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19763107365826509557751713 14822330524369882168313785)
      ·
        refine ⟨11116747893277411626235339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14822330524369882168313785 11116747893277411626235339)
        ·
          refine ⟨16675121839916117439353009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11116747893277411626235339 16675121839916117439353009)
          ·
            refine ⟨12506341379937088079514757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16675121839916117439353009 12506341379937088079514757)
            ·
              refine ⟨2344939008738204014909017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12506341379937088079514757 2344939008738204014909017)
              ·
                refine ⟨1758704256553653011181763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2344939008738204014909017 1758704256553653011181763)
                ·
                  refine ⟨2638056384830479516772645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758704256553653011181763 2638056384830479516772645)
                  ·
                    refine ⟨494635572155714909394871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2638056384830479516772645 494635572155714909394871)
                    ·
                      rfl

theorem cell22_1444949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_1444949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444949 prefixEnd_1444949 := by exact prefixLift 1444949
  have htrace : WordTrace (prefixWord ++ tailWord_1444949) baseStart_1444949 baseEnd_1444949 := by
    simpa [prefixWord, tailWord_1444949, baseEnd_1444949] using wordTrace_append hprefix tailTrace_1444949
  have hstable : (prefixWord ++ tailWord_1444949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444949).length < 2 ^ (prefixWord ++ tailWord_1444949).sum := by decide
  have hdescent : baseEnd_1444949 < baseStart_1444949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444957 : List Nat := [1, 4, 4, 1, 3, 1, 1, 3, 1, 3]
def baseStart_1444957 : Nat := 118140960795 + 1444957 * 2 ^ 59
def prefixEnd_1444957 : Nat := 4983230072969 + 3 ^ 40 * 1444957 * 2
def baseEnd_1444957 : Nat := 494638310719205555194847

theorem tailTrace_1444957 : CollatzResearch.WordTrace tailWord_1444957 prefixEnd_1444957 494638310719205555194847 := by
  unfold tailWord_1444957
  simp only [CollatzResearch.WordTrace]
  refine ⟨52701911426175042853629125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35134607617450028569086083 52701911426175042853629125)
  ·
    refine ⟨9881608392407820535055461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52701911426175042853629125 9881608392407820535055461)
    ·
      refine ⟨1852801573576466350322899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9881608392407820535055461 1852801573576466350322899)
      ·
        refine ⟨2779202360364699525484349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1852801573576466350322899 2779202360364699525484349)
        ·
          refine ⟨1042200885136762322056631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2779202360364699525484349 1042200885136762322056631)
          ·
            refine ⟨1563301327705143483084947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042200885136762322056631 1563301327705143483084947)
            ·
              refine ⟨2344951991557715224627421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563301327705143483084947 2344951991557715224627421)
              ·
                refine ⟨879356996834143209235283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2344951991557715224627421 879356996834143209235283)
                ·
                  refine ⟨1319035495251214813852925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 879356996834143209235283 1319035495251214813852925)
                  ·
                    refine ⟨494638310719205555194847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1319035495251214813852925 494638310719205555194847)
                    ·
                      rfl

theorem cell22_1444957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_1444957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444957 prefixEnd_1444957 := by exact prefixLift 1444957
  have htrace : WordTrace (prefixWord ++ tailWord_1444957) baseStart_1444957 baseEnd_1444957 := by
    simpa [prefixWord, tailWord_1444957, baseEnd_1444957] using wordTrace_append hprefix tailTrace_1444957
  have hstable : (prefixWord ++ tailWord_1444957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444957).length < 2 ^ (prefixWord ++ tailWord_1444957).sum := by decide
  have hdescent : baseEnd_1444957 < baseStart_1444957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444996 : List Nat := [2, 3, 2, 1, 2, 3, 1, 3, 2, 3]
def baseStart_1444996 : Nat := 118140960795 + 1444996 * 2 ^ 59
def prefixEnd_1444996 : Nat := 4983230072969 + 3 ^ 40 * 1444996 * 2
def baseEnd_1444996 : Nat := 494651661216222453469727

theorem tailTrace_1444996 : CollatzResearch.WordTrace tailWord_1444996 prefixEnd_1444996 494651661216222453469727 := by
  unfold tailWord_1444996
  simp only [CollatzResearch.WordTrace]
  refine ⟨26351666936516876257149421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35135555915355835009532561 26351666936516876257149421)
  ·
    refine ⟨9881875101193828596431033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26351666936516876257149421 9881875101193828596431033)
    ·
      refine ⟨7411406325895371447323275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9881875101193828596431033 7411406325895371447323275)
      ·
        refine ⟨11117109488843057170984913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7411406325895371447323275 11117109488843057170984913)
        ·
          refine ⟨8337832116632292878238685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11117109488843057170984913 8337832116632292878238685)
          ·
            refine ⟨3126687043737109829339507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8337832116632292878238685 3126687043737109829339507)
            ·
              refine ⟨4690030565605664744009261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3126687043737109829339507 4690030565605664744009261)
              ·
                refine ⟨1758761462102124279003473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4690030565605664744009261 1758761462102124279003473)
                ·
                  refine ⟨1319071096576593209252605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1758761462102124279003473 1319071096576593209252605)
                  ·
                    refine ⟨494651661216222453469727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1319071096576593209252605 494651661216222453469727)
                    ·
                      rfl

theorem cell22_1444996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_1444996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1444996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1444996 prefixEnd_1444996 := by exact prefixLift 1444996
  have htrace : WordTrace (prefixWord ++ tailWord_1444996) baseStart_1444996 baseEnd_1444996 := by
    simpa [prefixWord, tailWord_1444996, baseEnd_1444996] using wordTrace_append hprefix tailTrace_1444996
  have hstable : (prefixWord ++ tailWord_1444996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444996).length < 2 ^ (prefixWord ++ tailWord_1444996).sum := by decide
  have hdescent : baseEnd_1444996 < baseStart_1444996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445062 : List Nat := [6, 1, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_1445062 : Nat := 118140960795 + 1445062 * 2 ^ 59
def prefixEnd_1445062 : Nat := 4983230072969 + 3 ^ 40 * 1445062 * 2
def baseEnd_1445062 : Nat := 494674254365020281319525

theorem tailTrace_1445062 : CollatzResearch.WordTrace tailWord_1445062 prefixEnd_1445062 494674254365020281319525 := by
  unfold tailWord_1445062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1647054409087332680818795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35137160727196430524134293 1647054409087332680818795)
  ·
    refine ⟨2470581613630999021228193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1647054409087332680818795 2470581613630999021228193)
    ·
      refine ⟨1852936210223249265921145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2470581613630999021228193 1852936210223249265921145)
      ·
        refine ⟨1389702157667436949440859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1852936210223249265921145 1389702157667436949440859)
        ·
          refine ⟨2084553236501155424161289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1389702157667436949440859 2084553236501155424161289)
          ·
            refine ⟨1563414927375866568120967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2084553236501155424161289 1563414927375866568120967)
            ·
              refine ⟨2345122391063799852181451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563414927375866568120967 2345122391063799852181451)
              ·
                refine ⟨3517683586595699778272177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2345122391063799852181451 3517683586595699778272177)
                ·
                  refine ⟨2638262689946774833704133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3517683586595699778272177 2638262689946774833704133)
                  ·
                    refine ⟨494674254365020281319525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2638262689946774833704133 494674254365020281319525)
                    ·
                      rfl

theorem cell22_1445062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_1445062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445062 prefixEnd_1445062 := by exact prefixLift 1445062
  have htrace : WordTrace (prefixWord ++ tailWord_1445062) baseStart_1445062 baseEnd_1445062 := by
    simpa [prefixWord, tailWord_1445062, baseEnd_1445062] using wordTrace_append hprefix tailTrace_1445062
  have hstable : (prefixWord ++ tailWord_1445062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445062).length < 2 ^ (prefixWord ++ tailWord_1445062).sum := by decide
  have hdescent : baseEnd_1445062 < baseStart_1445062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445082 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 10]
def baseStart_1445082 : Nat := 118140960795 + 1445082 * 2 ^ 59
def prefixEnd_1445082 : Nat := 4983230072969 + 3 ^ 40 * 1445082 * 2
def baseEnd_1445082 : Nat := 164893700257915631939821

theorem tailTrace_1445082 : CollatzResearch.WordTrace tailWord_1445082 prefixEnd_1445082 164893700257915631939821 := by
  unfold tailWord_1445082
  simp only [CollatzResearch.WordTrace]
  refine ⟨13176617637680547300482375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35137647033814792801286333 13176617637680547300482375)
  ·
    refine ⟨19764926456520820950723563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13176617637680547300482375 19764926456520820950723563)
    ·
      refine ⟨29647389684781231426085345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19764926456520820950723563 29647389684781231426085345)
      ·
        refine ⟨22235542263585923569564009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29647389684781231426085345 22235542263585923569564009)
        ·
          refine ⟨16676656697689442677173007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22235542263585923569564009 16676656697689442677173007)
          ·
            refine ⟨25014985046534164015759511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16676656697689442677173007 25014985046534164015759511)
            ·
              refine ⟨37522477569801246023639267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25014985046534164015759511 37522477569801246023639267)
              ·
                refine ⟨56283716354701869035458901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37522477569801246023639267 56283716354701869035458901)
                ·
                  refine ⟨164893700257915631939821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 56283716354701869035458901 164893700257915631939821)
                  ·
                    rfl

theorem cell22_1445082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_1445082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445082 prefixEnd_1445082 := by exact prefixLift 1445082
  have htrace : WordTrace (prefixWord ++ tailWord_1445082) baseStart_1445082 baseEnd_1445082 := by
    simpa [prefixWord, tailWord_1445082, baseEnd_1445082] using wordTrace_append hprefix tailTrace_1445082
  have hstable : (prefixWord ++ tailWord_1445082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445082).length < 2 ^ (prefixWord ++ tailWord_1445082).sum := by decide
  have hdescent : baseEnd_1445082 < baseStart_1445082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445099 : List Nat := [1, 1, 1, 1, 2, 7, 2, 1, 6]
def baseStart_1445099 : Nat := 118140960795 + 1445099 * 2 ^ 59
def prefixEnd_1445099 : Nat := 4983230072969 + 3 ^ 40 * 1445099 * 2
def baseEnd_1445099 : Nat := 164895640073721506048137

theorem tailTrace_1445099 : CollatzResearch.WordTrace tailWord_1445099 prefixEnd_1445099 164895640073721506048137 := by
  unfold tailWord_1445099
  simp only [CollatzResearch.WordTrace]
  refine ⟨52707090591660601105298351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35138060394440400736865567 52707090591660601105298351)
  ·
    refine ⟨79060635887490901657947527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52707090591660601105298351 79060635887490901657947527)
    ·
      refine ⟨118590953831236352486921291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79060635887490901657947527 118590953831236352486921291)
      ·
        refine ⟨177886430746854528730381937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118590953831236352486921291 177886430746854528730381937)
        ·
          refine ⟨133414823060140896547786453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177886430746854528730381937 133414823060140896547786453)
          ·
            refine ⟨3126909915472052262838745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 133414823060140896547786453 3126909915472052262838745)
            ·
              refine ⟨2345182436604039197129059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3126909915472052262838745 2345182436604039197129059)
              ·
                refine ⟨3517773654906058795693589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2345182436604039197129059 3517773654906058795693589)
                ·
                  refine ⟨164895640073721506048137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3517773654906058795693589 164895640073721506048137)
                  ·
                    rfl

theorem cell22_1445099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 6].length) (baseStart_1445099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445099 prefixEnd_1445099 := by exact prefixLift 1445099
  have htrace : WordTrace (prefixWord ++ tailWord_1445099) baseStart_1445099 baseEnd_1445099 := by
    simpa [prefixWord, tailWord_1445099, baseEnd_1445099] using wordTrace_append hprefix tailTrace_1445099
  have hstable : (prefixWord ++ tailWord_1445099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445099).length < 2 ^ (prefixWord ++ tailWord_1445099).sum := by decide
  have hdescent : baseEnd_1445099 < baseStart_1445099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445118 : List Nat := [4, 2, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_1445118 : Nat := 118140960795 + 1445118 * 2 ^ 59
def prefixEnd_1445118 : Nat := 4983230072969 + 3 ^ 40 * 1445118 * 2
def baseEnd_1445118 : Nat := 494693424309454801919353

theorem tailTrace_1445118 : CollatzResearch.WordTrace tailWord_1445118 prefixEnd_1445118 494693424309454801919353 := by
  unfold tailWord_1445118
  simp only [CollatzResearch.WordTrace]
  refine ⟨6588472947323970918780001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35138522385727844900160005 6588472947323970918780001)
  ·
    refine ⟨4941354710492978189085001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6588472947323970918780001 4941354710492978189085001)
    ·
      refine ⟨3706016032869733641813751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4941354710492978189085001 3706016032869733641813751)
      ·
        refine ⟨5559024049304600462720627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3706016032869733641813751 5559024049304600462720627)
        ·
          refine ⟨8338536073956900694080941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5559024049304600462720627 8338536073956900694080941)
          ·
            refine ⟨3126951027733837760280353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8338536073956900694080941 3126951027733837760280353)
            ·
              refine ⟨2345213270800378320210265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3126951027733837760280353 2345213270800378320210265)
              ·
                refine ⟨1758909953100283740157699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2345213270800378320210265 1758909953100283740157699)
                ·
                  refine ⟨2638364929650425610236549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758909953100283740157699 2638364929650425610236549)
                  ·
                    refine ⟨494693424309454801919353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2638364929650425610236549 494693424309454801919353)
                    ·
                      rfl

theorem cell22_1445118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_1445118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445118 prefixEnd_1445118 := by exact prefixLift 1445118
  have htrace : WordTrace (prefixWord ++ tailWord_1445118) baseStart_1445118 baseEnd_1445118 := by
    simpa [prefixWord, tailWord_1445118, baseEnd_1445118] using wordTrace_append hprefix tailTrace_1445118
  have hstable : (prefixWord ++ tailWord_1445118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445118).length < 2 ^ (prefixWord ++ tailWord_1445118).sum := by decide
  have hdescent : baseEnd_1445118 < baseStart_1445118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445129 : List Nat := [1, 2, 1, 1, 3, 3, 2, 3, 2, 4]
def baseStart_1445129 : Nat := 118140960795 + 1445129 * 2 ^ 59
def prefixEnd_1445129 : Nat := 4983230072969 + 3 ^ 40 * 1445129 * 2
def baseEnd_1445129 : Nat := 494697189834254439894319

theorem tailTrace_1445129 : CollatzResearch.WordTrace tailWord_1445129 prefixEnd_1445129 494697189834254439894319 := by
  unfold tailWord_1445129
  simp only [CollatzResearch.WordTrace]
  refine ⟨52708184781551916228890441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35138789854367944152593627 52708184781551916228890441)
  ·
    refine ⟨39531138586163937171667831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52708184781551916228890441 39531138586163937171667831)
    ·
      refine ⟨59296707879245905757501747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39531138586163937171667831 59296707879245905757501747)
      ·
        refine ⟨88945061818868858636252621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59296707879245905757501747 88945061818868858636252621)
        ·
          refine ⟨33354398182075821988594733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88945061818868858636252621 33354398182075821988594733)
          ·
            refine ⟨12507899318278433245723025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33354398182075821988594733 12507899318278433245723025)
            ·
              refine ⟨9380924488708824934292269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12507899318278433245723025 9380924488708824934292269)
              ·
                refine ⟨3517846683265809350359601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9380924488708824934292269 3517846683265809350359601)
                ·
                  refine ⟨2638385012449357012769701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3517846683265809350359601 2638385012449357012769701)
                  ·
                    refine ⟨494697189834254439894319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2638385012449357012769701 494697189834254439894319)
                    ·
                      rfl

theorem cell22_1445129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_1445129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445129 prefixEnd_1445129 := by exact prefixLift 1445129
  have htrace : WordTrace (prefixWord ++ tailWord_1445129) baseStart_1445129 baseEnd_1445129 := by
    simpa [prefixWord, tailWord_1445129, baseEnd_1445129] using wordTrace_append hprefix tailTrace_1445129
  have hstable : (prefixWord ++ tailWord_1445129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445129).length < 2 ^ (prefixWord ++ tailWord_1445129).sum := by decide
  have hdescent : baseEnd_1445129 < baseStart_1445129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445144 : List Nat := [2, 1, 2, 3, 1, 5, 8]
def baseStart_1445144 : Nat := 118140960795 + 1445144 * 2 ^ 59
def prefixEnd_1445144 : Nat := 4983230072969 + 3 ^ 40 * 1445144 * 2
def baseEnd_1445144 : Nat := 18322308320029607435899

theorem tailTrace_1445144 : CollatzResearch.WordTrace tailWord_1445144 prefixEnd_1445144 18322308320029607435899 := by
  unfold tailWord_1445144
  simp only [CollatzResearch.WordTrace]
  refine ⟨26354365938248786895343243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35139154584331715860457657 26354365938248786895343243)
  ·
    refine ⟨39531548907373180343014865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26354365938248786895343243 39531548907373180343014865)
    ·
      refine ⟨29648661680529885257261149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39531548907373180343014865 29648661680529885257261149)
      ·
        refine ⟨11118248130198706971472931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29648661680529885257261149 11118248130198706971472931)
        ·
          refine ⟨16677372195298060457209397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11118248130198706971472931 16677372195298060457209397)
          ·
            refine ⟨1563503643309193167863381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16677372195298060457209397 1563503643309193167863381)
            ·
              refine ⟨18322308320029607435899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1563503643309193167863381 18322308320029607435899)
              ·
                rfl

theorem cell22_1445144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 8].length) (baseStart_1445144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445144 prefixEnd_1445144 := by exact prefixLift 1445144
  have htrace : WordTrace (prefixWord ++ tailWord_1445144) baseStart_1445144 baseEnd_1445144 := by
    simpa [prefixWord, tailWord_1445144, baseEnd_1445144] using wordTrace_append hprefix tailTrace_1445144
  have hstable : (prefixWord ++ tailWord_1445144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445144).length < 2 ^ (prefixWord ++ tailWord_1445144).sum := by decide
  have hdescent : baseEnd_1445144 < baseStart_1445144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445146 : List Nat := [3, 1, 1, 3, 3, 2, 1, 2, 2, 4]
def baseStart_1445146 : Nat := 118140960795 + 1445146 * 2 ^ 59
def prefixEnd_1445146 : Nat := 4983230072969 + 3 ^ 40 * 1445146 * 2
def baseEnd_1445146 : Nat := 494703009281672062219267

theorem tailTrace_1445146 : CollatzResearch.WordTrace tailWord_1445146 prefixEnd_1445146 494703009281672062219267 := by
  unfold tailWord_1445146
  simp only [CollatzResearch.WordTrace]
  refine ⟨13177201205622582033064823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35139203214993552088172861 13177201205622582033064823)
  ·
    refine ⟨19765801808433873049597235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13177201205622582033064823 19765801808433873049597235)
    ·
      refine ⟨29648702712650809574395853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19765801808433873049597235 29648702712650809574395853)
      ·
        refine ⟨11118263517244053590398445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29648702712650809574395853 11118263517244053590398445)
        ·
          refine ⟨4169348818966520096399417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11118263517244053590398445 4169348818966520096399417)
          ·
            refine ⟨3127011614224890072299563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4169348818966520096399417 3127011614224890072299563)
            ·
              refine ⟨4690517421337335108449345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127011614224890072299563 4690517421337335108449345)
              ·
                refine ⟨3517888066003001331337009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4690517421337335108449345 3517888066003001331337009)
                ·
                  refine ⟨2638416049502250998502757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3517888066003001331337009 2638416049502250998502757)
                  ·
                    refine ⟨494703009281672062219267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2638416049502250998502757 494703009281672062219267)
                    ·
                      rfl

theorem cell22_1445146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_1445146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445146 prefixEnd_1445146 := by exact prefixLift 1445146
  have htrace : WordTrace (prefixWord ++ tailWord_1445146) baseStart_1445146 baseEnd_1445146 := by
    simpa [prefixWord, tailWord_1445146, baseEnd_1445146] using wordTrace_append hprefix tailTrace_1445146
  have hstable : (prefixWord ++ tailWord_1445146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445146).length < 2 ^ (prefixWord ++ tailWord_1445146).sum := by decide
  have hdescent : baseEnd_1445146 < baseStart_1445146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445150 : List Nat := [4, 3, 2, 1, 2, 2, 1, 1, 6]
def baseStart_1445150 : Nat := 118140960795 + 1445150 * 2 ^ 59
def prefixEnd_1445150 : Nat := 4983230072969 + 3 ^ 40 * 1445150 * 2
def baseEnd_1445150 : Nat := 164901459521139128373085

theorem tailTrace_1445150 : CollatzResearch.WordTrace tailWord_1445150 prefixEnd_1445150 164901459521139128373085 := by
  unfold tailWord_1445150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6588618839309479601925613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35139300476317224543603269 6588618839309479601925613)
  ·
    refine ⟨2470732064741054850722105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6588618839309479601925613 2470732064741054850722105)
    ·
      refine ⟨1853049048555791138041579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2470732064741054850722105 1853049048555791138041579)
      ·
        refine ⟨2779573572833686707062369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1853049048555791138041579 2779573572833686707062369)
        ·
          refine ⟨2084680179625265030296777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2779573572833686707062369 2084680179625265030296777)
          ·
            refine ⟨1563510134718948772722583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2084680179625265030296777 1563510134718948772722583)
            ·
              refine ⟨2345265202078423159083875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563510134718948772722583 2345265202078423159083875)
              ·
                refine ⟨3517897803117634738625813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2345265202078423159083875 3517897803117634738625813)
                ·
                  refine ⟨164901459521139128373085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3517897803117634738625813 164901459521139128373085)
                  ·
                    rfl

theorem cell22_1445150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_1445150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445150 prefixEnd_1445150 := by exact prefixLift 1445150
  have htrace : WordTrace (prefixWord ++ tailWord_1445150) baseStart_1445150 baseEnd_1445150 := by
    simpa [prefixWord, tailWord_1445150, baseEnd_1445150] using wordTrace_append hprefix tailTrace_1445150
  have hstable : (prefixWord ++ tailWord_1445150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445150).length < 2 ^ (prefixWord ++ tailWord_1445150).sum := by decide
  have hdescent : baseEnd_1445150 < baseStart_1445150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445165 : List Nat := [1, 5, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_1445165 : Nat := 118140960795 + 1445165 * 2 ^ 59
def prefixEnd_1445165 : Nat := 4983230072969 + 3 ^ 40 * 1445165 * 2
def baseEnd_1445165 : Nat := 494709513369962345994209

theorem tailTrace_1445165 : CollatzResearch.WordTrace tailWord_1445165 prefixEnd_1445165 494709513369962345994209 := by
  unfold tailWord_1445165
  simp only [CollatzResearch.WordTrace]
  refine ⟨52709497809421494377200949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35139665206280996251467299 52709497809421494377200949)
  ·
    refine ⟨4941515419633265097862589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52709497809421494377200949 4941515419633265097862589)
    ·
      refine ⟨1853068282362474411698471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4941515419633265097862589 1853068282362474411698471)
      ·
        refine ⟨2779602423543711617547707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1853068282362474411698471 2779602423543711617547707)
        ·
          refine ⟨4169403635315567426321561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2779602423543711617547707 4169403635315567426321561)
          ·
            refine ⟨3127052726486675569741171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4169403635315567426321561 3127052726486675569741171)
            ·
              refine ⟨4690579089730013354611757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127052726486675569741171 4690579089730013354611757)
              ·
                refine ⟨1758967158648755007979409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4690579089730013354611757 1758967158648755007979409)
                ·
                  refine ⟨1319225368986566255984557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1758967158648755007979409 1319225368986566255984557)
                  ·
                    refine ⟨494709513369962345994209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1319225368986566255984557 494709513369962345994209)
                    ·
                      rfl

theorem cell22_1445165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_1445165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445165 prefixEnd_1445165 := by exact prefixLift 1445165
  have htrace : WordTrace (prefixWord ++ tailWord_1445165) baseStart_1445165 baseEnd_1445165 := by
    simpa [prefixWord, tailWord_1445165, baseEnd_1445165] using wordTrace_append hprefix tailTrace_1445165
  have hstable : (prefixWord ++ tailWord_1445165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445165).length < 2 ^ (prefixWord ++ tailWord_1445165).sum := by decide
  have hdescent : baseEnd_1445165 < baseStart_1445165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445210 : List Nat := [3, 1, 1, 2, 1, 2, 6, 2, 1, 3]
def baseStart_1445210 : Nat := 118140960795 + 1445210 * 2 ^ 59
def prefixEnd_1445210 : Nat := 4983230072969 + 3 ^ 40 * 1445210 * 2
def baseEnd_1445210 : Nat := 494724917789597228619071

theorem tailTrace_1445210 : CollatzResearch.WordTrace tailWord_1445210 prefixEnd_1445210 494724917789597228619071 := by
  unfold tailWord_1445210
  simp only [CollatzResearch.WordTrace]
  refine ⟨13177784773564616765647271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35140759396172311375059389 13177784773564616765647271)
  ·
    refine ⟨19766677160346925148470907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13177784773564616765647271 19766677160346925148470907)
    ·
      refine ⟨29650015740520387722706361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19766677160346925148470907 29650015740520387722706361)
      ·
        refine ⟨22237511805390290792029771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29650015740520387722706361 22237511805390290792029771)
        ·
          refine ⟨33356267708085436188044657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22237511805390290792029771 33356267708085436188044657)
          ·
            refine ⟨25017200781064077141033493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33356267708085436188044657 25017200781064077141033493)
            ·
              refine ⟨1172681286612378615985945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25017200781064077141033493 1172681286612378615985945)
              ·
                refine ⟨879510964959283961989459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1172681286612378615985945 879510964959283961989459)
                ·
                  refine ⟨1319266447438925942984189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 879510964959283961989459 1319266447438925942984189)
                  ·
                    refine ⟨494724917789597228619071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1319266447438925942984189 494724917789597228619071)
                    ·
                      rfl

theorem cell22_1445210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 1, 3].length) (baseStart_1445210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445210 prefixEnd_1445210 := by exact prefixLift 1445210
  have htrace : WordTrace (prefixWord ++ tailWord_1445210) baseStart_1445210 baseEnd_1445210 := by
    simpa [prefixWord, tailWord_1445210, baseEnd_1445210] using wordTrace_append hprefix tailTrace_1445210
  have hstable : (prefixWord ++ tailWord_1445210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445210).length < 2 ^ (prefixWord ++ tailWord_1445210).sum := by decide
  have hdescent : baseEnd_1445210 < baseStart_1445210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445253 : List Nat := [1, 3, 1, 1, 3, 1, 6, 1, 1, 4]
def baseStart_1445253 : Nat := 118140960795 + 1445253 * 2 ^ 59
def prefixEnd_1445253 : Nat := 4983230072969 + 3 ^ 40 * 1445253 * 2
def baseEnd_1445253 : Nat := 494739637568359449793939

theorem tailTrace_1445253 : CollatzResearch.WordTrace tailWord_1445253 prefixEnd_1445253 494739637568359449793939 := by
  unfold tailWord_1445253
  simp only [CollatzResearch.WordTrace]
  refine ⟨52712707433102685406404413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35141804955401790270936275 52712707433102685406404413)
  ·
    refine ⟨19767265287413507027401655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52712707433102685406404413 19767265287413507027401655)
    ·
      refine ⟨29650897931120260541102483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19767265287413507027401655 29650897931120260541102483)
      ·
        refine ⟨44476346896680390811653725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29650897931120260541102483 44476346896680390811653725)
        ·
          refine ⟨16678630086255146554370147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44476346896680390811653725 16678630086255146554370147)
          ·
            refine ⟨25017945129382719831555221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16678630086255146554370147 25017945129382719831555221)
            ·
              refine ⟨1172716177939814992104151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25017945129382719831555221 1172716177939814992104151)
              ·
                refine ⟨1759074266909722488156227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1172716177939814992104151 1759074266909722488156227)
                ·
                  refine ⟨2638611400364583732234341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1759074266909722488156227 2638611400364583732234341)
                  ·
                    refine ⟨494739637568359449793939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2638611400364583732234341 494739637568359449793939)
                    ·
                      rfl

theorem cell22_1445253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 1, 4].length) (baseStart_1445253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445253 prefixEnd_1445253 := by exact prefixLift 1445253
  have htrace : WordTrace (prefixWord ++ tailWord_1445253) baseStart_1445253 baseEnd_1445253 := by
    simpa [prefixWord, tailWord_1445253, baseEnd_1445253] using wordTrace_append hprefix tailTrace_1445253
  have hstable : (prefixWord ++ tailWord_1445253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445253).length < 2 ^ (prefixWord ++ tailWord_1445253).sum := by decide
  have hdescent : baseEnd_1445253 < baseStart_1445253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445268 : List Nat := [2, 4, 2, 1, 2, 2, 2, 1, 6]
def baseStart_1445268 : Nat := 118140960795 + 1445268 * 2 ^ 59
def prefixEnd_1445268 : Nat := 4983230072969 + 3 ^ 40 * 1445268 * 2
def baseEnd_1445268 : Nat := 164914924124968136889631

theorem tailTrace_1445268 : CollatzResearch.WordTrace tailWord_1445268 prefixEnd_1445268 164914924124968136889631 := by
  unfold tailWord_1445268
  simp only [CollatzResearch.WordTrace]
  refine ⟨26356627264024171484100229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35142169685365561978800305 26356627264024171484100229)
  ·
    refine ⟨4941867612004532153268793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26356627264024171484100229 4941867612004532153268793)
    ·
      refine ⟨3706400709003399114951595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4941867612004532153268793 3706400709003399114951595)
      ·
        refine ⟨5559601063505098672427393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3706400709003399114951595 5559601063505098672427393)
        ·
          refine ⟨4169700797628824004320545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5559601063505098672427393 4169700797628824004320545)
          ·
            refine ⟨3127275598221618003240409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4169700797628824004320545 3127275598221618003240409)
            ·
              refine ⟨2345456698666213502430307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3127275598221618003240409 2345456698666213502430307)
              ·
                refine ⟨3518185047999320253645461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2345456698666213502430307 3518185047999320253645461)
                ·
                  refine ⟨164914924124968136889631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3518185047999320253645461 164914924124968136889631)
                  ·
                    rfl

theorem cell22_1445268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_1445268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445268 prefixEnd_1445268 := by exact prefixLift 1445268
  have htrace : WordTrace (prefixWord ++ tailWord_1445268) baseStart_1445268 baseEnd_1445268 := by
    simpa [prefixWord, tailWord_1445268, baseEnd_1445268] using wordTrace_append hprefix tailTrace_1445268
  have hstable : (prefixWord ++ tailWord_1445268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445268).length < 2 ^ (prefixWord ++ tailWord_1445268).sum := by decide
  have hdescent : baseEnd_1445268 < baseStart_1445268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445311 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 5, 3]
def baseStart_1445311 : Nat := 118140960795 + 1445311 * 2 ^ 59
def prefixEnd_1445311 : Nat := 4983230072969 + 3 ^ 40 * 1445311 * 2
def baseEnd_1445311 : Nat := 494759492153666631843761

theorem tailTrace_1445311 : CollatzResearch.WordTrace tailWord_1445311 prefixEnd_1445311 494759492153666631843761 := by
  unfold tailWord_1445311
  simp only [CollatzResearch.WordTrace]
  refine ⟨52714822866892561312015787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35143215244595040874677191 52714822866892561312015787)
  ·
    refine ⟨79072234300338841968023681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52714822866892561312015787 79072234300338841968023681)
    ·
      refine ⟨59304175725254131476017761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79072234300338841968023681 59304175725254131476017761)
      ·
        refine ⟨44478131793940598607013321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59304175725254131476017761 44478131793940598607013321)
        ·
          refine ⟨33358598845455448955259991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44478131793940598607013321 33358598845455448955259991)
          ·
            refine ⟨50037898268183173432889987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33358598845455448955259991 50037898268183173432889987)
            ·
              refine ⟨75056847402274760149334981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50037898268183173432889987 75056847402274760149334981)
              ·
                refine ⟨14073158887926517528000309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75056847402274760149334981 14073158887926517528000309)
                ·
                  refine ⟨1319358645743111018250029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14073158887926517528000309 1319358645743111018250029)
                  ·
                    refine ⟨494759492153666631843761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1319358645743111018250029 494759492153666631843761)
                    ·
                      rfl

theorem cell22_1445311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 3].length) (baseStart_1445311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445311 prefixEnd_1445311 := by exact prefixLift 1445311
  have htrace : WordTrace (prefixWord ++ tailWord_1445311) baseStart_1445311 baseEnd_1445311 := by
    simpa [prefixWord, tailWord_1445311, baseEnd_1445311] using wordTrace_append hprefix tailTrace_1445311
  have hstable : (prefixWord ++ tailWord_1445311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445311).length < 2 ^ (prefixWord ++ tailWord_1445311).sum := by decide
  have hdescent : baseEnd_1445311 < baseStart_1445311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445334 : List Nat := [5, 2, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_1445334 : Nat := 118140960795 + 1445334 * 2 ^ 59
def prefixEnd_1445334 : Nat := 4983230072969 + 3 ^ 40 * 1445334 * 2
def baseEnd_1445334 : Nat := 494767365523702238518691

theorem tailTrace_1445334 : CollatzResearch.WordTrace tailWord_1445334 prefixEnd_1445334 494767365523702238518691 := by
  unfold tailWord_1445334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3294728859113077265006441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35143774497206157493402037 3294728859113077265006441)
  ·
    refine ⟨2471046644334807948754831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3294728859113077265006441 2471046644334807948754831)
    ·
      refine ⟨3706569966502211923132247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2471046644334807948754831 3706569966502211923132247)
      ·
        refine ⟨5559854949753317884698371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3706569966502211923132247 5559854949753317884698371)
        ·
          refine ⟨8339782424629976827047557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5559854949753317884698371 8339782424629976827047557)
          ·
            refine ⟨1563709204618120655071417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8339782424629976827047557 1563709204618120655071417)
            ·
              refine ⟨1172781903463590491303563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1563709204618120655071417 1172781903463590491303563)
              ·
                refine ⟨1759172855195385736955345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1172781903463590491303563 1759172855195385736955345)
                ·
                  refine ⟨1319379641396539302716509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1759172855195385736955345 1319379641396539302716509)
                  ·
                    refine ⟨494767365523702238518691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1319379641396539302716509 494767365523702238518691)
                    ·
                      rfl

theorem cell22_1445334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_1445334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445334 prefixEnd_1445334 := by exact prefixLift 1445334
  have htrace : WordTrace (prefixWord ++ tailWord_1445334) baseStart_1445334 baseEnd_1445334 := by
    simpa [prefixWord, tailWord_1445334, baseEnd_1445334] using wordTrace_append hprefix tailTrace_1445334
  have hstable : (prefixWord ++ tailWord_1445334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445334).length < 2 ^ (prefixWord ++ tailWord_1445334).sum := by decide
  have hdescent : baseEnd_1445334 < baseStart_1445334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445418 : List Nat := [3, 1, 4, 1, 1, 1, 1, 4, 1, 5]
def baseStart_1445418 : Nat := 118140960795 + 1445418 * 2 ^ 59
def prefixEnd_1445418 : Nat := 4983230072969 + 3 ^ 40 * 1445418 * 2
def baseEnd_1445418 : Nat := 494796120440354019418433

theorem tailTrace_1445418 : CollatzResearch.WordTrace tailWord_1445418 prefixEnd_1445418 494796120440354019418433 := by
  unfold tailWord_1445418
  simp only [CollatzResearch.WordTrace]
  refine ⟨13179681369376229646540227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35145816985003279057440605 13179681369376229646540227)
  ·
    refine ⟨19769522054064344469810341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13179681369376229646540227 19769522054064344469810341)
    ·
      refine ⟨3706785385137064588089439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19769522054064344469810341 3706785385137064588089439)
      ·
        refine ⟨5560178077705596882134159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3706785385137064588089439 5560178077705596882134159)
        ·
          refine ⟨8340267116558395323201239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5560178077705596882134159 8340267116558395323201239)
          ·
            refine ⟨12510400674837592984801859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8340267116558395323201239 12510400674837592984801859)
            ·
              refine ⟨18765601012256389477202789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12510400674837592984801859 18765601012256389477202789)
              ·
                refine ⟨3518550189798073026975523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18765601012256389477202789 3518550189798073026975523)
                ·
                  refine ⟨5277825284697109540463285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3518550189798073026975523 5277825284697109540463285)
                  ·
                    refine ⟨494796120440354019418433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5277825284697109540463285 494796120440354019418433)
                    ·
                      rfl

theorem cell22_1445418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_1445418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445418 prefixEnd_1445418 := by exact prefixLift 1445418
  have htrace : WordTrace (prefixWord ++ tailWord_1445418) baseStart_1445418 baseEnd_1445418 := by
    simpa [prefixWord, tailWord_1445418, baseEnd_1445418] using wordTrace_append hprefix tailTrace_1445418
  have hstable : (prefixWord ++ tailWord_1445418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445418).length < 2 ^ (prefixWord ++ tailWord_1445418).sum := by decide
  have hdescent : baseEnd_1445418 < baseStart_1445418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445422 : List Nat := [4, 1, 3, 1, 2, 1, 4, 1, 1, 4]
def baseStart_1445422 : Nat := 118140960795 + 1445422 * 2 ^ 59
def prefixEnd_1445422 : Nat := 4983230072969 + 3 ^ 40 * 1445422 * 2
def baseEnd_1445422 : Nat := 494797489722099342318421

theorem tailTrace_1445422 : CollatzResearch.WordTrace tailWord_1445422 prefixEnd_1445422 494797489722099342318421 := by
  unfold tailWord_1445422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6589858921186303408663315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35145914246326951512871013 6589858921186303408663315)
  ·
    refine ⟨9884788381779455112994973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6589858921186303408663315 9884788381779455112994973)
    ·
      refine ⟨3706795643167295667373115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9884788381779455112994973 3706795643167295667373115)
      ·
        refine ⟨5560193464750943501059673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3706795643167295667373115 5560193464750943501059673)
        ·
          refine ⟨4170145098563207625794755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5560193464750943501059673 4170145098563207625794755)
          ·
            refine ⟨6255217647844811438692133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4170145098563207625794755 6255217647844811438692133)
            ·
              refine ⟨1172853308970902144754775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6255217647844811438692133 1172853308970902144754775)
              ·
                refine ⟨1759279963456353217132163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1172853308970902144754775 1759279963456353217132163)
                ·
                  refine ⟨2638919945184529825698245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1759279963456353217132163 2638919945184529825698245)
                  ·
                    refine ⟨494797489722099342318421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2638919945184529825698245 494797489722099342318421)
                    ·
                      rfl

theorem cell22_1445422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_1445422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445422 prefixEnd_1445422 := by exact prefixLift 1445422
  have htrace : WordTrace (prefixWord ++ tailWord_1445422) baseStart_1445422 baseEnd_1445422 := by
    simpa [prefixWord, tailWord_1445422, baseEnd_1445422] using wordTrace_append hprefix tailTrace_1445422
  have hstable : (prefixWord ++ tailWord_1445422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445422).length < 2 ^ (prefixWord ++ tailWord_1445422).sum := by decide
  have hdescent : baseEnd_1445422 < baseStart_1445422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445431 : List Nat := [1, 1, 3, 1, 2, 5, 9]
def baseStart_1445431 : Nat := 118140960795 + 1445431 * 2 ^ 59
def prefixEnd_1445431 : Nat := 4983230072969 + 3 ^ 40 * 1445431 * 2
def baseEnd_1445431 : Nat := 18325947059482456253459

theorem tailTrace_1445431 : CollatzResearch.WordTrace tailWord_1445431 prefixEnd_1445431 18325947059482456253459 := by
  unfold tailWord_1445431
  simp only [CollatzResearch.WordTrace]
  refine ⟨52719199626457821806384147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35146133084305214537589431 52719199626457821806384147)
  ·
    refine ⟨79078799439686732709576221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52719199626457821806384147 79078799439686732709576221)
    ·
      refine ⟨29654549789882524766091083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79078799439686732709576221 29654549789882524766091083)
      ·
        refine ⟨44481824684823787149136625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29654549789882524766091083 44481824684823787149136625)
        ·
          refine ⟨33361368513617840361852469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44481824684823787149136625 33361368513617840361852469)
          ·
            refine ⟨3127628298151672533923669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33361368513617840361852469 3127628298151672533923669)
            ·
              refine ⟨18325947059482456253459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3127628298151672533923669 18325947059482456253459)
              ·
                rfl

theorem cell22_1445431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 9].length) (baseStart_1445431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445431 prefixEnd_1445431 := by exact prefixLift 1445431
  have htrace : WordTrace (prefixWord ++ tailWord_1445431) baseStart_1445431 baseEnd_1445431 := by
    simpa [prefixWord, tailWord_1445431, baseEnd_1445431] using wordTrace_append hprefix tailTrace_1445431
  have hstable : (prefixWord ++ tailWord_1445431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445431).length < 2 ^ (prefixWord ++ tailWord_1445431).sum := by decide
  have hdescent : baseEnd_1445431 < baseStart_1445431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445452 : List Nat := [2, 2, 1, 3, 1, 4, 3, 1, 2, 3]
def baseStart_1445452 : Nat := 118140960795 + 1445452 * 2 ^ 59
def prefixEnd_1445452 : Nat := 4983230072969 + 3 ^ 40 * 1445452 * 2
def baseEnd_1445452 : Nat := 494807759335189264068329

theorem tailTrace_1445452 : CollatzResearch.WordTrace tailWord_1445452 prefixEnd_1445452 494807759335189264068329 := by
  unfold tailWord_1445452
  simp only [CollatzResearch.WordTrace]
  refine ⟨26359982779690871196449305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35146643706254494928599073 26359982779690871196449305)
  ·
    refine ⟨19769987084768153397336979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26359982779690871196449305 19769987084768153397336979)
    ·
      refine ⟨29654980627152230096005469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19769987084768153397336979 29654980627152230096005469)
      ·
        refine ⟨11120617735182086286002051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29654980627152230096005469 11120617735182086286002051)
        ·
          refine ⟨16680926602773129429003077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11120617735182086286002051 16680926602773129429003077)
          ·
            refine ⟨3127673738019961767938077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16680926602773129429003077 3127673738019961767938077)
            ·
              refine ⟨1172877651757485662976779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3127673738019961767938077 1172877651757485662976779)
              ·
                refine ⟨1759316477636228494465169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1172877651757485662976779 1759316477636228494465169)
                ·
                  refine ⟨1319487358227171370848877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1759316477636228494465169 1319487358227171370848877)
                  ·
                    refine ⟨494807759335189264068329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1319487358227171370848877 494807759335189264068329)
                    ·
                      rfl

theorem cell22_1445452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 2, 3].length) (baseStart_1445452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445452 prefixEnd_1445452 := by exact prefixLift 1445452
  have htrace : WordTrace (prefixWord ++ tailWord_1445452) baseStart_1445452 baseEnd_1445452 := by
    simpa [prefixWord, tailWord_1445452, baseEnd_1445452] using wordTrace_append hprefix tailTrace_1445452
  have hstable : (prefixWord ++ tailWord_1445452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445452).length < 2 ^ (prefixWord ++ tailWord_1445452).sum := by decide
  have hdescent : baseEnd_1445452 < baseStart_1445452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445555 : List Nat := [1, 1, 1, 2, 3, 3, 3, 4, 4]
def baseStart_1445555 : Nat := 118140960795 + 1445555 * 2 ^ 59
def prefixEnd_1445555 : Nat := 4983230072969 + 3 ^ 40 * 1445555 * 2
def baseEnd_1445555 : Nat := 164947672780043776247671

theorem tailTrace_1445555 : CollatzResearch.WordTrace tailWord_1445555 prefixEnd_1445555 164947672780043776247671 := by
  unfold tailWord_1445555
  simp only [CollatzResearch.WordTrace]
  refine ⟨52723722278008590983898119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35149148185339060655932079 52723722278008590983898119)
  ·
    refine ⟨79085583417012886475847179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52723722278008590983898119 79085583417012886475847179)
    ·
      refine ⟨118628375125519329713770769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79085583417012886475847179 118628375125519329713770769)
      ·
        refine ⟨88971281344139497285328077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118628375125519329713770769 88971281344139497285328077)
        ·
          refine ⟨33364230504052311481998029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88971281344139497285328077 33364230504052311481998029)
          ·
            refine ⟨12511586439019616805749261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33364230504052311481998029 12511586439019616805749261)
            ·
              refine ⟨4691844914632356302155973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12511586439019616805749261 4691844914632356302155973)
              ·
                refine ⟨879720921493566806654245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4691844914632356302155973 879720921493566806654245)
                ·
                  refine ⟨164947672780043776247671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 879720921493566806654245 164947672780043776247671)
                  ·
                    rfl

theorem cell22_1445555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 4].length) (baseStart_1445555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445555 prefixEnd_1445555 := by exact prefixLift 1445555
  have htrace : WordTrace (prefixWord ++ tailWord_1445555) baseStart_1445555 baseEnd_1445555 := by
    simpa [prefixWord, tailWord_1445555, baseEnd_1445555] using wordTrace_append hprefix tailTrace_1445555
  have hstable : (prefixWord ++ tailWord_1445555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445555).length < 2 ^ (prefixWord ++ tailWord_1445555).sum := by decide
  have hdescent : baseEnd_1445555 < baseStart_1445555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445568 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 1, 6]
def baseStart_1445568 : Nat := 118140960795 + 1445568 * 2 ^ 59
def prefixEnd_1445568 : Nat := 4983230072969 + 3 ^ 40 * 1445568 * 2
def baseEnd_1445568 : Nat := 494847468505803628167973

theorem tailTrace_1445568 : CollatzResearch.WordTrace tailWord_1445568 prefixEnd_1445568 494847468505803628167973 := by
  unfold tailWord_1445568
  simp only [CollatzResearch.WordTrace]
  refine ⟨26362098213480747102060679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35149464284640996136080905 26362098213480747102060679)
  ·
    refine ⟨39543147320221120653091019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26362098213480747102060679 39543147320221120653091019)
    ·
      refine ⟨59314720980331680979636529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39543147320221120653091019 59314720980331680979636529)
      ·
        refine ⟨44486040735248760734727397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59314720980331680979636529 44486040735248760734727397)
        ·
          refine ⟨8341132637859142637761387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44486040735248760734727397 8341132637859142637761387)
          ·
            refine ⟨12511698956788713956642081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8341132637859142637761387 12511698956788713956642081)
            ·
              refine ⟨9383774217591535467481561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12511698956788713956642081 9383774217591535467481561)
              ·
                refine ⟨7037830663193651600611171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9383774217591535467481561 7037830663193651600611171)
                ·
                  refine ⟨10556745994790477400916757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7037830663193651600611171 10556745994790477400916757)
                  ·
                    refine ⟨494847468505803628167973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10556745994790477400916757 494847468505803628167973)
                    ·
                      rfl

theorem cell22_1445568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_1445568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445568 prefixEnd_1445568 := by exact prefixLift 1445568
  have htrace : WordTrace (prefixWord ++ tailWord_1445568) baseStart_1445568 baseEnd_1445568 := by
    simpa [prefixWord, tailWord_1445568, baseEnd_1445568] using wordTrace_append hprefix tailTrace_1445568
  have hstable : (prefixWord ++ tailWord_1445568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445568).length < 2 ^ (prefixWord ++ tailWord_1445568).sum := by decide
  have hdescent : baseEnd_1445568 < baseStart_1445568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445574 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1445574 : Nat := 118140960795 + 1445574 * 2 ^ 59
def prefixEnd_1445574 : Nat := 4983230072969 + 3 ^ 40 * 1445574 * 2
def baseEnd_1445574 : Nat := 494849522428421612517955

theorem tailTrace_1445574 : CollatzResearch.WordTrace tailWord_1445574 prefixEnd_1445574 494849522428421612517955 := by
  unfold tailWord_1445574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1647637977029367413401243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35149610176626504819226517 1647637977029367413401243)
  ·
    refine ⟨2471456965544051120101865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1647637977029367413401243 2471456965544051120101865)
    ·
      refine ⟨1853592724158038340076399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2471456965544051120101865 1853592724158038340076399)
      ·
        refine ⟨2780389086237057510114599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1853592724158038340076399 2780389086237057510114599)
        ·
          refine ⟨4170583629355586265171899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2780389086237057510114599 4170583629355586265171899)
          ·
            refine ⟨6255875444033379397757849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4170583629355586265171899 6255875444033379397757849)
            ·
              refine ⟨4691906583025034548318387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6255875444033379397757849 4691906583025034548318387)
              ·
                refine ⟨7037859874537551822477581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4691906583025034548318387 7037859874537551822477581)
                ·
                  refine ⟨2639197452951581933429093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7037859874537551822477581 2639197452951581933429093)
                  ·
                    refine ⟨494849522428421612517955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2639197452951581933429093 494849522428421612517955)
                    ·
                      rfl

theorem cell22_1445574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1445574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445574 prefixEnd_1445574 := by exact prefixLift 1445574
  have htrace : WordTrace (prefixWord ++ tailWord_1445574) baseStart_1445574 baseEnd_1445574 := by
    simpa [prefixWord, tailWord_1445574, baseEnd_1445574] using wordTrace_append hprefix tailTrace_1445574
  have hstable : (prefixWord ++ tailWord_1445574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445574).length < 2 ^ (prefixWord ++ tailWord_1445574).sum := by decide
  have hdescent : baseEnd_1445574 < baseStart_1445574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445585 : List Nat := [1, 2, 2, 1, 2, 4, 3, 1, 2, 4]
def baseStart_1445585 : Nat := 118140960795 + 1445585 * 2 ^ 59
def prefixEnd_1445585 : Nat := 4983230072969 + 3 ^ 40 * 1445585 * 2
def baseEnd_1445585 : Nat := 494853287953221250492921

theorem tailTrace_1445585 : CollatzResearch.WordTrace tailWord_1445585 prefixEnd_1445585 494853287953221250492921 := by
  unfold tailWord_1445585
  simp only [CollatzResearch.WordTrace]
  refine ⟨52724816467899906107490209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35149877645266604071660139 52724816467899906107490209)
  ·
    refine ⟨39543612350924929580617657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52724816467899906107490209 39543612350924929580617657)
    ·
      refine ⟨29657709263193697185463243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39543612350924929580617657 29657709263193697185463243)
      ·
        refine ⟨44486563894790545778194865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29657709263193697185463243 44486563894790545778194865)
        ·
          refine ⟨33364922921092909333646149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44486563894790545778194865 33364922921092909333646149)
          ·
            refine ⟨6255923047704920500058653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33364922921092909333646149 6255923047704920500058653)
            ·
              refine ⟨2345971142889345187521995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6255923047704920500058653 2345971142889345187521995)
              ·
                refine ⟨3518956714334017781282993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2345971142889345187521995 3518956714334017781282993)
                ·
                  refine ⟨2639217535750513335962245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3518956714334017781282993 2639217535750513335962245)
                  ·
                    refine ⟨494853287953221250492921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2639217535750513335962245 494853287953221250492921)
                    ·
                      rfl

theorem cell22_1445585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_1445585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445585 prefixEnd_1445585 := by exact prefixLift 1445585
  have htrace : WordTrace (prefixWord ++ tailWord_1445585) baseStart_1445585 baseEnd_1445585 := by
    simpa [prefixWord, tailWord_1445585, baseEnd_1445585] using wordTrace_append hprefix tailTrace_1445585
  have hstable : (prefixWord ++ tailWord_1445585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445585).length < 2 ^ (prefixWord ++ tailWord_1445585).sum := by decide
  have hdescent : baseEnd_1445585 < baseStart_1445585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445643 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 1, 7]
def baseStart_1445643 : Nat := 118140960795 + 1445643 * 2 ^ 59
def prefixEnd_1445643 : Nat := 4983230072969 + 3 ^ 40 * 1445643 * 2
def baseEnd_1445643 : Nat := 494873142538528432542743

theorem tailTrace_1445643 : CollatzResearch.WordTrace tailWord_1445643 prefixEnd_1445643 494873142538528432542743 := by
  unfold tailWord_1445643
  simp only [CollatzResearch.WordTrace]
  refine ⟨52726931901689782013101583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35151287934459854675401055 52726931901689782013101583)
  ·
    refine ⟨79090397852534673019652375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52726931901689782013101583 79090397852534673019652375)
    ·
      refine ⟨118635596778802009529478563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79090397852534673019652375 118635596778802009529478563)
      ·
        refine ⟨177953395168203014294217845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118635596778802009529478563 177953395168203014294217845)
        ·
          refine ⟨16683130797019032590082923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 177953395168203014294217845 16683130797019032590082923)
          ·
            refine ⟨25024696195528548885124385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16683130797019032590082923 25024696195528548885124385)
            ·
              refine ⟨18768522146646411663843289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25024696195528548885124385 18768522146646411663843289)
              ·
                refine ⟨14076391609984808747882467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18768522146646411663843289 14076391609984808747882467)
                ·
                  refine ⟨21114587414977213121823701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14076391609984808747882467 21114587414977213121823701)
                  ·
                    refine ⟨494873142538528432542743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21114587414977213121823701 494873142538528432542743)
                    ·
                      rfl

theorem cell22_1445643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 7].length) (baseStart_1445643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445643 prefixEnd_1445643 := by exact prefixLift 1445643
  have htrace : WordTrace (prefixWord ++ tailWord_1445643) baseStart_1445643 baseEnd_1445643 := by
    simpa [prefixWord, tailWord_1445643, baseEnd_1445643] using wordTrace_append hprefix tailTrace_1445643
  have hstable : (prefixWord ++ tailWord_1445643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445643).length < 2 ^ (prefixWord ++ tailWord_1445643).sum := by decide
  have hdescent : baseEnd_1445643 < baseStart_1445643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445666 : List Nat := [3, 3, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_1445666 : Nat := 118140960795 + 1445666 * 2 ^ 59
def prefixEnd_1445666 : Nat := 4983230072969 + 3 ^ 40 * 1445666 * 2
def baseEnd_1445666 : Nat := 494881015908564039217673

theorem tailTrace_1445666 : CollatzResearch.WordTrace tailWord_1445666 prefixEnd_1445666 494881015908564039217673 := by
  unfold tailWord_1445666
  simp only [CollatzResearch.WordTrace]
  refine ⟨13181942695151614235297213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35151847187070971294125901 13181942695151614235297213)
  ·
    refine ⟨4943228510681855338236455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13181942695151614235297213 4943228510681855338236455)
    ·
      refine ⟨7414842766022783007354683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4943228510681855338236455 7414842766022783007354683)
      ·
        refine ⟨11122264149034174511032025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7414842766022783007354683 11122264149034174511032025)
        ·
          refine ⟨8341698111775630883274019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11122264149034174511032025 8341698111775630883274019)
          ·
            refine ⟨12512547167663446324911029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8341698111775630883274019 12512547167663446324911029)
            ·
              refine ⟨1173051296968448092960409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12512547167663446324911029 1173051296968448092960409)
              ·
                refine ⟨879788472726336069720307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1173051296968448092960409 879788472726336069720307)
                ·
                  refine ⟨1319682709089504104580461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 879788472726336069720307 1319682709089504104580461)
                  ·
                    refine ⟨494881015908564039217673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1319682709089504104580461 494881015908564039217673)
                    ·
                      rfl

theorem cell22_1445666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_1445666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445666 prefixEnd_1445666 := by exact prefixLift 1445666
  have htrace : WordTrace (prefixWord ++ tailWord_1445666) baseStart_1445666 baseEnd_1445666 := by
    simpa [prefixWord, tailWord_1445666, baseEnd_1445666] using wordTrace_append hprefix tailTrace_1445666
  have hstable : (prefixWord ++ tailWord_1445666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445666).length < 2 ^ (prefixWord ++ tailWord_1445666).sum := by decide
  have hdescent : baseEnd_1445666 < baseStart_1445666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445692 : List Nat := [2, 2, 2, 2, 1, 1, 5, 2, 1, 4]
def baseStart_1445692 : Nat := 118140960795 + 1445692 * 2 ^ 59
def prefixEnd_1445692 : Nat := 4983230072969 + 3 ^ 40 * 1445692 * 2
def baseEnd_1445692 : Nat := 494889916239908638067593

theorem tailTrace_1445692 : CollatzResearch.WordTrace tailWord_1445692 prefixEnd_1445692 494889916239908638067593 := by
  unfold tailWord_1445692
  simp only [CollatzResearch.WordTrace]
  refine ⟨26364359539256131690817665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35152479385674842254423553 26364359539256131690817665)
  ·
    refine ⟨19773269654442098768113249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26364359539256131690817665 19773269654442098768113249)
    ·
      refine ⟨14829952240831574076084937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19773269654442098768113249 14829952240831574076084937)
      ·
        refine ⟨11122464180623680557063703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14829952240831574076084937 11122464180623680557063703)
        ·
          refine ⟨16683696270935520835595555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11122464180623680557063703 16683696270935520835595555)
          ·
            refine ⟨25025544406403281253393333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16683696270935520835595555 25025544406403281253393333)
            ·
              refine ⟨2346144788100307617505625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25025544406403281253393333 2346144788100307617505625)
              ·
                refine ⟨1759608591075230713129219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2346144788100307617505625 1759608591075230713129219)
                ·
                  refine ⟨2639412886612846069693829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1759608591075230713129219 2639412886612846069693829)
                  ·
                    refine ⟨494889916239908638067593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2639412886612846069693829 494889916239908638067593)
                    ·
                      rfl

theorem cell22_1445692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_1445692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445692 prefixEnd_1445692 := by exact prefixLift 1445692
  have htrace : WordTrace (prefixWord ++ tailWord_1445692) baseStart_1445692 baseEnd_1445692 := by
    simpa [prefixWord, tailWord_1445692, baseEnd_1445692] using wordTrace_append hprefix tailTrace_1445692
  have hstable : (prefixWord ++ tailWord_1445692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445692).length < 2 ^ (prefixWord ++ tailWord_1445692).sum := by decide
  have hdescent : baseEnd_1445692 < baseStart_1445692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445705 : List Nat := [1, 2, 1, 1, 2, 4, 3, 2, 1, 5]
def baseStart_1445705 : Nat := 118140960795 + 1445705 * 2 ^ 59
def prefixEnd_1445705 : Nat := 4983230072969 + 3 ^ 40 * 1445705 * 2
def baseEnd_1445705 : Nat := 494894366405580937492553

theorem tailTrace_1445705 : CollatzResearch.WordTrace tailWord_1445705 prefixEnd_1445705 494894366405580937492553 := by
  unfold tailWord_1445705
  simp only [CollatzResearch.WordTrace]
  refine ⟨52729193227465166601858569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35152795484976777734572379 52729193227465166601858569)
  ·
    refine ⟨39546894920598874951393927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52729193227465166601858569 39546894920598874951393927)
    ·
      refine ⟨59320342380898312427090891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39546894920598874951393927 59320342380898312427090891)
      ·
        refine ⟨88980513571347468640636337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59320342380898312427090891 88980513571347468640636337)
        ·
          refine ⟨66735385178510601480477253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88980513571347468640636337 66735385178510601480477253)
          ·
            refine ⟨12512884720970737777589485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66735385178510601480477253 12512884720970737777589485)
            ·
              refine ⟨4692331770364026666596057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12512884720970737777589485 4692331770364026666596057)
              ·
                refine ⟨3519248827773019999947043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4692331770364026666596057 3519248827773019999947043)
                ·
                  refine ⟨5278873241659529999920565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3519248827773019999947043 5278873241659529999920565)
                  ·
                    refine ⟨494894366405580937492553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5278873241659529999920565 494894366405580937492553)
                    ·
                      rfl

theorem cell22_1445705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_1445705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445705 prefixEnd_1445705 := by exact prefixLift 1445705
  have htrace : WordTrace (prefixWord ++ tailWord_1445705) baseStart_1445705 baseEnd_1445705 := by
    simpa [prefixWord, tailWord_1445705, baseEnd_1445705] using wordTrace_append hprefix tailTrace_1445705
  have hstable : (prefixWord ++ tailWord_1445705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445705).length < 2 ^ (prefixWord ++ tailWord_1445705).sum := by decide
  have hdescent : baseEnd_1445705 < baseStart_1445705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445790 : List Nat := [4, 3, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_1445790 : Nat := 118140960795 + 1445790 * 2 ^ 59
def prefixEnd_1445790 : Nat := 4983230072969 + 3 ^ 40 * 1445790 * 2
def baseEnd_1445790 : Nat := 494923463642669049117293

theorem tailTrace_1445790 : CollatzResearch.WordTrace tailWord_1445790 prefixEnd_1445790 494923463642669049117293 := by
  unfold tailWord_1445790
  simp only [CollatzResearch.WordTrace]
  refine ⟨6591536679019653264837853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35154862288104817412468549 6591536679019653264837853)
  ·
    refine ⟨2471826254632369974314195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6591536679019653264837853 2471826254632369974314195)
    ·
      refine ⟨3707739381948554961471293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2471826254632369974314195 3707739381948554961471293)
      ·
        refine ⟨1390402268230708110551735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3707739381948554961471293 1390402268230708110551735)
        ·
          refine ⟨2085603402346062165827603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1390402268230708110551735 2085603402346062165827603)
          ·
            refine ⟨3128405103519093248741405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2085603402346062165827603 3128405103519093248741405)
            ·
              refine ⟨1173151913819659968278027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3128405103519093248741405 1173151913819659968278027)
              ·
                refine ⟨1759727870729489952417041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173151913819659968278027 1759727870729489952417041)
                ·
                  refine ⟨1319795903047117464312781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1759727870729489952417041 1319795903047117464312781)
                  ·
                    refine ⟨494923463642669049117293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1319795903047117464312781 494923463642669049117293)
                    ·
                      rfl

theorem cell22_1445790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_1445790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445790 prefixEnd_1445790 := by exact prefixLift 1445790
  have htrace : WordTrace (prefixWord ++ tailWord_1445790) baseStart_1445790 baseEnd_1445790 := by
    simpa [prefixWord, tailWord_1445790, baseEnd_1445790] using wordTrace_append hprefix tailTrace_1445790
  have hstable : (prefixWord ++ tailWord_1445790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445790).length < 2 ^ (prefixWord ++ tailWord_1445790).sum := by decide
  have hdescent : baseEnd_1445790 < baseStart_1445790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445810 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_1445810 : Nat := 118140960795 + 1445810 * 2 ^ 59
def prefixEnd_1445810 : Nat := 4983230072969 + 3 ^ 40 * 1445810 * 2
def baseEnd_1445810 : Nat := 494930310051395663617231

theorem tailTrace_1445810 : CollatzResearch.WordTrace tailWord_1445810 prefixEnd_1445810 494930310051395663617231 := by
  unfold tailWord_1445810
  simp only [CollatzResearch.WordTrace]
  refine ⟨13183255723021192383607721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35155348594723179689620589 13183255723021192383607721)
  ·
    refine ⟨9887441792265894287705791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13183255723021192383607721 9887441792265894287705791)
    ·
      refine ⟨14831162688398841431558687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9887441792265894287705791 14831162688398841431558687)
      ·
        refine ⟨22246744032598262147338031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14831162688398841431558687 22246744032598262147338031)
        ·
          refine ⟨33370116048897393221007047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22246744032598262147338031 33370116048897393221007047)
          ·
            refine ⟨50055174073346089831510571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33370116048897393221007047 50055174073346089831510571)
            ·
              refine ⟨75082761110019134747265857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50055174073346089831510571 75082761110019134747265857)
              ·
                refine ⟨56312070832514351060449393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75082761110019134747265857 56312070832514351060449393)
                ·
                  refine ⟨42234053124385763295337045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56312070832514351060449393 42234053124385763295337045)
                  ·
                    refine ⟨494930310051395663617231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42234053124385763295337045 494930310051395663617231)
                    ·
                      rfl

theorem cell22_1445810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_1445810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445810 prefixEnd_1445810 := by exact prefixLift 1445810
  have htrace : WordTrace (prefixWord ++ tailWord_1445810) baseStart_1445810 baseEnd_1445810 := by
    simpa [prefixWord, tailWord_1445810, baseEnd_1445810] using wordTrace_append hprefix tailTrace_1445810
  have hstable : (prefixWord ++ tailWord_1445810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445810).length < 2 ^ (prefixWord ++ tailWord_1445810).sum := by decide
  have hdescent : baseEnd_1445810 < baseStart_1445810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445872 : List Nat := [2, 1, 1, 1, 3, 2, 3, 3, 2, 4]
def baseStart_1445872 : Nat := 118140960795 + 1445872 * 2 ^ 59
def prefixEnd_1445872 : Nat := 4983230072969 + 3 ^ 40 * 1445872 * 2
def baseEnd_1445872 : Nat := 494951533918448168567041

theorem tailTrace_1445872 : CollatzResearch.WordTrace tailWord_1445872 prefixEnd_1445872 494951533918448168567041 := by
  unfold tailWord_1445872
  simp only [CollatzResearch.WordTrace]
  refine ⟨26367642108930077061593935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35156856145240102748791913 26367642108930077061593935)
  ·
    refine ⟨39551463163395115592390903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26367642108930077061593935 39551463163395115592390903)
    ·
      refine ⟨59327194745092673388586355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39551463163395115592390903 59327194745092673388586355)
      ·
        refine ⟨88990792117639010082879533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59327194745092673388586355 88990792117639010082879533)
        ·
          refine ⟨33371547044114628781079825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88990792117639010082879533 33371547044114628781079825)
          ·
            refine ⟨25028660283085971585809869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33371547044114628781079825 25028660283085971585809869)
            ·
              refine ⟨9385747606157239344678701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25028660283085971585809869 9385747606157239344678701)
              ·
                refine ⟨3519655352308964754254513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9385747606157239344678701 3519655352308964754254513)
                ·
                  refine ⟨2639741514231723565690885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3519655352308964754254513 2639741514231723565690885)
                  ·
                    refine ⟨494951533918448168567041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2639741514231723565690885 494951533918448168567041)
                    ·
                      rfl

theorem cell22_1445872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_1445872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445872 prefixEnd_1445872 := by exact prefixLift 1445872
  have htrace : WordTrace (prefixWord ++ tailWord_1445872) baseStart_1445872 baseEnd_1445872 := by
    simpa [prefixWord, tailWord_1445872, baseEnd_1445872] using wordTrace_append hprefix tailTrace_1445872
  have hstable : (prefixWord ++ tailWord_1445872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445872).length < 2 ^ (prefixWord ++ tailWord_1445872).sum := by decide
  have hdescent : baseEnd_1445872 < baseStart_1445872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445878 : List Nat := [5, 1, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_1445878 : Nat := 118140960795 + 1445878 * 2 ^ 59
def prefixEnd_1445878 : Nat := 4983230072969 + 3 ^ 40 * 1445878 * 2
def baseEnd_1445878 : Nat := 494953587841066152917023

theorem tailTrace_1445878 : CollatzResearch.WordTrace tailWord_1445878 prefixEnd_1445878 494953587841066152917023 := by
  unfold tailWord_1445878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3295968940989901071744143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35157002037225611431937525 3295968940989901071744143)
  ·
    refine ⟨4943953411484851607616215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3295968940989901071744143 4943953411484851607616215)
    ·
      refine ⟨7415930117227277411424323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4943953411484851607616215 7415930117227277411424323)
      ·
        refine ⟨11123895175840916117136485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7415930117227277411424323 11123895175840916117136485)
        ·
          refine ⟨2085730345470171771963091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11123895175840916117136485 2085730345470171771963091)
          ·
            refine ⟨3128595518205257657944637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2085730345470171771963091 3128595518205257657944637)
            ·
              refine ⟨1173223319326971621729239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3128595518205257657944637 1173223319326971621729239)
              ·
                refine ⟨1759834978990457432593859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173223319326971621729239 1759834978990457432593859)
                ·
                  refine ⟨2639752468485686148890789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1759834978990457432593859 2639752468485686148890789)
                  ·
                    refine ⟨494953587841066152917023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2639752468485686148890789 494953587841066152917023)
                    ·
                      rfl

theorem cell22_1445878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_1445878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445878 prefixEnd_1445878 := by exact prefixLift 1445878
  have htrace : WordTrace (prefixWord ++ tailWord_1445878) baseStart_1445878 baseEnd_1445878 := by
    simpa [prefixWord, tailWord_1445878, baseEnd_1445878] using wordTrace_append hprefix tailTrace_1445878
  have hstable : (prefixWord ++ tailWord_1445878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445878).length < 2 ^ (prefixWord ++ tailWord_1445878).sum := by decide
  have hdescent : baseEnd_1445878 < baseStart_1445878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445908 : List Nat := [2, 4, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_1445908 : Nat := 118140960795 + 1445908 * 2 ^ 59
def prefixEnd_1445908 : Nat := 4983230072969 + 3 ^ 40 * 1445908 * 2
def baseEnd_1445908 : Nat := 494963857454156074666931

theorem tailTrace_1445908 : CollatzResearch.WordTrace tailWord_1445908 prefixEnd_1445908 494963857454156074666931 := by
  unfold tailWord_1445908
  simp only [CollatzResearch.WordTrace]
  refine ⟨26368298622864866135749189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35157731497153154847665585 26368298622864866135749189)
  ·
    refine ⟨4944055991787162400452973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26368298622864866135749189 4944055991787162400452973)
    ·
      refine ⟨1854020996920185900169865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4944055991787162400452973 1854020996920185900169865)
      ·
        refine ⟨1390515747690139425127399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1854020996920185900169865 1390515747690139425127399)
        ·
          refine ⟨2085773621535209137691099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1390515747690139425127399 2085773621535209137691099)
          ·
            refine ⟨3128660432302813706536649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2085773621535209137691099 3128660432302813706536649)
            ·
              refine ⟨2346495324227110279902487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3128660432302813706536649 2346495324227110279902487)
              ·
                refine ⟨3519742986340665419853731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2346495324227110279902487 3519742986340665419853731)
                ·
                  refine ⟨5279614479510998129780597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3519742986340665419853731 5279614479510998129780597)
                  ·
                    refine ⟨494963857454156074666931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5279614479510998129780597 494963857454156074666931)
                    ·
                      rfl

theorem cell22_1445908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_1445908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445908 prefixEnd_1445908 := by exact prefixLift 1445908
  have htrace : WordTrace (prefixWord ++ tailWord_1445908) baseStart_1445908 baseEnd_1445908 := by
    simpa [prefixWord, tailWord_1445908, baseEnd_1445908] using wordTrace_append hprefix tailTrace_1445908
  have hstable : (prefixWord ++ tailWord_1445908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445908).length < 2 ^ (prefixWord ++ tailWord_1445908).sum := by decide
  have hdescent : baseEnd_1445908 < baseStart_1445908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445919 : List Nat := [1, 1, 2, 4, 1, 2, 3, 2, 3, 3]
def baseStart_1445919 : Nat := 118140960795 + 1445919 * 2 ^ 59
def prefixEnd_1445919 : Nat := 4983230072969 + 3 ^ 40 * 1445919 * 2
def baseEnd_1445919 : Nat := 494967622978955712641897

theorem tailTrace_1445919 : CollatzResearch.WordTrace tailWord_1445919 prefixEnd_1445919 494967622978955712641897 := by
  unfold tailWord_1445919
  simp only [CollatzResearch.WordTrace]
  refine ⟨52736998448689881150148811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35157998965793254100099207 52736998448689881150148811)
  ·
    refine ⟨79105497673034821725223217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52736998448689881150148811 79105497673034821725223217)
    ·
      refine ⟨59329123254776116293917413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79105497673034821725223217 59329123254776116293917413)
      ·
        refine ⟨11124210610270521805109515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59329123254776116293917413 11124210610270521805109515)
        ·
          refine ⟨16686315915405782707664273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11124210610270521805109515 16686315915405782707664273)
          ·
            refine ⟨12514736936554337030748205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16686315915405782707664273 12514736936554337030748205)
            ·
              refine ⟨4693026351207876386530577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12514736936554337030748205 4693026351207876386530577)
              ·
                refine ⟨3519769763405907289897933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4693026351207876386530577 3519769763405907289897933)
                ·
                  refine ⟨1319913661277215233711725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3519769763405907289897933 1319913661277215233711725)
                  ·
                    refine ⟨494967622978955712641897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1319913661277215233711725 494967622978955712641897)
                    ·
                      rfl

theorem cell22_1445919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 3].length) (baseStart_1445919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445919 prefixEnd_1445919 := by exact prefixLift 1445919
  have htrace : WordTrace (prefixWord ++ tailWord_1445919) baseStart_1445919 baseEnd_1445919 := by
    simpa [prefixWord, tailWord_1445919, baseEnd_1445919] using wordTrace_append hprefix tailTrace_1445919
  have hstable : (prefixWord ++ tailWord_1445919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445919).length < 2 ^ (prefixWord ++ tailWord_1445919).sum := by decide
  have hdescent : baseEnd_1445919 < baseStart_1445919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445936 : List Nat := [2, 1, 1, 1, 2, 5, 1, 5, 1, 3]
def baseStart_1445936 : Nat := 118140960795 + 1445936 * 2 ^ 59
def prefixEnd_1445936 : Nat := 4983230072969 + 3 ^ 40 * 1445936 * 2
def baseEnd_1445936 : Nat := 494973442426373334966845

theorem tailTrace_1445936 : CollatzResearch.WordTrace tailWord_1445936 prefixEnd_1445936 494973442426373334966845 := by
  unfold tailWord_1445936
  simp only [CollatzResearch.WordTrace]
  refine ⟨26368809244814146526758831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35158412326418862035678441 26368809244814146526758831)
  ·
    refine ⟨39553213867221219790138247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26368809244814146526758831 39553213867221219790138247)
    ·
      refine ⟨59329820800831829685207371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39553213867221219790138247 59329820800831829685207371)
      ·
        refine ⟨88994731201247744527811057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59329820800831829685207371 88994731201247744527811057)
        ·
          refine ⟨66746048400935808395858293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88994731201247744527811057 66746048400935808395858293)
          ·
            refine ⟨6257442037587732037111715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66746048400935808395858293 6257442037587732037111715)
            ·
              refine ⟨9386163056381598055667573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6257442037587732037111715 9386163056381598055667573)
              ·
                refine ⟨879952786535774817718835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9386163056381598055667573 879952786535774817718835)
                ·
                  refine ⟨1319929179803662226578253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 879952786535774817718835 1319929179803662226578253)
                  ·
                    refine ⟨494973442426373334966845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1319929179803662226578253 494973442426373334966845)
                    ·
                      rfl

theorem cell22_1445936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 1, 3].length) (baseStart_1445936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445936 prefixEnd_1445936 := by exact prefixLift 1445936
  have htrace : WordTrace (prefixWord ++ tailWord_1445936) baseStart_1445936 baseEnd_1445936 := by
    simpa [prefixWord, tailWord_1445936, baseEnd_1445936] using wordTrace_append hprefix tailTrace_1445936
  have hstable : (prefixWord ++ tailWord_1445936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445936).length < 2 ^ (prefixWord ++ tailWord_1445936).sum := by decide
  have hdescent : baseEnd_1445936 < baseStart_1445936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445953 : List Nat := [1, 2, 5, 1, 2, 1, 2, 4, 1, 3]
def baseStart_1445953 : Nat := 118140960795 + 1445953 * 2 ^ 59
def prefixEnd_1445953 : Nat := 4983230072969 + 3 ^ 40 * 1445953 * 2
def baseEnd_1445953 : Nat := 494979261873790957291793

theorem tailTrace_1445953 : CollatzResearch.WordTrace tailWord_1445953 prefixEnd_1445953 494979261873790957291793 := by
  unfold tailWord_1445953
  simp only [CollatzResearch.WordTrace]
  refine ⟨52738238530566704956886513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35158825687044469971257675 52738238530566704956886513)
  ·
    refine ⟨39553678897925028717664885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52738238530566704956886513 39553678897925028717664885)
    ·
      refine ⟨3708157396680471442281083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39553678897925028717664885 3708157396680471442281083)
      ·
        refine ⟨5562236095020707163421625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3708157396680471442281083 5562236095020707163421625)
        ·
          refine ⟨4171677071265530372566219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5562236095020707163421625 4171677071265530372566219)
          ·
            refine ⟨6257515606898295558849329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4171677071265530372566219 6257515606898295558849329)
            ·
              refine ⟨4693136705173721669136997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6257515606898295558849329 4693136705173721669136997)
              ·
                refine ⟨879963132220072812963187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4693136705173721669136997 879963132220072812963187)
                ·
                  refine ⟨1319944698330109219444781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 879963132220072812963187 1319944698330109219444781)
                  ·
                    refine ⟨494979261873790957291793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1319944698330109219444781 494979261873790957291793)
                    ·
                      rfl

theorem cell22_1445953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_1445953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445953 prefixEnd_1445953 := by exact prefixLift 1445953
  have htrace : WordTrace (prefixWord ++ tailWord_1445953) baseStart_1445953 baseEnd_1445953 := by
    simpa [prefixWord, tailWord_1445953, baseEnd_1445953] using wordTrace_append hprefix tailTrace_1445953
  have hstable : (prefixWord ++ tailWord_1445953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445953).length < 2 ^ (prefixWord ++ tailWord_1445953).sum := by decide
  have hdescent : baseEnd_1445953 < baseStart_1445953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445966 : List Nat := [4, 1, 1, 1, 1, 5, 3, 1, 5]
def baseStart_1445966 : Nat := 118140960795 + 1445966 * 2 ^ 59
def prefixEnd_1445966 : Nat := 4983230072969 + 3 ^ 40 * 1445966 * 2
def baseEnd_1445966 : Nat := 164994570679821085572251

theorem tailTrace_1445966 : CollatzResearch.WordTrace tailWord_1445966 prefixEnd_1445966 164994570679821085572251 := by
  unfold tailWord_1445966
  simp only [CollatzResearch.WordTrace]
  refine ⟨6592339084939951022138719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35159141786346405451406501 6592339084939951022138719)
  ·
    refine ⟨9888508627409926533208079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6592339084939951022138719 9888508627409926533208079)
    ·
      refine ⟨14832762941114889799812119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9888508627409926533208079 14832762941114889799812119)
      ·
        refine ⟨22249144411672334699718179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14832762941114889799812119 22249144411672334699718179)
        ·
          refine ⟨33373716617508502049577269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22249144411672334699718179 33373716617508502049577269)
          ·
            refine ⟨3128785932891422067147869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33373716617508502049577269 3128785932891422067147869)
            ·
              refine ⟨1173294724834283275180451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3128785932891422067147869 1173294724834283275180451)
              ·
                refine ⟨1759942087251424912770677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173294724834283275180451 1759942087251424912770677)
                ·
                  refine ⟨164994570679821085572251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1759942087251424912770677 164994570679821085572251)
                  ·
                    rfl

theorem cell22_1445966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_1445966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445966 prefixEnd_1445966 := by exact prefixLift 1445966
  have htrace : WordTrace (prefixWord ++ tailWord_1445966) baseStart_1445966 baseEnd_1445966 := by
    simpa [prefixWord, tailWord_1445966, baseEnd_1445966] using wordTrace_append hprefix tailTrace_1445966
  have hstable : (prefixWord ++ tailWord_1445966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445966).length < 2 ^ (prefixWord ++ tailWord_1445966).sum := by decide
  have hdescent : baseEnd_1445966 < baseStart_1445966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445977 : List Nat := [1, 2, 1, 2, 2, 1, 3, 4, 6]
def baseStart_1445977 : Nat := 118140960795 + 1445977 * 2 ^ 59
def prefixEnd_1445977 : Nat := 4983230072969 + 3 ^ 40 * 1445977 * 2
def baseEnd_1445977 : Nat := 164995825854754298230573

theorem tailTrace_1445977 : CollatzResearch.WordTrace tailWord_1445977 prefixEnd_1445977 164995825854754298230573 := by
  unfold tailWord_1445977
  simp only [CollatzResearch.WordTrace]
  refine ⟨52739113882479757055760185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35159409254986504703840123 52739113882479757055760185)
  ·
    refine ⟨39554335411859817791820139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52739113882479757055760185 39554335411859817791820139)
    ·
      refine ⟨59331503117789726687730209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39554335411859817791820139 59331503117789726687730209)
      ·
        refine ⟨44498627338342295015797657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59331503117789726687730209 44498627338342295015797657)
        ·
          refine ⟨33373970503756721261848243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44498627338342295015797657 33373970503756721261848243)
          ·
            refine ⟨50060955755635081892772365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33373970503756721261848243 50060955755635081892772365)
            ·
              refine ⟨18772858408363155709789637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50060955755635081892772365 18772858408363155709789637)
              ·
                refine ⟨3519910951568091695585557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18772858408363155709789637 3519910951568091695585557)
                ·
                  refine ⟨164995825854754298230573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3519910951568091695585557 164995825854754298230573)
                  ·
                    rfl

theorem cell22_1445977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 6].length) (baseStart_1445977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1445977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1445977 prefixEnd_1445977 := by exact prefixLift 1445977
  have htrace : WordTrace (prefixWord ++ tailWord_1445977) baseStart_1445977 baseEnd_1445977 := by
    simpa [prefixWord, tailWord_1445977, baseEnd_1445977] using wordTrace_append hprefix tailTrace_1445977
  have hstable : (prefixWord ++ tailWord_1445977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445977).length < 2 ^ (prefixWord ++ tailWord_1445977).sum := by decide
  have hdescent : baseEnd_1445977 < baseStart_1445977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446030 : List Nat := [4, 1, 1, 3, 4, 1, 1, 2, 1, 4]
def baseStart_1446030 : Nat := 118140960795 + 1446030 * 2 ^ 59
def prefixEnd_1446030 : Nat := 4983230072969 + 3 ^ 40 * 1446030 * 2
def baseEnd_1446030 : Nat := 495005620547388423116557

theorem tailTrace_1446030 : CollatzResearch.WordTrace tailWord_1446030 prefixEnd_1446030 495005620547388423116557 := by
  unfold tailWord_1446030
  simp only [CollatzResearch.WordTrace]
  refine ⟨6592630868910968388429943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35160697967525164738293029 6592630868910968388429943)
  ·
    refine ⟨9888946303366452582644915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6592630868910968388429943 9888946303366452582644915)
    ·
      refine ⟨14833419455049678873967373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9888946303366452582644915 14833419455049678873967373)
      ·
        refine ⟨5562532295643629577737765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14833419455049678873967373 5562532295643629577737765)
        ·
          refine ⟨1042974805433180545825831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5562532295643629577737765 1042974805433180545825831)
          ·
            refine ⟨1564462208149770818738747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042974805433180545825831 1564462208149770818738747)
            ·
              refine ⟨2346693312224656228108121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1564462208149770818738747 2346693312224656228108121)
              ·
                refine ⟨1760019984168492171081091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2346693312224656228108121 1760019984168492171081091)
                ·
                  refine ⟨2640029976252738256621637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1760019984168492171081091 2640029976252738256621637)
                  ·
                    refine ⟨495005620547388423116557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2640029976252738256621637 495005620547388423116557)
                    ·
                      rfl

theorem cell22_1446030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_1446030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446030 prefixEnd_1446030 := by exact prefixLift 1446030
  have htrace : WordTrace (prefixWord ++ tailWord_1446030) baseStart_1446030 baseEnd_1446030 := by
    simpa [prefixWord, tailWord_1446030, baseEnd_1446030] using wordTrace_append hprefix tailTrace_1446030
  have hstable : (prefixWord ++ tailWord_1446030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446030).length < 2 ^ (prefixWord ++ tailWord_1446030).sum := by decide
  have hdescent : baseEnd_1446030 < baseStart_1446030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446129 : List Nat := [1, 2, 2, 2, 2, 1, 3, 3, 6]
def baseStart_1446129 : Nat := 118140960795 + 1446129 * 2 ^ 59
def prefixEnd_1446129 : Nat := 4983230072969 + 3 ^ 40 * 1446129 * 2
def baseEnd_1446129 : Nat := 165013170090195054963751

theorem tailTrace_1446129 : CollatzResearch.WordTrace tailWord_1446129 prefixEnd_1446129 165013170090195054963751 := by
  unfold tailWord_1446129
  simp only [CollatzResearch.WordTrace]
  refine ⟨52744657777929087015293441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35163105185286058010195627 52744657777929087015293441)
  ·
    refine ⟨39558493333446815261470081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52744657777929087015293441 39558493333446815261470081)
    ·
      refine ⟨29668870000085111446102561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39558493333446815261470081 29668870000085111446102561)
      ·
        refine ⟨22251652500063833584576921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29668870000085111446102561 22251652500063833584576921)
        ·
          refine ⟨16688739375047875188432691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22251652500063833584576921 16688739375047875188432691)
          ·
            refine ⟨25033109062571812782649037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16688739375047875188432691 25033109062571812782649037)
            ·
              refine ⟨9387415898464429793493389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25033109062571812782649037 9387415898464429793493389)
              ·
                refine ⟨3520280961924161172560021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9387415898464429793493389 3520280961924161172560021)
                ·
                  refine ⟨165013170090195054963751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3520280961924161172560021 165013170090195054963751)
                  ·
                    rfl

theorem cell22_1446129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 6].length) (baseStart_1446129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446129 prefixEnd_1446129 := by exact prefixLift 1446129
  have htrace : WordTrace (prefixWord ++ tailWord_1446129) baseStart_1446129 baseEnd_1446129 := by
    simpa [prefixWord, tailWord_1446129, baseEnd_1446129] using wordTrace_append hprefix tailTrace_1446129
  have hstable : (prefixWord ++ tailWord_1446129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446129).length < 2 ^ (prefixWord ++ tailWord_1446129).sum := by decide
  have hdescent : baseEnd_1446129 < baseStart_1446129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446159 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 6, 4]
def baseStart_1446159 : Nat := 118140960795 + 1446159 * 2 ^ 59
def prefixEnd_1446159 : Nat := 4983230072969 + 3 ^ 40 * 1446159 * 2
def baseEnd_1446159 : Nat := 495049779883675086641161

theorem tailTrace_1446159 : CollatzResearch.WordTrace tailWord_1446159 prefixEnd_1446159 495049779883675086641161 := by
  unfold tailWord_1446159
  simp only [CollatzResearch.WordTrace]
  refine ⟨52745751967820402138885531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35163834645213601425923687 52745751967820402138885531)
  ·
    refine ⟨79118627951730603208328297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52745751967820402138885531 79118627951730603208328297)
    ·
      refine ⟨59338970963797952406246223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79118627951730603208328297 59338970963797952406246223)
      ·
        refine ⟨89008456445696928609369335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59338970963797952406246223 89008456445696928609369335)
        ·
          refine ⟨133512684668545392914054003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89008456445696928609369335 133512684668545392914054003)
          ·
            refine ⟨200269027002818089371081005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133512684668545392914054003 200269027002818089371081005)
            ·
              refine ⟨75100885126056783514155377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200269027002818089371081005 75100885126056783514155377)
              ·
                refine ⟨56325663844542587635616533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75100885126056783514155377 56325663844542587635616533)
                ·
                  refine ⟨2640265492712933795419525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56325663844542587635616533 2640265492712933795419525)
                  ·
                    refine ⟨495049779883675086641161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2640265492712933795419525 495049779883675086641161)
                    ·
                      rfl

theorem cell22_1446159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_1446159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446159 prefixEnd_1446159 := by exact prefixLift 1446159
  have htrace : WordTrace (prefixWord ++ tailWord_1446159) baseStart_1446159 baseEnd_1446159 := by
    simpa [prefixWord, tailWord_1446159, baseEnd_1446159] using wordTrace_append hprefix tailTrace_1446159
  have hstable : (prefixWord ++ tailWord_1446159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446159).length < 2 ^ (prefixWord ++ tailWord_1446159).sum := by decide
  have hdescent : baseEnd_1446159 < baseStart_1446159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446161 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 4, 3]
def baseStart_1446161 : Nat := 118140960795 + 1446161 * 2 ^ 59
def prefixEnd_1446161 : Nat := 4983230072969 + 3 ^ 40 * 1446161 * 2
def baseEnd_1446161 : Nat := 495050464524547748091155

theorem tailTrace_1446161 : CollatzResearch.WordTrace tailWord_1446161 prefixEnd_1446161 495050464524547748091155 := by
  unfold tailWord_1446161
  simp only [CollatzResearch.WordTrace]
  refine ⟨52745824913813156480458337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35163883275875437653638891 52745824913813156480458337)
  ·
    refine ⟨39559368685359867360343753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52745824913813156480458337 39559368685359867360343753)
    ·
      refine ⟨29669526514019900520257815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39559368685359867360343753 29669526514019900520257815)
      ·
        refine ⟨44504289771029850780386723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29669526514019900520257815 44504289771029850780386723)
        ·
          refine ⟨66756434656544776170580085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44504289771029850780386723 66756434656544776170580085)
          ·
            refine ⟨6258415749051072765991883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66756434656544776170580085 6258415749051072765991883)
            ·
              refine ⟨9387623623576609148987825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6258415749051072765991883 9387623623576609148987825)
              ·
                refine ⟨7040717717682456861740869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9387623623576609148987825 7040717717682456861740869)
                ·
                  refine ⟨1320134572065460661576413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7040717717682456861740869 1320134572065460661576413)
                  ·
                    refine ⟨495050464524547748091155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1320134572065460661576413 495050464524547748091155)
                    ·
                      rfl

theorem cell22_1446161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_1446161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446161 prefixEnd_1446161 := by exact prefixLift 1446161
  have htrace : WordTrace (prefixWord ++ tailWord_1446161) baseStart_1446161 baseEnd_1446161 := by
    simpa [prefixWord, tailWord_1446161, baseEnd_1446161] using wordTrace_append hprefix tailTrace_1446161
  have hstable : (prefixWord ++ tailWord_1446161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446161).length < 2 ^ (prefixWord ++ tailWord_1446161).sum := by decide
  have hdescent : baseEnd_1446161 < baseStart_1446161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446176 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 4, 4]
def baseStart_1446176 : Nat := 118140960795 + 1446176 * 2 ^ 59
def prefixEnd_1446176 : Nat := 4983230072969 + 3 ^ 40 * 1446176 * 2
def baseEnd_1446176 : Nat := 495055599331092708966109

theorem tailTrace_1446176 : CollatzResearch.WordTrace tailWord_1446176 prefixEnd_1446176 495055599331092708966109 := by
  unfold tailWord_1446176
  simp only [CollatzResearch.WordTrace]
  refine ⟨26373186004379407021127191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35164248005839209361502921 26373186004379407021127191)
  ·
    refine ⟨39559779006569110531690787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26373186004379407021127191 39559779006569110531690787)
    ·
      refine ⟨59339668509853665797536181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39559779006569110531690787 59339668509853665797536181)
      ·
        refine ⟨5563093922798781168519017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59339668509853665797536181 5563093922798781168519017)
        ·
          refine ⟨4172320442099085876389263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5563093922798781168519017 4172320442099085876389263)
          ·
            refine ⟨6258480663148628814583895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4172320442099085876389263 6258480663148628814583895)
            ·
              refine ⟨9387720994722943221875843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6258480663148628814583895 9387720994722943221875843)
              ·
                refine ⟨14081581492084414832813765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9387720994722943221875843 14081581492084414832813765)
                ·
                  refine ⟨2640296529765827781152581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14081581492084414832813765 2640296529765827781152581)
                  ·
                    refine ⟨495055599331092708966109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2640296529765827781152581 495055599331092708966109)
                    ·
                      rfl

theorem cell22_1446176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_1446176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446176 prefixEnd_1446176 := by exact prefixLift 1446176
  have htrace : WordTrace (prefixWord ++ tailWord_1446176) baseStart_1446176 baseEnd_1446176 := by
    simpa [prefixWord, tailWord_1446176, baseEnd_1446176] using wordTrace_append hprefix tailTrace_1446176
  have hstable : (prefixWord ++ tailWord_1446176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446176).length < 2 ^ (prefixWord ++ tailWord_1446176).sum := by decide
  have hdescent : baseEnd_1446176 < baseStart_1446176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446178 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_1446178 : Nat := 118140960795 + 1446178 * 2 ^ 59
def prefixEnd_1446178 : Nat := 4983230072969 + 3 ^ 40 * 1446178 * 2
def baseEnd_1446178 : Nat := 495056283971965370416103

theorem tailTrace_1446178 : CollatzResearch.WordTrace tailWord_1446178 prefixEnd_1446178 495056283971965370416103 := by
  unfold tailWord_1446178
  simp only [CollatzResearch.WordTrace]
  refine ⟨13186611238687892095956797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35164296636501045589218125 13186611238687892095956797)
  ·
    refine ⟨4944979214507959535983799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13186611238687892095956797 4944979214507959535983799)
    ·
      refine ⟨7417468821761939303975699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4944979214507959535983799 7417468821761939303975699)
      ·
        refine ⟨11126203232642908955963549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7417468821761939303975699 11126203232642908955963549)
        ·
          refine ⟨4172326212241090858486331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11126203232642908955963549 4172326212241090858486331)
          ·
            refine ⟨6258489318361636287729497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4172326212241090858486331 6258489318361636287729497)
            ·
              refine ⟨4693866988771227215797123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6258489318361636287729497 4693866988771227215797123)
              ·
                refine ⟨7040800483156840823695685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4693866988771227215797123 7040800483156840823695685)
                ·
                  refine ⟨1320150090591907654442941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7040800483156840823695685 1320150090591907654442941)
                  ·
                    refine ⟨495056283971965370416103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1320150090591907654442941 495056283971965370416103)
                    ·
                      rfl

theorem cell22_1446178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_1446178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446178 prefixEnd_1446178 := by exact prefixLift 1446178
  have htrace : WordTrace (prefixWord ++ tailWord_1446178) baseStart_1446178 baseEnd_1446178 := by
    simpa [prefixWord, tailWord_1446178, baseEnd_1446178] using wordTrace_append hprefix tailTrace_1446178
  have hstable : (prefixWord ++ tailWord_1446178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446178).length < 2 ^ (prefixWord ++ tailWord_1446178).sum := by decide
  have hdescent : baseEnd_1446178 < baseStart_1446178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446180 : List Nat := [2, 3, 1, 3, 1, 3, 3, 2, 4]
def baseStart_1446180 : Nat := 118140960795 + 1446180 * 2 ^ 59
def prefixEnd_1446180 : Nat := 4983230072969 + 3 ^ 40 * 1446180 * 2
def baseEnd_1446180 : Nat := 165018989537612677288699

theorem tailTrace_1446180 : CollatzResearch.WordTrace tailWord_1446180 prefixEnd_1446180 165018989537612677288699 := by
  unfold tailWord_1446180
  simp only [CollatzResearch.WordTrace]
  refine ⟨26373258950372161362699997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35164345267162881816933329 26373258950372161362699997)
  ·
    refine ⟨9889972106389560511012499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26373258950372161362699997 9889972106389560511012499)
    ·
      refine ⟨14834958159584340766518749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9889972106389560511012499 14834958159584340766518749)
      ·
        refine ⟨5563109309844127787444531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14834958159584340766518749 5563109309844127787444531)
        ·
          refine ⟨8344663964766191681166797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5563109309844127787444531 8344663964766191681166797)
          ·
            refine ⟨3129248986787321880437549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8344663964766191681166797 3129248986787321880437549)
            ·
              refine ⟨1173468370045245705164081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3129248986787321880437549 1173468370045245705164081)
              ·
                refine ⟨880101277533934278873061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1173468370045245705164081 880101277533934278873061)
                ·
                  refine ⟨165018989537612677288699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 880101277533934278873061 165018989537612677288699)
                  ·
                    rfl

theorem cell22_1446180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_1446180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446180 prefixEnd_1446180 := by exact prefixLift 1446180
  have htrace : WordTrace (prefixWord ++ tailWord_1446180) baseStart_1446180 baseEnd_1446180 := by
    simpa [prefixWord, tailWord_1446180, baseEnd_1446180] using wordTrace_append hprefix tailTrace_1446180
  have hstable : (prefixWord ++ tailWord_1446180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446180).length < 2 ^ (prefixWord ++ tailWord_1446180).sum := by decide
  have hdescent : baseEnd_1446180 < baseStart_1446180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446219 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 7]
def baseStart_1446219 : Nat := 118140960795 + 1446219 * 2 ^ 59
def prefixEnd_1446219 : Nat := 4983230072969 + 3 ^ 40 * 1446219 * 2
def baseEnd_1446219 : Nat := 165023439703284976713659

theorem tailTrace_1446219 : CollatzResearch.WordTrace tailWord_1446219 prefixEnd_1446219 165023439703284976713659 := by
  unfold tailWord_1446219
  simp only [CollatzResearch.WordTrace]
  refine ⟨52747940347603032386069711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35165293565068688257379807 52747940347603032386069711)
  ·
    refine ⟨79121910521404548579104567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52747940347603032386069711 79121910521404548579104567)
    ·
      refine ⟨118682865782106822868656851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79121910521404548579104567 118682865782106822868656851)
      ·
        refine ⟨178024298673160234302985277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118682865782106822868656851 178024298673160234302985277)
        ·
          refine ⟨66759112002435087863619479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178024298673160234302985277 66759112002435087863619479)
          ·
            refine ⟨100138668003652631795429219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66759112002435087863619479 100138668003652631795429219)
            ·
              refine ⟨150208002005478947693143829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100138668003652631795429219 150208002005478947693143829)
              ·
                refine ⟨7041000094006825673116117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 150208002005478947693143829 7041000094006825673116117)
                ·
                  refine ⟨165023439703284976713659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7041000094006825673116117 165023439703284976713659)
                  ·
                    rfl

theorem cell22_1446219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 7].length) (baseStart_1446219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446219 prefixEnd_1446219 := by exact prefixLift 1446219
  have htrace : WordTrace (prefixWord ++ tailWord_1446219) baseStart_1446219 baseEnd_1446219 := by
    simpa [prefixWord, tailWord_1446219, baseEnd_1446219] using wordTrace_append hprefix tailTrace_1446219
  have hstable : (prefixWord ++ tailWord_1446219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446219).length < 2 ^ (prefixWord ++ tailWord_1446219).sum := by decide
  have hdescent : baseEnd_1446219 < baseStart_1446219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446283 : List Nat := [1, 1, 1, 1, 4, 5, 1, 3, 1, 4]
def baseStart_1446283 : Nat := 118140960795 + 1446283 * 2 ^ 59
def prefixEnd_1446283 : Nat := 4983230072969 + 3 ^ 40 * 1446283 * 2
def baseEnd_1446283 : Nat := 495092227617780096540781

theorem tailTrace_1446283 : CollatzResearch.WordTrace tailWord_1446283 prefixEnd_1446283 495092227617780096540781 := by
  unfold tailWord_1446283
  simp only [CollatzResearch.WordTrace]
  refine ⟨52750274619371171316399503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35166849746247447544266335 52750274619371171316399503)
  ·
    refine ⟨79125411929056756974599255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52750274619371171316399503 79125411929056756974599255)
    ·
      refine ⟨118688117893585135461898883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79125411929056756974599255 118688117893585135461898883)
      ·
        refine ⟨178032176840377703192848325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118688117893585135461898883 178032176840377703192848325)
        ·
          refine ⟨33381033157570819348659061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178032176840377703192848325 33381033157570819348659061)
          ·
            refine ⟨3129471858522264313936787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33381033157570819348659061 3129471858522264313936787)
            ·
              refine ⟨4694207787783396470905181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3129471858522264313936787 4694207787783396470905181)
              ·
                refine ⟨1760327920418773676589443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4694207787783396470905181 1760327920418773676589443)
                ·
                  refine ⟨2640491880628160514884165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1760327920418773676589443 2640491880628160514884165)
                  ·
                    refine ⟨495092227617780096540781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2640491880628160514884165 495092227617780096540781)
                    ·
                      rfl

theorem cell22_1446283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 4].length) (baseStart_1446283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446283 prefixEnd_1446283 := by exact prefixLift 1446283
  have htrace : WordTrace (prefixWord ++ tailWord_1446283) baseStart_1446283 baseEnd_1446283 := by
    simpa [prefixWord, tailWord_1446283, baseEnd_1446283] using wordTrace_append hprefix tailTrace_1446283
  have hstable : (prefixWord ++ tailWord_1446283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446283).length < 2 ^ (prefixWord ++ tailWord_1446283).sum := by decide
  have hdescent : baseEnd_1446283 < baseStart_1446283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446298 : List Nat := [3, 1, 1, 4, 1, 3, 2, 1, 6]
def baseStart_1446298 : Nat := 118140960795 + 1446298 * 2 ^ 59
def prefixEnd_1446298 : Nat := 4983230072969 + 3 ^ 40 * 1446298 * 2
def baseEnd_1446298 : Nat := 165032454141441685805245

theorem tailTrace_1446298 : CollatzResearch.WordTrace tailWord_1446298 prefixEnd_1446298 165032454141441685805245 := by
  unfold tailWord_1446298
  simp only [CollatzResearch.WordTrace]
  refine ⟨13187705428579207219548887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35167214476211219252130365 13187705428579207219548887)
  ·
    refine ⟨19781558142868810829323331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13187705428579207219548887 19781558142868810829323331)
    ·
      refine ⟨29672337214303216243984997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19781558142868810829323331 29672337214303216243984997)
      ·
        refine ⟨5563563227681853045747187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29672337214303216243984997 5563563227681853045747187)
        ·
          refine ⟨8345344841522779568620781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5563563227681853045747187 8345344841522779568620781)
          ·
            refine ⟨3129504315571042338232793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8345344841522779568620781 3129504315571042338232793)
            ·
              refine ⟨2347128236678281753674595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3129504315571042338232793 2347128236678281753674595)
              ·
                refine ⟨3520692355017422630511893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2347128236678281753674595 3520692355017422630511893)
                ·
                  refine ⟨165032454141441685805245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3520692355017422630511893 165032454141441685805245)
                  ·
                    rfl

theorem cell22_1446298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_1446298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446298 prefixEnd_1446298 := by exact prefixLift 1446298
  have htrace : WordTrace (prefixWord ++ tailWord_1446298) baseStart_1446298 baseEnd_1446298 := by
    simpa [prefixWord, tailWord_1446298, baseEnd_1446298] using wordTrace_append hprefix tailTrace_1446298
  have hstable : (prefixWord ++ tailWord_1446298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446298).length < 2 ^ (prefixWord ++ tailWord_1446298).sum := by decide
  have hdescent : baseEnd_1446298 < baseStart_1446298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446313 : List Nat := [1, 2, 1, 1, 1, 1, 3, 7, 2, 3]
def baseStart_1446313 : Nat := 118140960795 + 1446313 * 2 ^ 59
def prefixEnd_1446313 : Nat := 4983230072969 + 3 ^ 40 * 1446313 * 2
def baseEnd_1446313 : Nat := 495102497230870018290689

theorem tailTrace_1446313 : CollatzResearch.WordTrace tailWord_1446313 prefixEnd_1446313 495102497230870018290689 := by
  unfold tailWord_1446313
  simp only [CollatzResearch.WordTrace]
  refine ⟨52751368809262486439991593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35167579206174990959994395 52751368809262486439991593)
  ·
    refine ⟨39563526606946864829993695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52751368809262486439991593 39563526606946864829993695)
    ·
      refine ⟨59345289910420297244990543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39563526606946864829993695 59345289910420297244990543)
      ·
        refine ⟨89017934865630445867485815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59345289910420297244990543 89017934865630445867485815)
        ·
          refine ⟨133526902298445668801228723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89017934865630445867485815 133526902298445668801228723)
          ·
            refine ⟨200290353447668503201843085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133526902298445668801228723 200290353447668503201843085)
            ·
              refine ⟨75108882542875688700691157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200290353447668503201843085 75108882542875688700691157)
              ·
                refine ⟨1760364434598648953922449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 75108882542875688700691157 1760364434598648953922449)
                ·
                  refine ⟨1320273325948986715441837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1760364434598648953922449 1320273325948986715441837)
                  ·
                    refine ⟨495102497230870018290689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1320273325948986715441837 495102497230870018290689)
                    ·
                      rfl

theorem cell22_1446313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 3].length) (baseStart_1446313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446313 prefixEnd_1446313 := by exact prefixLift 1446313
  have htrace : WordTrace (prefixWord ++ tailWord_1446313) baseStart_1446313 baseEnd_1446313 := by
    simpa [prefixWord, tailWord_1446313, baseEnd_1446313] using wordTrace_append hprefix tailTrace_1446313
  have hstable : (prefixWord ++ tailWord_1446313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446313).length < 2 ^ (prefixWord ++ tailWord_1446313).sum := by decide
  have hdescent : baseEnd_1446313 < baseStart_1446313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446317 : List Nat := [1, 5, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_1446317 : Nat := 118140960795 + 1446317 * 2 ^ 59
def prefixEnd_1446317 : Nat := 4983230072969 + 3 ^ 40 * 1446317 * 2
def baseEnd_1446317 : Nat := 495103866512615341190677

theorem tailTrace_1446317 : CollatzResearch.WordTrace tailWord_1446317 prefixEnd_1446317 495103866512615341190677 := by
  unfold tailWord_1446317
  simp only [CollatzResearch.WordTrace]
  refine ⟨52751514701247995123137205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35167676467498663415424803 52751514701247995123137205)
  ·
    refine ⟨4945454503241999542794113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52751514701247995123137205 4945454503241999542794113)
    ·
      refine ⟨3709090877431499657095585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4945454503241999542794113 3709090877431499657095585)
      ·
        refine ⟨2781818158073624742821689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3709090877431499657095585 2781818158073624742821689)
        ·
          refine ⟨2086363618555218557116267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2781818158073624742821689 2086363618555218557116267)
          ·
            refine ⟨3129545427832827835674401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2086363618555218557116267 3129545427832827835674401)
            ·
              refine ⟨2347159070874620876755801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3129545427832827835674401 2347159070874620876755801)
              ·
                refine ⟨1760369303155965657566851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2347159070874620876755801 1760369303155965657566851)
                ·
                  refine ⟨2640553954733948486350277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1760369303155965657566851 2640553954733948486350277)
                  ·
                    refine ⟨495103866512615341190677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2640553954733948486350277 495103866512615341190677)
                    ·
                      rfl

theorem cell22_1446317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_1446317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446317 prefixEnd_1446317 := by exact prefixLift 1446317
  have htrace : WordTrace (prefixWord ++ tailWord_1446317) baseStart_1446317 baseEnd_1446317 := by
    simpa [prefixWord, tailWord_1446317, baseEnd_1446317] using wordTrace_append hprefix tailTrace_1446317
  have hstable : (prefixWord ++ tailWord_1446317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446317).length < 2 ^ (prefixWord ++ tailWord_1446317).sum := by decide
  have hdescent : baseEnd_1446317 < baseStart_1446317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446332 : List Nat := [2, 2, 2, 4, 1, 3, 1, 3, 4]
def baseStart_1446332 : Nat := 118140960795 + 1446332 * 2 ^ 59
def prefixEnd_1446332 : Nat := 4983230072969 + 3 ^ 40 * 1446332 * 2
def baseEnd_1446332 : Nat := 165036333773053434021877

theorem tailTrace_1446332 : CollatzResearch.WordTrace tailWord_1446332 prefixEnd_1446332 165036333773053434021877 := by
  unfold tailWord_1446332
  simp only [CollatzResearch.WordTrace]
  refine ⟨26376030898096826342466625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35168041197462435123288833 26376030898096826342466625)
  ·
    refine ⟨19782023173572619756849969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26376030898096826342466625 19782023173572619756849969)
    ·
      refine ⟨14836517380179464817637477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19782023173572619756849969 14836517380179464817637477)
      ·
        refine ⟨2781847008783649653307027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14836517380179464817637477 2781847008783649653307027)
        ·
          refine ⟨4172770513175474479960541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2781847008783649653307027 4172770513175474479960541)
          ·
            refine ⟨1564788942440802929985203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4172770513175474479960541 1564788942440802929985203)
            ·
              refine ⟨2347183413661204394977805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1564788942440802929985203 2347183413661204394977805)
              ·
                refine ⟨880193780122951648116677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2347183413661204394977805 880193780122951648116677)
                ·
                  refine ⟨165036333773053434021877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 880193780122951648116677 165036333773053434021877)
                  ·
                    rfl

theorem cell22_1446332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_1446332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446332 prefixEnd_1446332 := by exact prefixLift 1446332
  have htrace : WordTrace (prefixWord ++ tailWord_1446332) baseStart_1446332 baseEnd_1446332 := by
    simpa [prefixWord, tailWord_1446332, baseEnd_1446332] using wordTrace_append hprefix tailTrace_1446332
  have hstable : (prefixWord ++ tailWord_1446332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446332).length < 2 ^ (prefixWord ++ tailWord_1446332).sum := by decide
  have hdescent : baseEnd_1446332 < baseStart_1446332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446420 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1446420 : Nat := 118140960795 + 1446420 * 2 ^ 59
def prefixEnd_1446420 : Nat := 4983230072969 + 3 ^ 40 * 1446420 * 2
def baseEnd_1446420 : Nat := 495139125517557405865361

theorem tailTrace_1446420 : CollatzResearch.WordTrace tailWord_1446420 prefixEnd_1446420 495139125517557405865361 := by
  unfold tailWord_1446420
  simp only [CollatzResearch.WordTrace]
  refine ⟨26377635709937421857068357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35170180946583229142757809 26377635709937421857068357)
  ·
    refine ⟨4945806695613266598200317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26377635709937421857068357 4945806695613266598200317)
    ·
      refine ⟨1854677510854974974325119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4945806695613266598200317 1854677510854974974325119)
      ·
        refine ⟨2782016266282462461487679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1854677510854974974325119 2782016266282462461487679)
        ·
          refine ⟨4173024399423693692231519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2782016266282462461487679 4173024399423693692231519)
          ·
            refine ⟨6259536599135540538347279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4173024399423693692231519 6259536599135540538347279)
            ·
              refine ⟨9389304898703310807520919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6259536599135540538347279 9389304898703310807520919)
              ·
                refine ⟨14083957348054966211281379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9389304898703310807520919 14083957348054966211281379)
                ·
                  refine ⟨21125936022082449316922069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14083957348054966211281379 21125936022082449316922069)
                  ·
                    refine ⟨495139125517557405865361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21125936022082449316922069 495139125517557405865361)
                    ·
                      rfl

theorem cell22_1446420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1446420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446420 prefixEnd_1446420 := by exact prefixLift 1446420
  have htrace : WordTrace (prefixWord ++ tailWord_1446420) baseStart_1446420 baseEnd_1446420 := by
    simpa [prefixWord, tailWord_1446420, baseEnd_1446420] using wordTrace_append hprefix tailTrace_1446420
  have hstable : (prefixWord ++ tailWord_1446420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446420).length < 2 ^ (prefixWord ++ tailWord_1446420).sum := by decide
  have hdescent : baseEnd_1446420 < baseStart_1446420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446433 : List Nat := [1, 2, 3, 2, 2, 1, 3, 2, 6]
def baseStart_1446433 : Nat := 118140960795 + 1446433 * 2 ^ 59
def prefixEnd_1446433 : Nat := 4983230072969 + 3 ^ 40 * 1446433 * 2
def baseEnd_1446433 : Nat := 165047858561076568430107

theorem tailTrace_1446433 : CollatzResearch.WordTrace tailWord_1446433 prefixEnd_1446433 165047858561076568430107 := by
  unfold tailWord_1446433
  simp only [CollatzResearch.WordTrace]
  refine ⟨52755745568827746934359953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35170497045885164622906635 52755745568827746934359953)
  ·
    refine ⟨39566809176620810200769965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52755745568827746934359953 39566809176620810200769965)
    ·
      refine ⟨14837553441232803825288737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39566809176620810200769965 14837553441232803825288737)
      ·
        refine ⟨11128165080924602868966553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14837553441232803825288737 11128165080924602868966553)
        ·
          refine ⟨8346123810693452151724915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11128165080924602868966553 8346123810693452151724915)
          ·
            refine ⟨12519185716040178227587373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8346123810693452151724915 12519185716040178227587373)
            ·
              refine ⟨4694694643515066835345265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12519185716040178227587373 4694694643515066835345265)
              ·
                refine ⟨3521020982636300126508949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4694694643515066835345265 3521020982636300126508949)
                ·
                  refine ⟨165047858561076568430107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3521020982636300126508949 165047858561076568430107)
                  ·
                    rfl

theorem cell22_1446433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 6].length) (baseStart_1446433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446433 prefixEnd_1446433 := by exact prefixLift 1446433
  have htrace : WordTrace (prefixWord ++ tailWord_1446433) baseStart_1446433 baseEnd_1446433 := by
    simpa [prefixWord, tailWord_1446433, baseEnd_1446433] using wordTrace_append hprefix tailTrace_1446433
  have hstable : (prefixWord ++ tailWord_1446433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446433).length < 2 ^ (prefixWord ++ tailWord_1446433).sum := by decide
  have hdescent : baseEnd_1446433 < baseStart_1446433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446448 : List Nat := [2, 1, 1, 1, 2, 3, 4, 2, 1, 5]
def baseStart_1446448 : Nat := 118140960795 + 1446448 * 2 ^ 59
def prefixEnd_1446448 : Nat := 4983230072969 + 3 ^ 40 * 1446448 * 2
def baseEnd_1446448 : Nat := 495148710489774666165275

theorem tailTrace_1446448 : CollatzResearch.WordTrace tailWord_1446448 prefixEnd_1446448 495148710489774666165275 := by
  unfold tailWord_1446448
  simp only [CollatzResearch.WordTrace]
  refine ⟨26378146331886702248077999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35170861775848936330770665 26378146331886702248077999)
  ·
    refine ⟨39567219497830053372116999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26378146331886702248077999 39567219497830053372116999)
    ·
      refine ⟨59350829246745080058175499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39567219497830053372116999 59350829246745080058175499)
      ·
        refine ⟨89026243870117620087263249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59350829246745080058175499 89026243870117620087263249)
        ·
          refine ⟨66769682902588215065447437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89026243870117620087263249 66769682902588215065447437)
          ·
            refine ⟨25038631088470580649542789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66769682902588215065447437 25038631088470580649542789)
            ·
              refine ⟨4694743329088233871789273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25038631088470580649542789 4694743329088233871789273)
              ·
                refine ⟨3521057496816175403841955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4694743329088233871789273 3521057496816175403841955)
                ·
                  refine ⟨5281586245224263105762933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3521057496816175403841955 5281586245224263105762933)
                  ·
                    refine ⟨495148710489774666165275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5281586245224263105762933 495148710489774666165275)
                    ·
                      rfl

theorem cell22_1446448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_1446448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446448 prefixEnd_1446448 := by exact prefixLift 1446448
  have htrace : WordTrace (prefixWord ++ tailWord_1446448) baseStart_1446448 baseEnd_1446448 := by
    simpa [prefixWord, tailWord_1446448, baseEnd_1446448] using wordTrace_append hprefix tailTrace_1446448
  have hstable : (prefixWord ++ tailWord_1446448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446448).length < 2 ^ (prefixWord ++ tailWord_1446448).sum := by decide
  have hdescent : baseEnd_1446448 < baseStart_1446448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
