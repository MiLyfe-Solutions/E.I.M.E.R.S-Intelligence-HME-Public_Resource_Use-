import V185TrunkScan22Chunk109

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_986154 : List Nat := [3, 1, 4, 1, 3, 2, 2, 6]
def baseStart_986154 : Nat := 118140960795 + 986154 * 2 ^ 59
def prefixEnd_986154 : Nat := 4983230072969 + 3 ^ 40 * 986154 * 2
def baseEnd_986154 : Nat := 37508963063262214936279

theorem tailTrace_986154 : CollatzResearch.WordTrace tailWord_986154 prefixEnd_986154 37508963063262214936279 := by
  unfold tailWord_986154
  simp only [CollatzResearch.WordTrace]
  refine ⟨8991997817334988634893379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23978660846226636359715677 8991997817334988634893379)
  ·
    refine ⟨13487996726002482952340069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8991997817334988634893379 13487996726002482952340069)
    ·
      refine ⟨2528999386125465553563763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13487996726002482952340069 2528999386125465553563763)
      ·
        refine ⟨3793499079188198330345645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2528999386125465553563763 3793499079188198330345645)
        ·
          refine ⟨1422562154695574373879617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3793499079188198330345645 1422562154695574373879617)
          ·
            refine ⟨1066921616021680780409713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1422562154695574373879617 1066921616021680780409713)
            ·
              refine ⟨800191212016260585307285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1066921616021680780409713 800191212016260585307285)
              ·
                refine ⟨37508963063262214936279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 800191212016260585307285 37508963063262214936279)
                ·
                  rfl

theorem cell22_986154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 6].length) (baseStart_986154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986154 prefixEnd_986154 := by exact prefixLift 986154
  have htrace : WordTrace (prefixWord ++ tailWord_986154) baseStart_986154 baseEnd_986154 := by
    simpa [prefixWord, tailWord_986154, baseEnd_986154] using wordTrace_append hprefix tailTrace_986154
  have hstable : (prefixWord ++ tailWord_986154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986154).length < 2 ^ (prefixWord ++ tailWord_986154).sum := by decide
  have hdescent : baseEnd_986154 < baseStart_986154 := by decide
  rcases family_descends (prefixWord ++ tailWord_986154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986244 : List Nat := [2, 3, 2, 1, 2, 3, 1, 4, 4]
def baseStart_986244 : Nat := 118140960795 + 986244 * 2 ^ 59
def prefixEnd_986244 : Nat := 4983230072969 + 3 ^ 40 * 986244 * 2
def baseEnd_986244 : Nat := 112537158802876566558745

theorem tailTrace_986244 : CollatzResearch.WordTrace tailWord_986244 prefixEnd_986244 112537158802876566558745 := by
  unfold tailWord_986244
  simp only [CollatzResearch.WordTrace]
  refine ⟨17985636919506949955174893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23980849226009266606899857 17985636919506949955174893)
  ·
    refine ⟨6744613844815106233190585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17985636919506949955174893 6744613844815106233190585)
    ·
      refine ⟨5058460383611329674892939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6744613844815106233190585 5058460383611329674892939)
      ·
        refine ⟨7587690575416994512339409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5058460383611329674892939 7587690575416994512339409)
        ·
          refine ⟨5690767931562745884254557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7587690575416994512339409 5690767931562745884254557)
          ·
            refine ⟨2134037974336029706595459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5690767931562745884254557 2134037974336029706595459)
            ·
              refine ⟨3201056961504044559893189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134037974336029706595459 3201056961504044559893189)
              ·
                refine ⟨600198180282008354979973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3201056961504044559893189 600198180282008354979973)
                ·
                  refine ⟨112537158802876566558745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 600198180282008354979973 112537158802876566558745)
                  ·
                    rfl

theorem cell22_986244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_986244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986244 prefixEnd_986244 := by exact prefixLift 986244
  have htrace : WordTrace (prefixWord ++ tailWord_986244) baseStart_986244 baseEnd_986244 := by
    simpa [prefixWord, tailWord_986244, baseEnd_986244] using wordTrace_append hprefix tailTrace_986244
  have hstable : (prefixWord ++ tailWord_986244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986244).length < 2 ^ (prefixWord ++ tailWord_986244).sum := by decide
  have hdescent : baseEnd_986244 < baseStart_986244 := by decide
  rcases family_descends (prefixWord ++ tailWord_986244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986272 : List Nat := [2, 1, 1, 4, 2, 1, 5, 6]
def baseStart_986272 : Nat := 118140960795 + 986272 * 2 ^ 59
def prefixEnd_986272 : Nat := 4983230072969 + 3 ^ 40 * 986272 * 2
def baseEnd_986272 : Nat := 37513451264538551108461

theorem tailTrace_986272 : CollatzResearch.WordTrace tailWord_986272 prefixEnd_986272 37513451264538551108461 := by
  unfold tailWord_986272
  simp only [CollatzResearch.WordTrace]
  refine ⟨17986147541456230346184535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23981530055274973794912713 17986147541456230346184535)
  ·
    refine ⟨26979221312184345519276803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17986147541456230346184535 26979221312184345519276803)
    ·
      refine ⟨40468831968276518278915205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26979221312184345519276803 40468831968276518278915205)
      ·
        refine ⟨7587905994051847177296601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40468831968276518278915205 7587905994051847177296601)
        ·
          refine ⟨5690929495538885382972451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7587905994051847177296601 5690929495538885382972451)
          ·
            refine ⟨8536394243308328074458677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5690929495538885382972451 8536394243308328074458677)
            ·
              refine ⟨800286960310155756980501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8536394243308328074458677 800286960310155756980501)
              ·
                refine ⟨37513451264538551108461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 800286960310155756980501 37513451264538551108461)
                ·
                  rfl

theorem cell22_986272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 6].length) (baseStart_986272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986272 prefixEnd_986272 := by exact prefixLift 986272
  have htrace : WordTrace (prefixWord ++ tailWord_986272) baseStart_986272 baseEnd_986272 := by
    simpa [prefixWord, tailWord_986272, baseEnd_986272] using wordTrace_append hprefix tailTrace_986272
  have hstable : (prefixWord ++ tailWord_986272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986272).length < 2 ^ (prefixWord ++ tailWord_986272).sum := by decide
  have hdescent : baseEnd_986272 < baseStart_986272 := by decide
  rcases family_descends (prefixWord ++ tailWord_986272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986274 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_986274 : Nat := 118140960795 + 986274 * 2 ^ 59
def prefixEnd_986274 : Nat := 4983230072969 + 3 ^ 40 * 986274 * 2
def baseEnd_986274 : Nat := 337621746021719621426143

theorem tailTrace_986274 : CollatzResearch.WordTrace tailWord_986274 prefixEnd_986274 337621746021719621426143 := by
  unfold tailWord_986274
  simp only [CollatzResearch.WordTrace]
  refine ⟨8993092007226303758485469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23981578685936810022627917 8993092007226303758485469)
  ·
    refine ⟨3372409502709863909432051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8993092007226303758485469 3372409502709863909432051)
    ·
      refine ⟨5058614254064795864148077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3372409502709863909432051 5058614254064795864148077)
      ·
        refine ⟨1896980345274298449055529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5058614254064795864148077 1896980345274298449055529)
        ·
          refine ⟨1422735258955723836791647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1896980345274298449055529 1422735258955723836791647)
          ·
            refine ⟨2134102888433585755187471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422735258955723836791647 2134102888433585755187471)
            ·
              refine ⟨3201154332650378632781207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134102888433585755187471 3201154332650378632781207)
              ·
                refine ⟨4801731498975567949171811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3201154332650378632781207 4801731498975567949171811)
                ·
                  refine ⟨7202597248463351923757717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4801731498975567949171811 7202597248463351923757717)
                  ·
                    refine ⟨337621746021719621426143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7202597248463351923757717 337621746021719621426143)
                    ·
                      rfl

theorem cell22_986274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_986274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986274 prefixEnd_986274 := by exact prefixLift 986274
  have htrace : WordTrace (prefixWord ++ tailWord_986274) baseStart_986274 baseEnd_986274 := by
    simpa [prefixWord, tailWord_986274, baseEnd_986274] using wordTrace_append hprefix tailTrace_986274
  have hstable : (prefixWord ++ tailWord_986274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986274).length < 2 ^ (prefixWord ++ tailWord_986274).sum := by decide
  have hdescent : baseEnd_986274 < baseStart_986274 := by decide
  rcases family_descends (prefixWord ++ tailWord_986274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986310 : List Nat := [6, 1, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_986310 : Nat := 118140960795 + 986310 * 2 ^ 59
def prefixEnd_986310 : Nat := 4983230072969 + 3 ^ 40 * 986310 * 2
def baseEnd_986310 : Nat := 337634069557427527526033

theorem tailTrace_986310 : CollatzResearch.WordTrace tailWord_986310 prefixEnd_986310 337634069557427527526033 := by
  unfold tailWord_986310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1124177533024212286945387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23982454037849862121501589 1124177533024212286945387)
  ·
    refine ⟨1686266299536318430418081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1124177533024212286945387 1686266299536318430418081)
    ·
      refine ⟨1264699724652238822813561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1686266299536318430418081 1264699724652238822813561)
      ·
        refine ⟨948524793489179117110171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1264699724652238822813561 948524793489179117110171)
        ·
          refine ⟨1422787190233768675665257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948524793489179117110171 1422787190233768675665257)
          ·
            refine ⟨1067090392675326506748943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1422787190233768675665257 1067090392675326506748943)
            ·
              refine ⟨1600635589012989760123415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067090392675326506748943 1600635589012989760123415)
              ·
                refine ⟨2400953383519484640185123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1600635589012989760123415 2400953383519484640185123)
                ·
                  refine ⟨3601430075279226960277685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400953383519484640185123 3601430075279226960277685)
                  ·
                    refine ⟨337634069557427527526033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3601430075279226960277685 337634069557427527526033)
                    ·
                      rfl

theorem cell22_986310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_986310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986310 prefixEnd_986310 := by exact prefixLift 986310
  have htrace : WordTrace (prefixWord ++ tailWord_986310) baseStart_986310 baseEnd_986310 := by
    simpa [prefixWord, tailWord_986310, baseEnd_986310] using wordTrace_append hprefix tailTrace_986310
  have hstable : (prefixWord ++ tailWord_986310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986310).length < 2 ^ (prefixWord ++ tailWord_986310).sum := by decide
  have hdescent : baseEnd_986310 < baseStart_986310 := by decide
  rcases family_descends (prefixWord ++ tailWord_986310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986315 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 1, 7]
def baseStart_986315 : Nat := 118140960795 + 986315 * 2 ^ 59
def prefixEnd_986315 : Nat := 4983230072969 + 3 ^ 40 * 986315 * 2
def baseEnd_986315 : Nat := 337635781159609181151017

theorem tailTrace_986315 : CollatzResearch.WordTrace tailWord_986315 prefixEnd_986315 337635781159609181151017 := by
  unfold tailWord_986315
  simp only [CollatzResearch.WordTrace]
  refine ⟨35973863421756679036184399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23982575614504452690789599 35973863421756679036184399)
  ·
    refine ⟨53960795132635018554276599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35973863421756679036184399 53960795132635018554276599)
    ·
      refine ⟨80941192698952527831414899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53960795132635018554276599 80941192698952527831414899)
      ·
        refine ⟨121411789048428791747122349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80941192698952527831414899 121411789048428791747122349)
        ·
          refine ⟨45529420893160796905170881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121411789048428791747122349 45529420893160796905170881)
          ·
            refine ⟨34147065669870597678878161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45529420893160796905170881 34147065669870597678878161)
            ·
              refine ⟨25610299252402948259158621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34147065669870597678878161 25610299252402948259158621)
              ·
                refine ⟨9603862219651105597184483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25610299252402948259158621 9603862219651105597184483)
                ·
                  refine ⟨14405793329476658395776725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9603862219651105597184483 14405793329476658395776725)
                  ·
                    refine ⟨337635781159609181151017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14405793329476658395776725 337635781159609181151017)
                    ·
                      rfl

theorem cell22_986315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 7].length) (baseStart_986315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986315 prefixEnd_986315 := by exact prefixLift 986315
  have htrace : WordTrace (prefixWord ++ tailWord_986315) baseStart_986315 baseEnd_986315 := by
    simpa [prefixWord, tailWord_986315, baseEnd_986315] using wordTrace_append hprefix tailTrace_986315
  have hstable : (prefixWord ++ tailWord_986315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986315).length < 2 ^ (prefixWord ++ tailWord_986315).sum := by decide
  have hdescent : baseEnd_986315 < baseStart_986315 := by decide
  rcases family_descends (prefixWord ++ tailWord_986315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986377 : List Nat := [1, 2, 1, 1, 3, 3, 2, 3, 1, 5]
def baseStart_986377 : Nat := 118140960795 + 986377 * 2 ^ 59
def prefixEnd_986377 : Nat := 4983230072969 + 3 ^ 40 * 986377 * 2
def baseEnd_986377 : Nat := 337657005026661686100827

theorem tailTrace_986377 : CollatzResearch.WordTrace tailWord_986377 prefixEnd_986377 337657005026661686100827 := by
  unfold tailWord_986377
  simp only [CollatzResearch.WordTrace]
  refine ⟨35976124747532063624941385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23984083165021375749960923 35976124747532063624941385)
  ·
    refine ⟨26982093560649047718706039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35976124747532063624941385 26982093560649047718706039)
    ·
      refine ⟨40473140340973571578059059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26982093560649047718706039 40473140340973571578059059)
      ·
        refine ⟨60709710511460357367088589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40473140340973571578059059 60709710511460357367088589)
        ·
          refine ⟨22766141441797634012658221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60709710511460357367088589 22766141441797634012658221)
          ·
            refine ⟨8537303040674112754746833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22766141441797634012658221 8537303040674112754746833)
            ·
              refine ⟨6402977280505584566060125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8537303040674112754746833 6402977280505584566060125)
              ·
                refine ⟨2401116480189594212272547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6402977280505584566060125 2401116480189594212272547)
                ·
                  refine ⟨3601674720284391318408821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2401116480189594212272547 3601674720284391318408821)
                  ·
                    refine ⟨337657005026661686100827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3601674720284391318408821 337657005026661686100827)
                    ·
                      rfl

theorem cell22_986377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_986377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986377 prefixEnd_986377 := by exact prefixLift 986377
  have htrace : WordTrace (prefixWord ++ tailWord_986377) baseStart_986377 baseEnd_986377 := by
    simpa [prefixWord, tailWord_986377, baseEnd_986377] using wordTrace_append hprefix tailTrace_986377
  have hstable : (prefixWord ++ tailWord_986377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986377).length < 2 ^ (prefixWord ++ tailWord_986377).sum := by decide
  have hdescent : baseEnd_986377 < baseStart_986377 := by decide
  rcases family_descends (prefixWord ++ tailWord_986377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986394 : List Nat := [3, 1, 1, 3, 3, 2, 1, 2, 1, 5]
def baseStart_986394 : Nat := 118140960795 + 986394 * 2 ^ 59
def prefixEnd_986394 : Nat := 4983230072969 + 3 ^ 40 * 986394 * 2
def baseEnd_986394 : Nat := 337662824474079308425775

theorem tailTrace_986394 : CollatzResearch.WordTrace tailWord_986394 prefixEnd_986394 337662824474079308425775 := by
  unfold tailWord_986394
  simp only [CollatzResearch.WordTrace]
  refine ⟨8994186197117618882077559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23984496525646983685540157 8994186197117618882077559)
  ·
    refine ⟨13491279295676428323116339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8994186197117618882077559 13491279295676428323116339)
    ·
      refine ⟨20236918943514642484674509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13491279295676428323116339 20236918943514642484674509)
      ·
        refine ⟨7588844603817990931752941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20236918943514642484674509 7588844603817990931752941)
        ·
          refine ⟨2845816726431746599407353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7588844603817990931752941 2845816726431746599407353)
          ·
            refine ⟨2134362544823809949555515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2845816726431746599407353 2134362544823809949555515)
            ·
              refine ⟨3201543817235714924333273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134362544823809949555515 3201543817235714924333273)
              ·
                refine ⟨2401157862926786193249955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3201543817235714924333273 2401157862926786193249955)
                ·
                  refine ⟨3601736794390179289874933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2401157862926786193249955 3601736794390179289874933)
                  ·
                    refine ⟨337662824474079308425775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3601736794390179289874933 337662824474079308425775)
                    ·
                      rfl

theorem cell22_986394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_986394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986394 prefixEnd_986394 := by exact prefixLift 986394
  have htrace : WordTrace (prefixWord ++ tailWord_986394) baseStart_986394 baseEnd_986394 := by
    simpa [prefixWord, tailWord_986394, baseEnd_986394] using wordTrace_append hprefix tailTrace_986394
  have hstable : (prefixWord ++ tailWord_986394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986394).length < 2 ^ (prefixWord ++ tailWord_986394).sum := by decide
  have hdescent : baseEnd_986394 < baseStart_986394 := by decide
  rcases family_descends (prefixWord ++ tailWord_986394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986413 : List Nat := [1, 5, 3, 1, 1, 2, 1, 4, 4]
def baseStart_986413 : Nat := 118140960795 + 986413 * 2 ^ 59
def prefixEnd_986413 : Nat := 4983230072969 + 3 ^ 40 * 986413 * 2
def baseEnd_986413 : Nat := 112556442854123197400239

theorem tailTrace_986413 : CollatzResearch.WordTrace tailWord_986413 prefixEnd_986413 112556442854123197400239 := by
  unfold tailWord_986413
  simp only [CollatzResearch.WordTrace]
  refine ⟨35977437775401641773251893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23984958516934427848834595 35977437775401641773251893)
  ·
    refine ⟨3372884791443903916242365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35977437775401641773251893 3372884791443903916242365)
    ·
      refine ⟨1264831796791463968590887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3372884791443903916242365 1264831796791463968590887)
      ·
        refine ⟨1897247695187195952886331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1264831796791463968590887 1897247695187195952886331)
        ·
          refine ⟨2845871542780793929329497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897247695187195952886331 2845871542780793929329497)
          ·
            refine ⟨2134403657085595446997123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2845871542780793929329497 2134403657085595446997123)
            ·
              refine ⟨3201605485628393170495685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134403657085595446997123 3201605485628393170495685)
              ·
                refine ⟨600301028555323719467941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3201605485628393170495685 600301028555323719467941)
                ·
                  refine ⟨112556442854123197400239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 600301028555323719467941 112556442854123197400239)
                  ·
                    rfl

theorem cell22_986413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_986413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986413 prefixEnd_986413 := by exact prefixLift 986413
  have htrace : WordTrace (prefixWord ++ tailWord_986413) baseStart_986413 baseEnd_986413 := by
    simpa [prefixWord, tailWord_986413, baseEnd_986413] using wordTrace_append hprefix tailTrace_986413
  have hstable : (prefixWord ++ tailWord_986413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986413).length < 2 ^ (prefixWord ++ tailWord_986413).sum := by decide
  have hdescent : baseEnd_986413 < baseStart_986413 := by decide
  rcases family_descends (prefixWord ++ tailWord_986413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986439 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 5, 3]
def baseStart_986439 : Nat := 118140960795 + 986439 * 2 ^ 59
def prefixEnd_986439 : Nat := 4983230072969 + 3 ^ 40 * 986439 * 2
def baseEnd_986439 : Nat := 337678228893714191050637

theorem tailTrace_986439 : CollatzResearch.WordTrace tailWord_986439 prefixEnd_986439 337678228893714191050637 := by
  unfold tailWord_986439
  simp only [CollatzResearch.WordTrace]
  refine ⟨35978386073307448213698371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23985590715538298809132247 35978386073307448213698371)
  ·
    refine ⟨53967579109961172320547557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35978386073307448213698371 53967579109961172320547557)
    ·
      refine ⟨10118921083117719810102667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53967579109961172320547557 10118921083117719810102667)
      ·
        refine ⟨15178381624676579715154001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10118921083117719810102667 15178381624676579715154001)
        ·
          refine ⟨11383786218507434786365501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15178381624676579715154001 11383786218507434786365501)
          ·
            refine ⟨4268919831940288044887063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11383786218507434786365501 4268919831940288044887063)
            ·
              refine ⟨6403379747910432067330595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4268919831940288044887063 6403379747910432067330595)
              ·
                refine ⟨9605069621865648100995893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6403379747910432067330595 9605069621865648100995893)
                ·
                  refine ⟨900475277049904509468365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9605069621865648100995893 900475277049904509468365)
                  ·
                    refine ⟨337678228893714191050637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 900475277049904509468365 337678228893714191050637)
                    ·
                      rfl

theorem cell22_986439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_986439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986439 prefixEnd_986439 := by exact prefixLift 986439
  have htrace : WordTrace (prefixWord ++ tailWord_986439) baseStart_986439 baseEnd_986439 := by
    simpa [prefixWord, tailWord_986439, baseEnd_986439] using wordTrace_append hprefix tailTrace_986439
  have hstable : (prefixWord ++ tailWord_986439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986439).length < 2 ^ (prefixWord ++ tailWord_986439).sum := by decide
  have hdescent : baseEnd_986439 < baseStart_986439 := by decide
  rcases family_descends (prefixWord ++ tailWord_986439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986580 : List Nat := [2, 4, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_986580 : Nat := 118140960795 + 986580 * 2 ^ 59
def prefixEnd_986580 : Nat := 4983230072969 + 3 ^ 40 * 986580 * 2
def baseEnd_986580 : Nat := 337726496075236823275205

theorem tailTrace_986580 : CollatzResearch.WordTrace tailWord_986580 prefixEnd_986580 337726496075236823275205 := by
  unfold tailWord_986580
  simp only [CollatzResearch.WordTrace]
  refine ⟨17991764382898314647290597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23989019177197752863054129 17991764382898314647290597)
  ·
    refine ⟨3373455821793433996366987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17991764382898314647290597 3373455821793433996366987)
    ·
      refine ⟨5060183732690150994550481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3373455821793433996366987 5060183732690150994550481)
      ·
        refine ⟨3795137799517613245912861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5060183732690150994550481 3795137799517613245912861)
        ·
          refine ⟨1423176674819104967217323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3795137799517613245912861 1423176674819104967217323)
          ·
            refine ⟨2134765012228657450825985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423176674819104967217323 2134765012228657450825985)
            ·
              refine ⟨1601073759171493088119489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2134765012228657450825985 1601073759171493088119489)
              ·
                refine ⟨1200805319378619816089617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1601073759171493088119489 1200805319378619816089617)
                ·
                  refine ⟨900603989533964862067213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1200805319378619816089617 900603989533964862067213)
                  ·
                    refine ⟨337726496075236823275205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 900603989533964862067213 337726496075236823275205)
                    ·
                      rfl

theorem cell22_986580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_986580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986580 prefixEnd_986580 := by exact prefixLift 986580
  have htrace : WordTrace (prefixWord ++ tailWord_986580) baseStart_986580 baseEnd_986580 := by
    simpa [prefixWord, tailWord_986580, baseEnd_986580] using wordTrace_append hprefix tailTrace_986580
  have hstable : (prefixWord ++ tailWord_986580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986580).length < 2 ^ (prefixWord ++ tailWord_986580).sum := by decide
  have hdescent : baseEnd_986580 < baseStart_986580 := by decide
  rcases family_descends (prefixWord ++ tailWord_986580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986582 : List Nat := [5, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_986582 : Nat := 118140960795 + 986582 * 2 ^ 59
def prefixEnd_986582 : Nat := 4983230072969 + 3 ^ 40 * 986582 * 2
def baseEnd_986582 : Nat := 112575726905369828241733

theorem tailTrace_986582 : CollatzResearch.WordTrace tailWord_986582 prefixEnd_986582 112575726905369828241733 := by
  unfold tailWord_986582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2248975106986836477259625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23989067807859589090769333 2248975106986836477259625)
  ·
    refine ⟨1686731330240127357944719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2248975106986836477259625 1686731330240127357944719)
    ·
      refine ⟨2530096995360191036917079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1686731330240127357944719 2530096995360191036917079)
      ·
        refine ⟨3795145493040286555375619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2530096995360191036917079 3795145493040286555375619)
        ·
          refine ⟨5692718239560429833063429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3795145493040286555375619 5692718239560429833063429)
          ·
            refine ⟨1067384669917580593699393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5692718239560429833063429 1067384669917580593699393)
            ·
              refine ⟨800538502438185445274545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1067384669917580593699393 800538502438185445274545)
              ·
                refine ⟨600403876828639083955909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 800538502438185445274545 600403876828639083955909)
                ·
                  refine ⟨112575726905369828241733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 600403876828639083955909 112575726905369828241733)
                  ·
                    rfl

theorem cell22_986582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_986582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986582 prefixEnd_986582 := by exact prefixLift 986582
  have htrace : WordTrace (prefixWord ++ tailWord_986582) baseStart_986582 baseEnd_986582 := by
    simpa [prefixWord, tailWord_986582, baseEnd_986582] using wordTrace_append hprefix tailTrace_986582
  have hstable : (prefixWord ++ tailWord_986582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986582).length < 2 ^ (prefixWord ++ tailWord_986582).sum := by decide
  have hdescent : baseEnd_986582 < baseStart_986582 := by decide
  rcases family_descends (prefixWord ++ tailWord_986582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986591 : List Nat := [1, 1, 2, 3, 3, 1, 2, 3, 3, 3]
def baseStart_986591 : Nat := 118140960795 + 986591 * 2 ^ 59
def prefixEnd_986591 : Nat := 4983230072969 + 3 ^ 40 * 986591 * 2
def baseEnd_986591 : Nat := 337730261600036461250171

theorem tailTrace_986591 : CollatzResearch.WordTrace tailWord_986591 prefixEnd_986591 337730261600036461250171 := by
  unfold tailWord_986591
  simp only [CollatzResearch.WordTrace]
  refine ⟨35983929968756778173231627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23989286645837852115487751 35983929968756778173231627)
  ·
    refine ⟨53975894953135167259847441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35983929968756778173231627 53975894953135167259847441)
    ·
      refine ⟨40481921214851375444885581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53975894953135167259847441 40481921214851375444885581)
      ·
        refine ⟨15180720455569265791832093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40481921214851375444885581 15180720455569265791832093)
        ·
          refine ⟨5692770170838474671937035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15180720455569265791832093 5692770170838474671937035)
          ·
            refine ⟨8539155256257712007905553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5692770170838474671937035 8539155256257712007905553)
            ·
              refine ⟨6404366442193284005929165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8539155256257712007905553 6404366442193284005929165)
              ·
                refine ⟨2401637415822481502223437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6404366442193284005929165 2401637415822481502223437)
                ·
                  refine ⟨900614030933430563333789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2401637415822481502223437 900614030933430563333789)
                  ·
                    refine ⟨337730261600036461250171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 900614030933430563333789 337730261600036461250171)
                    ·
                      rfl

theorem cell22_986591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 3].length) (baseStart_986591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986591 prefixEnd_986591 := by exact prefixLift 986591
  have htrace : WordTrace (prefixWord ++ tailWord_986591) baseStart_986591 baseEnd_986591 := by
    simpa [prefixWord, tailWord_986591, baseEnd_986591] using wordTrace_append hprefix tailTrace_986591
  have hstable : (prefixWord ++ tailWord_986591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986591).length < 2 ^ (prefixWord ++ tailWord_986591).sum := by decide
  have hdescent : baseEnd_986591 < baseStart_986591 := by decide
  rcases family_descends (prefixWord ++ tailWord_986591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986666 : List Nat := [3, 1, 4, 1, 1, 1, 1, 4, 6]
def baseStart_986666 : Nat := 118140960795 + 986666 * 2 ^ 59
def prefixEnd_986666 : Nat := 4983230072969 + 3 ^ 40 * 986666 * 2
def baseEnd_986666 : Nat := 112585311877587088541647

theorem tailTrace_986666 : CollatzResearch.WordTrace tailWord_986666 prefixEnd_986666 112585311877587088541647 := by
  unfold tailWord_986666
  simp only [CollatzResearch.WordTrace]
  refine ⟨8996666360871266495552963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23991110295656710654807901 8996666360871266495552963)
  ·
    refine ⟨13494999541306899743329445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8996666360871266495552963 13494999541306899743329445)
    ·
      refine ⟨2530312413995043701874271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13494999541306899743329445 2530312413995043701874271)
      ·
        refine ⟨3795468620992565552811407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2530312413995043701874271 3795468620992565552811407)
        ·
          refine ⟨5693202931488848329217111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3795468620992565552811407 5693202931488848329217111)
          ·
            refine ⟨8539804397233272493825667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5693202931488848329217111 8539804397233272493825667)
            ·
              refine ⟨12809706595849908740738501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8539804397233272493825667 12809706595849908740738501)
              ·
                refine ⟨2401819986721857888888469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12809706595849908740738501 2401819986721857888888469)
                ·
                  refine ⟨112585311877587088541647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2401819986721857888888469 112585311877587088541647)
                  ·
                    rfl

theorem cell22_986666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_986666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986666 prefixEnd_986666 := by exact prefixLift 986666
  have htrace : WordTrace (prefixWord ++ tailWord_986666) baseStart_986666 baseEnd_986666 := by
    simpa [prefixWord, tailWord_986666, baseEnd_986666] using wordTrace_append hprefix tailTrace_986666
  have hstable : (prefixWord ++ tailWord_986666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986666).length < 2 ^ (prefixWord ++ tailWord_986666).sum := by decide
  have hdescent : baseEnd_986666 < baseStart_986666 := by decide
  rcases family_descends (prefixWord ++ tailWord_986666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986698 : List Nat := [3, 1, 2, 1, 1, 3, 2, 4, 2, 3]
def baseStart_986698 : Nat := 118140960795 + 986698 * 2 ^ 59
def prefixEnd_986698 : Nat := 4983230072969 + 3 ^ 40 * 986698 * 2
def baseEnd_986698 : Nat := 337766889886723848824843

theorem tailTrace_986698 : CollatzResearch.WordTrace tailWord_986698 prefixEnd_986698 337766889886723848824843 := by
  unfold tailWord_986698
  simp only [CollatzResearch.WordTrace]
  refine ⟨8996958144842283861844187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23991888386246090298251165 8996958144842283861844187)
  ·
    refine ⟨13495437217263425792766281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8996958144842283861844187 13495437217263425792766281)
    ·
      refine ⟨10121577912947569344574711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13495437217263425792766281 10121577912947569344574711)
      ·
        refine ⟨15182366869421354016862067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10121577912947569344574711 15182366869421354016862067)
        ·
          refine ⟨22773550304132031025293101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15182366869421354016862067 22773550304132031025293101)
          ·
            refine ⟨8540081364049511634484913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22773550304132031025293101 8540081364049511634484913)
            ·
              refine ⟨6405061023037133725863685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8540081364049511634484913 6405061023037133725863685)
              ·
                refine ⟨1200948941819462573599441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6405061023037133725863685 1200948941819462573599441)
                ·
                  refine ⟨900711706364596930199581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1200948941819462573599441 900711706364596930199581)
                  ·
                    refine ⟨337766889886723848824843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 900711706364596930199581 337766889886723848824843)
                    ·
                      rfl

theorem cell22_986698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_986698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986698 prefixEnd_986698 := by exact prefixLift 986698
  have htrace : WordTrace (prefixWord ++ tailWord_986698) baseStart_986698 baseEnd_986698 := by
    simpa [prefixWord, tailWord_986698, baseEnd_986698] using wordTrace_append hprefix tailTrace_986698
  have hstable : (prefixWord ++ tailWord_986698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986698).length < 2 ^ (prefixWord ++ tailWord_986698).sum := by decide
  have hdescent : baseEnd_986698 < baseStart_986698 := by decide
  rcases family_descends (prefixWord ++ tailWord_986698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986700 : List Nat := [2, 2, 1, 3, 1, 4, 3, 2, 4]
def baseStart_986700 : Nat := 118140960795 + 986700 * 2 ^ 59
def prefixEnd_986700 : Nat := 4983230072969 + 3 ^ 40 * 986700 * 2
def baseEnd_986700 : Nat := 112589191509198836758279

theorem tailTrace_986700 : CollatzResearch.WordTrace tailWord_986700 prefixEnd_986700 112589191509198836758279 := by
  unfold tailWord_986700
  simp only [CollatzResearch.WordTrace]
  refine ⟨17993952762680944894474777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23991937016907926525966369 17993952762680944894474777)
  ·
    refine ⟨13495464572010708670856083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17993952762680944894474777 13495464572010708670856083)
    ·
      refine ⟨20243196858016063006284125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13495464572010708670856083 20243196858016063006284125)
      ·
        refine ⟨7591198821756023627356547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20243196858016063006284125 7591198821756023627356547)
        ·
          refine ⟨11386798232634035441034821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7591198821756023627356547 11386798232634035441034821)
          ·
            refine ⟨2135024668618881645194029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11386798232634035441034821 2135024668618881645194029)
            ·
              refine ⟨800634250732080616947761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2135024668618881645194029 800634250732080616947761)
              ·
                refine ⟨600475688049060462710821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 800634250732080616947761 600475688049060462710821)
                ·
                  refine ⟨112589191509198836758279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 600475688049060462710821 112589191509198836758279)
                  ·
                    rfl

theorem cell22_986700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_986700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986700 prefixEnd_986700 := by exact prefixLift 986700
  have htrace : WordTrace (prefixWord ++ tailWord_986700) baseStart_986700 baseEnd_986700 := by
    simpa [prefixWord, tailWord_986700, baseEnd_986700] using wordTrace_append hprefix tailTrace_986700
  have hstable : (prefixWord ++ tailWord_986700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986700).length < 2 ^ (prefixWord ++ tailWord_986700).sum := by decide
  have hdescent : baseEnd_986700 < baseStart_986700 := by decide
  rcases family_descends (prefixWord ++ tailWord_986700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986711 : List Nat := [1, 1, 3, 2, 2, 4, 2, 7]
def baseStart_986711 : Nat := 118140960795 + 986711 * 2 ^ 59
def prefixEnd_986711 : Nat := 4983230072969 + 3 ^ 40 * 986711 * 2
def baseEnd_986711 : Nat := 37530148894710683138867

theorem tailTrace_986711 : CollatzResearch.WordTrace tailWord_986711 prefixEnd_986711 37530148894710683138867 := by
  unfold tailWord_986711
  simp only [CollatzResearch.WordTrace]
  refine ⟨35988306728322038667599987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23992204485548025778399991 35988306728322038667599987)
  ·
    refine ⟨53982460092483058001399981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35988306728322038667599987 53982460092483058001399981)
    ·
      refine ⟨20243422534681146750524993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53982460092483058001399981 20243422534681146750524993)
      ·
        refine ⟨15182566901010860062893745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20243422534681146750524993 15182566901010860062893745)
        ·
          refine ⟨11386925175758145047170309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15182566901010860062893745 11386925175758145047170309)
          ·
            refine ⟨2135048470454652196344433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11386925175758145047170309 2135048470454652196344433)
            ·
              refine ⟨1601286352840989147258325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2135048470454652196344433 1601286352840989147258325)
              ·
                refine ⟨37530148894710683138867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1601286352840989147258325 37530148894710683138867)
                ·
                  rfl

theorem cell22_986711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 7].length) (baseStart_986711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986711 prefixEnd_986711 := by exact prefixLift 986711
  have htrace : WordTrace (prefixWord ++ tailWord_986711) baseStart_986711 baseEnd_986711 := by
    simpa [prefixWord, tailWord_986711, baseEnd_986711] using wordTrace_append hprefix tailTrace_986711
  have hstable : (prefixWord ++ tailWord_986711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986711).length < 2 ^ (prefixWord ++ tailWord_986711).sum := by decide
  have hdescent : baseEnd_986711 < baseStart_986711 := by decide
  rcases family_descends (prefixWord ++ tailWord_986711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986803 : List Nat := [1, 1, 1, 2, 3, 3, 3, 3, 1, 4]
def baseStart_986803 : Nat := 118140960795 + 986803 * 2 ^ 59
def prefixEnd_986803 : Nat := 4983230072969 + 3 ^ 40 * 986803 * 2
def baseEnd_986803 : Nat := 337802833532538574949521

theorem tailTrace_986803 : CollatzResearch.WordTrace tailWord_986803 prefixEnd_986803 337802833532538574949521 := by
  unfold tailWord_986803
  simp only [CollatzResearch.WordTrace]
  refine ⟨35991662243988738379949063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23994441495992492253299375 35991662243988738379949063)
  ·
    refine ⟨53987493365983107569923595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35991662243988738379949063 53987493365983107569923595)
    ·
      refine ⟨80981240048974661354885393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53987493365983107569923595 80981240048974661354885393)
      ·
        refine ⟨60735930036730996016164045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80981240048974661354885393 60735930036730996016164045)
        ·
          refine ⟨22775973763774123506061517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60735930036730996016164045 22775973763774123506061517)
          ·
            refine ⟨8540990161415296314773069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22775973763774123506061517 8540990161415296314773069)
            ·
              refine ⟨3202871310530736118039901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8540990161415296314773069 3202871310530736118039901)
              ·
                refine ⟨1201076741449026044264963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3202871310530736118039901 1201076741449026044264963)
                ·
                  refine ⟨1801615112173539066397445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1201076741449026044264963 1801615112173539066397445)
                  ·
                    refine ⟨337802833532538574949521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1801615112173539066397445 337802833532538574949521)
                    ·
                      rfl

theorem cell22_986803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 4].length) (baseStart_986803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986803 prefixEnd_986803 := by exact prefixLift 986803
  have htrace : WordTrace (prefixWord ++ tailWord_986803) baseStart_986803 baseEnd_986803 := by
    simpa [prefixWord, tailWord_986803, baseEnd_986803] using wordTrace_append hprefix tailTrace_986803
  have hstable : (prefixWord ++ tailWord_986803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986803).length < 2 ^ (prefixWord ++ tailWord_986803).sum := by decide
  have hdescent : baseEnd_986803 < baseStart_986803 := by decide
  rcases family_descends (prefixWord ++ tailWord_986803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986822 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_986822 : Nat := 118140960795 + 986822 * 2 ^ 59
def prefixEnd_986822 : Nat := 4983230072969 + 3 ^ 40 * 986822 * 2
def baseEnd_986822 : Nat := 337809337620828858724463

theorem tailTrace_986822 : CollatzResearch.WordTrace tailWord_986822 prefixEnd_986822 337809337620828858724463 := by
  unfold tailWord_986822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1124761100966247019527835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23994903487279936416593813 1124761100966247019527835)
  ·
    refine ⟨1687141651449370529291753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1124761100966247019527835 1687141651449370529291753)
    ·
      refine ⟨1265356238587027896968815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1687141651449370529291753 1265356238587027896968815)
      ·
        refine ⟨1898034357880541845453223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1265356238587027896968815 1898034357880541845453223)
        ·
          refine ⟨2847051536820812768179835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1898034357880541845453223 2847051536820812768179835)
          ·
            refine ⟨4270577305231219152269753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2847051536820812768179835 4270577305231219152269753)
            ·
              refine ⟨3202932978923414364202315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4270577305231219152269753 3202932978923414364202315)
              ·
                refine ⟨4804399468385121546303473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202932978923414364202315 4804399468385121546303473)
                ·
                  refine ⟨3603299601288841159727605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4804399468385121546303473 3603299601288841159727605)
                  ·
                    refine ⟨337809337620828858724463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3603299601288841159727605 337809337620828858724463)
                    ·
                      rfl

theorem cell22_986822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_986822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986822 prefixEnd_986822 := by exact prefixLift 986822
  have htrace : WordTrace (prefixWord ++ tailWord_986822) baseStart_986822 baseEnd_986822 := by
    simpa [prefixWord, tailWord_986822, baseEnd_986822] using wordTrace_append hprefix tailTrace_986822
  have hstable : (prefixWord ++ tailWord_986822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986822).length < 2 ^ (prefixWord ++ tailWord_986822).sum := by decide
  have hdescent : baseEnd_986822 < baseStart_986822 := by decide
  rcases family_descends (prefixWord ++ tailWord_986822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986833 : List Nat := [1, 2, 2, 1, 2, 4, 3, 1, 1, 5]
def baseStart_986833 : Nat := 118140960795 + 986833 * 2 ^ 59
def prefixEnd_986833 : Nat := 4983230072969 + 3 ^ 40 * 986833 * 2
def baseEnd_986833 : Nat := 337813103145628496699429

theorem tailTrace_986833 : CollatzResearch.WordTrace tailWord_986833 prefixEnd_986833 337813103145628496699429 := by
  unfold tailWord_986833
  simp only [CollatzResearch.WordTrace]
  refine ⟨35992756433880053503541153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23995170955920035669027435 35992756433880053503541153)
  ·
    refine ⟨26994567325410040127655865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35992756433880053503541153 26994567325410040127655865)
    ·
      refine ⟨20245925494057530095741899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26994567325410040127655865 20245925494057530095741899)
      ·
        refine ⟨30368888241086295143612849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20245925494057530095741899 30368888241086295143612849)
        ·
          refine ⟨22776666180814721357709637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30368888241086295143612849 22776666180814721357709637)
          ·
            refine ⟨4270624908902760254570557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22776666180814721357709637 4270624908902760254570557)
            ·
              refine ⟨1601484340838535095463959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4270624908902760254570557 1601484340838535095463959)
              ·
                refine ⟨2402226511257802643195939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1601484340838535095463959 2402226511257802643195939)
                ·
                  refine ⟨3603339766886703964793909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2402226511257802643195939 3603339766886703964793909)
                  ·
                    refine ⟨337813103145628496699429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3603339766886703964793909 337813103145628496699429)
                    ·
                      rfl

theorem cell22_986833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_986833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986833 prefixEnd_986833 := by exact prefixLift 986833
  have htrace : WordTrace (prefixWord ++ tailWord_986833) baseStart_986833 baseEnd_986833 := by
    simpa [prefixWord, tailWord_986833, baseEnd_986833] using wordTrace_append hprefix tailTrace_986833
  have hstable : (prefixWord ++ tailWord_986833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986833).length < 2 ^ (prefixWord ++ tailWord_986833).sum := by decide
  have hdescent : baseEnd_986833 < baseStart_986833 := by decide
  rcases family_descends (prefixWord ++ tailWord_986833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986884 : List Nat := [2, 3, 2, 2, 1, 4, 2, 1, 2, 3]
def baseStart_986884 : Nat := 118140960795 + 986884 * 2 ^ 59
def prefixEnd_986884 : Nat := 4983230072969 + 3 ^ 40 * 986884 * 2
def baseEnd_986884 : Nat := 337830561487881363674273

theorem tailTrace_986884 : CollatzResearch.WordTrace tailWord_986884 prefixEnd_986884 337830561487881363674273 := by
  unfold tailWord_986884
  simp only [CollatzResearch.WordTrace]
  refine ⟨17997308278347644606823853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23996411037796859475765137 17997308278347644606823853)
  ·
    refine ⟨6748990604380366727558945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17997308278347644606823853 6748990604380366727558945)
    ·
      refine ⟨5061742953285275045669209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6748990604380366727558945 5061742953285275045669209)
      ·
        refine ⟨3796307214963956284251907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5061742953285275045669209 3796307214963956284251907)
        ·
          refine ⟨5694460822445934426377861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3796307214963956284251907 5694460822445934426377861)
          ·
            refine ⟨1067711404208612704945849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5694460822445934426377861 1067711404208612704945849)
            ·
              refine ⟨800783553156459528709387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1067711404208612704945849 800783553156459528709387)
              ·
                refine ⟨1201175329734689293064081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 800783553156459528709387 1201175329734689293064081)
                ·
                  refine ⟨900881497301016969798061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1201175329734689293064081 900881497301016969798061)
                  ·
                    refine ⟨337830561487881363674273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 900881497301016969798061 337830561487881363674273)
                    ·
                      rfl

theorem cell22_986884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_986884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986884 prefixEnd_986884 := by exact prefixLift 986884
  have htrace : WordTrace (prefixWord ++ tailWord_986884) baseStart_986884 baseEnd_986884 := by
    simpa [prefixWord, tailWord_986884, baseEnd_986884] using wordTrace_append hprefix tailTrace_986884
  have hstable : (prefixWord ++ tailWord_986884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986884).length < 2 ^ (prefixWord ++ tailWord_986884).sum := by decide
  have hdescent : baseEnd_986884 < baseStart_986884 := by decide
  rcases family_descends (prefixWord ++ tailWord_986884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986912 : List Nat := [2, 1, 1, 5, 1, 1, 2, 5, 1, 3]
def baseStart_986912 : Nat := 118140960795 + 986912 * 2 ^ 59
def prefixEnd_986912 : Nat := 4983230072969 + 3 ^ 40 * 986912 * 2
def baseEnd_986912 : Nat := 337840146460098623974187

theorem tailTrace_986912 : CollatzResearch.WordTrace tailWord_986912 prefixEnd_986912 337840146460098623974187 := by
  unfold tailWord_986912
  simp only [CollatzResearch.WordTrace]
  refine ⟨17997818900296924997833495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23997091867062566663777993 17997818900296924997833495)
  ·
    refine ⟨26996728350445387496750243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17997818900296924997833495 26996728350445387496750243)
    ·
      refine ⟨40495092525668081245125365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26996728350445387496750243 40495092525668081245125365)
      ·
        refine ⟨3796414924281382616730503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40495092525668081245125365 3796414924281382616730503)
        ·
          refine ⟨5694622386422073925095755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3796414924281382616730503 5694622386422073925095755)
          ·
            refine ⟨8541933579633110887643633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5694622386422073925095755 8541933579633110887643633)
            ·
              refine ⟨6406450184724833165732725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8541933579633110887643633 6406450184724833165732725)
              ·
                refine ⟨600604704817953109287443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6406450184724833165732725 600604704817953109287443)
                ·
                  refine ⟨900907057226929663931165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600604704817953109287443 900907057226929663931165)
                  ·
                    refine ⟨337840146460098623974187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 900907057226929663931165 337840146460098623974187)
                    ·
                      rfl

theorem cell22_986912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 1, 3].length) (baseStart_986912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986912 prefixEnd_986912 := by exact prefixLift 986912
  have htrace : WordTrace (prefixWord ++ tailWord_986912) baseStart_986912 baseEnd_986912 := by
    simpa [prefixWord, tailWord_986912, baseEnd_986912] using wordTrace_append hprefix tailTrace_986912
  have hstable : (prefixWord ++ tailWord_986912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986912).length < 2 ^ (prefixWord ++ tailWord_986912).sum := by decide
  have hdescent : baseEnd_986912 < baseStart_986912 := by decide
  rcases family_descends (prefixWord ++ tailWord_986912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986929 : List Nat := [1, 2, 2, 3, 2, 2, 4, 2, 1, 3]
def baseStart_986929 : Nat := 118140960795 + 986929 * 2 ^ 59
def prefixEnd_986929 : Nat := 4983230072969 + 3 ^ 40 * 986929 * 2
def baseEnd_986929 : Nat := 337845965907516246299135

theorem tailTrace_986929 : CollatzResearch.WordTrace tailWord_986929 prefixEnd_986929 337845965907516246299135 := by
  unfold tailWord_986929
  simp only [CollatzResearch.WordTrace]
  refine ⟨35996257841532261899035841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23997505227688174599357227 35996257841532261899035841)
  ·
    refine ⟨26997193381149196424276881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35996257841532261899035841 26997193381149196424276881)
    ·
      refine ⟨20247895035861897318207661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26997193381149196424276881 20247895035861897318207661)
      ·
        refine ⟨7592960638448211494327873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20247895035861897318207661 7592960638448211494327873)
        ·
          refine ⟨5694720478836158620745905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7592960638448211494327873 5694720478836158620745905)
          ·
            refine ⟨4271040359127118965559429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5694720478836158620745905 4271040359127118965559429)
            ·
              refine ⟨800820067336334806042393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4271040359127118965559429 800820067336334806042393)
              ·
                refine ⟨600615050502251104531795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 800820067336334806042393 600615050502251104531795)
                ·
                  refine ⟨900922575753376656797693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600615050502251104531795 900922575753376656797693)
                  ·
                    refine ⟨337845965907516246299135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 900922575753376656797693 337845965907516246299135)
                    ·
                      rfl

theorem cell22_986929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 1, 3].length) (baseStart_986929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986929 prefixEnd_986929 := by exact prefixLift 986929
  have htrace : WordTrace (prefixWord ++ tailWord_986929) baseStart_986929 baseEnd_986929 := by
    simpa [prefixWord, tailWord_986929, baseEnd_986929] using wordTrace_append hprefix tailTrace_986929
  have hstable : (prefixWord ++ tailWord_986929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986929).length < 2 ^ (prefixWord ++ tailWord_986929).sum := by decide
  have hdescent : baseEnd_986929 < baseStart_986929 := by decide
  rcases family_descends (prefixWord ++ tailWord_986929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986953 : List Nat := [1, 2, 1, 1, 2, 4, 3, 2, 6]
def baseStart_986953 : Nat := 118140960795 + 986953 * 2 ^ 59
def prefixEnd_986953 : Nat := 4983230072969 + 3 ^ 40 * 986953 * 2
def baseEnd_986953 : Nat := 112618060532662727899687

theorem tailTrace_986953 : CollatzResearch.WordTrace tailWord_986953 prefixEnd_986953 112618060532662727899687 := by
  unfold tailWord_986953
  simp only [CollatzResearch.WordTrace]
  refine ⟨35997133193445313997909513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23998088795630209331939675 35997133193445313997909513)
  ·
    refine ⟨26997849895083985498432135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35997133193445313997909513 26997849895083985498432135)
    ·
      refine ⟨40496774842625978247648203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26997849895083985498432135 40496774842625978247648203)
      ·
        refine ⟨60745162263938967371472305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40496774842625978247648203 60745162263938967371472305)
        ·
          refine ⟨45558871697954225528604229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60745162263938967371472305 45558871697954225528604229)
          ·
            refine ⟨8542288443366417286613293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45558871697954225528604229 8542288443366417286613293)
            ·
              refine ⟨3203358166262406482479985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8542288443366417286613293 3203358166262406482479985)
              ·
                refine ⟨2402518624696804861859989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3203358166262406482479985 2402518624696804861859989)
                ·
                  refine ⟨112618060532662727899687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2402518624696804861859989 112618060532662727899687)
                  ·
                    rfl

theorem cell22_986953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 6].length) (baseStart_986953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986953 prefixEnd_986953 := by exact prefixLift 986953
  have htrace : WordTrace (prefixWord ++ tailWord_986953) baseStart_986953 baseEnd_986953 := by
    simpa [prefixWord, tailWord_986953, baseEnd_986953] using wordTrace_append hprefix tailTrace_986953
  have hstable : (prefixWord ++ tailWord_986953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986953).length < 2 ^ (prefixWord ++ tailWord_986953).sum := by decide
  have hdescent : baseEnd_986953 < baseStart_986953 := by decide
  rcases family_descends (prefixWord ++ tailWord_986953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987013 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 2, 7]
def baseStart_987013 : Nat := 118140960795 + 987013 * 2 ^ 59
def prefixEnd_987013 : Nat := 4983230072969 + 3 ^ 40 * 987013 * 2
def baseEnd_987013 : Nat := 337874720824168027198877

theorem tailTrace_987013 : CollatzResearch.WordTrace tailWord_987013 prefixEnd_987013 337874720824168027198877 := by
  unfold tailWord_987013
  simp only [CollatzResearch.WordTrace]
  refine ⟨35999321573227944245093693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23999547715485296163395795 35999321573227944245093693)
  ·
    refine ⟨13499745589960479091910135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35999321573227944245093693 13499745589960479091910135)
    ·
      refine ⟨20249618384940718637865203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13499745589960479091910135 20249618384940718637865203)
      ·
        refine ⟨30374427577411077956797805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20249618384940718637865203 30374427577411077956797805)
        ·
          refine ⟨11390410341529154233799177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30374427577411077956797805 11390410341529154233799177)
          ·
            refine ⟨8542807756146865675349383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11390410341529154233799177 8542807756146865675349383)
            ·
              refine ⟨12814211634220298513024075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8542807756146865675349383 12814211634220298513024075)
              ·
                refine ⟨19221317451330447769536113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12814211634220298513024075 19221317451330447769536113)
                ·
                  refine ⟨14415988088497835827152085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19221317451330447769536113 14415988088497835827152085)
                  ·
                    refine ⟨337874720824168027198877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14415988088497835827152085 337874720824168027198877)
                    ·
                      rfl

theorem cell22_987013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_987013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987013 prefixEnd_987013 := by exact prefixLift 987013
  have htrace : WordTrace (prefixWord ++ tailWord_987013) baseStart_987013 baseEnd_987013 := by
    simpa [prefixWord, tailWord_987013, baseEnd_987013] using wordTrace_append hprefix tailTrace_987013
  have hstable : (prefixWord ++ tailWord_987013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987013).length < 2 ^ (prefixWord ++ tailWord_987013).sum := by decide
  have hdescent : baseEnd_987013 < baseStart_987013 := by decide
  rcases family_descends (prefixWord ++ tailWord_987013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987015 : List Nat := [1, 1, 4, 2, 4, 1, 1, 8]
def baseStart_987015 : Nat := 118140960795 + 987015 * 2 ^ 59
def prefixEnd_987015 : Nat := 4983230072969 + 3 ^ 40 * 987015 * 2
def baseEnd_987015 : Nat := 37541711718337854294319

theorem tailTrace_987015 : CollatzResearch.WordTrace tailWord_987015 prefixEnd_987015 37541711718337854294319 := by
  unfold tailWord_987015
  simp only [CollatzResearch.WordTrace]
  refine ⟨35999394519220698586666499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23999596346147132391110999 35999394519220698586666499)
  ·
    refine ⟨53999091778831047879999749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35999394519220698586666499 53999091778831047879999749)
    ·
      refine ⟨10124829708530821477499953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53999091778831047879999749 10124829708530821477499953)
      ·
        refine ⟨7593622281398116108124965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10124829708530821477499953 7593622281398116108124965)
        ·
          refine ⟨1423804177762146770273431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7593622281398116108124965 1423804177762146770273431)
          ·
            refine ⟨2135706266643220155410147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423804177762146770273431 2135706266643220155410147)
            ·
              refine ⟨3203559399964830233115221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135706266643220155410147 3203559399964830233115221)
              ·
                refine ⟨37541711718337854294319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3203559399964830233115221 37541711718337854294319)
                ·
                  rfl

theorem cell22_987015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 8].length) (baseStart_987015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987015 prefixEnd_987015 := by exact prefixLift 987015
  have htrace : WordTrace (prefixWord ++ tailWord_987015) baseStart_987015 baseEnd_987015 := by
    simpa [prefixWord, tailWord_987015, baseEnd_987015] using wordTrace_append hprefix tailTrace_987015
  have hstable : (prefixWord ++ tailWord_987015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987015).length < 2 ^ (prefixWord ++ tailWord_987015).sum := by decide
  have hdescent : baseEnd_987015 < baseStart_987015 := by decide
  rcases family_descends (prefixWord ++ tailWord_987015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987032 : List Nat := [2, 1, 2, 6, 1, 2, 8]
def baseStart_987032 : Nat := 118140960795 + 987032 * 2 ^ 59
def prefixEnd_987032 : Nat := 4983230072969 + 3 ^ 40 * 987032 * 2
def baseEnd_987032 : Nat := 12514119441202159665697

theorem tailTrace_987032 : CollatzResearch.WordTrace tailWord_987032 prefixEnd_987032 12514119441202159665697 := by
  unfold tailWord_987032
  simp only [CollatzResearch.WordTrace]
  refine ⟨18000007280079555245017675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24000009706772740326690233 18000007280079555245017675)
  ·
    refine ⟨27000010920119332867526513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18000007280079555245017675 27000010920119332867526513)
    ·
      refine ⟨20250008190089499650644885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27000010920119332867526513 20250008190089499650644885)
      ·
        refine ⟨949219133910445296123979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20250008190089499650644885 949219133910445296123979)
        ·
          refine ⟨1423828700865667944185969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949219133910445296123979 1423828700865667944185969)
          ·
            refine ⟨1067871525649250958139477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1423828700865667944185969 1067871525649250958139477)
            ·
              refine ⟨12514119441202159665697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1067871525649250958139477 12514119441202159665697)
              ·
                rfl

theorem cell22_987032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 8].length) (baseStart_987032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987032 prefixEnd_987032 := by exact prefixLift 987032
  have htrace : WordTrace (prefixWord ++ tailWord_987032) baseStart_987032 baseEnd_987032 := by
    simpa [prefixWord, tailWord_987032, baseEnd_987032] using wordTrace_append hprefix tailTrace_987032
  have hstable : (prefixWord ++ tailWord_987032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987032).length < 2 ^ (prefixWord ++ tailWord_987032).sum := by decide
  have hdescent : baseEnd_987032 < baseStart_987032 := by decide
  rcases family_descends (prefixWord ++ tailWord_987032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987038 : List Nat := [4, 3, 1, 3, 1, 1, 3, 2, 4]
def baseStart_987038 : Nat := 118140960795 + 987038 * 2 ^ 59
def prefixEnd_987038 : Nat := 4983230072969 + 3 ^ 40 * 987038 * 2
def baseEnd_987038 : Nat := 112627759611692098441267

theorem tailTrace_987038 : CollatzResearch.WordTrace tailWord_987038 prefixEnd_987038 112627759611692098441267 := by
  unfold tailWord_987038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4500029174767171689344221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24000155598758249009835845 4500029174767171689344221)
  ·
    refine ⟨1687510940537689383504083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4500029174767171689344221 1687510940537689383504083)
    ·
      refine ⟨2531266410806534075256125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1687510940537689383504083 2531266410806534075256125)
      ·
        refine ⟨949224904052450278221047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2531266410806534075256125 949224904052450278221047)
        ·
          refine ⟨1423837356078675417331571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949224904052450278221047 1423837356078675417331571)
          ·
            refine ⟨2135756034118013125997357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423837356078675417331571 2135756034118013125997357)
            ·
              refine ⟨800908512794254922249009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2135756034118013125997357 800908512794254922249009)
              ·
                refine ⟨600681384595691191686757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 800908512794254922249009 600681384595691191686757)
                ·
                  refine ⟨112627759611692098441267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 600681384595691191686757 112627759611692098441267)
                  ·
                    rfl

theorem cell22_987038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_987038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987038 prefixEnd_987038 := by exact prefixLift 987038
  have htrace : WordTrace (prefixWord ++ tailWord_987038) baseStart_987038 baseEnd_987038 := by
    simpa [prefixWord, tailWord_987038, baseEnd_987038] using wordTrace_append hprefix tailTrace_987038
  have hstable : (prefixWord ++ tailWord_987038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987038).length < 2 ^ (prefixWord ++ tailWord_987038).sum := by decide
  have hdescent : baseEnd_987038 < baseStart_987038 := by decide
  rcases family_descends (prefixWord ++ tailWord_987038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987098 : List Nat := [3, 1, 1, 2, 5, 2, 2, 2, 1, 3]
def baseStart_987098 : Nat := 118140960795 + 987098 * 2 ^ 59
def prefixEnd_987098 : Nat := 4983230072969 + 3 ^ 40 * 987098 * 2
def baseEnd_987098 : Nat := 337903818061256138823617

theorem tailTrace_987098 : CollatzResearch.WordTrace tailWord_987098 prefixEnd_987098 337903818061256138823617 := by
  unfold tailWord_987098
  simp only [CollatzResearch.WordTrace]
  refine ⟨9000605444480000940484487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24001614518613335841291965 9000605444480000940484487)
  ·
    refine ⟨13500908166720001410726731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9000605444480000940484487 13500908166720001410726731)
    ·
      refine ⟨20251362250080002116090097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13500908166720001410726731 20251362250080002116090097)
      ·
        refine ⟨15188521687560001587067573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20251362250080002116090097 15188521687560001587067573)
        ·
          refine ⟨1423923908208750148787585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15188521687560001587067573 1423923908208750148787585)
          ·
            refine ⟨1067942931156562611590689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1423923908208750148787585 1067942931156562611590689)
            ·
              refine ⟨800957198367421958693017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1067942931156562611590689 800957198367421958693017)
              ·
                refine ⟨600717898775566469019763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 800957198367421958693017 600717898775566469019763)
                ·
                  refine ⟨901076848163349703529645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600717898775566469019763 901076848163349703529645)
                  ·
                    refine ⟨337903818061256138823617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 901076848163349703529645 337903818061256138823617)
                    ·
                      rfl

theorem cell22_987098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 1, 3].length) (baseStart_987098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987098 prefixEnd_987098 := by exact prefixLift 987098
  have htrace : WordTrace (prefixWord ++ tailWord_987098) baseStart_987098 baseEnd_987098 := by
    simpa [prefixWord, tailWord_987098, baseEnd_987098] using wordTrace_append hprefix tailTrace_987098
  have hstable : (prefixWord ++ tailWord_987098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987098).length < 2 ^ (prefixWord ++ tailWord_987098).sum := by decide
  have hdescent : baseEnd_987098 < baseStart_987098 := by decide
  rcases family_descends (prefixWord ++ tailWord_987098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987120 : List Nat := [2, 1, 1, 1, 3, 2, 3, 3, 1, 5]
def baseStart_987120 : Nat := 118140960795 + 987120 * 2 ^ 59
def prefixEnd_987120 : Nat := 4983230072969 + 3 ^ 40 * 987120 * 2
def baseEnd_987120 : Nat := 337911349110855414773549

theorem tailTrace_987120 : CollatzResearch.WordTrace tailWord_987120 prefixEnd_987120 337911349110855414773549 := by
  unfold tailWord_987120
  simp only [CollatzResearch.WordTrace]
  refine ⟨18001612091920150759619407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24002149455893534346159209 18001612091920150759619407)
  ·
    refine ⟨27002418137880226139429111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18001612091920150759619407 27002418137880226139429111)
    ·
      refine ⟨40503627206820339209143667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27002418137880226139429111 40503627206820339209143667)
      ·
        refine ⟨60755440810230508813715501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40503627206820339209143667 60755440810230508813715501)
        ·
          refine ⟨22783290303836440805143313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60755440810230508813715501 22783290303836440805143313)
          ·
            refine ⟨17087467727877330603857485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22783290303836440805143313 17087467727877330603857485)
            ·
              refine ⟨6407800397953998976446557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17087467727877330603857485 6407800397953998976446557)
              ·
                refine ⟨2402925149232749616167459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6407800397953998976446557 2402925149232749616167459)
                ·
                  refine ⟨3604387723849124424251189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2402925149232749616167459 3604387723849124424251189)
                  ·
                    refine ⟨337911349110855414773549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3604387723849124424251189 337911349110855414773549)
                    ·
                      rfl

theorem cell22_987120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_987120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987120 prefixEnd_987120 := by exact prefixLift 987120
  have htrace : WordTrace (prefixWord ++ tailWord_987120) baseStart_987120 baseEnd_987120 := by
    simpa [prefixWord, tailWord_987120, baseEnd_987120] using wordTrace_append hprefix tailTrace_987120
  have hstable : (prefixWord ++ tailWord_987120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987120).length < 2 ^ (prefixWord ++ tailWord_987120).sum := by decide
  have hdescent : baseEnd_987120 < baseStart_987120 := by decide
  rcases family_descends (prefixWord ++ tailWord_987120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987137 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 4, 3]
def baseStart_987137 : Nat := 118140960795 + 987137 * 2 ^ 59
def prefixEnd_987137 : Nat := 4983230072969 + 3 ^ 40 * 987137 * 2
def baseEnd_987137 : Nat := 337917168558273037098497

theorem tailTrace_987137 : CollatzResearch.WordTrace tailWord_987137 prefixEnd_987137 337917168558273037098497 := by
  unfold tailWord_987137
  simp only [CollatzResearch.WordTrace]
  refine ⟨36003844224778713422607665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24002562816519142281738443 36003844224778713422607665)
  ·
    refine ⟨27002883168584035066955749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36003844224778713422607665 27002883168584035066955749)
    ·
      refine ⟨5063040594109506575054203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27002883168584035066955749 5063040594109506575054203)
      ·
        refine ⟨7594560891164259862581305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5063040594109506575054203 7594560891164259862581305)
        ·
          refine ⟨5695920668373194896935979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7594560891164259862581305 5695920668373194896935979)
          ·
            refine ⟨8543881002559792345403969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5695920668373194896935979 8543881002559792345403969)
            ·
              refine ⟨6407910751919844259052977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8543881002559792345403969 6407910751919844259052977)
              ·
                refine ⟨4805933063939883194289733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6407910751919844259052977 4805933063939883194289733)
                ·
                  refine ⟨901112449488728098929325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4805933063939883194289733 901112449488728098929325)
                  ·
                    refine ⟨337917168558273037098497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 901112449488728098929325 337917168558273037098497)
                    ·
                      rfl

theorem cell22_987137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_987137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987137 prefixEnd_987137 := by exact prefixLift 987137
  have htrace : WordTrace (prefixWord ++ tailWord_987137) baseStart_987137 baseEnd_987137 := by
    simpa [prefixWord, tailWord_987137, baseEnd_987137] using wordTrace_append hprefix tailTrace_987137
  have hstable : (prefixWord ++ tailWord_987137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987137).length < 2 ^ (prefixWord ++ tailWord_987137).sum := by decide
  have hdescent : baseEnd_987137 < baseStart_987137 := by decide
  rcases family_descends (prefixWord ++ tailWord_987137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987150 : List Nat := [4, 1, 1, 2, 2, 1, 11]
def baseStart_987150 : Nat := 118140960795 + 987150 * 2 ^ 59
def prefixEnd_987150 : Nat := 4983230072969 + 3 ^ 40 * 987150 * 2
def baseEnd_987150 : Nat := 12515615508294271723091

theorem tailTrace_987150 : CollatzResearch.WordTrace tailWord_987150 prefixEnd_987150 12515615508294271723091 := by
  unfold tailWord_987150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4500539796716452080353863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24002878915821077761887269 4500539796716452080353863)
  ·
    refine ⟨6750809695074678120530795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4500539796716452080353863 6750809695074678120530795)
    ·
      refine ⟨10126214542612017180796193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6750809695074678120530795 10126214542612017180796193)
      ·
        refine ⟨7594660906959012885597145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10126214542612017180796193 7594660906959012885597145)
        ·
          refine ⟨5695995680219259664197859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7594660906959012885597145 5695995680219259664197859)
          ·
            refine ⟨8543993520328889496296789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5695995680219259664197859 8543993520328889496296789)
            ·
              refine ⟨12515615508294271723091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8543993520328889496296789 12515615508294271723091)
              ·
                rfl

theorem cell22_987150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 11].length) (baseStart_987150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987150 prefixEnd_987150 := by exact prefixLift 987150
  have htrace : WordTrace (prefixWord ++ tailWord_987150) baseStart_987150 baseEnd_987150 := by
    simpa [prefixWord, tailWord_987150, baseEnd_987150] using wordTrace_append hprefix tailTrace_987150
  have hstable : (prefixWord ++ tailWord_987150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987150).length < 2 ^ (prefixWord ++ tailWord_987150).sum := by decide
  have hdescent : baseEnd_987150 < baseStart_987150 := by decide
  rcases family_descends (prefixWord ++ tailWord_987150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987156 : List Nat := [2, 4, 3, 2, 1, 1, 2, 1, 6]
def baseStart_987156 : Nat := 118140960795 + 987156 * 2 ^ 59
def prefixEnd_987156 : Nat := 4983230072969 + 3 ^ 40 * 987156 * 2
def baseEnd_987156 : Nat := 112641224215521106957813

theorem tailTrace_987156 : CollatzResearch.WordTrace tailWord_987156 prefixEnd_987156 112641224215521106957813 := by
  unfold tailWord_987156
  simp only [CollatzResearch.WordTrace]
  refine ⟨18002268605854939833774661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24003024807806586445032881 18002268605854939833774661)
  ·
    refine ⟨3375425363597801218832749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18002268605854939833774661 3375425363597801218832749)
    ·
      refine ⟨1265784511349175457062281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3375425363597801218832749 1265784511349175457062281)
      ·
        refine ⟨949338383511881592796711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1265784511349175457062281 949338383511881592796711)
        ·
          refine ⟨1424007575267822389195067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949338383511881592796711 1424007575267822389195067)
          ·
            refine ⟨2136011362901733583792601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424007575267822389195067 2136011362901733583792601)
            ·
              refine ⟨1602008522176300187844451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2136011362901733583792601 1602008522176300187844451)
              ·
                refine ⟨2403012783264450281766677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1602008522176300187844451 2403012783264450281766677)
                ·
                  refine ⟨112641224215521106957813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2403012783264450281766677 112641224215521106957813)
                  ·
                    rfl

theorem cell22_987156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_987156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987156 prefixEnd_987156 := by exact prefixLift 987156
  have htrace : WordTrace (prefixWord ++ tailWord_987156) baseStart_987156 baseEnd_987156 := by
    simpa [prefixWord, tailWord_987156, baseEnd_987156] using wordTrace_append hprefix tailTrace_987156
  have hstable : (prefixWord ++ tailWord_987156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987156).length < 2 ^ (prefixWord ++ tailWord_987156).sum := by decide
  have hdescent : baseEnd_987156 < baseStart_987156 := by decide
  rcases family_descends (prefixWord ++ tailWord_987156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987340 : List Nat := [2, 2, 1, 6, 1, 1, 3, 1, 2, 3]
def baseStart_987340 : Nat := 118140960795 + 987340 * 2 ^ 59
def prefixEnd_987340 : Nat := 4983230072969 + 3 ^ 40 * 987340 * 2
def baseEnd_987340 : Nat := 337986659606848174272875

theorem tailTrace_987340 : CollatzResearch.WordTrace tailWord_987340 prefixEnd_987340 337986659606848174272875 := by
  unfold tailWord_987340
  simp only [CollatzResearch.WordTrace]
  refine ⟨18005624121521639546123737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24007498828695519394831649 18005624121521639546123737)
  ·
    refine ⟨13504218091141229659592803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18005624121521639546123737 13504218091141229659592803)
    ·
      refine ⟨20256327136711844489389205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13504218091141229659592803 20256327136711844489389205)
      ·
        refine ⟨949515334533367710440119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20256327136711844489389205 949515334533367710440119)
        ·
          refine ⟨1424273001800051565660179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949515334533367710440119 1424273001800051565660179)
          ·
            refine ⟨2136409502700077348490269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424273001800051565660179 2136409502700077348490269)
            ·
              refine ⟨801153563512529005683851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2136409502700077348490269 801153563512529005683851)
              ·
                refine ⟨1201730345268793508525777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801153563512529005683851 1201730345268793508525777)
                ·
                  refine ⟨901297758951595131394333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1201730345268793508525777 901297758951595131394333)
                  ·
                    refine ⟨337986659606848174272875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 901297758951595131394333 337986659606848174272875)
                    ·
                      rfl

theorem cell22_987340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 2, 3].length) (baseStart_987340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987340 prefixEnd_987340 := by exact prefixLift 987340
  have htrace : WordTrace (prefixWord ++ tailWord_987340) baseStart_987340 baseEnd_987340 := by
    simpa [prefixWord, tailWord_987340, baseEnd_987340] using wordTrace_append hprefix tailTrace_987340
  have hstable : (prefixWord ++ tailWord_987340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987340).length < 2 ^ (prefixWord ++ tailWord_987340).sum := by decide
  have hdescent : baseEnd_987340 < baseStart_987340 := by decide
  rcases family_descends (prefixWord ++ tailWord_987340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987368 : List Nat := [2, 1, 4, 1, 2, 2, 3, 3, 1, 3]
def baseStart_987368 : Nat := 118140960795 + 987368 * 2 ^ 59
def prefixEnd_987368 : Nat := 4983230072969 + 3 ^ 40 * 987368 * 2
def baseEnd_987368 : Nat := 337996244579065434572789

theorem tailTrace_987368 : CollatzResearch.WordTrace tailWord_987368 prefixEnd_987368 337996244579065434572789 := by
  unfold tailWord_987368
  simp only [CollatzResearch.WordTrace]
  refine ⟨18006134743470919937133379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24008179657961226582844505 18006134743470919937133379)
  ·
    refine ⟨27009202115206379905700069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18006134743470919937133379 27009202115206379905700069)
    ·
      refine ⟨5064225396601196232318763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27009202115206379905700069 5064225396601196232318763)
      ·
        refine ⟨7596338094901794348478145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5064225396601196232318763 7596338094901794348478145)
        ·
          refine ⟨5697253571176345761358609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7596338094901794348478145 5697253571176345761358609)
          ·
            refine ⟨4272940178382259321018957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5697253571176345761358609 4272940178382259321018957)
            ·
              refine ⟨1602352566893347245382109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4272940178382259321018957 1602352566893347245382109)
              ·
                refine ⟨600882212585005217018291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1602352566893347245382109 600882212585005217018291)
                ·
                  refine ⟨901323318877507825527437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600882212585005217018291 901323318877507825527437)
                  ·
                    refine ⟨337996244579065434572789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 901323318877507825527437 337996244579065434572789)
                    ·
                      rfl

theorem cell22_987368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_987368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987368 prefixEnd_987368 := by exact prefixLift 987368
  have htrace : WordTrace (prefixWord ++ tailWord_987368) baseStart_987368 baseEnd_987368 := by
    simpa [prefixWord, tailWord_987368, baseEnd_987368] using wordTrace_append hprefix tailTrace_987368
  have hstable : (prefixWord ++ tailWord_987368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987368).length < 2 ^ (prefixWord ++ tailWord_987368).sum := by decide
  have hdescent : baseEnd_987368 < baseStart_987368 := by decide
  rcases family_descends (prefixWord ++ tailWord_987368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987407 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 5, 5]
def baseStart_987407 : Nat := 118140960795 + 987407 * 2 ^ 59
def prefixEnd_987407 : Nat := 4983230072969 + 3 ^ 40 * 987407 * 2
def baseEnd_987407 : Nat := 338009595076082332847669

theorem tailTrace_987407 : CollatzResearch.WordTrace tailWord_987407 prefixEnd_987407 338009595076082332847669 := by
  unfold tailWord_987407
  simp only [CollatzResearch.WordTrace]
  refine ⟨36013691933800549534936475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24009127955867033023290983 36013691933800549534936475)
  ·
    refine ⟨54020537900700824302404713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36013691933800549534936475 54020537900700824302404713)
    ·
      refine ⟨40515403425525618226803535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54020537900700824302404713 40515403425525618226803535)
      ·
        refine ⟨60773105138288427340205303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40515403425525618226803535 60773105138288427340205303)
        ·
          refine ⟨91159657707432641010307955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60773105138288427340205303 91159657707432641010307955)
          ·
            refine ⟨136739486561148961515461933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91159657707432641010307955 136739486561148961515461933)
            ·
              refine ⟨51277307460430860568298225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136739486561148961515461933 51277307460430860568298225)
              ·
                refine ⟨38457980595323145426223669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51277307460430860568298225 38457980595323145426223669)
                ·
                  refine ⟨3605435680811544883708469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38457980595323145426223669 3605435680811544883708469)
                  ·
                    refine ⟨338009595076082332847669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3605435680811544883708469 338009595076082332847669)
                    ·
                      rfl

theorem cell22_987407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_987407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987407 prefixEnd_987407 := by exact prefixLift 987407
  have htrace : WordTrace (prefixWord ++ tailWord_987407) baseStart_987407 baseEnd_987407 := by
    simpa [prefixWord, tailWord_987407, baseEnd_987407] using wordTrace_append hprefix tailTrace_987407
  have hstable : (prefixWord ++ tailWord_987407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987407).length < 2 ^ (prefixWord ++ tailWord_987407).sum := by decide
  have hdescent : baseEnd_987407 < baseStart_987407 := by decide
  rcases family_descends (prefixWord ++ tailWord_987407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987424 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 3, 5]
def baseStart_987424 : Nat := 118140960795 + 987424 * 2 ^ 59
def prefixEnd_987424 : Nat := 4983230072969 + 3 ^ 40 * 987424 * 2
def baseEnd_987424 : Nat := 338015414523499955172617

theorem tailTrace_987424 : CollatzResearch.WordTrace tailWord_987424 prefixEnd_987424 338015414523499955172617 := by
  unfold tailWord_987424
  simp only [CollatzResearch.WordTrace]
  refine ⟨18007155987369480719152663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24009541316492640958870217 18007155987369480719152663)
  ·
    refine ⟨27010733981054221078728995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18007155987369480719152663 27010733981054221078728995)
    ·
      refine ⟨40516100971581331618093493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27010733981054221078728995 40516100971581331618093493)
      ·
        refine ⟨3798384466085749839196265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40516100971581331618093493 3798384466085749839196265)
        ·
          refine ⟨2848788349564312379397199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3798384466085749839196265 2848788349564312379397199)
          ·
            refine ⟨4273182524346468569095799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848788349564312379397199 4273182524346468569095799)
            ·
              refine ⟨6409773786519702853643699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4273182524346468569095799 6409773786519702853643699)
              ·
                refine ⟨9614660679779554280465549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6409773786519702853643699 9614660679779554280465549)
                ·
                  refine ⟨3605497754917332855174581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9614660679779554280465549 3605497754917332855174581)
                  ·
                    refine ⟨338015414523499955172617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3605497754917332855174581 338015414523499955172617)
                    ·
                      rfl

theorem cell22_987424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_987424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987424 prefixEnd_987424 := by exact prefixLift 987424
  have htrace : WordTrace (prefixWord ++ tailWord_987424) baseStart_987424 baseEnd_987424 := by
    simpa [prefixWord, tailWord_987424, baseEnd_987424] using wordTrace_append hprefix tailTrace_987424
  have hstable : (prefixWord ++ tailWord_987424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987424).length < 2 ^ (prefixWord ++ tailWord_987424).sum := by decide
  have hdescent : baseEnd_987424 < baseStart_987424 := by decide
  rcases family_descends (prefixWord ++ tailWord_987424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987428 : List Nat := [2, 3, 1, 3, 1, 3, 3, 1, 1, 4]
def baseStart_987428 : Nat := 118140960795 + 987428 * 2 ^ 59
def prefixEnd_987428 : Nat := 4983230072969 + 3 ^ 40 * 987428 * 2
def baseEnd_987428 : Nat := 338016783805245278072605

theorem tailTrace_987428 : CollatzResearch.WordTrace tailWord_987428 prefixEnd_987428 338016783805245278072605 := by
  unfold tailWord_987428
  simp only [CollatzResearch.WordTrace]
  refine ⟨18007228933362235060725469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24009638577816313414300625 18007228933362235060725469)
  ·
    refine ⟨6752710850010838147772051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18007228933362235060725469 6752710850010838147772051)
    ·
      refine ⟨10129066275016257221658077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6752710850010838147772051 10129066275016257221658077)
      ·
        refine ⟨3798399853131096458121779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10129066275016257221658077 3798399853131096458121779)
        ·
          refine ⟨5697599779696644687182669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3798399853131096458121779 5697599779696644687182669)
          ·
            refine ⟨2136599917386241757693501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5697599779696644687182669 2136599917386241757693501)
            ·
              refine ⟨801224969019840659135063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2136599917386241757693501 801224969019840659135063)
              ·
                refine ⟨1201837453529760988702595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801224969019840659135063 1201837453529760988702595)
                ·
                  refine ⟨1802756180294641483053893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1201837453529760988702595 1802756180294641483053893)
                  ·
                    refine ⟨338016783805245278072605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1802756180294641483053893 338016783805245278072605)
                    ·
                      rfl

theorem cell22_987428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_987428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987428 prefixEnd_987428 := by exact prefixLift 987428
  have htrace : WordTrace (prefixWord ++ tailWord_987428) baseStart_987428 baseEnd_987428 := by
    simpa [prefixWord, tailWord_987428, baseEnd_987428] using wordTrace_append hprefix tailTrace_987428
  have hstable : (prefixWord ++ tailWord_987428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987428).length < 2 ^ (prefixWord ++ tailWord_987428).sum := by decide
  have hdescent : baseEnd_987428 < baseStart_987428 := by decide
  rcases family_descends (prefixWord ++ tailWord_987428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987439 : List Nat := [1, 1, 2, 1, 2, 1, 6, 2, 2, 4]
def baseStart_987439 : Nat := 118140960795 + 987439 * 2 ^ 59
def prefixEnd_987439 : Nat := 4983230072969 + 3 ^ 40 * 987439 * 2
def baseEnd_987439 : Nat := 338020549330044916047571

theorem tailTrace_987439 : CollatzResearch.WordTrace tailWord_987439 prefixEnd_987439 338020549330044916047571 := by
  unfold tailWord_987439
  simp only [CollatzResearch.WordTrace]
  refine ⟨36014859069684619000101371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24009906046456412666734247 36014859069684619000101371)
  ·
    refine ⟨54022288604526928500152057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36014859069684619000101371 54022288604526928500152057)
    ·
      refine ⟨40516716453395196375114043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54022288604526928500152057 40516716453395196375114043)
      ·
        refine ⟨60775074680092794562671065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40516716453395196375114043 60775074680092794562671065)
        ·
          refine ⟨45581306010069595922003299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60775074680092794562671065 45581306010069595922003299)
          ·
            refine ⟨68371959015104393883004949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45581306010069595922003299 68371959015104393883004949)
            ·
              refine ⟨3204935578833018463265857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68371959015104393883004949 3204935578833018463265857)
              ·
                refine ⟨2403701684124763847449393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3204935578833018463265857 2403701684124763847449393)
                ·
                  refine ⟨1802776263093572885587045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2403701684124763847449393 1802776263093572885587045)
                  ·
                    refine ⟨338020549330044916047571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1802776263093572885587045 338020549330044916047571)
                    ·
                      rfl

theorem cell22_987439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_987439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987439 prefixEnd_987439 := by exact prefixLift 987439
  have htrace : WordTrace (prefixWord ++ tailWord_987439) baseStart_987439 baseEnd_987439 := by
    simpa [prefixWord, tailWord_987439, baseEnd_987439] using wordTrace_append hprefix tailTrace_987439
  have hstable : (prefixWord ++ tailWord_987439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987439).length < 2 ^ (prefixWord ++ tailWord_987439).sum := by decide
  have hdescent : baseEnd_987439 < baseStart_987439 := by decide
  rcases family_descends (prefixWord ++ tailWord_987439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987522 : List Nat := [3, 4, 2, 1, 3, 1, 2, 6]
def baseStart_987522 : Nat := 118140960795 + 987522 * 2 ^ 59
def prefixEnd_987522 : Nat := 4983230072969 + 3 ^ 40 * 987522 * 2
def baseEnd_987522 : Nat := 37560995769584485135813

theorem tailTrace_987522 : CollatzResearch.WordTrace tailWord_987522 prefixEnd_987522 37560995769584485135813 := by
  unfold tailWord_987522
  simp only [CollatzResearch.WordTrace]
  refine ⟨9004471582095981043843205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24011924218922616116915213 9004471582095981043843205)
  ·
    refine ⟨1688338421642996445720601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9004471582095981043843205 1688338421642996445720601)
    ·
      refine ⟨1266253816232247334290451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1688338421642996445720601 1266253816232247334290451)
      ·
        refine ⟨1899380724348371001435677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1266253816232247334290451 1899380724348371001435677)
        ·
          refine ⟨712267771630639125538379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1899380724348371001435677 712267771630639125538379)
          ·
            refine ⟨1068401657445958688307569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712267771630639125538379 1068401657445958688307569)
            ·
              refine ⟨801301243084469016230677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1068401657445958688307569 801301243084469016230677)
              ·
                refine ⟨37560995769584485135813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 801301243084469016230677 37560995769584485135813)
                ·
                  rfl

theorem cell22_987522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 6].length) (baseStart_987522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987522 prefixEnd_987522 := by exact prefixLift 987522
  have htrace : WordTrace (prefixWord ++ tailWord_987522) baseStart_987522 baseEnd_987522 := by
    simpa [prefixWord, tailWord_987522, baseEnd_987522] using wordTrace_append hprefix tailTrace_987522
  have hstable : (prefixWord ++ tailWord_987522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987522).length < 2 ^ (prefixWord ++ tailWord_987522).sum := by decide
  have hdescent : baseEnd_987522 < baseStart_987522 := by decide
  rcases family_descends (prefixWord ++ tailWord_987522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987561 : List Nat := [1, 2, 1, 1, 1, 1, 3, 8, 4]
def baseStart_987561 : Nat := 118140960795 + 987561 * 2 ^ 59
def prefixEnd_987561 : Nat := 4983230072969 + 3 ^ 40 * 987561 * 2
def baseEnd_987561 : Nat := 112687437474425754832399

theorem tailTrace_987561 : CollatzResearch.WordTrace tailWord_987561 prefixEnd_987561 112687437474425754832399 := by
  unfold tailWord_987561
  simp only [CollatzResearch.WordTrace]
  refine ⟨36019308775242633836042537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24012872516828422557361691 36019308775242633836042537)
  ·
    refine ⟨27014481581431975377031903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36019308775242633836042537 27014481581431975377031903)
    ·
      refine ⟨40521722372147963065547855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27014481581431975377031903 40521722372147963065547855)
      ·
        refine ⟨60782583558221944598321783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40521722372147963065547855 60782583558221944598321783)
        ·
          refine ⟨91173875337332916897482675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60782583558221944598321783 91173875337332916897482675)
          ·
            refine ⟨136760813005999375346224013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91173875337332916897482675 136760813005999375346224013)
            ·
              refine ⟨51285304877249765754834005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136760813005999375346224013 51285304877249765754834005)
              ·
                refine ⟨600999666530270692439461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 51285304877249765754834005 600999666530270692439461)
                ·
                  refine ⟨112687437474425754832399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 600999666530270692439461 112687437474425754832399)
                  ·
                    rfl

theorem cell22_987561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 4].length) (baseStart_987561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987561 prefixEnd_987561 := by exact prefixLift 987561
  have htrace : WordTrace (prefixWord ++ tailWord_987561) baseStart_987561 baseEnd_987561 := by
    simpa [prefixWord, tailWord_987561, baseEnd_987561] using wordTrace_append hprefix tailTrace_987561
  have hstable : (prefixWord ++ tailWord_987561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987561).length < 2 ^ (prefixWord ++ tailWord_987561).sum := by decide
  have hdescent : baseEnd_987561 < baseStart_987561 := by decide
  rcases family_descends (prefixWord ++ tailWord_987561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987580 : List Nat := [2, 2, 2, 4, 1, 3, 1, 2, 1, 4]
def baseStart_987580 : Nat := 118140960795 + 987580 * 2 ^ 59
def prefixEnd_987580 : Nat := 4983230072969 + 3 ^ 40 * 987580 * 2
def baseEnd_987580 : Nat := 338068816511567548272139

theorem tailTrace_987580 : CollatzResearch.WordTrace tailWord_987580 prefixEnd_987580 338068816511567548272139 := by
  unfold tailWord_987580
  simp only [CollatzResearch.WordTrace]
  refine ⟨18010000881086900040492097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24013334508115866720656129 18010000881086900040492097)
  ·
    refine ⟨13507500660815175030369073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18010000881086900040492097 13507500660815175030369073)
    ·
      refine ⟨10130625495611381272776805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13507500660815175030369073 10130625495611381272776805)
      ·
        refine ⟨1899492280427133988645651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10130625495611381272776805 1899492280427133988645651)
        ·
          refine ⟨2849238420640700982968477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1899492280427133988645651 2849238420640700982968477)
          ·
            refine ⟨1068464407740262868613179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2849238420640700982968477 1068464407740262868613179)
            ·
              refine ⟨1602696611610394302919769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068464407740262868613179 1602696611610394302919769)
              ·
                refine ⟨1202022458707795727189827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1602696611610394302919769 1202022458707795727189827)
                ·
                  refine ⟨1803033688061693590784741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1202022458707795727189827 1803033688061693590784741)
                  ·
                    refine ⟨338068816511567548272139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1803033688061693590784741 338068816511567548272139)
                    ·
                      rfl

theorem cell22_987580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_987580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987580 prefixEnd_987580 := by exact prefixLift 987580
  have htrace : WordTrace (prefixWord ++ tailWord_987580) baseStart_987580 baseEnd_987580 := by
    simpa [prefixWord, tailWord_987580, baseEnd_987580] using wordTrace_append hprefix tailTrace_987580
  have hstable : (prefixWord ++ tailWord_987580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987580).length < 2 ^ (prefixWord ++ tailWord_987580).sum := by decide
  have hdescent : baseEnd_987580 < baseStart_987580 := by decide
  rcases family_descends (prefixWord ++ tailWord_987580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987591 : List Nat := [1, 1, 4, 1, 1, 4, 1, 3, 2, 4]
def baseStart_987591 : Nat := 118140960795 + 987591 * 2 ^ 59
def prefixEnd_987591 : Nat := 4983230072969 + 3 ^ 40 * 987591 * 2
def baseEnd_987591 : Nat := 338072582036367186247105

theorem tailTrace_987591 : CollatzResearch.WordTrace tailWord_987591 prefixEnd_987591 338072582036367186247105 := by
  unfold tailWord_987591
  simp only [CollatzResearch.WordTrace]
  refine ⟨36020402965133948959634627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24013601976755965973089751 36020402965133948959634627)
  ·
    refine ⟨54030604447700923439451941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36020402965133948959634627 54030604447700923439451941)
    ·
      refine ⟨10130738333943923144897239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54030604447700923439451941 10130738333943923144897239)
      ·
        refine ⟨15196107500915884717345859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10130738333943923144897239 15196107500915884717345859)
        ·
          refine ⟨22794161251373827076018789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15196107500915884717345859 22794161251373827076018789)
          ·
            refine ⟨4273905234632592576753523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22794161251373827076018789 4273905234632592576753523)
            ·
              refine ⟨6410857851948888865130285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4273905234632592576753523 6410857851948888865130285)
              ·
                refine ⟨2404071694480833324423857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6410857851948888865130285 2404071694480833324423857)
                ·
                  refine ⟨1803053770860624993317893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2404071694480833324423857 1803053770860624993317893)
                  ·
                    refine ⟨338072582036367186247105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1803053770860624993317893 338072582036367186247105)
                    ·
                      rfl

theorem cell22_987591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_987591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987591 prefixEnd_987591 := by exact prefixLift 987591
  have htrace : WordTrace (prefixWord ++ tailWord_987591) baseStart_987591 baseEnd_987591 := by
    simpa [prefixWord, tailWord_987591, baseEnd_987591] using wordTrace_append hprefix tailTrace_987591
  have hstable : (prefixWord ++ tailWord_987591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987591).length < 2 ^ (prefixWord ++ tailWord_987591).sum := by decide
  have hdescent : baseEnd_987591 < baseStart_987591 := by decide
  rcases family_descends (prefixWord ++ tailWord_987591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987696 : List Nat := [2, 1, 1, 1, 2, 3, 4, 2, 6]
def baseStart_987696 : Nat := 118140960795 + 987696 * 2 ^ 59
def prefixEnd_987696 : Nat := 4983230072969 + 3 ^ 40 * 987696 * 2
def baseEnd_987696 : Nat := 112702841894060637457261

theorem tailTrace_987696 : CollatzResearch.WordTrace tailWord_987696 prefixEnd_987696 112702841894060637457261 := by
  unfold tailWord_987696
  simp only [CollatzResearch.WordTrace]
  refine ⟨18012116314876775946103471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24016155086502367928137961 18012116314876775946103471)
  ·
    refine ⟨27018174472315163919155207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18012116314876775946103471 27018174472315163919155207)
    ·
      refine ⟨40527261708472745878732811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27018174472315163919155207 40527261708472745878732811)
      ·
        refine ⟨60790892562709118818099217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40527261708472745878732811 60790892562709118818099217)
        ·
          refine ⟨45593169422031839113574413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60790892562709118818099217 45593169422031839113574413)
          ·
            refine ⟨17097438533261939667590405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45593169422031839113574413 17097438533261939667590405)
            ·
              refine ⟨3205769724986613687673201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17097438533261939667590405 3205769724986613687673201)
              ·
                refine ⟨2404327293739960265754901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3205769724986613687673201 2404327293739960265754901)
                ·
                  refine ⟨112702841894060637457261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2404327293739960265754901 112702841894060637457261)
                  ·
                    rfl

theorem cell22_987696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 6].length) (baseStart_987696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987696 prefixEnd_987696 := by exact prefixLift 987696
  have htrace : WordTrace (prefixWord ++ tailWord_987696) baseStart_987696 baseEnd_987696 := by
    simpa [prefixWord, tailWord_987696, baseEnd_987696] using wordTrace_append hprefix tailTrace_987696
  have hstable : (prefixWord ++ tailWord_987696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987696).length < 2 ^ (prefixWord ++ tailWord_987696).sum := by decide
  have hdescent : baseEnd_987696 < baseStart_987696 := by decide
  rcases family_descends (prefixWord ++ tailWord_987696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987698 : List Nat := [3, 2, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_987698 : Nat := 118140960795 + 987698 * 2 ^ 59
def prefixEnd_987698 : Nat := 4983230072969 + 3 ^ 40 * 987698 * 2
def baseEnd_987698 : Nat := 338109210323054573821777

theorem tailTrace_987698 : CollatzResearch.WordTrace tailWord_987698 prefixEnd_987698 338109210323054573821777 := by
  unfold tailWord_987698
  simp only [CollatzResearch.WordTrace]
  refine ⟨9006076393936576558444937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24016203717164204155853165 9006076393936576558444937)
  ·
    refine ⟨6754557295452432418833703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9006076393936576558444937 6754557295452432418833703)
    ·
      refine ⟨10131835943178648628250555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6754557295452432418833703 10131835943178648628250555)
      ·
        refine ⟨15197753914767972942375833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10131835943178648628250555 15197753914767972942375833)
        ·
          refine ⟨11398315436075979706781875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15197753914767972942375833 11398315436075979706781875)
          ·
            refine ⟨17097473154113969560172813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11398315436075979706781875 17097473154113969560172813)
            ·
              refine ⟨6411552432792738585064805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17097473154113969560172813 6411552432792738585064805)
              ·
                refine ⟨1202166081148638484699651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6411552432792738585064805 1202166081148638484699651)
                ·
                  refine ⟨1803249121722957727049477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1202166081148638484699651 1803249121722957727049477)
                  ·
                    refine ⟨338109210323054573821777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1803249121722957727049477 338109210323054573821777)
                    ·
                      rfl

theorem cell22_987698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_987698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987698 prefixEnd_987698 := by exact prefixLift 987698
  have htrace : WordTrace (prefixWord ++ tailWord_987698) baseStart_987698 baseEnd_987698 := by
    simpa [prefixWord, tailWord_987698, baseEnd_987698] using wordTrace_append hprefix tailTrace_987698
  have hstable : (prefixWord ++ tailWord_987698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987698).length < 2 ^ (prefixWord ++ tailWord_987698).sum := by decide
  have hdescent : baseEnd_987698 < baseStart_987698 := by decide
  rcases family_descends (prefixWord ++ tailWord_987698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987711 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 3, 5]
def baseStart_987711 : Nat := 118140960795 + 987711 * 2 ^ 59
def prefixEnd_987711 : Nat := 4983230072969 + 3 ^ 40 * 987711 * 2
def baseEnd_987711 : Nat := 338113660488726873246737

theorem tailTrace_987711 : CollatzResearch.WordTrace tailWord_987711 prefixEnd_987711 338113660488726873246737 := by
  unfold tailWord_987711
  simp only [CollatzResearch.WordTrace]
  refine ⟨36024779724699209454002987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24016519816466139636001991 36024779724699209454002987)
  ·
    refine ⟨54037169587048814181004481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36024779724699209454002987 54037169587048814181004481)
    ·
      refine ⟨40527877190286610635753361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54037169587048814181004481 40527877190286610635753361)
      ·
        refine ⟨30395907892714957976815021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40527877190286610635753361 30395907892714957976815021)
        ·
          refine ⟨11398465459768109241305633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30395907892714957976815021 11398465459768109241305633)
          ·
            refine ⟨8548849094826081930979225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11398465459768109241305633 8548849094826081930979225)
            ·
              refine ⟨6411636821119561448234419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8548849094826081930979225 6411636821119561448234419)
              ·
                refine ⟨9617455231679342172351629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6411636821119561448234419 9617455231679342172351629)
                ·
                  refine ⟨3606545711879753314631861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9617455231679342172351629 3606545711879753314631861)
                  ·
                    refine ⟨338113660488726873246737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3606545711879753314631861 338113660488726873246737)
                    ·
                      rfl

theorem cell22_987711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_987711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987711 prefixEnd_987711 := by exact prefixLift 987711
  have htrace : WordTrace (prefixWord ++ tailWord_987711) baseStart_987711 baseEnd_987711 := by
    simpa [prefixWord, tailWord_987711, baseEnd_987711] using wordTrace_append hprefix tailTrace_987711
  have hstable : (prefixWord ++ tailWord_987711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987711).length < 2 ^ (prefixWord ++ tailWord_987711).sum := by decide
  have hdescent : baseEnd_987711 < baseStart_987711 := by decide
  rcases family_descends (prefixWord ++ tailWord_987711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987745 : List Nat := [1, 2, 3, 1, 1, 5, 1, 3, 2, 3]
def baseStart_987745 : Nat := 118140960795 + 987745 * 2 ^ 59
def prefixEnd_987745 : Nat := 4983230072969 + 3 ^ 40 * 987745 * 2
def baseEnd_987745 : Nat := 338125299383562117896633

theorem tailTrace_987745 : CollatzResearch.WordTrace tailWord_987745 prefixEnd_987745 338125299383562117896633 := by
  unfold tailWord_987745
  simp only [CollatzResearch.WordTrace]
  refine ⟨36026019806576033260740689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24017346537717355507160459 36026019806576033260740689)
  ·
    refine ⟨27019514854932024945555517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36026019806576033260740689 27019514854932024945555517)
    ·
      refine ⟨10132318070599509354583319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27019514854932024945555517 10132318070599509354583319)
      ·
        refine ⟨15198477105899264031874979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10132318070599509354583319 15198477105899264031874979)
        ·
          refine ⟨22797715658848896047812469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15198477105899264031874979 22797715658848896047812469)
          ·
            refine ⟨2137285843017084004482419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22797715658848896047812469 2137285843017084004482419)
            ·
              refine ⟨3205928764525626006723629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2137285843017084004482419 3205928764525626006723629)
              ·
                refine ⟨1202223286697109752521361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3205928764525626006723629 1202223286697109752521361)
                ·
                  refine ⟨901667465022832314391021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1202223286697109752521361 901667465022832314391021)
                  ·
                    refine ⟨338125299383562117896633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 901667465022832314391021 338125299383562117896633)
                    ·
                      rfl

theorem cell22_987745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_987745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987745 prefixEnd_987745 := by exact prefixLift 987745
  have htrace : WordTrace (prefixWord ++ tailWord_987745) baseStart_987745 baseEnd_987745 := by
    simpa [prefixWord, tailWord_987745, baseEnd_987745] using wordTrace_append hprefix tailTrace_987745
  have hstable : (prefixWord ++ tailWord_987745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987745).length < 2 ^ (prefixWord ++ tailWord_987745).sum := by decide
  have hdescent : baseEnd_987745 < baseStart_987745 := by decide
  rcases family_descends (prefixWord ++ tailWord_987745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987756 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 2, 7]
def baseStart_987756 : Nat := 118140960795 + 987756 * 2 ^ 59
def prefixEnd_987756 : Nat := 4983230072969 + 3 ^ 40 * 987756 * 2
def baseEnd_987756 : Nat := 338129064908361755871599

theorem tailTrace_987756 : CollatzResearch.WordTrace tailWord_987756 prefixEnd_987756 338129064908361755871599 := by
  unfold tailWord_987756
  simp only [CollatzResearch.WordTrace]
  refine ⟨18013210504768091069695561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24017614006357454759594081 18013210504768091069695561)
  ·
    refine ⟨13509907878576068302271671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18013210504768091069695561 13509907878576068302271671)
    ·
      refine ⟨20264861817864102453407507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13509907878576068302271671 20264861817864102453407507)
      ·
        refine ⟨30397292726796153680111261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20264861817864102453407507 30397292726796153680111261)
        ·
          refine ⟨11398984772548557630041723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30397292726796153680111261 11398984772548557630041723)
          ·
            refine ⟨17098477158822836445062585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11398984772548557630041723 17098477158822836445062585)
            ·
              refine ⟨12823857869117127333796939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17098477158822836445062585 12823857869117127333796939)
              ·
                refine ⟨19235786803675691000695409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12823857869117127333796939 19235786803675691000695409)
                ·
                  refine ⟨14426840102756768250521557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19235786803675691000695409 14426840102756768250521557)
                  ·
                    refine ⟨338129064908361755871599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14426840102756768250521557 338129064908361755871599)
                    ·
                      rfl

theorem cell22_987756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_987756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987756 prefixEnd_987756 := by exact prefixLift 987756
  have htrace : WordTrace (prefixWord ++ tailWord_987756) baseStart_987756 baseEnd_987756 := by
    simpa [prefixWord, tailWord_987756, baseEnd_987756] using wordTrace_append hprefix tailTrace_987756
  have hstable : (prefixWord ++ tailWord_987756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987756).length < 2 ^ (prefixWord ++ tailWord_987756).sum := by decide
  have hdescent : baseEnd_987756 < baseStart_987756 := by decide
  rcases family_descends (prefixWord ++ tailWord_987756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987758 : List Nat := [4, 1, 2, 2, 2, 1, 2, 8]
def baseStart_987758 : Nat := 118140960795 + 987758 * 2 ^ 59
def prefixEnd_987758 : Nat := 4983230072969 + 3 ^ 40 * 987758 * 2
def baseEnd_987758 : Nat := 37569972172137157480177

theorem tailTrace_987758 : CollatzResearch.WordTrace tailWord_987758 prefixEnd_987758 37569972172137157480177 := by
  unfold tailWord_987758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4503311744441117060120491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24017662637019290987309285 4503311744441117060120491)
  ·
    refine ⟨6754967616661675590180737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4503311744441117060120491 6754967616661675590180737)
    ·
      refine ⟨5066225712496256692635553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6754967616661675590180737 5066225712496256692635553)
      ·
        refine ⟨3799669284372192519476665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5066225712496256692635553 3799669284372192519476665)
        ·
          refine ⟨2849751963279144389607499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3799669284372192519476665 2849751963279144389607499)
          ·
            refine ⟨4274627944918716584411249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2849751963279144389607499 4274627944918716584411249)
            ·
              refine ⟨3205970958689037438308437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4274627944918716584411249 3205970958689037438308437)
              ·
                refine ⟨37569972172137157480177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3205970958689037438308437 37569972172137157480177)
                ·
                  rfl

theorem cell22_987758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_987758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987758 prefixEnd_987758 := by exact prefixLift 987758
  have htrace : WordTrace (prefixWord ++ tailWord_987758) baseStart_987758 baseEnd_987758 := by
    simpa [prefixWord, tailWord_987758, baseEnd_987758] using wordTrace_append hprefix tailTrace_987758
  have hstable : (prefixWord ++ tailWord_987758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987758).length < 2 ^ (prefixWord ++ tailWord_987758).sum := by decide
  have hdescent : baseEnd_987758 < baseStart_987758 := by decide
  rcases family_descends (prefixWord ++ tailWord_987758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987760 : List Nat := [2, 1, 1, 1, 7, 1, 2, 1, 2, 4]
def baseStart_987760 : Nat := 118140960795 + 987760 * 2 ^ 59
def prefixEnd_987760 : Nat := 4983230072969 + 3 ^ 40 * 987760 * 2
def baseEnd_987760 : Nat := 338130434190107078771587

theorem tailTrace_987760 : CollatzResearch.WordTrace tailWord_987760 prefixEnd_987760 338130434190107078771587 := by
  unfold tailWord_987760
  simp only [CollatzResearch.WordTrace]
  refine ⟨18013283450760845411268367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24017711267681127215024489 18013283450760845411268367)
  ·
    refine ⟨27019925176141268116902551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18013283450760845411268367 27019925176141268116902551)
    ·
      refine ⟨40529887764211902175353827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27019925176141268116902551 40529887764211902175353827)
      ·
        refine ⟨60794831646317853263030741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40529887764211902175353827 60794831646317853263030741)
        ·
          refine ⟨1424878866710574685852283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 60794831646317853263030741 1424878866710574685852283)
          ·
            refine ⟨2137318300065862028778425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424878866710574685852283 2137318300065862028778425)
            ·
              refine ⟨1602988725049396521583819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2137318300065862028778425 1602988725049396521583819)
              ·
                refine ⟨2404483087574094782375729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1602988725049396521583819 2404483087574094782375729)
                ·
                  refine ⟨1803362315680571086781797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2404483087574094782375729 1803362315680571086781797)
                  ·
                    refine ⟨338130434190107078771587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1803362315680571086781797 338130434190107078771587)
                    ·
                      rfl

theorem cell22_987760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 2, 4].length) (baseStart_987760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987760 prefixEnd_987760 := by exact prefixLift 987760
  have htrace : WordTrace (prefixWord ++ tailWord_987760) baseStart_987760 baseEnd_987760 := by
    simpa [prefixWord, tailWord_987760, baseEnd_987760] using wordTrace_append hprefix tailTrace_987760
  have hstable : (prefixWord ++ tailWord_987760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987760).length < 2 ^ (prefixWord ++ tailWord_987760).sum := by decide
  have hdescent : baseEnd_987760 < baseStart_987760 := by decide
  rcases family_descends (prefixWord ++ tailWord_987760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987790 : List Nat := [4, 1, 1, 3, 1, 1, 2, 3, 3, 3]
def baseStart_987790 : Nat := 118140960795 + 987790 * 2 ^ 59
def prefixEnd_987790 : Nat := 4983230072969 + 3 ^ 40 * 987790 * 2
def baseEnd_987790 : Nat := 338140703803197000521495

theorem tailTrace_987790 : CollatzResearch.WordTrace tailWord_987790 prefixEnd_987790 338140703803197000521495 := by
  unfold tailWord_987790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4503457636426625743266103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24018440727608670630752549 4503457636426625743266103)
  ·
    refine ⟨6755186454639938614899155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4503457636426625743266103 6755186454639938614899155)
    ·
      refine ⟨10132779681959907922348733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6755186454639938614899155 10132779681959907922348733)
      ·
        refine ⟨3799792380734965470880775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10132779681959907922348733 3799792380734965470880775)
        ·
          refine ⟨5699688571102448206321163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3799792380734965470880775 5699688571102448206321163)
          ·
            refine ⟨8549532856653672309481745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5699688571102448206321163 8549532856653672309481745)
            ·
              refine ⟨6412149642490254232111309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8549532856653672309481745 6412149642490254232111309)
              ·
                refine ⟨2404556115933845337041741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6412149642490254232111309 2404556115933845337041741)
                ·
                  refine ⟨901708543475192001390653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2404556115933845337041741 901708543475192001390653)
                  ·
                    refine ⟨338140703803197000521495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 901708543475192001390653 338140703803197000521495)
                    ·
                      rfl

theorem cell22_987790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_987790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987790 prefixEnd_987790 := by exact prefixLift 987790
  have htrace : WordTrace (prefixWord ++ tailWord_987790) baseStart_987790 baseEnd_987790 := by
    simpa [prefixWord, tailWord_987790, baseEnd_987790] using wordTrace_append hprefix tailTrace_987790
  have hstable : (prefixWord ++ tailWord_987790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987790).length < 2 ^ (prefixWord ++ tailWord_987790).sum := by decide
  have hdescent : baseEnd_987790 < baseStart_987790 := by decide
  rcases family_descends (prefixWord ++ tailWord_987790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987848 : List Nat := [2, 1, 3, 1, 2, 3, 1, 3, 6]
def baseStart_987848 : Nat := 118140960795 + 987848 * 2 ^ 59
def prefixEnd_987848 : Nat := 4983230072969 + 3 ^ 40 * 987848 * 2
def baseEnd_987848 : Nat := 112720186129501394190439

theorem tailTrace_987848 : CollatzResearch.WordTrace tailWord_987848 prefixEnd_987848 112720186129501394190439 := by
  unfold tailWord_987848
  simp only [CollatzResearch.WordTrace]
  refine ⟨18014888262601440925870099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24019851016801921234493465 18014888262601440925870099)
  ·
    refine ⟨27022332393902161388805149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18014888262601440925870099 27022332393902161388805149)
    ·
      refine ⟨10133374647713310520801931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27022332393902161388805149 10133374647713310520801931)
      ·
        refine ⟨15200061971569965781202897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10133374647713310520801931 15200061971569965781202897)
        ·
          refine ⟨11400046478677474335902173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15200061971569965781202897 11400046478677474335902173)
          ·
            refine ⟨4275017429504052875963315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11400046478677474335902173 4275017429504052875963315)
            ·
              refine ⟨6412526144256079313944973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4275017429504052875963315 6412526144256079313944973)
              ·
                refine ⟨2404697304096029742729365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6412526144256079313944973 2404697304096029742729365)
                ·
                  refine ⟨112720186129501394190439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2404697304096029742729365 112720186129501394190439)
                  ·
                    rfl

theorem cell22_987848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 6].length) (baseStart_987848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987848 prefixEnd_987848 := by exact prefixLift 987848
  have htrace : WordTrace (prefixWord ++ tailWord_987848) baseStart_987848 baseEnd_987848 := by
    simpa [prefixWord, tailWord_987848, baseEnd_987848] using wordTrace_append hprefix tailTrace_987848
  have hstable : (prefixWord ++ tailWord_987848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987848).length < 2 ^ (prefixWord ++ tailWord_987848).sum := by decide
  have hdescent : baseEnd_987848 < baseStart_987848 := by decide
  rcases family_descends (prefixWord ++ tailWord_987848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987925 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 5, 3]
def baseStart_987925 : Nat := 118140960795 + 987925 * 2 ^ 59
def prefixEnd_987925 : Nat := 4983230072969 + 3 ^ 40 * 987925 * 2
def baseEnd_987925 : Nat := 338186917062101648396081

theorem tailTrace_987925 : CollatzResearch.WordTrace tailWord_987925 prefixEnd_987925 338186917062101648396081 := by
  unfold tailWord_987925
  simp only [CollatzResearch.WordTrace]
  refine ⟨36032584945923924002293229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24021723297282616001528819 36032584945923924002293229)
  ·
    refine ⟨13512219354721471500859961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36032584945923924002293229 13512219354721471500859961)
    ·
      refine ⟨10134164516041103625644971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13512219354721471500859961 10134164516041103625644971)
      ·
        refine ⟨15201246774061655438467457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10134164516041103625644971 15201246774061655438467457)
        ·
          refine ⟨11400935080546241578850593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15201246774061655438467457 11400935080546241578850593)
          ·
            refine ⟨8550701310409681184137945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11400935080546241578850593 8550701310409681184137945)
            ·
              refine ⟨6413025982807260888103459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8550701310409681184137945 6413025982807260888103459)
              ·
                refine ⟨9619538974210891332155189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6413025982807260888103459 9619538974210891332155189)
                ·
                  refine ⟨901831778832271062389549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9619538974210891332155189 901831778832271062389549)
                  ·
                    refine ⟨338186917062101648396081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 901831778832271062389549 338186917062101648396081)
                    ·
                      rfl

theorem cell22_987925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_987925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987925 prefixEnd_987925 := by exact prefixLift 987925
  have htrace : WordTrace (prefixWord ++ tailWord_987925) baseStart_987925 baseEnd_987925 := by
    simpa [prefixWord, tailWord_987925, baseEnd_987925] using wordTrace_append hprefix tailTrace_987925
  have hstable : (prefixWord ++ tailWord_987925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987925).length < 2 ^ (prefixWord ++ tailWord_987925).sum := by decide
  have hdescent : baseEnd_987925 < baseStart_987925 := by decide
  rcases family_descends (prefixWord ++ tailWord_987925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987955 : List Nat := [1, 1, 1, 2, 6, 1, 1, 4, 5]
def baseStart_987955 : Nat := 118140960795 + 987955 * 2 ^ 59
def prefixEnd_987955 : Nat := 4983230072969 + 3 ^ 40 * 987955 * 2
def baseEnd_987955 : Nat := 112732395558397190048663

theorem tailTrace_987955 : CollatzResearch.WordTrace tailWord_987955 prefixEnd_987955 112732395558397190048663 := by
  unfold tailWord_987955
  simp only [CollatzResearch.WordTrace]
  refine ⟨36033679135815239125885319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24022452757210159417256879 36033679135815239125885319)
  ·
    refine ⟨54050518703722858688827979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36033679135815239125885319 54050518703722858688827979)
    ·
      refine ⟨81075778055584288033241969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54050518703722858688827979 81075778055584288033241969)
      ·
        refine ⟨60806833541688216024931477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81075778055584288033241969 60806833541688216024931477)
        ·
          refine ⟨2850320322266635126168663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60806833541688216024931477 2850320322266635126168663)
          ·
            refine ⟨4275480483399952689252995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2850320322266635126168663 4275480483399952689252995)
            ·
              refine ⟨6413220725099929033879493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4275480483399952689252995 6413220725099929033879493)
              ·
                refine ⟨1202478885956236693852405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6413220725099929033879493 1202478885956236693852405)
                ·
                  refine ⟨112732395558397190048663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1202478885956236693852405 112732395558397190048663)
                  ·
                    rfl

theorem cell22_987955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 5].length) (baseStart_987955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_987955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_987955 prefixEnd_987955 := by exact prefixLift 987955
  have htrace : WordTrace (prefixWord ++ tailWord_987955) baseStart_987955 baseEnd_987955 := by
    simpa [prefixWord, tailWord_987955, baseEnd_987955] using wordTrace_append hprefix tailTrace_987955
  have hstable : (prefixWord ++ tailWord_987955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987955).length < 2 ^ (prefixWord ++ tailWord_987955).sum := by decide
  have hdescent : baseEnd_987955 < baseStart_987955 := by decide
  rcases family_descends (prefixWord ++ tailWord_987955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988017 : List Nat := [1, 2, 2, 2, 1, 4, 2, 4, 4]
def baseStart_988017 : Nat := 118140960795 + 988017 * 2 ^ 59
def prefixEnd_988017 : Nat := 4983230072969 + 3 ^ 40 * 988017 * 2
def baseEnd_988017 : Nat := 112739470180748025031933

theorem tailTrace_988017 : CollatzResearch.WordTrace tailWord_988017 prefixEnd_988017 112739470180748025031933 := by
  unfold tailWord_988017
  simp only [CollatzResearch.WordTrace]
  refine ⟨36035940461590623714642305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24023960307727082476428203 36035940461590623714642305)
  ·
    refine ⟨27026955346192967785981729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36035940461590623714642305 27026955346192967785981729)
    ·
      refine ⟨20270216509644725839486297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27026955346192967785981729 20270216509644725839486297)
      ·
        refine ⟨15202662382233544379614723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20270216509644725839486297 15202662382233544379614723)
        ·
          refine ⟨22803993573350316569422085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15202662382233544379614723 22803993573350316569422085)
          ·
            refine ⟨4275748795003184356766641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22803993573350316569422085 4275748795003184356766641)
            ·
              refine ⟨3206811596252388267574981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4275748795003184356766641 3206811596252388267574981)
              ·
                refine ⟨601277174297322800170309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3206811596252388267574981 601277174297322800170309)
                ·
                  refine ⟨112739470180748025031933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 601277174297322800170309 112739470180748025031933)
                  ·
                    rfl

theorem cell22_988017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 4].length) (baseStart_988017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988017 prefixEnd_988017 := by exact prefixLift 988017
  have htrace : WordTrace (prefixWord ++ tailWord_988017) baseStart_988017 baseEnd_988017 := by
    simpa [prefixWord, tailWord_988017, baseEnd_988017] using wordTrace_append hprefix tailTrace_988017
  have hstable : (prefixWord ++ tailWord_988017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988017).length < 2 ^ (prefixWord ++ tailWord_988017).sum := by decide
  have hdescent : baseEnd_988017 < baseStart_988017 := by decide
  rcases family_descends (prefixWord ++ tailWord_988017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988167 : List Nat := [1, 1, 4, 3, 1, 1, 1, 4, 1, 5]
def baseStart_988167 : Nat := 118140960795 + 988167 * 2 ^ 59
def prefixEnd_988167 : Nat := 4983230072969 + 3 ^ 40 * 988167 * 2
def baseEnd_988167 : Nat := 338269758607693683845339

theorem tailTrace_988167 : CollatzResearch.WordTrace tailWord_988167 prefixEnd_988167 338269758607693683845339 := by
  unfold tailWord_988167
  simp only [CollatzResearch.WordTrace]
  refine ⟨36041411411047199332602755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24027607607364799555068503 36041411411047199332602755)
  ·
    refine ⟨54062117116570798998904133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36041411411047199332602755 54062117116570798998904133)
    ·
      refine ⟨10136646959357024812294525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54062117116570798998904133 10136646959357024812294525)
      ·
        refine ⟨3801242609758884304610447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10136646959357024812294525 3801242609758884304610447)
        ·
          refine ⟨5701863914638326456915671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3801242609758884304610447 5701863914638326456915671)
          ·
            refine ⟨8552795871957489685373507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5701863914638326456915671 8552795871957489685373507)
            ·
              refine ⟨12829193807936234528060261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8552795871957489685373507 12829193807936234528060261)
              ·
                refine ⟨2405473838988043974011299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12829193807936234528060261 2405473838988043974011299)
                ·
                  refine ⟨3608210758482065961016949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2405473838988043974011299 3608210758482065961016949)
                  ·
                    refine ⟨338269758607693683845339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3608210758482065961016949 338269758607693683845339)
                    ·
                      rfl

theorem cell22_988167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_988167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988167 prefixEnd_988167 := by exact prefixLift 988167
  have htrace : WordTrace (prefixWord ++ tailWord_988167) baseStart_988167 baseEnd_988167 := by
    simpa [prefixWord, tailWord_988167, baseEnd_988167] using wordTrace_append hprefix tailTrace_988167
  have hstable : (prefixWord ++ tailWord_988167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988167).length < 2 ^ (prefixWord ++ tailWord_988167).sum := by decide
  have hdescent : baseEnd_988167 < baseStart_988167 := by decide
  rcases family_descends (prefixWord ++ tailWord_988167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988171 : List Nat := [1, 1, 1, 1, 6, 4, 2, 1, 1, 4]
def baseStart_988171 : Nat := 118140960795 + 988171 * 2 ^ 59
def prefixEnd_988171 : Nat := 4983230072969 + 3 ^ 40 * 988171 * 2
def baseEnd_988171 : Nat := 338271127889439006745327

theorem tailTrace_988171 : CollatzResearch.WordTrace tailWord_988171 prefixEnd_988171 338271127889439006745327 := by
  unfold tailWord_988171
  simp only [CollatzResearch.WordTrace]
  refine ⟨36041557303032708015748367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24027704868688472010498911 36041557303032708015748367)
  ·
    refine ⟨54062335954549062023622551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36041557303032708015748367 54062335954549062023622551)
    ·
      refine ⟨81093503931823593035433827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54062335954549062023622551 81093503931823593035433827)
      ·
        refine ⟨121640255897735389553150741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81093503931823593035433827 121640255897735389553150741)
        ·
          refine ⟨5701886995206346385303941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121640255897735389553150741 5701886995206346385303941)
          ·
            refine ⟨1069103811601189947244489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5701886995206346385303941 1069103811601189947244489)
            ·
              refine ⟨801827858700892460433367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1069103811601189947244489 801827858700892460433367)
              ·
                refine ⟨1202741788051338690650051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801827858700892460433367 1202741788051338690650051)
                ·
                  refine ⟨1804112682077008035975077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1202741788051338690650051 1804112682077008035975077)
                  ·
                    refine ⟨338271127889439006745327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1804112682077008035975077 338271127889439006745327)
                    ·
                      rfl

theorem cell22_988171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 1, 4].length) (baseStart_988171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988171 prefixEnd_988171 := by exact prefixLift 988171
  have htrace : WordTrace (prefixWord ++ tailWord_988171) baseStart_988171 baseEnd_988171 := by
    simpa [prefixWord, tailWord_988171, baseEnd_988171] using wordTrace_append hprefix tailTrace_988171
  have hstable : (prefixWord ++ tailWord_988171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988171).length < 2 ^ (prefixWord ++ tailWord_988171).sum := by decide
  have hdescent : baseEnd_988171 < baseStart_988171 := by decide
  rcases family_descends (prefixWord ++ tailWord_988171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988184 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 4, 3]
def baseStart_988184 : Nat := 118140960795 + 988184 * 2 ^ 59
def prefixEnd_988184 : Nat := 4983230072969 + 3 ^ 40 * 988184 * 2
def baseEnd_988184 : Nat := 338275578055111306170287

theorem tailTrace_988184 : CollatzResearch.WordTrace tailWord_988184 prefixEnd_988184 338275578055111306170287 := by
  unfold tailWord_988184
  simp only [CollatzResearch.WordTrace]
  refine ⟨18021015725992805617985803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24028020967990407490647737 18021015725992805617985803)
  ·
    refine ⟨27031523588989208426978705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18021015725992805617985803 27031523588989208426978705)
    ·
      refine ⟨20273642691741906320234029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27031523588989208426978705 20273642691741906320234029)
      ·
        refine ⟨7602616009403214870087761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20273642691741906320234029 7602616009403214870087761)
        ·
          refine ⟨5701962007052411152565821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7602616009403214870087761 5701962007052411152565821)
          ·
            refine ⟨2138235752644654182212183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5701962007052411152565821 2138235752644654182212183)
            ·
              refine ⟨3207353628966981273318275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2138235752644654182212183 3207353628966981273318275)
              ·
                refine ⟨4811030443450471909977413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3207353628966981273318275 4811030443450471909977413)
                ·
                  refine ⟨902068208146963483120765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4811030443450471909977413 902068208146963483120765)
                  ·
                    refine ⟨338275578055111306170287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 902068208146963483120765 338275578055111306170287)
                    ·
                      rfl

theorem cell22_988184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_988184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988184 prefixEnd_988184 := by exact prefixLift 988184
  have htrace : WordTrace (prefixWord ++ tailWord_988184) baseStart_988184 baseEnd_988184 := by
    simpa [prefixWord, tailWord_988184, baseEnd_988184] using wordTrace_append hprefix tailTrace_988184
  have hstable : (prefixWord ++ tailWord_988184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988184).length < 2 ^ (prefixWord ++ tailWord_988184).sum := by decide
  have hdescent : baseEnd_988184 < baseStart_988184 := by decide
  rcases family_descends (prefixWord ++ tailWord_988184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988199 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 1, 6]
def baseStart_988199 : Nat := 118140960795 + 988199 * 2 ^ 59
def prefixEnd_988199 : Nat := 4983230072969 + 3 ^ 40 * 988199 * 2
def baseEnd_988199 : Nat := 338280712861656267045241

theorem tailTrace_988199 : CollatzResearch.WordTrace tailWord_988199 prefixEnd_988199 338280712861656267045241 := by
  unfold tailWord_988199
  simp only [CollatzResearch.WordTrace]
  refine ⟨36042578546931268797767651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24028385697954179198511767 36042578546931268797767651)
  ·
    refine ⟨54063867820396903196651477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36042578546931268797767651 54063867820396903196651477)
    ·
      refine ⟨1267121902040552418671519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 54063867820396903196651477 1267121902040552418671519)
      ·
        refine ⟨1900682853060828628007279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1267121902040552418671519 1900682853060828628007279)
        ·
          refine ⟨2851024279591242942010919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900682853060828628007279 2851024279591242942010919)
          ·
            refine ⟨4276536419386864413016379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2851024279591242942010919 4276536419386864413016379)
            ·
              refine ⟨6414804629080296619524569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4276536419386864413016379 6414804629080296619524569)
              ·
                refine ⟨4811103471810222464643427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6414804629080296619524569 4811103471810222464643427)
                ·
                  refine ⟨7216655207715333696965141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4811103471810222464643427 7216655207715333696965141)
                  ·
                    refine ⟨338280712861656267045241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7216655207715333696965141 338280712861656267045241)
                    ·
                      rfl

theorem cell22_988199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_988199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988199 prefixEnd_988199 := by exact prefixLift 988199
  have htrace : WordTrace (prefixWord ++ tailWord_988199) baseStart_988199 baseEnd_988199 := by
    simpa [prefixWord, tailWord_988199, baseEnd_988199] using wordTrace_append hprefix tailTrace_988199
  have hstable : (prefixWord ++ tailWord_988199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988199).length < 2 ^ (prefixWord ++ tailWord_988199).sum := by decide
  have hdescent : baseEnd_988199 < baseStart_988199 := by decide
  rcases family_descends (prefixWord ++ tailWord_988199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988214 : List Nat := [5, 1, 2, 1, 1, 3, 1, 8]
def baseStart_988214 : Nat := 118140960795 + 988214 * 2 ^ 59
def prefixEnd_988214 : Nat := 4983230072969 + 3 ^ 40 * 988214 * 2
def baseEnd_988214 : Nat := 37587316407577914213355

theorem tailTrace_988214 : CollatzResearch.WordTrace tailWord_988214 prefixEnd_988214 37587316407577914213355 := by
  unfold tailWord_988214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2252695352617307897472731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24028750427917950906375797 2252695352617307897472731)
  ·
    refine ⟨3379043028925961846209097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2252695352617307897472731 3379043028925961846209097)
    ·
      refine ⟨2534282271694471384656823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3379043028925961846209097 2534282271694471384656823)
      ·
        refine ⟨3801423407541707076985235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2534282271694471384656823 3801423407541707076985235)
        ·
          refine ⟨5702135111312560615477853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3801423407541707076985235 5702135111312560615477853)
          ·
            refine ⟨2138300666742210230804195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5702135111312560615477853 2138300666742210230804195)
            ·
              refine ⟨3207451000113315346206293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2138300666742210230804195 3207451000113315346206293)
              ·
                refine ⟨37587316407577914213355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3207451000113315346206293 37587316407577914213355)
                ·
                  rfl

theorem cell22_988214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_988214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988214 prefixEnd_988214 := by exact prefixLift 988214
  have htrace : WordTrace (prefixWord ++ tailWord_988214) baseStart_988214 baseEnd_988214 := by
    simpa [prefixWord, tailWord_988214, baseEnd_988214] using wordTrace_append hprefix tailTrace_988214
  have hstable : (prefixWord ++ tailWord_988214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988214).length < 2 ^ (prefixWord ++ tailWord_988214).sum := by decide
  have hdescent : baseEnd_988214 < baseStart_988214 := by decide
  rcases family_descends (prefixWord ++ tailWord_988214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988257 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 2, 5]
def baseStart_988257 : Nat := 118140960795 + 988257 * 2 ^ 59
def prefixEnd_988257 : Nat := 4983230072969 + 3 ^ 40 * 988257 * 2
def baseEnd_988257 : Nat := 338300567446963449095063

theorem tailTrace_988257 : CollatzResearch.WordTrace tailWord_988257 prefixEnd_988257 338300567446963449095063 := by
  unfold tailWord_988257
  simp only [CollatzResearch.WordTrace]
  refine ⟨36044693980721144703379025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24029795987147429802252683 36044693980721144703379025)
  ·
    refine ⟨27033520485540858527534269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36044693980721144703379025 27033520485540858527534269)
    ·
      refine ⟨10137570182077821947825351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27033520485540858527534269 10137570182077821947825351)
      ·
        refine ⟨15206355273116732921738027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10137570182077821947825351 15206355273116732921738027)
        ·
          refine ⟨22809532909675099382607041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15206355273116732921738027 22809532909675099382607041)
          ·
            refine ⟨17107149682256324536955281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22809532909675099382607041 17107149682256324536955281)
            ·
              refine ⟨12830362261692243402716461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17107149682256324536955281 12830362261692243402716461)
              ·
                refine ⟨4811385848134591276018673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12830362261692243402716461 4811385848134591276018673)
                ·
                  refine ⟨3608539386100943457014005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4811385848134591276018673 3608539386100943457014005)
                  ·
                    refine ⟨338300567446963449095063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3608539386100943457014005 338300567446963449095063)
                    ·
                      rfl

theorem cell22_988257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_988257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988257 prefixEnd_988257 := by exact prefixLift 988257
  have htrace : WordTrace (prefixWord ++ tailWord_988257) baseStart_988257 baseEnd_988257 := by
    simpa [prefixWord, tailWord_988257, baseEnd_988257] using wordTrace_append hprefix tailTrace_988257
  have hstable : (prefixWord ++ tailWord_988257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988257).length < 2 ^ (prefixWord ++ tailWord_988257).sum := by decide
  have hdescent : baseEnd_988257 < baseStart_988257 := by decide
  rcases family_descends (prefixWord ++ tailWord_988257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988353 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 4, 3]
def baseStart_988353 : Nat := 118140960795 + 988353 * 2 ^ 59
def prefixEnd_988353 : Nat := 4983230072969 + 3 ^ 40 * 988353 * 2
def baseEnd_988353 : Nat := 338333430208851198694769

theorem tailTrace_988353 : CollatzResearch.WordTrace tailWord_988353 prefixEnd_988353 338333430208851198694769 := by
  unfold tailWord_988353
  simp only [CollatzResearch.WordTrace]
  refine ⟨36048195388373353098873713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24032130258915568732582475 36048195388373353098873713)
  ·
    refine ⟨27036146541280014824155285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36048195388373353098873713 27036146541280014824155285)
    ·
      refine ⟨1267319369122500694882279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27036146541280014824155285 1267319369122500694882279)
      ·
        refine ⟨1900979053683751042323419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1267319369122500694882279 1900979053683751042323419)
        ·
          refine ⟨2851468580525626563485129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900979053683751042323419 2851468580525626563485129)
          ·
            refine ⟨2138601435394219922613847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2851468580525626563485129 2138601435394219922613847)
            ·
              refine ⟨3207902153091329883920771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2138601435394219922613847 3207902153091329883920771)
              ·
                refine ⟨4811853229636994825881157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3207902153091329883920771 4811853229636994825881157)
                ·
                  refine ⟨902222480556936529852717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4811853229636994825881157 902222480556936529852717)
                  ·
                    refine ⟨338333430208851198694769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 902222480556936529852717 338333430208851198694769)
                    ·
                      rfl

theorem cell22_988353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_988353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988353 prefixEnd_988353 := by exact prefixLift 988353
  have htrace : WordTrace (prefixWord ++ tailWord_988353) baseStart_988353 baseEnd_988353 := by
    simpa [prefixWord, tailWord_988353, baseEnd_988353] using wordTrace_append hprefix tailTrace_988353
  have hstable : (prefixWord ++ tailWord_988353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988353).length < 2 ^ (prefixWord ++ tailWord_988353).sum := by decide
  have hdescent : baseEnd_988353 < baseStart_988353 := by decide
  rcases family_descends (prefixWord ++ tailWord_988353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988394 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 7]
def baseStart_988394 : Nat := 118140960795 + 988394 * 2 ^ 59
def prefixEnd_988394 : Nat := 4983230072969 + 3 ^ 40 * 988394 * 2
def baseEnd_988394 : Nat := 112782488448913586139881

theorem tailTrace_988394 : CollatzResearch.WordTrace tailWord_988394 prefixEnd_988394 112782488448913586139881 := by
  unfold tailWord_988394
  simp only [CollatzResearch.WordTrace]
  refine ⟨9012422695306204275279059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24033127187483211400744157 9012422695306204275279059)
  ·
    refine ⟨13518634042959306412918589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9012422695306204275279059 13518634042959306412918589)
    ·
      refine ⟨5069487766109739904844471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13518634042959306412918589 5069487766109739904844471)
      ·
        refine ⟨7604231649164609857266707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5069487766109739904844471 7604231649164609857266707)
        ·
          refine ⟨11406347473746914785900061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7604231649164609857266707 11406347473746914785900061)
          ·
            refine ⟨4277380302655093044712523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11406347473746914785900061 4277380302655093044712523)
            ·
              refine ⟨6416070453982639567068785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4277380302655093044712523 6416070453982639567068785)
              ·
                refine ⟨4812052840486979675301589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6416070453982639567068785 4812052840486979675301589)
                ·
                  refine ⟨112782488448913586139881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4812052840486979675301589 112782488448913586139881)
                  ·
                    rfl

theorem cell22_988394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_988394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988394 prefixEnd_988394 := by exact prefixLift 988394
  have htrace : WordTrace (prefixWord ++ tailWord_988394) baseStart_988394 baseEnd_988394 := by
    simpa [prefixWord, tailWord_988394, baseEnd_988394] using wordTrace_append hprefix tailTrace_988394
  have hstable : (prefixWord ++ tailWord_988394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988394).length < 2 ^ (prefixWord ++ tailWord_988394).sum := by decide
  have hdescent : baseEnd_988394 < baseStart_988394 := by decide
  rcases family_descends (prefixWord ++ tailWord_988394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988415 : List Nat := [1, 1, 2, 2, 1, 6, 3, 2, 1, 3]
def baseStart_988415 : Nat := 118140960795 + 988415 * 2 ^ 59
def prefixEnd_988415 : Nat := 4983230072969 + 3 ^ 40 * 988415 * 2
def baseEnd_988415 : Nat := 338354654075903703644579

theorem tailTrace_988415 : CollatzResearch.WordTrace tailWord_988415 prefixEnd_988415 338354654075903703644579 := by
  unfold tailWord_988415
  simp only [CollatzResearch.WordTrace]
  refine ⟨36050456714148737687630699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24033637809432491791753799 36050456714148737687630699)
  ·
    refine ⟨54075685071223106531446049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36050456714148737687630699 54075685071223106531446049)
    ·
      refine ⟨40556763803417329898584537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54075685071223106531446049 40556763803417329898584537)
      ·
        refine ⟨30417572852562997423938403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40556763803417329898584537 30417572852562997423938403)
        ·
          refine ⟨45626359278844496135907605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30417572852562997423938403 45626359278844496135907605)
          ·
            refine ⟨2138735591195835756370669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45626359278844496135907605 2138735591195835756370669)
            ·
              refine ⟨802025846698438408639001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2138735591195835756370669 802025846698438408639001)
              ·
                refine ⟨601519385023828806479251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 802025846698438408639001 601519385023828806479251)
                ·
                  refine ⟨902279077535743209718877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601519385023828806479251 902279077535743209718877)
                  ·
                    refine ⟨338354654075903703644579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 902279077535743209718877 338354654075903703644579)
                    ·
                      rfl

theorem cell22_988415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 1, 3].length) (baseStart_988415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988415 prefixEnd_988415 := by exact prefixLift 988415
  have htrace : WordTrace (prefixWord ++ tailWord_988415) baseStart_988415 baseEnd_988415 := by
    simpa [prefixWord, tailWord_988415, baseEnd_988415] using wordTrace_append hprefix tailTrace_988415
  have hstable : (prefixWord ++ tailWord_988415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988415).length < 2 ^ (prefixWord ++ tailWord_988415).sum := by decide
  have hdescent : baseEnd_988415 < baseStart_988415 := by decide
  rcases family_descends (prefixWord ++ tailWord_988415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988428 : List Nat := [2, 2, 1, 2, 2, 5, 2, 1, 5]
def baseStart_988428 : Nat := 118140960795 + 988428 * 2 ^ 59
def prefixEnd_988428 : Nat := 4983230072969 + 3 ^ 40 * 988428 * 2
def baseEnd_988428 : Nat := 112786368080525334356513

theorem tailTrace_988428 : CollatzResearch.WordTrace tailWord_988428 prefixEnd_988428 112786368080525334356513 := by
  unfold tailWord_988428
  simp only [CollatzResearch.WordTrace]
  refine ⟨18025465431550820453926969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24033953908734427271902625 18025465431550820453926969)
  ·
    refine ⟨13519099073663115340445227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18025465431550820453926969 13519099073663115340445227)
    ·
      refine ⟨20278648610494673010667841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13519099073663115340445227 20278648610494673010667841)
      ·
        refine ⟨15208986457871004758000881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20278648610494673010667841 15208986457871004758000881)
        ·
          refine ⟨11406739843403253568500661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15208986457871004758000881 11406739843403253568500661)
          ·
            refine ⟨1069381860319055022046937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11406739843403253568500661 1069381860319055022046937)
            ·
              refine ⟨802036395239291266535203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1069381860319055022046937 802036395239291266535203)
              ·
                refine ⟨1203054592858936899802805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802036395239291266535203 1203054592858936899802805)
                ·
                  refine ⟨112786368080525334356513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1203054592858936899802805 112786368080525334356513)
                  ·
                    rfl

theorem cell22_988428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_988428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988428 prefixEnd_988428 := by exact prefixLift 988428
  have htrace : WordTrace (prefixWord ++ tailWord_988428) baseStart_988428 baseEnd_988428 := by
    simpa [prefixWord, tailWord_988428, baseEnd_988428] using wordTrace_append hprefix tailTrace_988428
  have hstable : (prefixWord ++ tailWord_988428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988428).length < 2 ^ (prefixWord ++ tailWord_988428).sum := by decide
  have hdescent : baseEnd_988428 < baseStart_988428 := by decide
  rcases family_descends (prefixWord ++ tailWord_988428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988439 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 8]
def baseStart_988439 : Nat := 118140960795 + 988439 * 2 ^ 59
def prefixEnd_988439 : Nat := 4983230072969 + 3 ^ 40 * 988439 * 2
def baseEnd_988439 : Nat := 112787623255458547014835

theorem tailTrace_988439 : CollatzResearch.WordTrace tailWord_988439 prefixEnd_988439 112787623255458547014835 := by
  unfold tailWord_988439
  simp only [CollatzResearch.WordTrace]
  refine ⟨36051332066061789786504371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24034221377374526524336247 36051332066061789786504371)
  ·
    refine ⟨54076998099092684679756557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36051332066061789786504371 54076998099092684679756557)
    ·
      refine ⟨20278874287159756754908709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54076998099092684679756557 20278874287159756754908709)
      ·
        refine ⟨3802288928842454391545383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20278874287159756754908709 3802288928842454391545383)
        ·
          refine ⟨5703433393263681587318075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3802288928842454391545383 5703433393263681587318075)
          ·
            refine ⟨8555150089895522380977113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5703433393263681587318075 8555150089895522380977113)
            ·
              refine ⟨6416362567421641785732835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8555150089895522380977113 6416362567421641785732835)
              ·
                refine ⟨9624543851132462678599253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6416362567421641785732835 9624543851132462678599253)
                ·
                  refine ⟨112787623255458547014835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9624543851132462678599253 112787623255458547014835)
                  ·
                    rfl

theorem cell22_988439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 8].length) (baseStart_988439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988439 prefixEnd_988439 := by exact prefixLift 988439
  have htrace : WordTrace (prefixWord ++ tailWord_988439) baseStart_988439 baseEnd_988439 := by
    simpa [prefixWord, tailWord_988439, baseEnd_988439] using wordTrace_append hprefix tailTrace_988439
  have hstable : (prefixWord ++ tailWord_988439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988439).length < 2 ^ (prefixWord ++ tailWord_988439).sum := by decide
  have hdescent : baseEnd_988439 < baseStart_988439 := by decide
  rcases family_descends (prefixWord ++ tailWord_988439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988503 : List Nat := [1, 1, 3, 2, 3, 4, 1, 1, 2, 4]
def baseStart_988503 : Nat := 118140960795 + 988503 * 2 ^ 59
def prefixEnd_988503 : Nat := 4983230072969 + 3 ^ 40 * 988503 * 2
def baseEnd_988503 : Nat := 338384778274300807444309

theorem tailTrace_988503 : CollatzResearch.WordTrace tailWord_988503 prefixEnd_988503 338384778274300807444309 := by
  unfold tailWord_988503
  simp only [CollatzResearch.WordTrace]
  refine ⟨36053666337829928716834163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24035777558553285811222775 36053666337829928716834163)
  ·
    refine ⟨54080499506744893075251245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36053666337829928716834163 54080499506744893075251245)
    ·
      refine ⟨20280187315029334903219217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54080499506744893075251245 20280187315029334903219217)
      ·
        refine ⟨15210140486272001177414413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20280187315029334903219217 15210140486272001177414413)
        ·
          refine ⟨5703802682352000441530405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15210140486272001177414413 5703802682352000441530405)
          ·
            refine ⟨1069463002941000082786951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5703802682352000441530405 1069463002941000082786951)
            ·
              refine ⟨1604194504411500124180427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1069463002941000082786951 1604194504411500124180427)
              ·
                refine ⟨2406291756617250186270641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1604194504411500124180427 2406291756617250186270641)
                ·
                  refine ⟨1804718817462937639702981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2406291756617250186270641 1804718817462937639702981)
                  ·
                    refine ⟨338384778274300807444309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1804718817462937639702981 338384778274300807444309)
                    ·
                      rfl

theorem cell22_988503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_988503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988503 prefixEnd_988503 := by exact prefixLift 988503
  have htrace : WordTrace (prefixWord ++ tailWord_988503) baseStart_988503 baseEnd_988503 := by
    simpa [prefixWord, tailWord_988503, baseEnd_988503] using wordTrace_append hprefix tailTrace_988503
  have hstable : (prefixWord ++ tailWord_988503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988503).length < 2 ^ (prefixWord ++ tailWord_988503).sum := by decide
  have hdescent : baseEnd_988503 < baseStart_988503 := by decide
  rcases family_descends (prefixWord ++ tailWord_988503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988522 : List Nat := [3, 1, 3, 3, 2, 2, 1, 2, 2, 3]
def baseStart_988522 : Nat := 118140960795 + 988522 * 2 ^ 59
def prefixEnd_988522 : Nat := 4983230072969 + 3 ^ 40 * 988522 * 2
def baseEnd_988522 : Nat := 338391282362591091219251

theorem tailTrace_988522 : CollatzResearch.WordTrace tailWord_988522 prefixEnd_988522 338391282362591091219251 := by
  unfold tailWord_988522
  simp only [CollatzResearch.WordTrace]
  refine ⟨9013589831190273740443955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24036239549840729974517213 9013589831190273740443955)
  ·
    refine ⟨13520384746785410610665933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9013589831190273740443955 13520384746785410610665933)
    ·
      refine ⟨5070144280044528978999725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13520384746785410610665933 5070144280044528978999725)
      ·
        refine ⟨1901304105016698367124897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5070144280044528978999725 1901304105016698367124897)
        ·
          refine ⟨1425978078762523775343673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1901304105016698367124897 1425978078762523775343673)
          ·
            refine ⟨1069483559071892831507755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1425978078762523775343673 1069483559071892831507755)
            ·
              refine ⟨1604225338607839247261633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1069483559071892831507755 1604225338607839247261633)
              ·
                refine ⟨1203169003955879435446225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1604225338607839247261633 1203169003955879435446225)
                ·
                  refine ⟨902376752966909576584669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1203169003955879435446225 902376752966909576584669)
                  ·
                    refine ⟨338391282362591091219251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 902376752966909576584669 338391282362591091219251)
                    ·
                      rfl

theorem cell22_988522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_988522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988522 prefixEnd_988522 := by exact prefixLift 988522
  have htrace : WordTrace (prefixWord ++ tailWord_988522) baseStart_988522 baseEnd_988522 := by
    simpa [prefixWord, tailWord_988522, baseEnd_988522] using wordTrace_append hprefix tailTrace_988522
  have hstable : (prefixWord ++ tailWord_988522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988522).length < 2 ^ (prefixWord ++ tailWord_988522).sum := by decide
  have hdescent : baseEnd_988522 < baseStart_988522 := by decide
  rcases family_descends (prefixWord ++ tailWord_988522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988584 : List Nat := [2, 1, 6, 1, 3, 1, 1, 1, 3, 3]
def baseStart_988584 : Nat := 118140960795 + 988584 * 2 ^ 59
def prefixEnd_988584 : Nat := 4983230072969 + 3 ^ 40 * 988584 * 2
def baseEnd_988584 : Nat := 338412506229643596169061

theorem tailTrace_988584 : CollatzResearch.WordTrace tailWord_988584 prefixEnd_988584 338412506229643596169061 := by
  unfold tailWord_988584
  simp only [CollatzResearch.WordTrace]
  refine ⟨18028310325268239775266403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24037747100357653033688537 18028310325268239775266403)
  ·
    refine ⟨27042465487902359662899605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18028310325268239775266403 27042465487902359662899605)
    ·
      refine ⟨1267615569745423109198419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27042465487902359662899605 1267615569745423109198419)
      ·
        refine ⟨1901423354618134663797629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1267615569745423109198419 1901423354618134663797629)
        ·
          refine ⟨713033757981800498924111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1901423354618134663797629 713033757981800498924111)
          ·
            refine ⟨1069550636972700748386167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713033757981800498924111 1069550636972700748386167)
            ·
              refine ⟨1604325955459051122579251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1069550636972700748386167 1604325955459051122579251)
              ·
                refine ⟨2406488933188576683868877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1604325955459051122579251 2406488933188576683868877)
                ·
                  refine ⟨902433349945716256450829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2406488933188576683868877 902433349945716256450829)
                  ·
                    refine ⟨338412506229643596169061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 902433349945716256450829 338412506229643596169061)
                    ·
                      rfl

theorem cell22_988584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_988584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988584 prefixEnd_988584 := by exact prefixLift 988584
  have htrace : WordTrace (prefixWord ++ tailWord_988584) baseStart_988584 baseEnd_988584 := by
    simpa [prefixWord, tailWord_988584, baseEnd_988584] using wordTrace_append hprefix tailTrace_988584
  have hstable : (prefixWord ++ tailWord_988584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988584).length < 2 ^ (prefixWord ++ tailWord_988584).sum := by decide
  have hdescent : baseEnd_988584 < baseStart_988584 := by decide
  rcases family_descends (prefixWord ++ tailWord_988584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988666 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 2, 6]
def baseStart_988666 : Nat := 118140960795 + 988666 * 2 ^ 59
def prefixEnd_988666 : Nat := 4983230072969 + 3 ^ 40 * 988666 * 2
def baseEnd_988666 : Nat := 338440576505422715618809

theorem tailTrace_988666 : CollatzResearch.WordTrace tailWord_988666 prefixEnd_988666 338440576505422715618809 := by
  unfold tailWord_988666
  simp only [CollatzResearch.WordTrace]
  refine ⟨9014902859059851888754463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24039740957492938370011901 9014902859059851888754463)
  ·
    refine ⟨13522354288589777833131695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9014902859059851888754463 13522354288589777833131695)
    ·
      refine ⟨20283531432884666749697543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13522354288589777833131695 20283531432884666749697543)
      ·
        refine ⟨30425297149327000124546315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20283531432884666749697543 30425297149327000124546315)
        ·
          refine ⟨45637945723990500186819473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30425297149327000124546315 45637945723990500186819473)
          ·
            refine ⟨34228459292992875140114605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45637945723990500186819473 34228459292992875140114605)
            ·
              refine ⟨12835672234872328177542977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34228459292992875140114605 12835672234872328177542977)
              ·
                refine ⟨9626754176154246133157233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12835672234872328177542977 9626754176154246133157233)
                ·
                  refine ⟨7220065632115684599867925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9626754176154246133157233 7220065632115684599867925)
                  ·
                    refine ⟨338440576505422715618809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7220065632115684599867925 338440576505422715618809)
                    ·
                      rfl

theorem cell22_988666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_988666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988666 prefixEnd_988666 := by exact prefixLift 988666
  have htrace : WordTrace (prefixWord ++ tailWord_988666) baseStart_988666 baseEnd_988666 := by
    simpa [prefixWord, tailWord_988666, baseEnd_988666] using wordTrace_append hprefix tailTrace_988666
  have hstable : (prefixWord ++ tailWord_988666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988666).length < 2 ^ (prefixWord ++ tailWord_988666).sum := by decide
  have hdescent : baseEnd_988666 < baseStart_988666 := by decide
  rcases family_descends (prefixWord ++ tailWord_988666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988668 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 5, 3]
def baseStart_988668 : Nat := 118140960795 + 988668 * 2 ^ 59
def prefixEnd_988668 : Nat := 4983230072969 + 3 ^ 40 * 988668 * 2
def baseEnd_988668 : Nat := 338441261146295377068803

theorem tailTrace_988668 : CollatzResearch.WordTrace tailWord_988668 prefixEnd_988668 338441261146295377068803 := by
  unfold tailWord_988668
  simp only [CollatzResearch.WordTrace]
  refine ⟨18029842191116080948295329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24039789588154774597727105 18029842191116080948295329)
  ·
    refine ⟨13522381643337060711221497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18029842191116080948295329 13522381643337060711221497)
    ·
      refine ⟨10141786232502795533416123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13522381643337060711221497 10141786232502795533416123)
      ·
        refine ⟨15212679348754193300124185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10141786232502795533416123 15212679348754193300124185)
        ·
          refine ⟨11409509511565644975093139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15212679348754193300124185 11409509511565644975093139)
          ·
            refine ⟨17114264267348467462639709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11409509511565644975093139 17114264267348467462639709)
            ·
              refine ⟨6417849100255675298489891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17114264267348467462639709 6417849100255675298489891)
              ·
                refine ⟨9626773650383512947734837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6417849100255675298489891 9626773650383512947734837)
                ·
                  refine ⟨902510029723454338850141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9626773650383512947734837 902510029723454338850141)
                  ·
                    refine ⟨338441261146295377068803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 902510029723454338850141 338441261146295377068803)
                    ·
                      rfl

theorem cell22_988668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_988668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988668 prefixEnd_988668 := by exact prefixLift 988668
  have htrace : WordTrace (prefixWord ++ tailWord_988668) baseStart_988668 baseEnd_988668 := by
    simpa [prefixWord, tailWord_988668, baseEnd_988668] using wordTrace_append hprefix tailTrace_988668
  have hstable : (prefixWord ++ tailWord_988668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988668).length < 2 ^ (prefixWord ++ tailWord_988668).sum := by decide
  have hdescent : baseEnd_988668 < baseStart_988668 := by decide
  rcases family_descends (prefixWord ++ tailWord_988668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988678 : List Nat := [6, 2, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_988678 : Nat := 118140960795 + 988678 * 2 ^ 59
def prefixEnd_988678 : Nat := 4983230072969 + 3 ^ 40 * 988678 * 2
def baseEnd_988678 : Nat := 338444684350658684318773

theorem tailTrace_988678 : CollatzResearch.WordTrace tailWord_988678 prefixEnd_988678 338444684350658684318773 := by
  unfold tailWord_988678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1126876534756122925139209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24040032741463955736303125 1126876534756122925139209)
  ·
    refine ⟨845157401067092193854407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1126876534756122925139209 845157401067092193854407)
    ·
      refine ⟨1267736101600638290781611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 845157401067092193854407 1267736101600638290781611)
      ·
        refine ⟨1901604152400957436172417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1267736101600638290781611 1901604152400957436172417)
        ·
          refine ⟨1426203114300718077129313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1901604152400957436172417 1426203114300718077129313)
          ·
            refine ⟨1069652335725538557846985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1426203114300718077129313 1069652335725538557846985)
            ·
              refine ⟨802239251794153918385239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1069652335725538557846985 802239251794153918385239)
              ·
                refine ⟨1203358877691230877577859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802239251794153918385239 1203358877691230877577859)
                ·
                  refine ⟨1805038316536846316366789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1203358877691230877577859 1805038316536846316366789)
                  ·
                    refine ⟨338444684350658684318773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1805038316536846316366789 338444684350658684318773)
                    ·
                      rfl

theorem cell22_988678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_988678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988678 prefixEnd_988678 := by exact prefixLift 988678
  have htrace : WordTrace (prefixWord ++ tailWord_988678) baseStart_988678 baseEnd_988678 := by
    simpa [prefixWord, tailWord_988678, baseEnd_988678] using wordTrace_append hprefix tailTrace_988678
  have hstable : (prefixWord ++ tailWord_988678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988678).length < 2 ^ (prefixWord ++ tailWord_988678).sum := by decide
  have hdescent : baseEnd_988678 < baseStart_988678 := by decide
  rcases family_descends (prefixWord ++ tailWord_988678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988681 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 7]
def baseStart_988681 : Nat := 118140960795 + 988681 * 2 ^ 59
def prefixEnd_988681 : Nat := 4983230072969 + 3 ^ 40 * 988681 * 2
def baseEnd_988681 : Nat := 112815237103989225497921

theorem tailTrace_988681 : CollatzResearch.WordTrace tailWord_988681 prefixEnd_988681 112815237103989225497921 := by
  unfold tailWord_988681
  simp only [CollatzResearch.WordTrace]
  refine ⟨36060158531185065116813897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24040105687456710077875931 36060158531185065116813897)
  ·
    refine ⟨27045118898388798837610423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36060158531185065116813897 27045118898388798837610423)
    ·
      refine ⟨40567678347583198256415635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27045118898388798837610423 40567678347583198256415635)
      ·
        refine ⟨60851517521374797384623453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40567678347583198256415635 60851517521374797384623453)
        ·
          refine ⟨22819319070515549019233795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60851517521374797384623453 22819319070515549019233795)
          ·
            refine ⟨34228978605773323528850693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22819319070515549019233795 34228978605773323528850693)
            ·
              refine ⟨6417933488582498161659505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34228978605773323528850693 6417933488582498161659505)
              ·
                refine ⟨4813450116436873621244629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6417933488582498161659505 4813450116436873621244629)
                ·
                  refine ⟨112815237103989225497921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4813450116436873621244629 112815237103989225497921)
                  ·
                    rfl

theorem cell22_988681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 7].length) (baseStart_988681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988681 prefixEnd_988681 := by exact prefixLift 988681
  have htrace : WordTrace (prefixWord ++ tailWord_988681) baseStart_988681 baseEnd_988681 := by
    simpa [prefixWord, tailWord_988681, baseEnd_988681] using wordTrace_append hprefix tailTrace_988681
  have hstable : (prefixWord ++ tailWord_988681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988681).length < 2 ^ (prefixWord ++ tailWord_988681).sum := by decide
  have hdescent : baseEnd_988681 < baseStart_988681 := by decide
  rcases family_descends (prefixWord ++ tailWord_988681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988884 : List Nat := [2, 4, 1, 3, 1, 2, 3, 1, 5]
def baseStart_988884 : Nat := 118140960795 + 988884 * 2 ^ 59
def prefixEnd_988884 : Nat := 4983230072969 + 3 ^ 40 * 988884 * 2
def baseEnd_988884 : Nat := 112838400786847604556047

theorem tailTrace_988884 : CollatzResearch.WordTrace tailWord_988884 prefixEnd_988884 112838400786847604556047 := by
  unfold tailWord_988884
  simp only [CollatzResearch.WordTrace]
  refine ⟨18033781274724815393226853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24045041699633087190969137 18033781274724815393226853)
  ·
    refine ⟨3381333989010902886230035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18033781274724815393226853 3381333989010902886230035)
    ·
      refine ⟨5072000983516354329345053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3381333989010902886230035 5072000983516354329345053)
      ·
        refine ⟨1902000368818632873504395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5072000983516354329345053 1902000368818632873504395)
        ·
          refine ⟨2853000553227949310256593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1902000368818632873504395 2853000553227949310256593)
          ·
            refine ⟨2139750414920961982692445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2853000553227949310256593 2139750414920961982692445)
            ·
              refine ⟨802406405595360743509667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2139750414920961982692445 802406405595360743509667)
              ·
                refine ⟨1203609608393041115264501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802406405595360743509667 1203609608393041115264501)
                ·
                  refine ⟨112838400786847604556047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1203609608393041115264501 112838400786847604556047)
                  ·
                    rfl

theorem cell22_988884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_988884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988884 prefixEnd_988884 := by exact prefixLift 988884
  have htrace : WordTrace (prefixWord ++ tailWord_988884) baseStart_988884 baseEnd_988884 := by
    simpa [prefixWord, tailWord_988884, baseEnd_988884] using wordTrace_append hprefix tailTrace_988884
  have hstable : (prefixWord ++ tailWord_988884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988884).length < 2 ^ (prefixWord ++ tailWord_988884).sum := by decide
  have hdescent : baseEnd_988884 < baseStart_988884 := by decide
  rcases family_descends (prefixWord ++ tailWord_988884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988910 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_988910 : Nat := 118140960795 + 988910 * 2 ^ 59
def prefixEnd_988910 : Nat := 4983230072969 + 3 ^ 40 * 988910 * 2
def baseEnd_988910 : Nat := 338524102691887412518061

theorem tailTrace_988910 : CollatzResearch.WordTrace tailWord_988910 prefixEnd_988910 338524102691887412518061 := by
  unfold tailWord_988910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4508563855919429653362523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24045673898236958151266789 4508563855919429653362523)
  ·
    refine ⟨6762845783879144480043785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4508563855919429653362523 6762845783879144480043785)
    ·
      refine ⟨5072134337909358360032839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6762845783879144480043785 5072134337909358360032839)
      ·
        refine ⟨7608201506864037540049259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5072134337909358360032839 7608201506864037540049259)
        ·
          refine ⟨11412302260296056310073889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7608201506864037540049259 11412302260296056310073889)
          ·
            refine ⟨8559226695222042232555417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11412302260296056310073889 8559226695222042232555417)
            ·
              refine ⟨6419420021416531674416563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8559226695222042232555417 6419420021416531674416563)
              ·
                refine ⟨9629130032124797511624845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6419420021416531674416563 9629130032124797511624845)
                ·
                  refine ⟨3610923762046799066859317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9629130032124797511624845 3610923762046799066859317)
                  ·
                    refine ⟨338524102691887412518061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3610923762046799066859317 338524102691887412518061)
                    ·
                      rfl

theorem cell22_988910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_988910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_988910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_988910 prefixEnd_988910 := by exact prefixLift 988910
  have htrace : WordTrace (prefixWord ++ tailWord_988910) baseStart_988910 baseEnd_988910 := by
    simpa [prefixWord, tailWord_988910, baseEnd_988910] using wordTrace_append hprefix tailTrace_988910
  have hstable : (prefixWord ++ tailWord_988910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988910).length < 2 ^ (prefixWord ++ tailWord_988910).sum := by decide
  have hdescent : baseEnd_988910 < baseStart_988910 := by decide
  rcases family_descends (prefixWord ++ tailWord_988910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989000 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 1, 7]
def baseStart_989000 : Nat := 118140960795 + 989000 * 2 ^ 59
def prefixEnd_989000 : Nat := 4983230072969 + 3 ^ 40 * 989000 * 2
def baseEnd_989000 : Nat := 338554911531157177767785

theorem tailTrace_989000 : CollatzResearch.WordTrace tailWord_989000 prefixEnd_989000 338554911531157177767785 := by
  unfold tailWord_989000
  simp only [CollatzResearch.WordTrace]
  refine ⟨18035896708514691298838227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24047862278019588398450969 18035896708514691298838227)
  ·
    refine ⟨27053845062772036948257341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18035896708514691298838227 27053845062772036948257341)
    ·
      refine ⟨10145191898539513855596503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27053845062772036948257341 10145191898539513855596503)
      ·
        refine ⟨15217787847809270783394755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10145191898539513855596503 15217787847809270783394755)
        ·
          refine ⟨22826681771713906175092133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15217787847809270783394755 22826681771713906175092133)
          ·
            refine ⟨4280002832196357407829775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22826681771713906175092133 4280002832196357407829775)
            ·
              refine ⟨6420004248294536111744663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4280002832196357407829775 6420004248294536111744663)
              ·
                refine ⟨9630006372441804167616995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6420004248294536111744663 9630006372441804167616995)
                ·
                  refine ⟨14445009558662706251425493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9630006372441804167616995 14445009558662706251425493)
                  ·
                    refine ⟨338554911531157177767785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14445009558662706251425493 338554911531157177767785)
                    ·
                      rfl

theorem cell22_989000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_989000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989000 prefixEnd_989000 := by exact prefixLift 989000
  have htrace : WordTrace (prefixWord ++ tailWord_989000) baseStart_989000 baseEnd_989000 := by
    simpa [prefixWord, tailWord_989000, baseEnd_989000] using wordTrace_append hprefix tailTrace_989000
  have hstable : (prefixWord ++ tailWord_989000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989000).length < 2 ^ (prefixWord ++ tailWord_989000).sum := by decide
  have hdescent : baseEnd_989000 < baseStart_989000 := by decide
  rcases family_descends (prefixWord ++ tailWord_989000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989066 : List Nat := [3, 1, 2, 4, 2, 1, 2, 2, 1, 4]
def baseStart_989066 : Nat := 118140960795 + 989066 * 2 ^ 59
def prefixEnd_989066 : Nat := 4983230072969 + 3 ^ 40 * 989066 * 2
def baseEnd_989066 : Nat := 338577504679955005617583

theorem tailTrace_989066 : CollatzResearch.WordTrace tailWord_989066 prefixEnd_989066 338577504679955005617583 := by
  unfold tailWord_989066
  simp only [CollatzResearch.WordTrace]
  refine ⟨9018550158697568967394763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24049467089860183913052701 9018550158697568967394763)
  ·
    refine ⟨13527825238046353451092145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9018550158697568967394763 13527825238046353451092145)
    ·
      refine ⟨10145868928534765088319109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13527825238046353451092145 10145868928534765088319109)
      ·
        refine ⟨1902350424100268454059833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10145868928534765088319109 1902350424100268454059833)
        ·
          refine ⟨1426762818075201340544875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1902350424100268454059833 1426762818075201340544875)
          ·
            refine ⟨2140144227112802010817313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426762818075201340544875 2140144227112802010817313)
            ·
              refine ⟨1605108170334601508112985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2140144227112802010817313 1605108170334601508112985)
              ·
                refine ⟨1203831127750951131084739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1605108170334601508112985 1203831127750951131084739)
                ·
                  refine ⟨1805746691626426696627109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1203831127750951131084739 1805746691626426696627109)
                  ·
                    refine ⟨338577504679955005617583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1805746691626426696627109 338577504679955005617583)
                    ·
                      rfl

theorem cell22_989066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_989066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989066 prefixEnd_989066 := by exact prefixLift 989066
  have htrace : WordTrace (prefixWord ++ tailWord_989066) baseStart_989066 baseEnd_989066 := by
    simpa [prefixWord, tailWord_989066, baseEnd_989066] using wordTrace_append hprefix tailTrace_989066
  have hstable : (prefixWord ++ tailWord_989066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989066).length < 2 ^ (prefixWord ++ tailWord_989066).sum := by decide
  have hdescent : baseEnd_989066 < baseStart_989066 := by decide
  rcases family_descends (prefixWord ++ tailWord_989066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989077 : List Nat := [1, 3, 2, 1, 1, 3, 2, 3, 2, 4]
def baseStart_989077 : Nat := 118140960795 + 989077 * 2 ^ 59
def prefixEnd_989077 : Nat := 4983230072969 + 3 ^ 40 * 989077 * 2
def baseEnd_989077 : Nat := 338581270204754643592549

theorem tailTrace_989077 : CollatzResearch.WordTrace tailWord_989077 prefixEnd_989077 338581270204754643592549 := by
  unfold tailWord_989077
  simp only [CollatzResearch.WordTrace]
  refine ⟨36074601837750424748229485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24049734558500283165486323 36074601837750424748229485)
  ·
    refine ⟨13527975689156409280586057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36074601837750424748229485 13527975689156409280586057)
    ·
      refine ⟨10145981766867306960439543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13527975689156409280586057 10145981766867306960439543)
      ·
        refine ⟨15218972650300960440659315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10145981766867306960439543 15218972650300960440659315)
        ·
          refine ⟨22828458975451440660988973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15218972650300960440659315 22828458975451440660988973)
          ·
            refine ⟨8560672115794290247870865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22828458975451440660988973 8560672115794290247870865)
            ·
              refine ⟨6420504086845717685903149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8560672115794290247870865 6420504086845717685903149)
              ·
                refine ⟨2407689032567144132213681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6420504086845717685903149 2407689032567144132213681)
                ·
                  refine ⟨1805766774425358099160261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2407689032567144132213681 1805766774425358099160261)
                  ·
                    refine ⟨338581270204754643592549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1805766774425358099160261 338581270204754643592549)
                    ·
                      rfl

theorem cell22_989077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_989077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989077 prefixEnd_989077 := by exact prefixLift 989077
  have htrace : WordTrace (prefixWord ++ tailWord_989077) baseStart_989077 baseEnd_989077 := by
    simpa [prefixWord, tailWord_989077, baseEnd_989077] using wordTrace_append hprefix tailTrace_989077
  have hstable : (prefixWord ++ tailWord_989077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989077).length < 2 ^ (prefixWord ++ tailWord_989077).sum := by decide
  have hdescent : baseEnd_989077 < baseStart_989077 := by decide
  rcases family_descends (prefixWord ++ tailWord_989077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989092 : List Nat := [2, 3, 1, 2, 1, 5, 8]
def baseStart_989092 : Nat := 118140960795 + 989092 * 2 ^ 59
def prefixEnd_989092 : Nat := 4983230072969 + 3 ^ 40 * 989092 * 2
def baseEnd_989092 : Nat := 12540237222640726091389

theorem tailTrace_989092 : CollatzResearch.WordTrace tailWord_989092 prefixEnd_989092 12540237222640726091389 := by
  unfold tailWord_989092
  simp only [CollatzResearch.WordTrace]
  refine ⟨18037574466348041155012765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24050099288464054873350353 18037574466348041155012765)
  ·
    refine ⟨6764090424880515433129787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18037574466348041155012765 6764090424880515433129787)
    ·
      refine ⟨10146135637320773149694681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6764090424880515433129787 10146135637320773149694681)
      ·
        refine ⟨7609601727990579862271011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10146135637320773149694681 7609601727990579862271011)
        ·
          refine ⟨11414402591985869793406517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7609601727990579862271011 11414402591985869793406517)
          ·
            refine ⟨1070100242998675293131861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11414402591985869793406517 1070100242998675293131861)
            ·
              refine ⟨12540237222640726091389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1070100242998675293131861 12540237222640726091389)
              ·
                rfl

theorem cell22_989092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 8].length) (baseStart_989092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989092 prefixEnd_989092 := by exact prefixLift 989092
  have htrace : WordTrace (prefixWord ++ tailWord_989092) baseStart_989092 baseEnd_989092 := by
    simpa [prefixWord, tailWord_989092, baseEnd_989092] using wordTrace_append hprefix tailTrace_989092
  have hstable : (prefixWord ++ tailWord_989092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989092).length < 2 ^ (prefixWord ++ tailWord_989092).sum := by decide
  have hdescent : baseEnd_989092 < baseStart_989092 := by decide
  rcases family_descends (prefixWord ++ tailWord_989092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989167 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 5, 4]
def baseStart_989167 : Nat := 118140960795 + 989167 * 2 ^ 59
def prefixEnd_989167 : Nat := 4983230072969 + 3 ^ 40 * 989167 * 2
def baseEnd_989167 : Nat := 338612079044024408842273

theorem tailTrace_989167 : CollatzResearch.WordTrace tailWord_989167 prefixEnd_989167 338612079044024408842273 := by
  unfold tailWord_989167
  simp only [CollatzResearch.WordTrace]
  refine ⟨36077884407424370119005755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24051922938282913412670503 36077884407424370119005755)
  ·
    refine ⟨54116826611136555178508633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36077884407424370119005755 54116826611136555178508633)
    ·
      refine ⟨40587619958352416383881475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54116826611136555178508633 40587619958352416383881475)
      ·
        refine ⟨60881429937528624575822213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40587619958352416383881475 60881429937528624575822213)
        ·
          refine ⟨11415268113286617107966665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60881429937528624575822213 11415268113286617107966665)
          ·
            refine ⟨8561451084964962830974999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11415268113286617107966665 8561451084964962830974999)
            ·
              refine ⟨12842176627447444246462499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8561451084964962830974999 12842176627447444246462499)
              ·
                refine ⟨19263264941171166369693749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12842176627447444246462499 19263264941171166369693749)
                ·
                  refine ⟨1805931088234796847158789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19263264941171166369693749 1805931088234796847158789)
                  ·
                    refine ⟨338612079044024408842273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1805931088234796847158789 338612079044024408842273)
                    ·
                      rfl

theorem cell22_989167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_989167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989167 prefixEnd_989167 := by exact prefixLift 989167
  have htrace : WordTrace (prefixWord ++ tailWord_989167) baseStart_989167 baseEnd_989167 := by
    simpa [prefixWord, tailWord_989167, baseEnd_989167] using wordTrace_append hprefix tailTrace_989167
  have hstable : (prefixWord ++ tailWord_989167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989167).length < 2 ^ (prefixWord ++ tailWord_989167).sum := by decide
  have hdescent : baseEnd_989167 < baseStart_989167 := by decide
  rcases family_descends (prefixWord ++ tailWord_989167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989169 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 2, 5]
def baseStart_989169 : Nat := 118140960795 + 989169 * 2 ^ 59
def prefixEnd_989169 : Nat := 4983230072969 + 3 ^ 40 * 989169 * 2
def baseEnd_989169 : Nat := 338612763684897070292267

theorem tailTrace_989169 : CollatzResearch.WordTrace tailWord_989169 prefixEnd_989169 338612763684897070292267 := by
  unfold tailWord_989169
  simp only [CollatzResearch.WordTrace]
  refine ⟨36077957353417124460578561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24051971568944749640385707 36077957353417124460578561)
  ·
    refine ⟨27058468015062843345433921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36077957353417124460578561 27058468015062843345433921)
    ·
      refine ⟨20293851011297132509075441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27058468015062843345433921 20293851011297132509075441)
      ·
        refine ⟨15220388258472849381806581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20293851011297132509075441 15220388258472849381806581)
        ·
          refine ⟨1426911399231829629544367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15220388258472849381806581 1426911399231829629544367)
          ·
            refine ⟨2140367098847744444316551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426911399231829629544367 2140367098847744444316551)
            ·
              refine ⟨3210550648271616666474827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2140367098847744444316551 3210550648271616666474827)
              ·
                refine ⟨4815825972407424999712241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3210550648271616666474827 4815825972407424999712241)
                ·
                  refine ⟨3611869479305568749784181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4815825972407424999712241 3611869479305568749784181)
                  ·
                    refine ⟨338612763684897070292267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3611869479305568749784181 338612763684897070292267)
                    ·
                      rfl

theorem cell22_989169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_989169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989169 prefixEnd_989169 := by exact prefixLift 989169
  have htrace : WordTrace (prefixWord ++ tailWord_989169) baseStart_989169 baseEnd_989169 := by
    simpa [prefixWord, tailWord_989169, baseEnd_989169] using wordTrace_append hprefix tailTrace_989169
  have hstable : (prefixWord ++ tailWord_989169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989169).length < 2 ^ (prefixWord ++ tailWord_989169).sum := by decide
  have hdescent : baseEnd_989169 < baseStart_989169 := by decide
  rcases family_descends (prefixWord ++ tailWord_989169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989242 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 1, 9]
def baseStart_989242 : Nat := 118140960795 + 989242 * 2 ^ 59
def prefixEnd_989242 : Nat := 4983230072969 + 3 ^ 40 * 989242 * 2
def baseEnd_989242 : Nat := 338637753076749213217043

theorem tailTrace_989242 : CollatzResearch.WordTrace tailWord_989242 prefixEnd_989242 338637753076749213217043 := by
  unfold tailWord_989242
  simp only [CollatzResearch.WordTrace]
  refine ⟨9020154970538164481996495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24053746588101771951990653 9020154970538164481996495)
  ·
    refine ⟨13530232455807246722994743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9020154970538164481996495 13530232455807246722994743)
    ·
      refine ⟨20295348683710870084492115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13530232455807246722994743 20295348683710870084492115)
      ·
        refine ⟨30443023025566305126738173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20295348683710870084492115 30443023025566305126738173)
        ·
          refine ⟨11416133634587364422526815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30443023025566305126738173 11416133634587364422526815)
          ·
            refine ⟨17124200451881046633790223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11416133634587364422526815 17124200451881046633790223)
            ·
              refine ⟨25686300677821569950685335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17124200451881046633790223 25686300677821569950685335)
              ·
                refine ⟨38529451016732354926028003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25686300677821569950685335 38529451016732354926028003)
                ·
                  refine ⟨57794176525098532389042005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38529451016732354926028003 57794176525098532389042005)
                  ·
                    refine ⟨338637753076749213217043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 57794176525098532389042005 338637753076749213217043)
                    ·
                      rfl

theorem cell22_989242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_989242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989242 prefixEnd_989242 := by exact prefixLift 989242
  have htrace : WordTrace (prefixWord ++ tailWord_989242) baseStart_989242 baseEnd_989242 := by
    simpa [prefixWord, tailWord_989242, baseEnd_989242] using wordTrace_append hprefix tailTrace_989242
  have hstable : (prefixWord ++ tailWord_989242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989242).length < 2 ^ (prefixWord ++ tailWord_989242).sum := by decide
  have hdescent : baseEnd_989242 < baseStart_989242 := by decide
  rcases family_descends (prefixWord ++ tailWord_989242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989282 : List Nat := [3, 3, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_989282 : Nat := 118140960795 + 989282 * 2 ^ 59
def prefixEnd_989282 : Nat := 4983230072969 + 3 ^ 40 * 989282 * 2
def baseEnd_989282 : Nat := 338651445894202442216921

theorem tailTrace_989282 : CollatzResearch.WordTrace tailWord_989282 prefixEnd_989282 338651445894202442216921 := by
  unfold tailWord_989282
  simp only [CollatzResearch.WordTrace]
  refine ⟨9020519700501936189860525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24054719201338496506294733 9020519700501936189860525)
  ·
    refine ⟨3382694887688226071197697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9020519700501936189860525 3382694887688226071197697)
    ·
      refine ⟨2537021165766169553398273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3382694887688226071197697 2537021165766169553398273)
      ·
        refine ⟨1902765874324627165048705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2537021165766169553398273 1902765874324627165048705)
        ·
          refine ⟨1427074405743470373786529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1902765874324627165048705 1427074405743470373786529)
          ·
            refine ⟨1070305804307602780339897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1427074405743470373786529 1070305804307602780339897)
            ·
              refine ⟨802729353230702085254923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070305804307602780339897 802729353230702085254923)
              ·
                refine ⟨1204094029846053127882385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802729353230702085254923 1204094029846053127882385)
                ·
                  refine ⟨903070522384539845911789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1204094029846053127882385 903070522384539845911789)
                  ·
                    refine ⟨338651445894202442216921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 903070522384539845911789 338651445894202442216921)
                    ·
                      rfl

theorem cell22_989282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_989282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989282 prefixEnd_989282 := by exact prefixLift 989282
  have htrace : WordTrace (prefixWord ++ tailWord_989282) baseStart_989282 baseEnd_989282 := by
    simpa [prefixWord, tailWord_989282, baseEnd_989282] using wordTrace_append hprefix tailTrace_989282
  have hstable : (prefixWord ++ tailWord_989282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989282).length < 2 ^ (prefixWord ++ tailWord_989282).sum := by decide
  have hdescent : baseEnd_989282 < baseStart_989282 := by decide
  rcases family_descends (prefixWord ++ tailWord_989282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989289 : List Nat := [1, 2, 1, 1, 1, 5, 3, 3, 5]
def baseStart_989289 : Nat := 118140960795 + 989289 * 2 ^ 59
def prefixEnd_989289 : Nat := 4983230072969 + 3 ^ 40 * 989289 * 2
def baseEnd_989289 : Nat := 112884614045752252430633

theorem tailTrace_989289 : CollatzResearch.WordTrace tailWord_989289 prefixEnd_989289 112884614045752252430633 := by
  unfold tailWord_989289
  simp only [CollatzResearch.WordTrace]
  refine ⟨36082334112982384954946921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24054889408654923303297947 36082334112982384954946921)
  ·
    refine ⟨27061750584736788716210191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36082334112982384954946921 27061750584736788716210191)
    ·
      refine ⟨40592625877105183074315287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27061750584736788716210191 40592625877105183074315287)
      ·
        refine ⟨60888938815657774611472931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40592625877105183074315287 60888938815657774611472931)
        ·
          refine ⟨91333408223486661917209397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60888938815657774611472931 91333408223486661917209397)
          ·
            refine ⟨8562507020951874554738381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91333408223486661917209397 8562507020951874554738381)
            ·
              refine ⟨3210940132856952958026893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8562507020951874554738381 3210940132856952958026893)
              ·
                refine ⟨1204102549821357359260085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3210940132856952958026893 1204102549821357359260085)
                ·
                  refine ⟨112884614045752252430633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1204102549821357359260085 112884614045752252430633)
                  ·
                    rfl

theorem cell22_989289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 5].length) (baseStart_989289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989289 prefixEnd_989289 := by exact prefixLift 989289
  have htrace : WordTrace (prefixWord ++ tailWord_989289) baseStart_989289 baseEnd_989289 := by
    simpa [prefixWord, tailWord_989289, baseEnd_989289] using wordTrace_append hprefix tailTrace_989289
  have hstable : (prefixWord ++ tailWord_989289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989289).length < 2 ^ (prefixWord ++ tailWord_989289).sum := by decide
  have hdescent : baseEnd_989289 < baseStart_989289 := by decide
  rcases family_descends (prefixWord ++ tailWord_989289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989398 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_989398 : Nat := 118140960795 + 989398 * 2 ^ 59
def prefixEnd_989398 : Nat := 4983230072969 + 3 ^ 40 * 989398 * 2
def baseEnd_989398 : Nat := 338691155064816806316565

theorem tailTrace_989398 : CollatzResearch.WordTrace tailWord_989398 prefixEnd_989398 338691155064816806316565 := by
  unfold tailWord_989398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2255394354349218535666553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24057539779724997713776565 2255394354349218535666553)
  ·
    refine ⟨1691545765761913901749915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2255394354349218535666553 1691545765761913901749915)
    ·
      refine ⟨2537318648642870852624873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1691545765761913901749915 2537318648642870852624873)
      ·
        refine ⟨1902988986482153139468655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2537318648642870852624873 1902988986482153139468655)
        ·
          refine ⟨2854483479723229709202983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1902988986482153139468655 2854483479723229709202983)
          ·
            refine ⟨4281725219584844563804475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854483479723229709202983 4281725219584844563804475)
            ·
              refine ⟨6422587829377266845706713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4281725219584844563804475 6422587829377266845706713)
              ·
                refine ⟨4816940872032950134280035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6422587829377266845706713 4816940872032950134280035)
                ·
                  refine ⟨7225411308049425201420053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4816940872032950134280035 7225411308049425201420053)
                  ·
                    refine ⟨338691155064816806316565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7225411308049425201420053 338691155064816806316565)
                    ·
                      rfl

theorem cell22_989398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_989398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989398 prefixEnd_989398 := by exact prefixLift 989398
  have htrace : WordTrace (prefixWord ++ tailWord_989398) baseStart_989398 baseEnd_989398 := by
    simpa [prefixWord, tailWord_989398, baseEnd_989398] using wordTrace_append hprefix tailTrace_989398
  have hstable : (prefixWord ++ tailWord_989398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989398).length < 2 ^ (prefixWord ++ tailWord_989398).sum := by decide
  have hdescent : baseEnd_989398 < baseStart_989398 := by decide
  rcases family_descends (prefixWord ++ tailWord_989398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989400 : List Nat := [2, 1, 2, 2, 4, 2, 3, 1, 2, 3]
def baseStart_989400 : Nat := 118140960795 + 989400 * 2 ^ 59
def prefixEnd_989400 : Nat := 4983230072969 + 3 ^ 40 * 989400 * 2
def baseEnd_989400 : Nat := 338691839705689467766559

theorem tailTrace_989400 : CollatzResearch.WordTrace tailWord_989400 prefixEnd_989400 338691839705689467766559 := by
  unfold tailWord_989400
  simp only [CollatzResearch.WordTrace]
  refine ⟨18043191307790125456118827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24057588410386833941491769 18043191307790125456118827)
  ·
    refine ⟨27064786961685188184178241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18043191307790125456118827 27064786961685188184178241)
    ·
      refine ⟨20298590221263891138133681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27064786961685188184178241 20298590221263891138133681)
      ·
        refine ⟨15223942665947918353600261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20298590221263891138133681 15223942665947918353600261)
        ·
          refine ⟨2854489249865234691300049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15223942665947918353600261 2854489249865234691300049)
          ·
            refine ⟨2140866937398926018475037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2854489249865234691300049 2140866937398926018475037)
            ·
              refine ⟨802825101524597256928139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2140866937398926018475037 802825101524597256928139)
              ·
                refine ⟨1204237652286895885392209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802825101524597256928139 1204237652286895885392209)
                ·
                  refine ⟨903178239215171914044157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1204237652286895885392209 903178239215171914044157)
                  ·
                    refine ⟨338691839705689467766559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 903178239215171914044157 338691839705689467766559)
                    ·
                      rfl

theorem cell22_989400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 2, 3].length) (baseStart_989400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989400 prefixEnd_989400 := by exact prefixLift 989400
  have htrace : WordTrace (prefixWord ++ tailWord_989400) baseStart_989400 baseEnd_989400 := by
    simpa [prefixWord, tailWord_989400, baseEnd_989400] using wordTrace_append hprefix tailTrace_989400
  have hstable : (prefixWord ++ tailWord_989400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989400).length < 2 ^ (prefixWord ++ tailWord_989400).sum := by decide
  have hdescent : baseEnd_989400 < baseStart_989400 := by decide
  rcases family_descends (prefixWord ++ tailWord_989400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989413 : List Nat := [1, 3, 1, 4, 2, 3, 2, 6]
def baseStart_989413 : Nat := 118140960795 + 989413 * 2 ^ 59
def prefixEnd_989413 : Nat := 4983230072969 + 3 ^ 40 * 989413 * 2
def baseEnd_989413 : Nat := 37632921096817974132391

theorem tailTrace_989413 : CollatzResearch.WordTrace tailWord_989413 prefixEnd_989413 37632921096817974132391 := by
  unfold tailWord_989413
  simp only [CollatzResearch.WordTrace]
  refine ⟨36086856764533154132460893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24057904509688769421640595 36086856764533154132460893)
  ·
    refine ⟨13532571286699932799672835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36086856764533154132460893 13532571286699932799672835)
    ·
      refine ⟨20298856930049899199509253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13532571286699932799672835 20298856930049899199509253)
      ·
        refine ⟨3806035674384356099907985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20298856930049899199509253 3806035674384356099907985)
        ·
          refine ⟨2854526755788267074930989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3806035674384356099907985 2854526755788267074930989)
          ·
            refine ⟨1070447533420600153099121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2854526755788267074930989 1070447533420600153099121)
            ·
              refine ⟨802835650065450114824341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070447533420600153099121 802835650065450114824341)
              ·
                refine ⟨37632921096817974132391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 802835650065450114824341 37632921096817974132391)
                ·
                  rfl

theorem cell22_989413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 6].length) (baseStart_989413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989413 prefixEnd_989413 := by exact prefixLift 989413
  have htrace : WordTrace (prefixWord ++ tailWord_989413) baseStart_989413 baseEnd_989413 := by
    simpa [prefixWord, tailWord_989413, baseEnd_989413] using wordTrace_append hprefix tailTrace_989413
  have hstable : (prefixWord ++ tailWord_989413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989413).length < 2 ^ (prefixWord ++ tailWord_989413).sum := by decide
  have hdescent : baseEnd_989413 < baseStart_989413 := by decide
  rcases family_descends (prefixWord ++ tailWord_989413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989441 : List Nat := [1, 2, 4, 1, 1, 2, 2, 4, 5]
def baseStart_989441 : Nat := 118140960795 + 989441 * 2 ^ 59
def prefixEnd_989441 : Nat := 4983230072969 + 3 ^ 40 * 989441 * 2
def baseEnd_989441 : Nat := 112901958281193009163811

theorem tailTrace_989441 : CollatzResearch.WordTrace tailWord_989441 prefixEnd_989441 112901958281193009163811 := by
  unfold tailWord_989441
  simp only [CollatzResearch.WordTrace]
  refine ⟨36087878008431714914480177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24058585338954476609653451 36087878008431714914480177)
  ·
    refine ⟨27065908506323786185860133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36087878008431714914480177 27065908506323786185860133)
    ·
      refine ⟨5074857844935709909848775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27065908506323786185860133 5074857844935709909848775)
      ·
        refine ⟨7612286767403564864773163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5074857844935709909848775 7612286767403564864773163)
        ·
          refine ⟨11418430151105347297159745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7612286767403564864773163 11418430151105347297159745)
          ·
            refine ⟨8563822613329010472869809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11418430151105347297159745 8563822613329010472869809)
            ·
              refine ⟨6422866959996757854652357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8563822613329010472869809 6422866959996757854652357)
              ·
                refine ⟨1204287554999392097747317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6422866959996757854652357 1204287554999392097747317)
                ·
                  refine ⟨112901958281193009163811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1204287554999392097747317 112901958281193009163811)
                  ·
                    rfl

theorem cell22_989441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 5].length) (baseStart_989441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989441 prefixEnd_989441 := by exact prefixLift 989441
  have htrace : WordTrace (prefixWord ++ tailWord_989441) baseStart_989441 baseEnd_989441 := by
    simpa [prefixWord, tailWord_989441, baseEnd_989441] using wordTrace_append hprefix tailTrace_989441
  have hstable : (prefixWord ++ tailWord_989441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989441).length < 2 ^ (prefixWord ++ tailWord_989441).sum := by decide
  have hdescent : baseEnd_989441 < baseStart_989441 := by decide
  rcases family_descends (prefixWord ++ tailWord_989441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989503 : List Nat := [1, 1, 2, 2, 4, 1, 3, 4, 4]
def baseStart_989503 : Nat := 118140960795 + 989503 * 2 ^ 59
def prefixEnd_989503 : Nat := 4983230072969 + 3 ^ 40 * 989503 * 2
def baseEnd_989503 : Nat := 112909032903543844147081

theorem tailTrace_989503 : CollatzResearch.WordTrace tailWord_989503 prefixEnd_989503 112909032903543844147081 := by
  unfold tailWord_989503
  simp only [CollatzResearch.WordTrace]
  refine ⟨36090139334207099503237163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24060092889471399668824775 36090139334207099503237163)
  ·
    refine ⟨54135209001310649254855745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36090139334207099503237163 54135209001310649254855745)
    ·
      refine ⟨40601406750982986941141809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54135209001310649254855745 40601406750982986941141809)
      ·
        refine ⟨30451055063237240205856357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40601406750982986941141809 30451055063237240205856357)
        ·
          refine ⟨5709572824356982538598067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30451055063237240205856357 5709572824356982538598067)
          ·
            refine ⟨8564359236535473807897101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5709572824356982538598067 8564359236535473807897101)
            ·
              refine ⟨3211634713700802677961413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8564359236535473807897101 3211634713700802677961413)
              ·
                refine ⟨602181508818900502117765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3211634713700802677961413 602181508818900502117765)
                ·
                  refine ⟨112909032903543844147081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 602181508818900502117765 112909032903543844147081)
                  ·
                    rfl

theorem cell22_989503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 4].length) (baseStart_989503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989503 prefixEnd_989503 := by exact prefixLift 989503
  have htrace : WordTrace (prefixWord ++ tailWord_989503) baseStart_989503 baseEnd_989503 := by
    simpa [prefixWord, tailWord_989503, baseEnd_989503] using wordTrace_append hprefix tailTrace_989503
  have hstable : (prefixWord ++ tailWord_989503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989503).length < 2 ^ (prefixWord ++ tailWord_989503).sum := by decide
  have hdescent : baseEnd_989503 < baseStart_989503 := by decide
  rcases family_descends (prefixWord ++ tailWord_989503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989516 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 1, 6]
def baseStart_989516 : Nat := 118140960795 + 989516 * 2 ^ 59
def prefixEnd_989516 : Nat := 4983230072969 + 3 ^ 40 * 989516 * 2
def baseEnd_989516 : Nat := 338731548876303831866203

theorem tailTrace_989516 : CollatzResearch.WordTrace tailWord_989516 prefixEnd_989516 338731548876303831866203 := by
  unfold tailWord_989516
  simp only [CollatzResearch.WordTrace]
  refine ⟨18045306741580001361730201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24060408988773335148973601 18045306741580001361730201)
  ·
    refine ⟨13533980056185001021297651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18045306741580001361730201 13533980056185001021297651)
    ·
      refine ⟨20300970084277501531946477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13533980056185001021297651 20300970084277501531946477)
      ·
        refine ⟨7612863781604063074479929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20300970084277501531946477 7612863781604063074479929)
        ·
          refine ⟨5709647836203047305859947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7612863781604063074479929 5709647836203047305859947)
          ·
            refine ⟨8564471754304570958789921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5709647836203047305859947 8564471754304570958789921)
            ·
              refine ⟨6423353815728428219092441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8564471754304570958789921 6423353815728428219092441)
              ·
                refine ⟨4817515361796321164319331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6423353815728428219092441 4817515361796321164319331)
                ·
                  refine ⟨7226273042694481746478997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4817515361796321164319331 7226273042694481746478997)
                  ·
                    refine ⟨338731548876303831866203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7226273042694481746478997 338731548876303831866203)
                    ·
                      rfl

theorem cell22_989516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_989516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989516 prefixEnd_989516 := by exact prefixLift 989516
  have htrace : WordTrace (prefixWord ++ tailWord_989516) baseStart_989516 baseEnd_989516 := by
    simpa [prefixWord, tailWord_989516, baseEnd_989516] using wordTrace_append hprefix tailTrace_989516
  have hstable : (prefixWord ++ tailWord_989516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989516).length < 2 ^ (prefixWord ++ tailWord_989516).sum := by decide
  have hdescent : baseEnd_989516 < baseStart_989516 := by decide
  rcases family_descends (prefixWord ++ tailWord_989516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989563 : List Nat := [1, 1, 1, 1, 1, 7, 1, 3, 3, 3]
def baseStart_989563 : Nat := 118140960795 + 989563 * 2 ^ 59
def prefixEnd_989563 : Nat := 4983230072969 + 3 ^ 40 * 989563 * 2
def baseEnd_989563 : Nat := 338747637936811375941059

theorem tailTrace_989563 : CollatzResearch.WordTrace tailWord_989563 prefixEnd_989563 338747637936811375941059 := by
  unfold tailWord_989563
  simp only [CollatzResearch.WordTrace]
  refine ⟨36092327713989729750421343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24061551809326486500280895 36092327713989729750421343)
  ·
    refine ⟨54138491570984594625632015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36092327713989729750421343 54138491570984594625632015)
    ·
      refine ⟨81207737356476891938448023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54138491570984594625632015 81207737356476891938448023)
      ·
        refine ⟨121811606034715337907672035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81207737356476891938448023 121811606034715337907672035)
        ·
          refine ⟨182717409052073006861508053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121811606034715337907672035 182717409052073006861508053)
          ·
            refine ⟨4282439274657961098316595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 182717409052073006861508053 4282439274657961098316595)
            ·
              refine ⟨6423658911986941647474893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4282439274657961098316595 6423658911986941647474893)
              ·
                refine ⟨2408872091995103117803085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6423658911986941647474893 2408872091995103117803085)
                ·
                  refine ⟨903327034498163669176157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2408872091995103117803085 903327034498163669176157)
                  ·
                    refine ⟨338747637936811375941059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 903327034498163669176157 338747637936811375941059)
                    ·
                      rfl

theorem cell22_989563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 3].length) (baseStart_989563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989563 prefixEnd_989563 := by exact prefixLift 989563
  have htrace : WordTrace (prefixWord ++ tailWord_989563) baseStart_989563 baseEnd_989563 := by
    simpa [prefixWord, tailWord_989563, baseEnd_989563] using wordTrace_append hprefix tailTrace_989563
  have hstable : (prefixWord ++ tailWord_989563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989563).length < 2 ^ (prefixWord ++ tailWord_989563).sum := by decide
  have hdescent : baseEnd_989563 < baseStart_989563 := by decide
  rcases family_descends (prefixWord ++ tailWord_989563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989591 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 1, 7]
def baseStart_989591 : Nat := 118140960795 + 989591 * 2 ^ 59
def prefixEnd_989591 : Nat := 4983230072969 + 3 ^ 40 * 989591 * 2
def baseEnd_989591 : Nat := 338757222909028636240973

theorem tailTrace_989591 : CollatzResearch.WordTrace tailWord_989591 prefixEnd_989591 338757222909028636240973 := by
  unfold tailWord_989591
  simp only [CollatzResearch.WordTrace]
  refine ⟨36093348957888290532440627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24062232638592193688293751 36093348957888290532440627)
  ·
    refine ⟨54140023436832435798660941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36093348957888290532440627 54140023436832435798660941)
    ·
      refine ⟨20302508788812163424497853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54140023436832435798660941 20302508788812163424497853)
      ·
        refine ⟨7613440795804561284186695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20302508788812163424497853 7613440795804561284186695)
        ·
          refine ⟨11420161193706841926280043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7613440795804561284186695 11420161193706841926280043)
          ·
            refine ⟨17130241790560262889420065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11420161193706841926280043 17130241790560262889420065)
            ·
              refine ⟨12847681342920197167065049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17130241790560262889420065 12847681342920197167065049)
              ·
                refine ⟨9635761007190147875298787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12847681342920197167065049 9635761007190147875298787)
                ·
                  refine ⟨14453641510785221812948181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9635761007190147875298787 14453641510785221812948181)
                  ·
                    refine ⟨338757222909028636240973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14453641510785221812948181 338757222909028636240973)
                    ·
                      rfl

theorem cell22_989591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_989591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989591 prefixEnd_989591 := by exact prefixLift 989591
  have htrace : WordTrace (prefixWord ++ tailWord_989591) baseStart_989591 baseEnd_989591 := by
    simpa [prefixWord, tailWord_989591, baseEnd_989591] using wordTrace_append hprefix tailTrace_989591
  have hstable : (prefixWord ++ tailWord_989591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989591).length < 2 ^ (prefixWord ++ tailWord_989591).sum := by decide
  have hdescent : baseEnd_989591 < baseStart_989591 := by decide
  rcases family_descends (prefixWord ++ tailWord_989591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989640 : List Nat := [2, 1, 3, 1, 3, 2, 3, 2, 1, 4]
def baseStart_989640 : Nat := 118140960795 + 989640 * 2 ^ 59
def prefixEnd_989640 : Nat := 4983230072969 + 3 ^ 40 * 989640 * 2
def baseEnd_989640 : Nat := 338773996610408841765823

theorem tailTrace_989640 : CollatzResearch.WordTrace tailWord_989640 prefixEnd_989640 338773996610408841765823 := by
  unfold tailWord_989640
  simp only [CollatzResearch.WordTrace]
  refine ⟨18047568067355385950487187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24063424089807181267316249 18047568067355385950487187)
  ·
    refine ⟨27071352101033078925730781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18047568067355385950487187 27071352101033078925730781)
    ·
      refine ⟨10151757037887404597149043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27071352101033078925730781 10151757037887404597149043)
      ·
        refine ⟨15227635556831106895723565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10151757037887404597149043 15227635556831106895723565)
        ·
          refine ⟨5710363333811665085896337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15227635556831106895723565 5710363333811665085896337)
          ·
            refine ⟨4282772500358748814422253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5710363333811665085896337 4282772500358748814422253)
            ·
              refine ⟨1606039687634530805408345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4282772500358748814422253 1606039687634530805408345)
              ·
                refine ⟨1204529765725898104056259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1606039687634530805408345 1204529765725898104056259)
                ·
                  refine ⟨1806794648588847156084389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1204529765725898104056259 1806794648588847156084389)
                  ·
                    refine ⟨338773996610408841765823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1806794648588847156084389 338773996610408841765823)
                    ·
                      rfl

theorem cell22_989640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_989640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989640 prefixEnd_989640 := by exact prefixLift 989640
  have htrace : WordTrace (prefixWord ++ tailWord_989640) baseStart_989640 baseEnd_989640 := by
    simpa [prefixWord, tailWord_989640, baseEnd_989640] using wordTrace_append hprefix tailTrace_989640
  have hstable : (prefixWord ++ tailWord_989640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989640).length < 2 ^ (prefixWord ++ tailWord_989640).sum := by decide
  have hdescent : baseEnd_989640 < baseStart_989640 := by decide
  rcases family_descends (prefixWord ++ tailWord_989640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989651 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 7, 6]
def baseStart_989651 : Nat := 118140960795 + 989651 * 2 ^ 59
def prefixEnd_989651 : Nat := 4983230072969 + 3 ^ 40 * 989651 * 2
def baseEnd_989651 : Nat := 338777762135208479740789

theorem tailTrace_989651 : CollatzResearch.WordTrace tailWord_989651 prefixEnd_989651 338777762135208479740789 := by
  unfold tailWord_989651
  simp only [CollatzResearch.WordTrace]
  refine ⟨36095537337670920779624807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24063691558447280519749871 36095537337670920779624807)
  ·
    refine ⟨54143306006506381169437211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36095537337670920779624807 54143306006506381169437211)
    ·
      refine ⟨81214959009759571754155817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54143306006506381169437211 81214959009759571754155817)
      ·
        refine ⟨60911219257319678815616863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81214959009759571754155817 60911219257319678815616863)
        ·
          refine ⟨91366828885979518223425295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60911219257319678815616863 91366828885979518223425295)
          ·
            refine ⟨137050243328969277335137943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91366828885979518223425295 137050243328969277335137943)
            ·
              refine ⟨205575364993453916002706915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137050243328969277335137943 205575364993453916002706915)
              ·
                refine ⟨308363047490180874004060373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205575364993453916002706915 308363047490180874004060373)
                ·
                  refine ⟨7227258925551114234470165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 308363047490180874004060373 7227258925551114234470165)
                  ·
                    refine ⟨338777762135208479740789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7227258925551114234470165 338777762135208479740789)
                    ·
                      rfl

theorem cell22_989651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 6].length) (baseStart_989651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989651 prefixEnd_989651 := by exact prefixLift 989651
  have htrace : WordTrace (prefixWord ++ tailWord_989651) baseStart_989651 baseEnd_989651 := by
    simpa [prefixWord, tailWord_989651, baseEnd_989651] using wordTrace_append hprefix tailTrace_989651
  have hstable : (prefixWord ++ tailWord_989651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989651).length < 2 ^ (prefixWord ++ tailWord_989651).sum := by decide
  have hdescent : baseEnd_989651 < baseStart_989651 := by decide
  rcases family_descends (prefixWord ++ tailWord_989651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989653 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 3, 5]
def baseStart_989653 : Nat := 118140960795 + 989653 * 2 ^ 59
def prefixEnd_989653 : Nat := 4983230072969 + 3 ^ 40 * 989653 * 2
def baseEnd_989653 : Nat := 338778446776081141190783

theorem tailTrace_989653 : CollatzResearch.WordTrace tailWord_989653 prefixEnd_989653 338778446776081141190783 := by
  unfold tailWord_989653
  simp only [CollatzResearch.WordTrace]
  refine ⟨36095610283663675121197613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24063740189109116747465075 36095610283663675121197613)
  ·
    refine ⟨13535853856373878170449105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36095610283663675121197613 13535853856373878170449105)
    ·
      refine ⟨10151890392280408627836829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13535853856373878170449105 10151890392280408627836829)
      ·
        refine ⟨3806958897105153235438811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10151890392280408627836829 3806958897105153235438811)
        ·
          refine ⟨5710438345657729853158217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3806958897105153235438811 5710438345657729853158217)
          ·
            refine ⟨4282828759243297389868663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5710438345657729853158217 4282828759243297389868663)
            ·
              refine ⟨6424243138864946084802995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4282828759243297389868663 6424243138864946084802995)
              ·
                refine ⟨9636364708297419127204493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6424243138864946084802995 9636364708297419127204493)
                ·
                  refine ⟨3613636765611532172701685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9636364708297419127204493 3613636765611532172701685)
                  ·
                    refine ⟨338778446776081141190783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3613636765611532172701685 338778446776081141190783)
                    ·
                      rfl

theorem cell22_989653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_989653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989653 prefixEnd_989653 := by exact prefixLift 989653
  have htrace : WordTrace (prefixWord ++ tailWord_989653) baseStart_989653 baseEnd_989653 := by
    simpa [prefixWord, tailWord_989653, baseEnd_989653] using wordTrace_append hprefix tailTrace_989653
  have hstable : (prefixWord ++ tailWord_989653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989653).length < 2 ^ (prefixWord ++ tailWord_989653).sum := by decide
  have hdescent : baseEnd_989653 < baseStart_989653 := by decide
  rcases family_descends (prefixWord ++ tailWord_989653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989672 : List Nat := [2, 1, 4, 1, 1, 3, 4, 2, 4]
def baseStart_989672 : Nat := 118140960795 + 989672 * 2 ^ 59
def prefixEnd_989672 : Nat := 4983230072969 + 3 ^ 40 * 989672 * 2
def baseEnd_989672 : Nat := 112928316954790474988575

theorem tailTrace_989672 : CollatzResearch.WordTrace tailWord_989672 prefixEnd_989672 112928316954790474988575 := by
  unfold tailWord_989672
  simp only [CollatzResearch.WordTrace]
  refine ⟨18048151635297420683069635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24064202180396560910759513 18048151635297420683069635)
  ·
    refine ⟨27072227452946131024604453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18048151635297420683069635 27072227452946131024604453)
    ·
      refine ⟨5076042647427399567113335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27072227452946131024604453 5076042647427399567113335)
      ·
        refine ⟨7614063971141099350670003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5076042647427399567113335 7614063971141099350670003)
        ·
          refine ⟨11421095956711649026005005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7614063971141099350670003 11421095956711649026005005)
          ·
            refine ⟨4282910983766868384751877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11421095956711649026005005 4282910983766868384751877)
            ·
              refine ⟨803045809456287822140977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4282910983766868384751877 803045809456287822140977)
              ·
                refine ⟨602284357092215866605733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 803045809456287822140977 602284357092215866605733)
                ·
                  refine ⟨112928316954790474988575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 602284357092215866605733 112928316954790474988575)
                  ·
                    rfl

theorem cell22_989672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 4].length) (baseStart_989672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989672 prefixEnd_989672 := by exact prefixLift 989672
  have htrace : WordTrace (prefixWord ++ tailWord_989672) baseStart_989672 baseEnd_989672 := by
    simpa [prefixWord, tailWord_989672, baseEnd_989672] using wordTrace_append hprefix tailTrace_989672
  have hstable : (prefixWord ++ tailWord_989672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989672).length < 2 ^ (prefixWord ++ tailWord_989672).sum := by decide
  have hdescent : baseEnd_989672 < baseStart_989672 := by decide
  rcases family_descends (prefixWord ++ tailWord_989672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989775 : List Nat := [1, 1, 2, 1, 1, 2, 6, 3, 1, 4]
def baseStart_989775 : Nat := 118140960795 + 989775 * 2 ^ 59
def prefixEnd_989775 : Nat := 4983230072969 + 3 ^ 40 * 989775 * 2
def baseEnd_989775 : Nat := 338820209869313489640409

theorem tailTrace_989775 : CollatzResearch.WordTrace tailWord_989775 prefixEnd_989775 338820209869313489640409 := by
  unfold tailWord_989775
  simp only [CollatzResearch.WordTrace]
  refine ⟨36100059989221689957138779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24066706659481126638092519 36100059989221689957138779)
  ·
    refine ⟨54150089983832534935708169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36100059989221689957138779 54150089983832534935708169)
    ·
      refine ⟨40612567487874401201781127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54150089983832534935708169 40612567487874401201781127)
      ·
        refine ⟨60918851231811601802671691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40612567487874401201781127 60918851231811601802671691)
        ·
          refine ⟨91378276847717402704007537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60918851231811601802671691 91378276847717402704007537)
          ·
            refine ⟨68533707635788052028005653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91378276847717402704007537 68533707635788052028005653)
            ·
              refine ⟨3212517545427564938812765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68533707635788052028005653 3212517545427564938812765)
              ·
                refine ⟨1204694079535336852054787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3212517545427564938812765 1204694079535336852054787)
                ·
                  refine ⟨1807041119303005278082181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1204694079535336852054787 1807041119303005278082181)
                  ·
                    refine ⟨338820209869313489640409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1807041119303005278082181 338820209869313489640409)
                    ·
                      rfl

theorem cell22_989775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 4].length) (baseStart_989775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989775 prefixEnd_989775 := by exact prefixLift 989775
  have htrace : WordTrace (prefixWord ++ tailWord_989775) baseStart_989775 baseEnd_989775 := by
    simpa [prefixWord, tailWord_989775, baseEnd_989775] using wordTrace_append hprefix tailTrace_989775
  have hstable : (prefixWord ++ tailWord_989775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989775).length < 2 ^ (prefixWord ++ tailWord_989775).sum := by decide
  have hdescent : baseEnd_989775 < baseStart_989775 := by decide
  rcases family_descends (prefixWord ++ tailWord_989775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989803 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 1, 6]
def baseStart_989803 : Nat := 118140960795 + 989803 * 2 ^ 59
def prefixEnd_989803 : Nat := 4983230072969 + 3 ^ 40 * 989803 * 2
def baseEnd_989803 : Nat := 338829794841530749940323

theorem tailTrace_989803 : CollatzResearch.WordTrace tailWord_989803 prefixEnd_989803 338829794841530749940323 := by
  unfold tailWord_989803
  simp only [CollatzResearch.WordTrace]
  refine ⟨36101081233120250739158063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24067387488746833826105375 36101081233120250739158063)
  ·
    refine ⟨54151621849680376108737095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36101081233120250739158063 54151621849680376108737095)
    ·
      refine ⟨81227432774520564163105643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54151621849680376108737095 81227432774520564163105643)
      ·
        refine ⟨121841149161780846244658465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81227432774520564163105643 121841149161780846244658465)
        ·
          refine ⟨91380861871335634683493849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121841149161780846244658465 91380861871335634683493849)
          ·
            refine ⟨68535646403501726012620387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91380861871335634683493849 68535646403501726012620387)
            ·
              refine ⟨102803469605252589018930581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68535646403501726012620387 102803469605252589018930581)
              ·
                refine ⟨4818912637746215110262371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102803469605252589018930581 4818912637746215110262371)
                ·
                  refine ⟨7228368956619322665393557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4818912637746215110262371 7228368956619322665393557)
                  ·
                    refine ⟨338829794841530749940323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7228368956619322665393557 338829794841530749940323)
                    ·
                      rfl

theorem cell22_989803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 6].length) (baseStart_989803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989803 prefixEnd_989803 := by exact prefixLift 989803
  have htrace : WordTrace (prefixWord ++ tailWord_989803) baseStart_989803 baseEnd_989803 := by
    simpa [prefixWord, tailWord_989803, baseEnd_989803] using wordTrace_append hprefix tailTrace_989803
  have hstable : (prefixWord ++ tailWord_989803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989803).length < 2 ^ (prefixWord ++ tailWord_989803).sum := by decide
  have hdescent : baseEnd_989803 < baseStart_989803 := by decide
  rcases family_descends (prefixWord ++ tailWord_989803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989820 : List Nat := [2, 2, 2, 1, 1, 2, 3, 3, 2, 4]
def baseStart_989820 : Nat := 118140960795 + 989820 * 2 ^ 59
def prefixEnd_989820 : Nat := 4983230072969 + 3 ^ 40 * 989820 * 2
def baseEnd_989820 : Nat := 338835614288948372265271

theorem tailTrace_989820 : CollatzResearch.WordTrace tailWord_989820 prefixEnd_989820 338835614288948372265271 := by
  unfold tailWord_989820
  simp only [CollatzResearch.WordTrace]
  refine ⟨18050850637029331321263457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24067800849372441761684609 18050850637029331321263457)
  ·
    refine ⟨13538137977771998490947593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18050850637029331321263457 13538137977771998490947593)
    ·
      refine ⟨10153603483328998868210695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13538137977771998490947593 10153603483328998868210695)
      ·
        refine ⟨15230405224993498302316043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10153603483328998868210695 15230405224993498302316043)
        ·
          refine ⟨22845607837490247453474065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15230405224993498302316043 22845607837490247453474065)
          ·
            refine ⟨17134205878117685590105549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22845607837490247453474065 17134205878117685590105549)
            ·
              refine ⟨6425327204294132096289581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17134205878117685590105549 6425327204294132096289581)
              ·
                refine ⟨2409497701610299536108593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6425327204294132096289581 2409497701610299536108593)
                ·
                  refine ⟨1807123276207724652081445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2409497701610299536108593 1807123276207724652081445)
                  ·
                    refine ⟨338835614288948372265271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1807123276207724652081445 338835614288948372265271)
                    ·
                      rfl

theorem cell22_989820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_989820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989820 prefixEnd_989820 := by exact prefixLift 989820
  have htrace : WordTrace (prefixWord ++ tailWord_989820) baseStart_989820 baseEnd_989820 := by
    simpa [prefixWord, tailWord_989820, baseEnd_989820] using wordTrace_append hprefix tailTrace_989820
  have hstable : (prefixWord ++ tailWord_989820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989820).length < 2 ^ (prefixWord ++ tailWord_989820).sum := by decide
  have hdescent : baseEnd_989820 < baseStart_989820 := by decide
  rcases family_descends (prefixWord ++ tailWord_989820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989852 : List Nat := [2, 2, 3, 2, 2, 3, 1, 7]
def baseStart_989852 : Nat := 118140960795 + 989852 * 2 ^ 59
def prefixEnd_989852 : Nat := 4983230072969 + 3 ^ 40 * 989852 * 2
def baseEnd_989852 : Nat := 37649618726990106162797

theorem tailTrace_989852 : CollatzResearch.WordTrace tailWord_989852 prefixEnd_989852 37649618726990106162797 := by
  unfold tailWord_989852
  simp only [CollatzResearch.WordTrace]
  refine ⟨18051434204971366053845905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24068578939961821405127873 18051434204971366053845905)
  ·
    refine ⟨13538575653728524540384429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18051434204971366053845905 13538575653728524540384429)
    ·
      refine ⟨5076965870148196702644161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13538575653728524540384429 5076965870148196702644161)
      ·
        refine ⟨3807724402611147526983121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5076965870148196702644161 3807724402611147526983121)
        ·
          refine ⟨2855793301958360645237341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3807724402611147526983121 2855793301958360645237341)
          ·
            refine ⟨1070922488234385241964003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2855793301958360645237341 1070922488234385241964003)
            ·
              refine ⟨1606383732351577862946005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070922488234385241964003 1606383732351577862946005)
              ·
                refine ⟨37649618726990106162797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1606383732351577862946005 37649618726990106162797)
                ·
                  rfl

theorem cell22_989852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 7].length) (baseStart_989852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989852 prefixEnd_989852 := by exact prefixLift 989852
  have htrace : WordTrace (prefixWord ++ tailWord_989852) baseStart_989852 baseEnd_989852 := by
    simpa [prefixWord, tailWord_989852, baseEnd_989852] using wordTrace_append hprefix tailTrace_989852
  have hstable : (prefixWord ++ tailWord_989852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989852).length < 2 ^ (prefixWord ++ tailWord_989852).sum := by decide
  have hdescent : baseEnd_989852 < baseStart_989852 := by decide
  rcases family_descends (prefixWord ++ tailWord_989852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989959 : List Nat := [1, 1, 4, 4, 1, 3, 1, 1, 6]
def baseStart_989959 : Nat := 118140960795 + 989959 * 2 ^ 59
def prefixEnd_989959 : Nat := 4983230072969 + 3 ^ 40 * 989959 * 2
def baseEnd_989959 : Nat := 112961065609866114346615

theorem tailTrace_989959 : CollatzResearch.WordTrace tailWord_989959 prefixEnd_989959 112961065609866114346615 := by
  unfold tailWord_989959
  simp only [CollatzResearch.WordTrace]
  refine ⟨36106771020555089381836931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24071180680370059587891287 36106771020555089381836931)
  ·
    refine ⟨54160156530832634072755397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36106771020555089381836931 54160156530832634072755397)
    ·
      refine ⟨10155029349531118888641637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54160156530832634072755397 10155029349531118888641637)
      ·
        refine ⟨1904068003037084791620307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10155029349531118888641637 1904068003037084791620307)
        ·
          refine ⟨2856102004555627187430461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1904068003037084791620307 2856102004555627187430461)
          ·
            refine ⟨1071038251708360195286423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2856102004555627187430461 1071038251708360195286423)
            ·
              refine ⟨1606557377562540292929635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071038251708360195286423 1606557377562540292929635)
              ·
                refine ⟨2409836066343810439394453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1606557377562540292929635 2409836066343810439394453)
                ·
                  refine ⟨112961065609866114346615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2409836066343810439394453 112961065609866114346615)
                  ·
                    rfl

theorem cell22_989959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 6].length) (baseStart_989959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_989959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_989959 prefixEnd_989959 := by exact prefixLift 989959
  have htrace : WordTrace (prefixWord ++ tailWord_989959) baseStart_989959 baseEnd_989959 := by
    simpa [prefixWord, tailWord_989959, baseEnd_989959] using wordTrace_append hprefix tailTrace_989959
  have hstable : (prefixWord ++ tailWord_989959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989959).length < 2 ^ (prefixWord ++ tailWord_989959).sum := by decide
  have hdescent : baseEnd_989959 < baseStart_989959 := by decide
  rcases family_descends (prefixWord ++ tailWord_989959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990000 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 4, 6]
def baseStart_990000 : Nat := 118140960795 + 990000 * 2 ^ 59
def prefixEnd_990000 : Nat := 4983230072969 + 3 ^ 40 * 990000 * 2
def baseEnd_990000 : Nat := 338897231967487902764719

theorem tailTrace_990000 : CollatzResearch.WordTrace tailWord_990000 prefixEnd_990000 338897231967487902764719 := by
  unfold tailWord_990000
  simp only [CollatzResearch.WordTrace]
  refine ⟨18054133206703276692039727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24072177608937702256052969 18054133206703276692039727)
  ·
    refine ⟨27081199810054915038059591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18054133206703276692039727 27081199810054915038059591)
    ·
      refine ⟨40621799715082372557089387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27081199810054915038059591 40621799715082372557089387)
      ·
        refine ⟨60932699572623558835634081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40621799715082372557089387 60932699572623558835634081)
        ·
          refine ⟨45699524679467669126725561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60932699572623558835634081 45699524679467669126725561)
          ·
            refine ⟨34274643509600751845044171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45699524679467669126725561 34274643509600751845044171)
            ·
              refine ⟨51411965264401127767566257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34274643509600751845044171 51411965264401127767566257)
              ·
                refine ⟨38558973948300845825674693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51411965264401127767566257 38558973948300845825674693)
                ·
                  refine ⟨7229807615306408592314005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38558973948300845825674693 7229807615306408592314005)
                  ·
                    refine ⟨338897231967487902764719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7229807615306408592314005 338897231967487902764719)
                    ·
                      rfl

theorem cell22_990000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_990000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990000 prefixEnd_990000 := by exact prefixLift 990000
  have htrace : WordTrace (prefixWord ++ tailWord_990000) baseStart_990000 baseEnd_990000 := by
    simpa [prefixWord, tailWord_990000, baseEnd_990000] using wordTrace_append hprefix tailTrace_990000
  have hstable : (prefixWord ++ tailWord_990000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990000).length < 2 ^ (prefixWord ++ tailWord_990000).sum := by decide
  have hdescent : baseEnd_990000 < baseStart_990000 := by decide
  rcases family_descends (prefixWord ++ tailWord_990000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990004 : List Nat := [2, 5, 1, 1, 4, 9]
def baseStart_990004 : Nat := 118140960795 + 990004 * 2 ^ 59
def prefixEnd_990004 : Nat := 4983230072969 + 3 ^ 40 * 990004 * 2
def baseEnd_990004 : Nat := 4183933348755965748947

theorem tailTrace_990004 : CollatzResearch.WordTrace tailWord_990004 prefixEnd_990004 4183933348755965748947 := by
  unfold tailWord_990004
  simp only [CollatzResearch.WordTrace]
  refine ⟨18054206152696031033612533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24072274870261374711483377 18054206152696031033612533)
  ·
    refine ⟨1692581826815252909401175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18054206152696031033612533 1692581826815252909401175)
    ·
      refine ⟨2538872740222879364101763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1692581826815252909401175 2538872740222879364101763)
      ·
        refine ⟨3808309110334319046152645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2538872740222879364101763 3808309110334319046152645)
        ·
          refine ⟨714057958187684821153621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3808309110334319046152645 714057958187684821153621)
          ·
            refine ⟨4183933348755965748947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 714057958187684821153621 4183933348755965748947)
            ·
              rfl

theorem cell22_990004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 9].length) (baseStart_990004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990004 prefixEnd_990004 := by exact prefixLift 990004
  have htrace : WordTrace (prefixWord ++ tailWord_990004) baseStart_990004 baseEnd_990004 := by
    simpa [prefixWord, tailWord_990004, baseEnd_990004] using wordTrace_append hprefix tailTrace_990004
  have hstable : (prefixWord ++ tailWord_990004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990004).length < 2 ^ (prefixWord ++ tailWord_990004).sum := by decide
  have hdescent : baseEnd_990004 < baseStart_990004 := by decide
  rcases family_descends (prefixWord ++ tailWord_990004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990032 : List Nat := [2, 1, 1, 1, 1, 4, 4, 3, 5]
def baseStart_990032 : Nat := 118140960795 + 990032 * 2 ^ 59
def prefixEnd_990032 : Nat := 4983230072969 + 3 ^ 40 * 990032 * 2
def baseEnd_990032 : Nat := 112969395407150161988207

theorem tailTrace_990032 : CollatzResearch.WordTrace tailWord_990032 prefixEnd_990032 112969395407150161988207 := by
  unfold tailWord_990032
  simp only [CollatzResearch.WordTrace]
  refine ⟨18054716774645311424622175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24072955699527081899496233 18054716774645311424622175)
  ·
    refine ⟨27082075161967967136933263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18054716774645311424622175 27082075161967967136933263)
    ·
      refine ⟨40623112742951950705399895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27082075161967967136933263 40623112742951950705399895)
      ·
        refine ⟨60934669114427926058099843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40623112742951950705399895 60934669114427926058099843)
        ·
          refine ⟨91402003671641889087149765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60934669114427926058099843 91402003671641889087149765)
          ·
            refine ⟨17137875688432854203840581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91402003671641889087149765 17137875688432854203840581)
            ·
              refine ⟨3213351691581160163220109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17137875688432854203840581 3213351691581160163220109)
              ·
                refine ⟨1205006884342935061207541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3213351691581160163220109 1205006884342935061207541)
                ·
                  refine ⟨112969395407150161988207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1205006884342935061207541 112969395407150161988207)
                  ·
                    rfl

theorem cell22_990032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 5].length) (baseStart_990032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990032 prefixEnd_990032 := by exact prefixLift 990032
  have htrace : WordTrace (prefixWord ++ tailWord_990032) baseStart_990032 baseEnd_990032 := by
    simpa [prefixWord, tailWord_990032, baseEnd_990032] using wordTrace_append hprefix tailTrace_990032
  have hstable : (prefixWord ++ tailWord_990032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990032).length < 2 ^ (prefixWord ++ tailWord_990032).sum := by decide
  have hdescent : baseEnd_990032 < baseStart_990032 := by decide
  rcases family_descends (prefixWord ++ tailWord_990032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990036 : List Nat := [2, 4, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_990036 : Nat := 118140960795 + 990036 * 2 ^ 59
def prefixEnd_990036 : Nat := 4983230072969 + 3 ^ 40 * 990036 * 2
def baseEnd_990036 : Nat := 338909555503195808864609

theorem tailTrace_990036 : CollatzResearch.WordTrace tailWord_990036 prefixEnd_990036 338909555503195808864609 := by
  unfold tailWord_990036
  simp only [CollatzResearch.WordTrace]
  refine ⟨18054789720638065766194981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24073052960850754354926641 18054789720638065766194981)
  ·
    refine ⟨3385273072619637331161559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18054789720638065766194981 3385273072619637331161559)
    ·
      refine ⟨5077909608929455996742339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3385273072619637331161559 5077909608929455996742339)
      ·
        refine ⟨7616864413394183995113509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5077909608929455996742339 7616864413394183995113509)
        ·
          refine ⟨1428162077511409499083783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7616864413394183995113509 1428162077511409499083783)
          ·
            refine ⟨2142243116267114248625675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1428162077511409499083783 2142243116267114248625675)
            ·
              refine ⟨3213364674400671372938513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2142243116267114248625675 3213364674400671372938513)
              ·
                refine ⟨2410023505800503529703885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3213364674400671372938513 2410023505800503529703885)
                ·
                  refine ⟨903758814675188823638957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2410023505800503529703885 903758814675188823638957)
                  ·
                    refine ⟨338909555503195808864609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 903758814675188823638957 338909555503195808864609)
                    ·
                      rfl

theorem cell22_990036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_990036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990036 prefixEnd_990036 := by exact prefixLift 990036
  have htrace : WordTrace (prefixWord ++ tailWord_990036) baseStart_990036 baseEnd_990036 := by
    simpa [prefixWord, tailWord_990036, baseEnd_990036] using wordTrace_append hprefix tailTrace_990036
  have hstable : (prefixWord ++ tailWord_990036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990036).length < 2 ^ (prefixWord ++ tailWord_990036).sum := by decide
  have hdescent : baseEnd_990036 < baseStart_990036 := by decide
  rcases family_descends (prefixWord ++ tailWord_990036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990077 : List Nat := [1, 4, 1, 1, 2, 1, 3, 3, 6]
def baseStart_990077 : Nat := 118140960795 + 990077 * 2 ^ 59
def prefixEnd_990077 : Nat := 4983230072969 + 3 ^ 40 * 990077 * 2
def baseEnd_990077 : Nat := 112974530213695122863161

theorem tailTrace_990077 : CollatzResearch.WordTrace tailWord_990077 prefixEnd_990077 112974530213695122863161 := by
  unfold tailWord_990077
  simp only [CollatzResearch.WordTrace]
  refine ⟨36111074834127595534632485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24074049889418397023088323 36111074834127595534632485)
  ·
    refine ⟨6770826531398924162743591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36111074834127595534632485 6770826531398924162743591)
    ·
      refine ⟨10156239797098386244115387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6770826531398924162743591 10156239797098386244115387)
      ·
        refine ⟨15234359695647579366173081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10156239797098386244115387 15234359695647579366173081)
        ·
          refine ⟨11425769771735684524629811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15234359695647579366173081 11425769771735684524629811)
          ·
            refine ⟨17138654657603526786944717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11425769771735684524629811 17138654657603526786944717)
            ·
              refine ⟨6426995496601322545104269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17138654657603526786944717 6426995496601322545104269)
              ·
                refine ⟨2410123311225495954414101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6426995496601322545104269 2410123311225495954414101)
                ·
                  refine ⟨112974530213695122863161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2410123311225495954414101 112974530213695122863161)
                  ·
                    rfl

theorem cell22_990077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_990077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990077 prefixEnd_990077 := by exact prefixLift 990077
  have htrace : WordTrace (prefixWord ++ tailWord_990077) baseStart_990077 baseEnd_990077 := by
    simpa [prefixWord, tailWord_990077, baseEnd_990077] using wordTrace_append hprefix tailTrace_990077
  have hstable : (prefixWord ++ tailWord_990077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990077).length < 2 ^ (prefixWord ++ tailWord_990077).sum := by decide
  have hdescent : baseEnd_990077 < baseStart_990077 := by decide
  rcases family_descends (prefixWord ++ tailWord_990077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990109 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 6, 3]
def baseStart_990109 : Nat := 118140960795 + 990109 * 2 ^ 59
def prefixEnd_990109 : Nat := 4983230072969 + 3 ^ 40 * 990109 * 2
def baseEnd_990109 : Nat := 338934544895047951789385

theorem tailTrace_990109 : CollatzResearch.WordTrace tailWord_990109 prefixEnd_990109 338934544895047951789385 := by
  unfold tailWord_990109
  simp only [CollatzResearch.WordTrace]
  refine ⟨36112241970011664999797381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24074827980007776666531587 36112241970011664999797381)
  ·
    refine ⟨6771045369377187187462009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36112241970011664999797381 6771045369377187187462009)
    ·
      refine ⟨5078284027032890390596507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6771045369377187187462009 5078284027032890390596507)
      ·
        refine ⟨7617426040549335585894761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5078284027032890390596507 7617426040549335585894761)
        ·
          refine ⟨5713069530412001689421071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7617426040549335585894761 5713069530412001689421071)
          ·
            refine ⟨8569604295618002534131607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5713069530412001689421071 8569604295618002534131607)
            ·
              refine ⟨12854406443427003801197411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8569604295618002534131607 12854406443427003801197411)
              ·
                refine ⟨19281609665140505701796117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12854406443427003801197411 19281609665140505701796117)
                ·
                  refine ⟨903825453053461204771693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19281609665140505701796117 903825453053461204771693)
                  ·
                    refine ⟨338934544895047951789385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 903825453053461204771693 338934544895047951789385)
                    ·
                      rfl

theorem cell22_990109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_990109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990109 prefixEnd_990109 := by exact prefixLift 990109
  have htrace : WordTrace (prefixWord ++ tailWord_990109) baseStart_990109 baseEnd_990109 := by
    simpa [prefixWord, tailWord_990109, baseEnd_990109] using wordTrace_append hprefix tailTrace_990109
  have hstable : (prefixWord ++ tailWord_990109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990109).length < 2 ^ (prefixWord ++ tailWord_990109).sum := by decide
  have hdescent : baseEnd_990109 < baseStart_990109 := by decide
  rcases family_descends (prefixWord ++ tailWord_990109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990111 : List Nat := [1, 1, 2, 5, 2, 1, 3, 3, 4]
def baseStart_990111 : Nat := 118140960795 + 990111 * 2 ^ 59
def prefixEnd_990111 : Nat := 4983230072969 + 3 ^ 40 * 990111 * 2
def baseEnd_990111 : Nat := 112978409845306871079793

theorem tailTrace_990111 : CollatzResearch.WordTrace tailWord_990111 prefixEnd_990111 112978409845306871079793 := by
  unfold tailWord_990111
  simp only [CollatzResearch.WordTrace]
  refine ⟨36112314916004419341370187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24074876610669612894246791 36112314916004419341370187)
  ·
    refine ⟨54168472374006629012055281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36112314916004419341370187 54168472374006629012055281)
    ·
      refine ⟨40626354280504971759041461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54168472374006629012055281 40626354280504971759041461)
      ·
        refine ⟨3808720713797341102410137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40626354280504971759041461 3808720713797341102410137)
        ·
          refine ⟨2856540535348005826807603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3808720713797341102410137 2856540535348005826807603)
          ·
            refine ⟨4284810803022008740211405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2856540535348005826807603 4284810803022008740211405)
            ·
              refine ⟨1606804051133253277579277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4284810803022008740211405 1606804051133253277579277)
              ·
                refine ⟨602551519174969979092229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1606804051133253277579277 602551519174969979092229)
                ·
                  refine ⟨112978409845306871079793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 602551519174969979092229 112978409845306871079793)
                  ·
                    rfl

theorem cell22_990111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 4].length) (baseStart_990111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990111 prefixEnd_990111 := by exact prefixLift 990111
  have htrace : WordTrace (prefixWord ++ tailWord_990111) baseStart_990111 baseEnd_990111 := by
    simpa [prefixWord, tailWord_990111, baseEnd_990111] using wordTrace_append hprefix tailTrace_990111
  have hstable : (prefixWord ++ tailWord_990111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990111).length < 2 ^ (prefixWord ++ tailWord_990111).sum := by decide
  have hdescent : baseEnd_990111 < baseStart_990111 := by decide
  rcases family_descends (prefixWord ++ tailWord_990111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990134 : List Nat := [5, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_990134 : Nat := 118140960795 + 990134 * 2 ^ 59
def prefixEnd_990134 : Nat := 4983230072969 + 3 ^ 40 * 990134 * 2
def baseEnd_990134 : Nat := 112981034301985406638103

theorem tailTrace_990134 : CollatzResearch.WordTrace tailWord_990134 prefixEnd_990134 112981034301985406638103 := by
  unfold tailWord_990134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2257072112182568391841091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24075435863280729512971637 2257072112182568391841091)
  ·
    refine ⟨3385608168273852587761637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2257072112182568391841091 3385608168273852587761637)
    ·
      refine ⟨634801531551347360205307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3385608168273852587761637 634801531551347360205307)
      ·
        refine ⟨952202297327021040307961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634801531551347360205307 952202297327021040307961)
        ·
          refine ⟨714151722995265780230971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 952202297327021040307961 714151722995265780230971)
          ·
            refine ⟨1071227584492898670346457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714151722995265780230971 1071227584492898670346457)
            ·
              refine ⟨803420688369674002759843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1071227584492898670346457 803420688369674002759843)
              ·
                refine ⟨1205131032554511004139765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803420688369674002759843 1205131032554511004139765)
                ·
                  refine ⟨112981034301985406638103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1205131032554511004139765 112981034301985406638103)
                  ·
                    rfl

theorem cell22_990134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_990134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990134 prefixEnd_990134 := by exact prefixLift 990134
  have htrace : WordTrace (prefixWord ++ tailWord_990134) baseStart_990134 baseEnd_990134 := by
    simpa [prefixWord, tailWord_990134, baseEnd_990134] using wordTrace_append hprefix tailTrace_990134
  have hstable : (prefixWord ++ tailWord_990134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990134).length < 2 ^ (prefixWord ++ tailWord_990134).sum := by decide
  have hdescent : baseEnd_990134 < baseStart_990134 := by decide
  rcases family_descends (prefixWord ++ tailWord_990134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990154 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 5, 3]
def baseStart_990154 : Nat := 118140960795 + 990154 * 2 ^ 59
def prefixEnd_990154 : Nat := 4983230072969 + 3 ^ 40 * 990154 * 2
def baseEnd_990154 : Nat := 338949949314682834414247

theorem tailTrace_990154 : CollatzResearch.WordTrace tailWord_990154 prefixEnd_990154 338949949314682834414247 := by
  unfold tailWord_990154
  simp only [CollatzResearch.WordTrace]
  refine ⟨9028470813712159421296379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24075922169899091790123677 9028470813712159421296379)
  ·
    refine ⟨13542706220568239131944569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9028470813712159421296379 13542706220568239131944569)
    ·
      refine ⟨10157029665426179348958427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13542706220568239131944569 10157029665426179348958427)
      ·
        refine ⟨15235544498139269023437641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10157029665426179348958427 15235544498139269023437641)
        ·
          refine ⟨11426658373604451767578231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15235544498139269023437641 11426658373604451767578231)
          ·
            refine ⟨17139987560406677651367347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11426658373604451767578231 17139987560406677651367347)
            ·
              refine ⟨25709981340610016477051021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17139987560406677651367347 25709981340610016477051021)
              ·
                refine ⟨9641243002728756178894133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25709981340610016477051021 9641243002728756178894133)
                ·
                  refine ⟨903866531505820891771325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9641243002728756178894133 903866531505820891771325)
                  ·
                    refine ⟨338949949314682834414247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 903866531505820891771325 338949949314682834414247)
                    ·
                      rfl

theorem cell22_990154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_990154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990154 prefixEnd_990154 := by exact prefixLift 990154
  have htrace : WordTrace (prefixWord ++ tailWord_990154) baseStart_990154 baseEnd_990154 := by
    simpa [prefixWord, tailWord_990154, baseEnd_990154] using wordTrace_append hprefix tailTrace_990154
  have hstable : (prefixWord ++ tailWord_990154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990154).length < 2 ^ (prefixWord ++ tailWord_990154).sum := by decide
  have hdescent : baseEnd_990154 < baseStart_990154 := by decide
  rcases family_descends (prefixWord ++ tailWord_990154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990167 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 7]
def baseStart_990167 : Nat := 118140960795 + 990167 * 2 ^ 59
def prefixEnd_990167 : Nat := 4983230072969 + 3 ^ 40 * 990167 * 2
def baseEnd_990167 : Nat := 112984799826785044613069

theorem tailTrace_990167 : CollatzResearch.WordTrace tailWord_990167 prefixEnd_990167 112984799826785044613069 := by
  unfold tailWord_990167
  simp only [CollatzResearch.WordTrace]
  refine ⟨36114357403801540905408755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24076238269201027270272503 36114357403801540905408755)
  ·
    refine ⟨54171536105702311358113133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36114357403801540905408755 54171536105702311358113133)
    ·
      refine ⟨20314326039638366759292425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54171536105702311358113133 20314326039638366759292425)
      ·
        refine ⟨15235744529728775069469319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20314326039638366759292425 15235744529728775069469319)
        ·
          refine ⟨22853616794593162604203979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15235744529728775069469319 22853616794593162604203979)
          ·
            refine ⟨34280425191889743906305969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22853616794593162604203979 34280425191889743906305969)
            ·
              refine ⟨25710318893917307929729477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34280425191889743906305969 25710318893917307929729477)
              ·
                refine ⟨4820684792609495236824277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25710318893917307929729477 4820684792609495236824277)
                ·
                  refine ⟨112984799826785044613069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4820684792609495236824277 112984799826785044613069)
                  ·
                    rfl

theorem cell22_990167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 7].length) (baseStart_990167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990167 prefixEnd_990167 := by exact prefixLift 990167
  have htrace : WordTrace (prefixWord ++ tailWord_990167) baseStart_990167 baseEnd_990167 := by
    simpa [prefixWord, tailWord_990167, baseEnd_990167] using wordTrace_append hprefix tailTrace_990167
  have hstable : (prefixWord ++ tailWord_990167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990167).length < 2 ^ (prefixWord ++ tailWord_990167).sum := by decide
  have hdescent : baseEnd_990167 < baseStart_990167 := by decide
  rcases family_descends (prefixWord ++ tailWord_990167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990184 : List Nat := [2, 1, 4, 1, 1, 1, 3, 4, 5]
def baseStart_990184 : Nat := 118140960795 + 990184 * 2 ^ 59
def prefixEnd_990184 : Nat := 4983230072969 + 3 ^ 40 * 990184 * 2
def baseEnd_990184 : Nat := 112986739642590918721385

theorem tailTrace_990184 : CollatzResearch.WordTrace tailWord_990184 prefixEnd_990184 112986739642590918721385 := by
  unfold tailWord_990184
  simp only [CollatzResearch.WordTrace]
  refine ⟨18057488722369976404388803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24076651629826635205851737 18057488722369976404388803)
  ·
    refine ⟨27086233083554964606583205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18057488722369976404388803 27086233083554964606583205)
    ·
      refine ⟨5078668703166555863734351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27086233083554964606583205 5078668703166555863734351)
      ·
        refine ⟨7618003054749833795601527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5078668703166555863734351 7618003054749833795601527)
        ·
          refine ⟨11427004582124750693402291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7618003054749833795601527 11427004582124750693402291)
          ·
            refine ⟨17140506873187126040103437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11427004582124750693402291 17140506873187126040103437)
            ·
              refine ⟨6427690077445172265038789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17140506873187126040103437 6427690077445172265038789)
              ·
                refine ⟨1205191889520969799694773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6427690077445172265038789 1205191889520969799694773)
                ·
                  refine ⟨112986739642590918721385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1205191889520969799694773 112986739642590918721385)
                  ·
                    rfl

theorem cell22_990184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 5].length) (baseStart_990184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990184 prefixEnd_990184 := by exact prefixLift 990184
  have htrace : WordTrace (prefixWord ++ tailWord_990184) baseStart_990184 baseEnd_990184 := by
    simpa [prefixWord, tailWord_990184, baseEnd_990184] using wordTrace_append hprefix tailTrace_990184
  have hstable : (prefixWord ++ tailWord_990184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990184).length < 2 ^ (prefixWord ++ tailWord_990184).sum := by decide
  have hdescent : baseEnd_990184 < baseStart_990184 := by decide
  rcases family_descends (prefixWord ++ tailWord_990184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990304 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 2, 6]
def baseStart_990304 : Nat := 118140960795 + 990304 * 2 ^ 59
def prefixEnd_990304 : Nat := 4983230072969 + 3 ^ 40 * 990304 * 2
def baseEnd_990304 : Nat := 339001297380132443163787

theorem tailTrace_990304 : CollatzResearch.WordTrace tailWord_990304 prefixEnd_990304 339001297380132443163787 := by
  unfold tailWord_990304
  simp only [CollatzResearch.WordTrace]
  refine ⟨18059677102152606651572983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24079569469536808868763977 18059677102152606651572983)
  ·
    refine ⟨27089515653228909977359475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18059677102152606651572983 27089515653228909977359475)
    ·
      refine ⟨40634273479843364966039213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27089515653228909977359475 40634273479843364966039213)
      ·
        refine ⟨15237852554941261862264705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40634273479843364966039213 15237852554941261862264705)
        ·
          refine ⟨11428389416205946396698529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15237852554941261862264705 11428389416205946396698529)
          ·
            refine ⟨8571292062154459797523897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11428389416205946396698529 8571292062154459797523897)
            ·
              refine ⟨6428469046615844848142923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8571292062154459797523897 6428469046615844848142923)
              ·
                refine ⟨9642703569923767272214385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6428469046615844848142923 9642703569923767272214385)
                ·
                  refine ⟨7232027677442825454160789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9642703569923767272214385 7232027677442825454160789)
                  ·
                    refine ⟨339001297380132443163787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7232027677442825454160789 339001297380132443163787)
                    ·
                      rfl

theorem cell22_990304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_990304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990304 prefixEnd_990304 := by exact prefixLift 990304
  have htrace : WordTrace (prefixWord ++ tailWord_990304) baseStart_990304 baseEnd_990304 := by
    simpa [prefixWord, tailWord_990304, baseEnd_990304] using wordTrace_append hprefix tailTrace_990304
  have hstable : (prefixWord ++ tailWord_990304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990304).length < 2 ^ (prefixWord ++ tailWord_990304).sum := by decide
  have hdescent : baseEnd_990304 < baseStart_990304 := by decide
  rcases family_descends (prefixWord ++ tailWord_990304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990443 : List Nat := [1, 1, 1, 1, 2, 8, 2, 6]
def baseStart_990443 : Nat := 118140960795 + 990443 * 2 ^ 59
def prefixEnd_990443 : Nat := 4983230072969 + 3 ^ 40 * 990443 * 2
def baseEnd_990443 : Nat := 37672097768975823770929

theorem tailTrace_990443 : CollatzResearch.WordTrace tailWord_990443 prefixEnd_990443 37672097768975823770929 := by
  unfold tailWord_990443
  simp only [CollatzResearch.WordTrace]
  refine ⟨36124423950801640042455983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24082949300534426694970655 36124423950801640042455983)
  ·
    refine ⟨54186635926202460063683975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36124423950801640042455983 54186635926202460063683975)
    ·
      refine ⟨81279953889303690095525963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54186635926202460063683975 81279953889303690095525963)
      ·
        refine ⟨121919930833955535143288945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81279953889303690095525963 121919930833955535143288945)
        ·
          refine ⟨91439948125466651357466709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121919930833955535143288945 91439948125466651357466709)
          ·
            refine ⟨1071561892095312320595313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 91439948125466651357466709 1071561892095312320595313)
            ·
              refine ⟨803671419071484240446485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1071561892095312320595313 803671419071484240446485)
              ·
                refine ⟨37672097768975823770929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 803671419071484240446485 37672097768975823770929)
                ·
                  rfl

theorem cell22_990443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 6].length) (baseStart_990443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990443 prefixEnd_990443 := by exact prefixLift 990443
  have htrace : WordTrace (prefixWord ++ tailWord_990443) baseStart_990443 baseEnd_990443 := by
    simpa [prefixWord, tailWord_990443, baseEnd_990443] using wordTrace_append hprefix tailTrace_990443
  have hstable : (prefixWord ++ tailWord_990443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990443).length < 2 ^ (prefixWord ++ tailWord_990443).sum := by decide
  have hdescent : baseEnd_990443 < baseStart_990443 := by decide
  rcases family_descends (prefixWord ++ tailWord_990443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990475 : List Nat := [1, 1, 1, 1, 5, 5, 1, 1, 3, 3]
def baseStart_990475 : Nat := 118140960795 + 990475 * 2 ^ 59
def prefixEnd_990475 : Nat := 4983230072969 + 3 ^ 40 * 990475 * 2
def baseEnd_990475 : Nat := 339059834174744997138263

theorem tailTrace_990475 : CollatzResearch.WordTrace tailWord_990475 prefixEnd_990475 339059834174744997138263 := by
  unfold tailWord_990475
  simp only [CollatzResearch.WordTrace]
  refine ⟨36125591086685709507620879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24083727391123806338413919 36125591086685709507620879)
  ·
    refine ⟨54188386630028564261431319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36125591086685709507620879 54188386630028564261431319)
    ·
      refine ⟨81282579945042846392146979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54188386630028564261431319 81282579945042846392146979)
      ·
        refine ⟨121923869917564269588220469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81282579945042846392146979 121923869917564269588220469)
        ·
          refine ⟨11430362804771650273895669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121923869917564269588220469 11430362804771650273895669)
          ·
            refine ⟨1071596512947342213177719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11430362804771650273895669 1071596512947342213177719)
            ·
              refine ⟨1607394769421013319766579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071596512947342213177719 1607394769421013319766579)
              ·
                refine ⟨2411092154131519979649869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1607394769421013319766579 2411092154131519979649869)
                ·
                  refine ⟨904159557799319992368701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2411092154131519979649869 904159557799319992368701)
                  ·
                    refine ⟨339059834174744997138263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 904159557799319992368701 339059834174744997138263)
                    ·
                      rfl

theorem cell22_990475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 3].length) (baseStart_990475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990475 prefixEnd_990475 := by exact prefixLift 990475
  have htrace : WordTrace (prefixWord ++ tailWord_990475) baseStart_990475 baseEnd_990475 := by
    simpa [prefixWord, tailWord_990475, baseEnd_990475] using wordTrace_append hprefix tailTrace_990475
  have hstable : (prefixWord ++ tailWord_990475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990475).length < 2 ^ (prefixWord ++ tailWord_990475).sum := by decide
  have hdescent : baseEnd_990475 < baseStart_990475 := by decide
  rcases family_descends (prefixWord ++ tailWord_990475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990488 : List Nat := [2, 1, 2, 3, 1, 4, 1, 3, 5]
def baseStart_990488 : Nat := 118140960795 + 990488 * 2 ^ 59
def prefixEnd_990488 : Nat := 4983230072969 + 3 ^ 40 * 990488 * 2
def baseEnd_990488 : Nat := 113021428113472432187741

theorem tailTrace_990488 : CollatzResearch.WordTrace tailWord_990488 prefixEnd_990488 113021428113472432187741 := by
  unfold tailWord_990488
  simp only [CollatzResearch.WordTrace]
  refine ⟨18063032617819306363922059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24084043490425741818562745 18063032617819306363922059)
  ·
    refine ⟨27094548926728959545883089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18063032617819306363922059 27094548926728959545883089)
    ·
      refine ⟨20320911695046719659412317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27094548926728959545883089 20320911695046719659412317)
      ·
        refine ⟨7620341885642519872279619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20320911695046719659412317 7620341885642519872279619)
        ·
          refine ⟨11430512828463779808419429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7620341885642519872279619 11430512828463779808419429)
          ·
            refine ⟨2143221155336958714078643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11430512828463779808419429 2143221155336958714078643)
            ·
              refine ⟨3214831733005438071117965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2143221155336958714078643 3214831733005438071117965)
              ·
                refine ⟨1205561899877039276669237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3214831733005438071117965 1205561899877039276669237)
                ·
                  refine ⟨113021428113472432187741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1205561899877039276669237 113021428113472432187741)
                  ·
                    rfl

theorem cell22_990488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 5].length) (baseStart_990488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990488 prefixEnd_990488 := by exact prefixLift 990488
  have htrace : WordTrace (prefixWord ++ tailWord_990488) baseStart_990488 baseEnd_990488 := by
    simpa [prefixWord, tailWord_990488, baseEnd_990488] using wordTrace_append hprefix tailTrace_990488
  have hstable : (prefixWord ++ tailWord_990488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990488).length < 2 ^ (prefixWord ++ tailWord_990488).sum := by decide
  have hdescent : baseEnd_990488 < baseStart_990488 := by decide
  rcases family_descends (prefixWord ++ tailWord_990488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990531 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 5, 5]
def baseStart_990531 : Nat := 118140960795 + 990531 * 2 ^ 59
def prefixEnd_990531 : Nat := 4983230072969 + 3 ^ 40 * 990531 * 2
def baseEnd_990531 : Nat := 339079004119179517738091

theorem tailTrace_990531 : CollatzResearch.WordTrace tailWord_990531 prefixEnd_990531 339079004119179517738091 := by
  unfold tailWord_990531
  simp only [CollatzResearch.WordTrace]
  refine ⟨36127633574482831071659447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24085089049655220714439631 36127633574482831071659447)
  ·
    refine ⟨54191450361724246607489171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36127633574482831071659447 54191450361724246607489171)
    ·
      refine ⟨81287175542586369911233757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54191450361724246607489171 81287175542586369911233757)
      ·
        refine ⟨30482690828469888716712659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81287175542586369911233757 30482690828469888716712659)
        ·
          refine ⟨45724036242704833075068989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30482690828469888716712659 45724036242704833075068989)
          ·
            refine ⟨17146513591014312403150871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45724036242704833075068989 17146513591014312403150871)
            ·
              refine ⟨25719770386521468604726307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17146513591014312403150871 25719770386521468604726307)
              ·
                refine ⟨38579655579782202907089461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25719770386521468604726307 38579655579782202907089461)
                ·
                  refine ⟨3616842710604581522539637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38579655579782202907089461 3616842710604581522539637)
                  ·
                    refine ⟨339079004119179517738091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3616842710604581522539637 339079004119179517738091)
                    ·
                      rfl

theorem cell22_990531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 5].length) (baseStart_990531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990531 prefixEnd_990531 := by exact prefixLift 990531
  have htrace : WordTrace (prefixWord ++ tailWord_990531) baseStart_990531 baseEnd_990531 := by
    simpa [prefixWord, tailWord_990531, baseEnd_990531] using wordTrace_append hprefix tailTrace_990531
  have hstable : (prefixWord ++ tailWord_990531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990531).length < 2 ^ (prefixWord ++ tailWord_990531).sum := by decide
  have hdescent : baseEnd_990531 < baseStart_990531 := by decide
  rcases family_descends (prefixWord ++ tailWord_990531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990561 : List Nat := [1, 2, 3, 1, 1, 1, 1, 12]
def baseStart_990561 : Nat := 118140960795 + 990561 * 2 ^ 59
def prefixEnd_990561 : Nat := 4983230072969 + 3 ^ 40 * 990561 * 2
def baseEnd_990561 : Nat := 37676585970252159943111

theorem tailTrace_990561 : CollatzResearch.WordTrace tailWord_990561 prefixEnd_990561 37676585970252159943111 := by
  unfold tailWord_990561
  simp only [CollatzResearch.WordTrace]
  refine ⟨36128727764374146195251537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24085818509582764130167691 36128727764374146195251537)
  ·
    refine ⟨27096545823280609646438653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36128727764374146195251537 27096545823280609646438653)
    ·
      refine ⟨10161204683730228617414495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27096545823280609646438653 10161204683730228617414495)
      ·
        refine ⟨15241807025595342926121743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10161204683730228617414495 15241807025595342926121743)
        ·
          refine ⟨22862710538393014389182615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15241807025595342926121743 22862710538393014389182615)
          ·
            refine ⟨34294065807589521583773923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22862710538393014389182615 34294065807589521583773923)
            ·
              refine ⟨51441098711384282375660885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34294065807589521583773923 51441098711384282375660885)
              ·
                refine ⟨37676585970252159943111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 51441098711384282375660885 37676585970252159943111)
                ·
                  rfl

theorem cell22_990561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 12].length) (baseStart_990561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990561 prefixEnd_990561 := by exact prefixLift 990561
  have htrace : WordTrace (prefixWord ++ tailWord_990561) baseStart_990561 baseEnd_990561 := by
    simpa [prefixWord, tailWord_990561, baseEnd_990561] using wordTrace_append hprefix tailTrace_990561
  have hstable : (prefixWord ++ tailWord_990561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990561).length < 2 ^ (prefixWord ++ tailWord_990561).sum := by decide
  have hdescent : baseEnd_990561 < baseStart_990561 := by decide
  rcases family_descends (prefixWord ++ tailWord_990561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990563 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 1, 6]
def baseStart_990563 : Nat := 118140960795 + 990563 * 2 ^ 59
def prefixEnd_990563 : Nat := 4983230072969 + 3 ^ 40 * 990563 * 2
def baseEnd_990563 : Nat := 339089958373142100937993

theorem tailTrace_990563 : CollatzResearch.WordTrace tailWord_990563 prefixEnd_990563 339089958373142100937993 := by
  unfold tailWord_990563
  simp only [CollatzResearch.WordTrace]
  refine ⟨36128800710366900536824343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24085867140244600357882895 36128800710366900536824343)
  ·
    refine ⟨54193201065550350805236515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36128800710366900536824343 54193201065550350805236515)
    ·
      refine ⟨81289801598325526207854773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54193201065550350805236515 81289801598325526207854773)
      ·
        refine ⟨7620918899843018081986385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81289801598325526207854773 7620918899843018081986385)
        ·
          refine ⟨5715689174882263561489789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7620918899843018081986385 5715689174882263561489789)
          ·
            refine ⟨2143383440580848835558671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5715689174882263561489789 2143383440580848835558671)
            ·
              refine ⟨3215075160871273253338007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2143383440580848835558671 3215075160871273253338007)
              ·
                refine ⟨4822612741306909880007011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3215075160871273253338007 4822612741306909880007011)
                ·
                  refine ⟨7233919111960364820010517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4822612741306909880007011 7233919111960364820010517)
                  ·
                    refine ⟨339089958373142100937993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7233919111960364820010517 339089958373142100937993)
                    ·
                      rfl

theorem cell22_990563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 6].length) (baseStart_990563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990563 prefixEnd_990563 := by exact prefixLift 990563
  have htrace : WordTrace (prefixWord ++ tailWord_990563) baseStart_990563 baseEnd_990563 := by
    simpa [prefixWord, tailWord_990563, baseEnd_990563] using wordTrace_append hprefix tailTrace_990563
  have hstable : (prefixWord ++ tailWord_990563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990563).length < 2 ^ (prefixWord ++ tailWord_990563).sum := by decide
  have hdescent : baseEnd_990563 < baseStart_990563 := by decide
  rcases family_descends (prefixWord ++ tailWord_990563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990567 : List Nat := [1, 1, 5, 1, 4, 1, 2, 3, 4]
def baseStart_990567 : Nat := 118140960795 + 990567 * 2 ^ 59
def prefixEnd_990567 : Nat := 4983230072969 + 3 ^ 40 * 990567 * 2
def baseEnd_990567 : Nat := 113030442551629141279327

theorem tailTrace_990567 : CollatzResearch.WordTrace tailWord_990567 prefixEnd_990567 113030442551629141279327 := by
  unfold tailWord_990567
  simp only [CollatzResearch.WordTrace]
  refine ⟨36128946602352409219969955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24085964401568272813313303 36128946602352409219969955)
  ·
    refine ⟨54193419903528613829954933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36128946602352409219969955 54193419903528613829954933)
    ·
      refine ⟨5080633115955807546558275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54193419903528613829954933 5080633115955807546558275)
      ·
        refine ⟨7620949673933711319837413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5080633115955807546558275 7620949673933711319837413)
        ·
          refine ⟨1428928063862570872469515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7620949673933711319837413 1428928063862570872469515)
          ·
            refine ⟨2143392095793856308704273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1428928063862570872469515 2143392095793856308704273)
            ·
              refine ⟨1607544071845392231528205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2143392095793856308704273 1607544071845392231528205)
              ·
                refine ⟨602829026942022086823077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1607544071845392231528205 602829026942022086823077)
                ·
                  refine ⟨113030442551629141279327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 602829026942022086823077 113030442551629141279327)
                  ·
                    rfl

theorem cell22_990567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 4].length) (baseStart_990567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990567 prefixEnd_990567 := by exact prefixLift 990567
  have htrace : WordTrace (prefixWord ++ tailWord_990567) baseStart_990567 baseEnd_990567 := by
    simpa [prefixWord, tailWord_990567, baseEnd_990567] using wordTrace_append hprefix tailTrace_990567
  have hstable : (prefixWord ++ tailWord_990567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990567).length < 2 ^ (prefixWord ++ tailWord_990567).sum := by decide
  have hdescent : baseEnd_990567 < baseStart_990567 := by decide
  rcases family_descends (prefixWord ++ tailWord_990567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990612 : List Nat := [2, 4, 2, 1, 2, 3, 2, 6]
def baseStart_990612 : Nat := 118140960795 + 990612 * 2 ^ 59
def prefixEnd_990612 : Nat := 4983230072969 + 3 ^ 40 * 990612 * 2
def baseEnd_990612 : Nat := 37678525786058034051427

theorem tailTrace_990612 : CollatzResearch.WordTrace tailWord_990612 prefixEnd_990612 37678525786058034051427 := by
  unfold tailWord_990612
  simp only [CollatzResearch.WordTrace]
  refine ⟨18065293943594690952679045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24087058591459587936905393 18065293943594690952679045)
  ·
    refine ⟨3387242614424004553627321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18065293943594690952679045 3387242614424004553627321)
    ·
      refine ⟨2540431960818003415220491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3387242614424004553627321 2540431960818003415220491)
      ·
        refine ⟨3810647941227005122830737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2540431960818003415220491 3810647941227005122830737)
        ·
          refine ⟨2857985955920253842123053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3810647941227005122830737 2857985955920253842123053)
          ·
            refine ⟨1071744733470095190796145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2857985955920253842123053 1071744733470095190796145)
            ·
              refine ⟨803808550102571393097109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1071744733470095190796145 803808550102571393097109)
              ·
                refine ⟨37678525786058034051427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 803808550102571393097109 37678525786058034051427)
                ·
                  rfl

theorem cell22_990612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 6].length) (baseStart_990612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990612 prefixEnd_990612 := by exact prefixLift 990612
  have htrace : WordTrace (prefixWord ++ tailWord_990612) baseStart_990612 baseEnd_990612 := by
    simpa [prefixWord, tailWord_990612, baseEnd_990612] using wordTrace_append hprefix tailTrace_990612
  have hstable : (prefixWord ++ tailWord_990612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990612).length < 2 ^ (prefixWord ++ tailWord_990612).sum := by decide
  have hdescent : baseEnd_990612 < baseStart_990612 := by decide
  rcases family_descends (prefixWord ++ tailWord_990612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990623 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 7]
def baseStart_990623 : Nat := 118140960795 + 990623 * 2 ^ 59
def prefixEnd_990623 : Nat := 4983230072969 + 3 ^ 40 * 990623 * 2
def baseEnd_990623 : Nat := 113036832533107314812603

theorem tailTrace_990623 : CollatzResearch.WordTrace tailWord_990623 prefixEnd_990623 113036832533107314812603 := by
  unfold tailWord_990623
  simp only [CollatzResearch.WordTrace]
  refine ⟨36130989090149530784008523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24087326060099687189339015 36130989090149530784008523)
  ·
    refine ⟨54196483635224296176012785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36130989090149530784008523 54196483635224296176012785)
    ·
      refine ⟨40647362726418222132009589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54196483635224296176012785 40647362726418222132009589)
      ·
        refine ⟨3810690255601708324875899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40647362726418222132009589 3810690255601708324875899)
        ·
          refine ⟨5716035383402562487313849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3810690255601708324875899 5716035383402562487313849)
          ·
            refine ⟨4287026537551921865485387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5716035383402562487313849 4287026537551921865485387)
            ·
              refine ⟨6430539806327882798228081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4287026537551921865485387 6430539806327882798228081)
              ·
                refine ⟨4822904854745912098671061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6430539806327882798228081 4822904854745912098671061)
                ·
                  refine ⟨113036832533107314812603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4822904854745912098671061 113036832533107314812603)
                  ·
                    rfl

theorem cell22_990623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 7].length) (baseStart_990623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990623 prefixEnd_990623 := by exact prefixLift 990623
  have htrace : WordTrace (prefixWord ++ tailWord_990623) baseStart_990623 baseEnd_990623 := by
    simpa [prefixWord, tailWord_990623, baseEnd_990623] using wordTrace_append hprefix tailTrace_990623
  have hstable : (prefixWord ++ tailWord_990623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990623).length < 2 ^ (prefixWord ++ tailWord_990623).sum := by decide
  have hdescent : baseEnd_990623 < baseStart_990623 := by decide
  rcases family_descends (prefixWord ++ tailWord_990623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990687 : List Nat := [1, 1, 2, 3, 3, 1, 5, 1, 1, 4]
def baseStart_990687 : Nat := 118140960795 + 990687 * 2 ^ 59
def prefixEnd_990687 : Nat := 4983230072969 + 3 ^ 40 * 990687 * 2
def baseEnd_990687 : Nat := 339132406107247110837613

theorem tailTrace_990687 : CollatzResearch.WordTrace tailWord_990687 prefixEnd_990687 339132406107247110837613 := by
  unfold tailWord_990687
  simp only [CollatzResearch.WordTrace]
  refine ⟨36133323361917669714338315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24088882241278446476225543 36133323361917669714338315)
  ·
    refine ⟨54199985042876504571507473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36133323361917669714338315 54199985042876504571507473)
    ·
      refine ⟨40649988782157378428630605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54199985042876504571507473 40649988782157378428630605)
      ·
        refine ⟨15243745793309016910736477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40649988782157378428630605 15243745793309016910736477)
        ·
          refine ⟨5716404672490881341526179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15243745793309016910736477 5716404672490881341526179)
          ·
            refine ⟨8574607008736322012289269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5716404672490881341526179 8574607008736322012289269)
            ·
              refine ⟨803869407069030188652119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8574607008736322012289269 803869407069030188652119)
              ·
                refine ⟨1205804110603545282978179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803869407069030188652119 1205804110603545282978179)
                ·
                  refine ⟨1808706165905317924467269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1205804110603545282978179 1808706165905317924467269)
                  ·
                    refine ⟨339132406107247110837613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1808706165905317924467269 339132406107247110837613)
                    ·
                      rfl

theorem cell22_990687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 1, 4].length) (baseStart_990687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990687 prefixEnd_990687 := by exact prefixLift 990687
  have htrace : WordTrace (prefixWord ++ tailWord_990687) baseStart_990687 baseEnd_990687 := by
    simpa [prefixWord, tailWord_990687, baseEnd_990687] using wordTrace_append hprefix tailTrace_990687
  have hstable : (prefixWord ++ tailWord_990687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990687).length < 2 ^ (prefixWord ++ tailWord_990687).sum := by decide
  have hdescent : baseEnd_990687 < baseStart_990687 := by decide
  rcases family_descends (prefixWord ++ tailWord_990687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990702 : List Nat := [4, 1, 2, 1, 2, 1, 3, 4, 4]
def baseStart_990702 : Nat := 118140960795 + 990702 * 2 ^ 59
def prefixEnd_990702 : Nat := 4983230072969 + 3 ^ 40 * 990702 * 2
def baseEnd_990702 : Nat := 113045846971264023904189

theorem tailTrace_990702 : CollatzResearch.WordTrace tailWord_990702 prefixEnd_990702 113045846971264023904189 := by
  unfold tailWord_990702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4516733807107915909516795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24089246971242218184089573 4516733807107915909516795)
  ·
    refine ⟨6775100710661873864275193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4516733807107915909516795 6775100710661873864275193)
    ·
      refine ⟨5081325532996405398206395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6775100710661873864275193 5081325532996405398206395)
      ·
        refine ⟨7621988299494608097309593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5081325532996405398206395 7621988299494608097309593)
        ·
          refine ⟨5716491224620956072982195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7621988299494608097309593 5716491224620956072982195)
          ·
            refine ⟨8574736836931434109473293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5716491224620956072982195 8574736836931434109473293)
            ·
              refine ⟨3215526313849287791052485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8574736836931434109473293 3215526313849287791052485)
              ·
                refine ⟨602911183846741460822341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3215526313849287791052485 602911183846741460822341)
                ·
                  refine ⟨113045846971264023904189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 602911183846741460822341 113045846971264023904189)
                  ·
                    rfl

theorem cell22_990702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_990702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990702 prefixEnd_990702 := by exact prefixLift 990702
  have htrace : WordTrace (prefixWord ++ tailWord_990702) baseStart_990702 baseEnd_990702 := by
    simpa [prefixWord, tailWord_990702, baseEnd_990702] using wordTrace_append hprefix tailTrace_990702
  have hstable : (prefixWord ++ tailWord_990702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990702).length < 2 ^ (prefixWord ++ tailWord_990702).sum := by decide
  have hdescent : baseEnd_990702 < baseStart_990702 := by decide
  rcases family_descends (prefixWord ++ tailWord_990702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990717 : List Nat := [1, 4, 1, 1, 1, 4, 2, 3, 2, 3]
def baseStart_990717 : Nat := 118140960795 + 990717 * 2 ^ 59
def prefixEnd_990717 : Nat := 4983230072969 + 3 ^ 40 * 990717 * 2
def baseEnd_990717 : Nat := 339142675720337032587521

theorem tailTrace_990717 : CollatzResearch.WordTrace tailWord_990717 prefixEnd_990717 339142675720337032587521 := by
  unfold tailWord_990717
  simp only [CollatzResearch.WordTrace]
  refine ⟨36134417551808984837930405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24089611701205989891953603 36134417551808984837930405)
  ·
    refine ⟨6775203290964184657111951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36134417551808984837930405 6775203290964184657111951)
    ·
      refine ⟨10162804936446276985667927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6775203290964184657111951 10162804936446276985667927)
      ·
        refine ⟨15244207404669415478501891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10162804936446276985667927 15244207404669415478501891)
        ·
          refine ⟨22866311107004123217752837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15244207404669415478501891 22866311107004123217752837)
          ·
            refine ⟨4287433332563273103328657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22866311107004123217752837 4287433332563273103328657)
            ·
              refine ⟨3215574999422454827496493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4287433332563273103328657 3215574999422454827496493)
              ·
                refine ⟨1205840624783420560311185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3215574999422454827496493 1205840624783420560311185)
                ·
                  refine ⟨904380468587565420233389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1205840624783420560311185 904380468587565420233389)
                  ·
                    refine ⟨339142675720337032587521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 904380468587565420233389 339142675720337032587521)
                    ·
                      rfl

theorem cell22_990717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_990717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990717 prefixEnd_990717 := by exact prefixLift 990717
  have htrace : WordTrace (prefixWord ++ tailWord_990717) baseStart_990717 baseEnd_990717 := by
    simpa [prefixWord, tailWord_990717, baseEnd_990717] using wordTrace_append hprefix tailTrace_990717
  have hstable : (prefixWord ++ tailWord_990717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990717).length < 2 ^ (prefixWord ++ tailWord_990717).sum := by decide
  have hdescent : baseEnd_990717 < baseStart_990717 := by decide
  rcases family_descends (prefixWord ++ tailWord_990717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990796 : List Nat := [2, 2, 1, 3, 1, 5, 1, 3, 1, 3]
def baseStart_990796 : Nat := 118140960795 + 990796 * 2 ^ 59
def prefixEnd_990796 : Nat := 4983230072969 + 3 ^ 40 * 990796 * 2
def baseEnd_990796 : Nat := 339169719034807159862279

theorem tailTrace_990796 : CollatzResearch.WordTrace tailWord_990796 prefixEnd_990796 339169719034807159862279 := by
  unfold tailWord_990796
  simp only [CollatzResearch.WordTrace]
  refine ⟨18068649459261390665028121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24091532612348520886704161 18068649459261390665028121)
  ·
    refine ⟨13551487094446042998771091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18068649459261390665028121 13551487094446042998771091)
    ·
      refine ⟨20327230641669064498156637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13551487094446042998771091 20327230641669064498156637)
      ·
        refine ⟨7622711490625899186808739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20327230641669064498156637 7622711490625899186808739)
        ·
          refine ⟨11434067235938848780213109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7622711490625899186808739 11434067235938848780213109)
          ·
            refine ⟨1071943803369267073144979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11434067235938848780213109 1071943803369267073144979)
            ·
              refine ⟨1607915705053900609717469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071943803369267073144979 1607915705053900609717469)
              ·
                refine ⟨602968389395212728644051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1607915705053900609717469 602968389395212728644051)
                ·
                  refine ⟨904452584092819092966077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 602968389395212728644051 904452584092819092966077)
                  ·
                    refine ⟨339169719034807159862279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 904452584092819092966077 339169719034807159862279)
                    ·
                      rfl

theorem cell22_990796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 1, 3].length) (baseStart_990796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990796 prefixEnd_990796 := by exact prefixLift 990796
  have htrace : WordTrace (prefixWord ++ tailWord_990796) baseStart_990796 baseEnd_990796 := by
    simpa [prefixWord, tailWord_990796, baseEnd_990796] using wordTrace_append hprefix tailTrace_990796
  have hstable : (prefixWord ++ tailWord_990796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990796).length < 2 ^ (prefixWord ++ tailWord_990796).sum := by decide
  have hdescent : baseEnd_990796 < baseStart_990796 := by decide
  rcases family_descends (prefixWord ++ tailWord_990796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990805 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 5, 4]
def baseStart_990805 : Nat := 118140960795 + 990805 * 2 ^ 59
def prefixEnd_990805 : Nat := 4983230072969 + 3 ^ 40 * 990805 * 2
def baseEnd_990805 : Nat := 339172799918734136387251

theorem tailTrace_990805 : CollatzResearch.WordTrace tailWord_990805 prefixEnd_990805 339172799918734136387251 := by
  unfold tailWord_990805
  simp only [CollatzResearch.WordTrace]
  refine ⟨36137627175490175867133869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24091751450326783911422579 36137627175490175867133869)
  ·
    refine ⟨13551610190808815950175201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36137627175490175867133869 13551610190808815950175201)
    ·
      refine ⟨10163707643106611962631401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13551610190808815950175201 10163707643106611962631401)
      ·
        refine ⟨7622780732329958971973551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10163707643106611962631401 7622780732329958971973551)
        ·
          refine ⟨11434171098494938457960327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7622780732329958971973551 11434171098494938457960327)
          ·
            refine ⟨17151256647742407686940491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11434171098494938457960327 17151256647742407686940491)
            ·
              refine ⟨25726884971613611530410737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17151256647742407686940491 25726884971613611530410737)
              ·
                refine ⟨19295163728710208647808053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25726884971613611530410737 19295163728710208647808053)
                ·
                  refine ⟨1808921599566582060732005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19295163728710208647808053 1808921599566582060732005)
                  ·
                    refine ⟨339172799918734136387251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1808921599566582060732005 339172799918734136387251)
                    ·
                      rfl

theorem cell22_990805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_990805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990805 prefixEnd_990805 := by exact prefixLift 990805
  have htrace : WordTrace (prefixWord ++ tailWord_990805) baseStart_990805 baseEnd_990805 := by
    simpa [prefixWord, tailWord_990805, baseEnd_990805] using wordTrace_append hprefix tailTrace_990805
  have hstable : (prefixWord ++ tailWord_990805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990805).length < 2 ^ (prefixWord ++ tailWord_990805).sum := by decide
  have hdescent : baseEnd_990805 < baseStart_990805 := by decide
  rcases family_descends (prefixWord ++ tailWord_990805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990813 : List Nat := [1, 4, 4, 2, 1, 2, 1, 1, 3, 3]
def baseStart_990813 : Nat := 118140960795 + 990813 * 2 ^ 59
def prefixEnd_990813 : Nat := 4983230072969 + 3 ^ 40 * 990813 * 2
def baseEnd_990813 : Nat := 339175538482224782187227

theorem tailTrace_990813 : CollatzResearch.WordTrace tailWord_990813 prefixEnd_990813 339175538482224782187227 := by
  unfold tailWord_990813
  simp only [CollatzResearch.WordTrace]
  refine ⟨36137918959461193233425093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24091945972974128822283395 36137918959461193233425093)
  ·
    refine ⟨6775859804898973731267205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36137918959461193233425093 6775859804898973731267205)
    ·
      refine ⟨1270473713418557574612601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6775859804898973731267205 1270473713418557574612601)
      ·
        refine ⟨952855285063918180959451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1270473713418557574612601 952855285063918180959451)
        ·
          refine ⟨1429282927595877271439177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952855285063918180959451 1429282927595877271439177)
          ·
            refine ⟨1071962195696907953579383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1429282927595877271439177 1071962195696907953579383)
            ·
              refine ⟨1607943293545361930369075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071962195696907953579383 1607943293545361930369075)
              ·
                refine ⟨2411914940318042895553613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1607943293545361930369075 2411914940318042895553613)
                ·
                  refine ⟨904468102619266085832605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2411914940318042895553613 904468102619266085832605)
                  ·
                    refine ⟨339175538482224782187227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 904468102619266085832605 339175538482224782187227)
                    ·
                      rfl

theorem cell22_990813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_990813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990813 prefixEnd_990813 := by exact prefixLift 990813
  have htrace : WordTrace (prefixWord ++ tailWord_990813) baseStart_990813 baseEnd_990813 := by
    simpa [prefixWord, tailWord_990813, baseEnd_990813] using wordTrace_append hprefix tailTrace_990813
  have hstable : (prefixWord ++ tailWord_990813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990813).length < 2 ^ (prefixWord ++ tailWord_990813).sum := by decide
  have hdescent : baseEnd_990813 < baseStart_990813 := by decide
  rcases family_descends (prefixWord ++ tailWord_990813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990871 : List Nat := [1, 1, 3, 3, 2, 4, 2, 2, 4]
def baseStart_990871 : Nat := 118140960795 + 990871 * 2 ^ 59
def prefixEnd_990871 : Nat := 4983230072969 + 3 ^ 40 * 990871 * 2
def baseEnd_990871 : Nat := 113065131022510654745683

theorem tailTrace_990871 : CollatzResearch.WordTrace tailWord_990871 prefixEnd_990871 113065131022510654745683 := by
  unfold tailWord_990871
  simp only [CollatzResearch.WordTrace]
  refine ⟨36140034393251069139036467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24093356262167379426024311 36140034393251069139036467)
  ·
    refine ⟨54210051589876603708554701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36140034393251069139036467 54210051589876603708554701)
    ·
      refine ⟨20328769346203726390708013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54210051589876603708554701 20328769346203726390708013)
      ·
        refine ⟨7623288504826397396515505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20328769346203726390708013 7623288504826397396515505)
        ·
          refine ⟨5717466378619798047386629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7623288504826397396515505 5717466378619798047386629)
          ·
            refine ⟨1072024945991212133884993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5717466378619798047386629 1072024945991212133884993)
            ·
              refine ⟨804018709493409100413745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072024945991212133884993 804018709493409100413745)
              ·
                refine ⟨603014032120056825310309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 804018709493409100413745 603014032120056825310309)
                ·
                  refine ⟨113065131022510654745683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 603014032120056825310309 113065131022510654745683)
                  ·
                    rfl

theorem cell22_990871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 4].length) (baseStart_990871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990871 prefixEnd_990871 := by exact prefixLift 990871
  have htrace : WordTrace (prefixWord ++ tailWord_990871) baseStart_990871 baseEnd_990871 := by
    simpa [prefixWord, tailWord_990871, baseEnd_990871] using wordTrace_append hprefix tailTrace_990871
  have hstable : (prefixWord ++ tailWord_990871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990871).length < 2 ^ (prefixWord ++ tailWord_990871).sum := by decide
  have hdescent : baseEnd_990871 < baseStart_990871 := by decide
  rcases family_descends (prefixWord ++ tailWord_990871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990895 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 2, 6]
def baseStart_990895 : Nat := 118140960795 + 990895 * 2 ^ 59
def prefixEnd_990895 : Nat := 4983230072969 + 3 ^ 40 * 990895 * 2
def baseEnd_990895 : Nat := 339203608758003901636975

theorem tailTrace_990895 : CollatzResearch.WordTrace tailWord_990895 prefixEnd_990895 339203608758003901636975 := by
  unfold tailWord_990895
  simp only [CollatzResearch.WordTrace]
  refine ⟨36140909745164121237910139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24093939830109414158606759 36140909745164121237910139)
  ·
    refine ⟨54211364617746181856865209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36140909745164121237910139 54211364617746181856865209)
    ·
      refine ⟨40658523463309636392648907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54211364617746181856865209 40658523463309636392648907)
      ·
        refine ⟨60987785194964454588973361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40658523463309636392648907 60987785194964454588973361)
        ·
          refine ⟨45740838896223340941730021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60987785194964454588973361 45740838896223340941730021)
          ·
            refine ⟨8576407293041876426574379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45740838896223340941730021 8576407293041876426574379)
            ·
              refine ⟨12864610939562814639861569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8576407293041876426574379 12864610939562814639861569)
              ·
                refine ⟨9648458204672110979896177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12864610939562814639861569 9648458204672110979896177)
                ·
                  refine ⟨7236343653504083234922133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9648458204672110979896177 7236343653504083234922133)
                  ·
                    refine ⟨339203608758003901636975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7236343653504083234922133 339203608758003901636975)
                    ·
                      rfl

theorem cell22_990895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_990895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990895 prefixEnd_990895 := by exact prefixLift 990895
  have htrace : WordTrace (prefixWord ++ tailWord_990895) baseStart_990895 baseEnd_990895 := by
    simpa [prefixWord, tailWord_990895, baseEnd_990895] using wordTrace_append hprefix tailTrace_990895
  have hstable : (prefixWord ++ tailWord_990895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990895).length < 2 ^ (prefixWord ++ tailWord_990895).sum := by decide
  have hdescent : baseEnd_990895 < baseStart_990895 := by decide
  rcases family_descends (prefixWord ++ tailWord_990895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990901 : List Nat := [1, 3, 3, 3, 2, 2, 1, 1, 2, 4]
def baseStart_990901 : Nat := 118140960795 + 990901 * 2 ^ 59
def prefixEnd_990901 : Nat := 4983230072969 + 3 ^ 40 * 990901 * 2
def baseEnd_990901 : Nat := 339205662680621885986957

theorem tailTrace_990901 : CollatzResearch.WordTrace tailWord_990901 prefixEnd_990901 339205662680621885986957 := by
  unfold tailWord_990901
  simp only [CollatzResearch.WordTrace]
  refine ⟨36141128583142384262628557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24094085722094922841752371 36141128583142384262628557)
  ·
    refine ⟨13552923218678394098485709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36141128583142384262628557 13552923218678394098485709)
    ·
      refine ⟨5082346207004397786932141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13552923218678394098485709 5082346207004397786932141)
      ·
        refine ⟨1905879827626649170099553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5082346207004397786932141 1905879827626649170099553)
        ·
          refine ⟨1429409870719986877574665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1905879827626649170099553 1429409870719986877574665)
          ·
            refine ⟨1072057403039990158180999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1429409870719986877574665 1072057403039990158180999)
            ·
              refine ⟨1608086104559985237271499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1072057403039990158180999 1608086104559985237271499)
              ·
                refine ⟨2412129156839977855907249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1608086104559985237271499 2412129156839977855907249)
                ·
                  refine ⟨1809096867629983391930437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2412129156839977855907249 1809096867629983391930437)
                  ·
                    refine ⟨339205662680621885986957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1809096867629983391930437 339205662680621885986957)
                    ·
                      rfl

theorem cell22_990901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_990901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_990901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_990901 prefixEnd_990901 := by exact prefixLift 990901
  have htrace : WordTrace (prefixWord ++ tailWord_990901) baseStart_990901 baseEnd_990901 := by
    simpa [prefixWord, tailWord_990901, baseEnd_990901] using wordTrace_append hprefix tailTrace_990901
  have hstable : (prefixWord ++ tailWord_990901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990901).length < 2 ^ (prefixWord ++ tailWord_990901).sum := by decide
  have hdescent : baseEnd_990901 < baseStart_990901 := by decide
  rcases family_descends (prefixWord ++ tailWord_990901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991038 : List Nat := [4, 2, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_991038 : Nat := 118140960795 + 991038 * 2 ^ 59
def prefixEnd_991038 : Nat := 4983230072969 + 3 ^ 40 * 991038 * 2
def baseEnd_991038 : Nat := 339252560580399195311537

theorem tailTrace_991038 : CollatzResearch.WordTrace tailWord_991038 prefixEnd_991038 339252560580399195311537 := by
  unfold tailWord_991038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4518265672955757082545721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24097416922430704440243845 4518265672955757082545721)
  ·
    refine ⟨3388699254716817811909291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4518265672955757082545721 3388699254716817811909291)
    ·
      refine ⟨5083048882075226717863937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3388699254716817811909291 5083048882075226717863937)
      ·
        refine ⟨3812286661556420038397953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5083048882075226717863937 3812286661556420038397953)
        ·
          refine ⟨2859214996167315028798465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3812286661556420038397953 2859214996167315028798465)
          ·
            refine ⟨2144411247125486271598849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2859214996167315028798465 2144411247125486271598849)
            ·
              refine ⟨1608308435344114703699137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2144411247125486271598849 1608308435344114703699137)
              ·
                refine ⟨1206231326508086027774353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1608308435344114703699137 1206231326508086027774353)
                ·
                  refine ⟨904673494881064520830765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1206231326508086027774353 904673494881064520830765)
                  ·
                    refine ⟨339252560580399195311537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 904673494881064520830765 339252560580399195311537)
                    ·
                      rfl

theorem cell22_991038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_991038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991038 prefixEnd_991038 := by exact prefixLift 991038
  have htrace : WordTrace (prefixWord ++ tailWord_991038) baseStart_991038 baseEnd_991038 := by
    simpa [prefixWord, tailWord_991038, baseEnd_991038] using wordTrace_append hprefix tailTrace_991038
  have hstable : (prefixWord ++ tailWord_991038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991038).length < 2 ^ (prefixWord ++ tailWord_991038).sum := by decide
  have hdescent : baseEnd_991038 < baseStart_991038 := by decide
  rcases family_descends (prefixWord ++ tailWord_991038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991047 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 2, 6]
def baseStart_991047 : Nat := 118140960795 + 991047 * 2 ^ 59
def prefixEnd_991047 : Nat := 4983230072969 + 3 ^ 40 * 991047 * 2
def baseEnd_991047 : Nat := 339255641464326171836509

theorem tailTrace_991047 : CollatzResearch.WordTrace tailWord_991047 prefixEnd_991047 339255641464326171836509 := by
  unfold tailWord_991047
  simp only [CollatzResearch.WordTrace]
  refine ⟨36146453640613451197443395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24097635760408967464962263 36146453640613451197443395)
  ·
    refine ⟨54219680460920176796165093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36146453640613451197443395 54219680460920176796165093)
    ·
      refine ⟨10166190086422533149280955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54219680460920176796165093 10166190086422533149280955)
      ·
        refine ⟨15249285129633799723921433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10166190086422533149280955 15249285129633799723921433)
        ·
          refine ⟨11436963847225349792941075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15249285129633799723921433 11436963847225349792941075)
          ·
            refine ⟨17155445770838024689411613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11436963847225349792941075 17155445770838024689411613)
            ·
              refine ⟨6433292164064259258529355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17155445770838024689411613 6433292164064259258529355)
              ·
                refine ⟨9649938246096388887794033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6433292164064259258529355 9649938246096388887794033)
                ·
                  refine ⟨7237453684572291665845525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9649938246096388887794033 7237453684572291665845525)
                  ·
                    refine ⟨339255641464326171836509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7237453684572291665845525 339255641464326171836509)
                    ·
                      rfl

theorem cell22_991047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_991047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991047 prefixEnd_991047 := by exact prefixLift 991047
  have htrace : WordTrace (prefixWord ++ tailWord_991047) baseStart_991047 baseEnd_991047 := by
    simpa [prefixWord, tailWord_991047, baseEnd_991047] using wordTrace_append hprefix tailTrace_991047
  have hstable : (prefixWord ++ tailWord_991047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991047).length < 2 ^ (prefixWord ++ tailWord_991047).sum := by decide
  have hdescent : baseEnd_991047 < baseStart_991047 := by decide
  rcases family_descends (prefixWord ++ tailWord_991047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991049 : List Nat := [1, 2, 1, 1, 2, 4, 2, 3, 3, 3]
def baseStart_991049 : Nat := 118140960795 + 991049 * 2 ^ 59
def prefixEnd_991049 : Nat := 4983230072969 + 3 ^ 40 * 991049 * 2
def baseEnd_991049 : Nat := 339256326105198833286503

theorem tailTrace_991049 : CollatzResearch.WordTrace tailWord_991049 prefixEnd_991049 339256326105198833286503 := by
  unfold tailWord_991049
  simp only [CollatzResearch.WordTrace]
  refine ⟨36146526586606205539016201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24097684391070803692677467 36146526586606205539016201)
  ·
    refine ⟨27109894939954654154262151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36146526586606205539016201 27109894939954654154262151)
    ·
      refine ⟨40664842409931981231393227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27109894939954654154262151 40664842409931981231393227)
      ·
        refine ⟨60997263614897971847089841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40664842409931981231393227 60997263614897971847089841)
        ·
          refine ⟨45747947711173478885317381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60997263614897971847089841 45747947711173478885317381)
          ·
            refine ⟨8577740195845027290997009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45747947711173478885317381 8577740195845027290997009)
            ·
              refine ⟨6433305146883770468247757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8577740195845027290997009 6433305146883770468247757)
              ·
                refine ⟨2412489430081413925592909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6433305146883770468247757 2412489430081413925592909)
                ·
                  refine ⟨904683536280530222097341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2412489430081413925592909 904683536280530222097341)
                  ·
                    refine ⟨339256326105198833286503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 904683536280530222097341 339256326105198833286503)
                    ·
                      rfl

theorem cell22_991049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 3].length) (baseStart_991049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991049 prefixEnd_991049 := by exact prefixLift 991049
  have htrace : WordTrace (prefixWord ++ tailWord_991049) baseStart_991049 baseEnd_991049 := by
    simpa [prefixWord, tailWord_991049, baseEnd_991049] using wordTrace_append hprefix tailTrace_991049
  have hstable : (prefixWord ++ tailWord_991049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991049).length < 2 ^ (prefixWord ++ tailWord_991049).sum := by decide
  have hdescent : baseEnd_991049 < baseStart_991049 := by decide
  rcases family_descends (prefixWord ++ tailWord_991049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991077 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 3, 7]
def baseStart_991077 : Nat := 118140960795 + 991077 * 2 ^ 59
def prefixEnd_991077 : Nat := 4983230072969 + 3 ^ 40 * 991077 * 2
def baseEnd_991077 : Nat := 339265911077416093586417

theorem tailTrace_991077 : CollatzResearch.WordTrace tailWord_991077 prefixEnd_991077 339265911077416093586417 := by
  unfold tailWord_991077
  simp only [CollatzResearch.WordTrace]
  refine ⟨36147547830504766321035485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24098365220336510880690323 36147547830504766321035485)
  ·
    refine ⟨13555330436439287370388307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36147547830504766321035485 13555330436439287370388307)
    ·
      refine ⟨20332995654658931055582461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13555330436439287370388307 20332995654658931055582461)
      ·
        refine ⟨7624873370497099145843423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20332995654658931055582461 7624873370497099145843423)
        ·
          refine ⟨11437310055745648718765135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7624873370497099145843423 11437310055745648718765135)
          ·
            refine ⟨17155965083618473078147703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11437310055745648718765135 17155965083618473078147703)
            ·
              refine ⟨25733947625427709617221555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17155965083618473078147703 25733947625427709617221555)
              ·
                refine ⟨38600921438141564425832333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25733947625427709617221555 38600921438141564425832333)
                ·
                  refine ⟨14475345539303086659687125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38600921438141564425832333 14475345539303086659687125)
                  ·
                    refine ⟨339265911077416093586417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14475345539303086659687125 339265911077416093586417)
                    ·
                      rfl

theorem cell22_991077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_991077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991077 prefixEnd_991077 := by exact prefixLift 991077
  have htrace : WordTrace (prefixWord ++ tailWord_991077) baseStart_991077 baseEnd_991077 := by
    simpa [prefixWord, tailWord_991077, baseEnd_991077] using wordTrace_append hprefix tailTrace_991077
  have hstable : (prefixWord ++ tailWord_991077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991077).length < 2 ^ (prefixWord ++ tailWord_991077).sum := by decide
  have hdescent : baseEnd_991077 < baseStart_991077 := by decide
  rcases family_descends (prefixWord ++ tailWord_991077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991134 : List Nat := [4, 3, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_991134 : Nat := 118140960795 + 991134 * 2 ^ 59
def prefixEnd_991134 : Nat := 4983230072969 + 3 ^ 40 * 991134 * 2
def baseEnd_991134 : Nat := 339285423342286944911243

theorem tailTrace_991134 : CollatzResearch.WordTrace tailWord_991134 prefixEnd_991134 339285423342286944911243 := by
  unfold tailWord_991134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4518703348912283131982557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24099751194198843370573637 4518703348912283131982557)
  ·
    refine ⟨1694513755842106174493459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4518703348912283131982557 1694513755842106174493459)
    ·
      refine ⟨2541770633763159261740189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1694513755842106174493459 2541770633763159261740189)
      ·
        refine ⟨953163987661184723152571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2541770633763159261740189 953163987661184723152571)
        ·
          refine ⟨1429745981491777084728857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953163987661184723152571 1429745981491777084728857)
          ·
            refine ⟨1072309486118832813546643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1429745981491777084728857 1072309486118832813546643)
            ·
              refine ⟨1608464229178249220319965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1072309486118832813546643 1608464229178249220319965)
              ·
                refine ⟨603174085941843457619987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1608464229178249220319965 603174085941843457619987)
                ·
                  refine ⟨904761128912765186429981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 603174085941843457619987 904761128912765186429981)
                  ·
                    refine ⟨339285423342286944911243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 904761128912765186429981 339285423342286944911243)
                    ·
                      rfl

theorem cell22_991134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_991134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991134 prefixEnd_991134 := by exact prefixLift 991134
  have htrace : WordTrace (prefixWord ++ tailWord_991134) baseStart_991134 baseEnd_991134 := by
    simpa [prefixWord, tailWord_991134, baseEnd_991134] using wordTrace_append hprefix tailTrace_991134
  have hstable : (prefixWord ++ tailWord_991134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991134).length < 2 ^ (prefixWord ++ tailWord_991134).sum := by decide
  have hdescent : baseEnd_991134 < baseStart_991134 := by decide
  rcases family_descends (prefixWord ++ tailWord_991134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991229 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_991229 : Nat := 118140960795 + 991229 * 2 ^ 59
def prefixEnd_991229 : Nat := 4983230072969 + 3 ^ 40 * 991229 * 2
def baseEnd_991229 : Nat := 339317943783738363785951

theorem tailTrace_991229 : CollatzResearch.WordTrace tailWord_991229 prefixEnd_991229 339317943783738363785951 := by
  unfold tailWord_991229
  simp only [CollatzResearch.WordTrace]
  refine ⟨36153091725954096280568741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24102061150636064187045827 36153091725954096280568741)
  ·
    refine ⟨6778704698616393052606639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36153091725954096280568741 6778704698616393052606639)
    ·
      refine ⟨10168057047924589578909959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6778704698616393052606639 10168057047924589578909959)
      ·
        refine ⟨15252085571886884368364939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10168057047924589578909959 15252085571886884368364939)
        ·
          refine ⟨22878128357830326552547409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15252085571886884368364939 22878128357830326552547409)
          ·
            refine ⟨17158596268372744914410557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22878128357830326552547409 17158596268372744914410557)
            ·
              refine ⟨6434473600639779342903959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17158596268372744914410557 6434473600639779342903959)
              ·
                refine ⟨9651710400959669014355939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6434473600639779342903959 9651710400959669014355939)
                ·
                  refine ⟨14477565601439503521533909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9651710400959669014355939 14477565601439503521533909)
                  ·
                    refine ⟨339317943783738363785951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14477565601439503521533909 339317943783738363785951)
                    ·
                      rfl

theorem cell22_991229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_991229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991229 prefixEnd_991229 := by exact prefixLift 991229
  have htrace : WordTrace (prefixWord ++ tailWord_991229) baseStart_991229 baseEnd_991229 := by
    simpa [prefixWord, tailWord_991229, baseEnd_991229] using wordTrace_append hprefix tailTrace_991229
  have hstable : (prefixWord ++ tailWord_991229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991229).length < 2 ^ (prefixWord ++ tailWord_991229).sum := by decide
  have hdescent : baseEnd_991229 < baseStart_991229 := by decide
  rcases family_descends (prefixWord ++ tailWord_991229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991265 : List Nat := [1, 2, 3, 2, 5, 1, 1, 2, 5]
def baseStart_991265 : Nat := 118140960795 + 991265 * 2 ^ 59
def prefixEnd_991265 : Nat := 4983230072969 + 3 ^ 40 * 991265 * 2
def baseEnd_991265 : Nat := 113110089106482089961947

theorem tailTrace_991265 : CollatzResearch.WordTrace tailWord_991265 prefixEnd_991265 113110089106482089961947 := by
  unfold tailWord_991265
  simp only [CollatzResearch.WordTrace]
  refine ⟨36154404753823674428879249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24102936502549116285919499 36154404753823674428879249)
  ·
    refine ⟨27115803565367755821659437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36154404753823674428879249 27115803565367755821659437)
    ·
      refine ⟨10168426337012908433122289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27115803565367755821659437 10168426337012908433122289)
      ·
        refine ⟨7626319752759681324841717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10168426337012908433122289 7626319752759681324841717)
        ·
          refine ⟨714967476821220124203911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7626319752759681324841717 714967476821220124203911)
          ·
            refine ⟨1072451215231830186305867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714967476821220124203911 1072451215231830186305867)
            ·
              refine ⟨1608676822847745279458801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1072451215231830186305867 1608676822847745279458801)
              ·
                refine ⟨1206507617135808959594101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1608676822847745279458801 1206507617135808959594101)
                ·
                  refine ⟨113110089106482089961947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1206507617135808959594101 113110089106482089961947)
                  ·
                    rfl

theorem cell22_991265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 5].length) (baseStart_991265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991265 prefixEnd_991265 := by exact prefixLift 991265
  have htrace : WordTrace (prefixWord ++ tailWord_991265) baseStart_991265 baseEnd_991265 := by
    simpa [prefixWord, tailWord_991265, baseEnd_991265] using wordTrace_append hprefix tailTrace_991265
  have hstable : (prefixWord ++ tailWord_991265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991265).length < 2 ^ (prefixWord ++ tailWord_991265).sum := by decide
  have hdescent : baseEnd_991265 < baseStart_991265 := by decide
  rcases family_descends (prefixWord ++ tailWord_991265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991306 : List Nat := [3, 1, 2, 1, 1, 2, 1, 5, 2, 4]
def baseStart_991306 : Nat := 118140960795 + 991306 * 2 ^ 59
def prefixEnd_991306 : Nat := 4983230072969 + 3 ^ 40 * 991306 * 2
def baseEnd_991306 : Nat := 339344302457335829610715

theorem tailTrace_991306 : CollatzResearch.WordTrace tailWord_991306 prefixEnd_991306 339344302457335829610715 := by
  unfold tailWord_991306
  simp only [CollatzResearch.WordTrace]
  refine ⟨9038975036668784607780443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24103933431116758954081181 9038975036668784607780443)
  ·
    refine ⟨13558462555003176911670665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9038975036668784607780443 13558462555003176911670665)
    ·
      refine ⟨10168846916252382683752999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13558462555003176911670665 10168846916252382683752999)
      ·
        refine ⟨15253270374378574025629499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10168846916252382683752999 15253270374378574025629499)
        ·
          refine ⟨22879905561567861038444249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15253270374378574025629499 22879905561567861038444249)
          ·
            refine ⟨17159929171175895778833187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22879905561567861038444249 17159929171175895778833187)
            ·
              refine ⟨25739893756763843668249781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17159929171175895778833187 25739893756763843668249781)
              ·
                refine ⟨2413115039696610343898417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25739893756763843668249781 2413115039696610343898417)
                ·
                  refine ⟨1809836279772457757923813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2413115039696610343898417 1809836279772457757923813)
                  ·
                    refine ⟨339344302457335829610715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1809836279772457757923813 339344302457335829610715)
                    ·
                      rfl

theorem cell22_991306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_991306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991306 prefixEnd_991306 := by exact prefixLift 991306
  have htrace : WordTrace (prefixWord ++ tailWord_991306) baseStart_991306 baseEnd_991306 := by
    simpa [prefixWord, tailWord_991306, baseEnd_991306] using wordTrace_append hprefix tailTrace_991306
  have hstable : (prefixWord ++ tailWord_991306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991306).length < 2 ^ (prefixWord ++ tailWord_991306).sum := by decide
  have hdescent : baseEnd_991306 < baseStart_991306 := by decide
  rcases family_descends (prefixWord ++ tailWord_991306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991310 : List Nat := [4, 1, 1, 1, 1, 6, 1, 3, 4]
def baseStart_991310 : Nat := 118140960795 + 991310 * 2 ^ 59
def prefixEnd_991310 : Nat := 4983230072969 + 3 ^ 40 * 991310 * 2
def baseEnd_991310 : Nat := 113115223913027050836901

theorem tailTrace_991310 : CollatzResearch.WordTrace tailWord_991310 prefixEnd_991310 113115223913027050836901 := by
  unfold tailWord_991310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4519505754832580889283423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24104030692440431409511589 4519505754832580889283423)
  ·
    refine ⟨6779258632248871333925135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4519505754832580889283423 6779258632248871333925135)
    ·
      refine ⟨10168887948373307000887703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6779258632248871333925135 10168887948373307000887703)
      ·
        refine ⟨15253331922559960501331555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10168887948373307000887703 15253331922559960501331555)
        ·
          refine ⟨22879997883839940751997333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15253331922559960501331555 22879997883839940751997333)
          ·
            refine ⟨1072499900804997222749875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22879997883839940751997333 1072499900804997222749875)
            ·
              refine ⟨1608749851207495834124813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1072499900804997222749875 1608749851207495834124813)
              ·
                refine ⟨603281194202810937796805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1608749851207495834124813 603281194202810937796805)
                ·
                  refine ⟨113115223913027050836901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 603281194202810937796805 113115223913027050836901)
                  ·
                    rfl

theorem cell22_991310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_991310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991310 prefixEnd_991310 := by exact prefixLift 991310
  have htrace : WordTrace (prefixWord ++ tailWord_991310) baseStart_991310 baseEnd_991310 := by
    simpa [prefixWord, tailWord_991310, baseEnd_991310] using wordTrace_append hprefix tailTrace_991310
  have hstable : (prefixWord ++ tailWord_991310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991310).length < 2 ^ (prefixWord ++ tailWord_991310).sum := by decide
  have hdescent : baseEnd_991310 < baseStart_991310 := by decide
  rcases family_descends (prefixWord ++ tailWord_991310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991325 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 4, 3]
def baseStart_991325 : Nat := 118140960795 + 991325 * 2 ^ 59
def prefixEnd_991325 : Nat := 4983230072969 + 3 ^ 40 * 991325 * 2
def baseEnd_991325 : Nat := 339350806545626113385657

theorem tailTrace_991325 : CollatzResearch.WordTrace tailWord_991325 prefixEnd_991325 339350806545626113385657 := by
  unfold tailWord_991325
  simp only [CollatzResearch.WordTrace]
  refine ⟨36156593133606304676063429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24104395422404203117375619 36156593133606304676063429)
  ·
    refine ⟨6779361212551182126761893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36156593133606304676063429 6779361212551182126761893)
    ·
      refine ⟨1271130227353346648767855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6779361212551182126761893 1271130227353346648767855)
      ·
        refine ⟨1906695341030019973151783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1271130227353346648767855 1906695341030019973151783)
        ·
          refine ⟨2860043011545029959727675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1906695341030019973151783 2860043011545029959727675)
          ·
            refine ⟨4290064517317544939591513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2860043011545029959727675 4290064517317544939591513)
            ·
              refine ⟨3217548387988158704693635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4290064517317544939591513 3217548387988158704693635)
              ·
                refine ⟨4826322581982238057040453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3217548387988158704693635 4826322581982238057040453)
                ·
                  refine ⟨904935484121669635695085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4826322581982238057040453 904935484121669635695085)
                  ·
                    refine ⟨339350806545626113385657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 904935484121669635695085 339350806545626113385657)
                    ·
                      rfl

theorem cell22_991325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_991325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991325 prefixEnd_991325 := by exact prefixLift 991325
  have htrace : WordTrace (prefixWord ++ tailWord_991325) baseStart_991325 baseEnd_991325 := by
    simpa [prefixWord, tailWord_991325, baseEnd_991325] using wordTrace_append hprefix tailTrace_991325
  have hstable : (prefixWord ++ tailWord_991325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991325).length < 2 ^ (prefixWord ++ tailWord_991325).sum := by decide
  have hdescent : baseEnd_991325 < baseStart_991325 := by decide
  rcases family_descends (prefixWord ++ tailWord_991325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991338 : List Nat := [3, 1, 3, 2, 3, 1, 2, 7]
def baseStart_991338 : Nat := 118140960795 + 991338 * 2 ^ 59
def prefixEnd_991338 : Nat := 4983230072969 + 3 ^ 40 * 991338 * 2
def baseEnd_991338 : Nat := 37706139634588712534513

theorem tailTrace_991338 : CollatzResearch.WordTrace tailWord_991338 prefixEnd_991338 37706139634588712534513 := by
  unfold tailWord_991338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9039266820639801974071667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24104711521706138597524445 9039266820639801974071667)
  ·
    refine ⟨13558900230959702961107501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9039266820639801974071667 13558900230959702961107501)
    ·
      refine ⟨5084587586609888610415313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13558900230959702961107501 5084587586609888610415313)
      ·
        refine ⟨3813440689957416457811485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5084587586609888610415313 3813440689957416457811485)
        ·
          refine ⟨1430040258734031171679307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3813440689957416457811485 1430040258734031171679307)
          ·
            refine ⟨2145060388101046757518961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430040258734031171679307 2145060388101046757518961)
            ·
              refine ⟨1608795291075785068139221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2145060388101046757518961 1608795291075785068139221)
              ·
                refine ⟨37706139634588712534513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1608795291075785068139221 37706139634588712534513)
                ·
                  rfl

theorem cell22_991338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 7].length) (baseStart_991338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991338 prefixEnd_991338 := by exact prefixLift 991338
  have htrace : WordTrace (prefixWord ++ tailWord_991338) baseStart_991338 baseEnd_991338 := by
    simpa [prefixWord, tailWord_991338, baseEnd_991338] using wordTrace_append hprefix tailTrace_991338
  have hstable : (prefixWord ++ tailWord_991338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991338).length < 2 ^ (prefixWord ++ tailWord_991338).sum := by decide
  have hdescent : baseEnd_991338 < baseStart_991338 := by decide
  rcases family_descends (prefixWord ++ tailWord_991338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991381 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 2, 5]
def baseStart_991381 : Nat := 118140960795 + 991381 * 2 ^ 59
def prefixEnd_991381 : Nat := 4983230072969 + 3 ^ 40 * 991381 * 2
def baseEnd_991381 : Nat := 339369976490060633985485

theorem tailTrace_991381 : CollatzResearch.WordTrace tailWord_991381 prefixEnd_991381 339369976490060633985485 := by
  unfold tailWord_991381
  simp only [CollatzResearch.WordTrace]
  refine ⟨36158635621403426240101997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24105757080935617493401331 36158635621403426240101997)
  ·
    refine ⟨13559488358026284840038249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36158635621403426240101997 13559488358026284840038249)
    ·
      refine ⟨10169616268519713630028687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13559488358026284840038249 10169616268519713630028687)
      ·
        refine ⟨15254424402779570445043031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10169616268519713630028687 15254424402779570445043031)
        ·
          refine ⟨22881636604169355667564547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15254424402779570445043031 22881636604169355667564547)
          ·
            refine ⟨34322454906254033501346821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22881636604169355667564547 34322454906254033501346821)
            ·
              refine ⟨6435460294922631281502529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34322454906254033501346821 6435460294922631281502529)
              ·
                refine ⟨4826595221191973461126897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6435460294922631281502529 4826595221191973461126897)
                ·
                  refine ⟨3619946415893980095845173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4826595221191973461126897 3619946415893980095845173)
                  ·
                    refine ⟨339369976490060633985485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3619946415893980095845173 339369976490060633985485)
                    ·
                      rfl

theorem cell22_991381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_991381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991381 prefixEnd_991381 := by exact prefixLift 991381
  have htrace : WordTrace (prefixWord ++ tailWord_991381) baseStart_991381 baseEnd_991381 := by
    simpa [prefixWord, tailWord_991381, baseEnd_991381] using wordTrace_append hprefix tailTrace_991381
  have hstable : (prefixWord ++ tailWord_991381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991381).length < 2 ^ (prefixWord ++ tailWord_991381).sum := by decide
  have hdescent : baseEnd_991381 < baseStart_991381 := by decide
  rcases family_descends (prefixWord ++ tailWord_991381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991445 : List Nat := [1, 3, 2, 4, 2, 1, 2, 1, 6]
def baseStart_991445 : Nat := 118140960795 + 991445 * 2 ^ 59
def prefixEnd_991445 : Nat := 4983230072969 + 3 ^ 40 * 991445 * 2
def baseEnd_991445 : Nat := 113130628332661933461763

theorem tailTrace_991445 : CollatzResearch.WordTrace tailWord_991445 prefixEnd_991445 113130628332661933461763 := by
  unfold tailWord_991445
  simp only [CollatzResearch.WordTrace]
  refine ⟨36160969893171565170431789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24107313262114376780287859 36160969893171565170431789)
  ·
    refine ⟨13560363709939336938911921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36160969893171565170431789 13560363709939336938911921)
    ·
      refine ⟨10170272782454502704183941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13560363709939336938911921 10170272782454502704183941)
      ·
        refine ⟨1906926146710219257034489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10170272782454502704183941 1906926146710219257034489)
        ·
          refine ⟨1430194610032664442775867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1906926146710219257034489 1430194610032664442775867)
          ·
            refine ⟨2145291915048996664163801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430194610032664442775867 2145291915048996664163801)
            ·
              refine ⟨1608968936286747498122851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2145291915048996664163801 1608968936286747498122851)
              ·
                refine ⟨2413453404430121247184277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1608968936286747498122851 2413453404430121247184277)
                ·
                  refine ⟨113130628332661933461763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2413453404430121247184277 113130628332661933461763)
                  ·
                    rfl

theorem cell22_991445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_991445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991445 prefixEnd_991445 := by exact prefixLift 991445
  have htrace : WordTrace (prefixWord ++ tailWord_991445) baseStart_991445 baseEnd_991445 := by
    simpa [prefixWord, tailWord_991445, baseEnd_991445] using wordTrace_append hprefix tailTrace_991445
  have hstable : (prefixWord ++ tailWord_991445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991445).length < 2 ^ (prefixWord ++ tailWord_991445).sum := by decide
  have hdescent : baseEnd_991445 < baseStart_991445 := by decide
  rcases family_descends (prefixWord ++ tailWord_991445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991456 : List Nat := [2, 1, 1, 3, 1, 3, 2, 9]
def baseStart_991456 : Nat := 118140960795 + 991456 * 2 ^ 59
def prefixEnd_991456 : Nat := 4983230072969 + 3 ^ 40 * 991456 * 2
def baseEnd_991456 : Nat := 37710627835865048706695

theorem tailTrace_991456 : CollatzResearch.WordTrace tailWord_991456 prefixEnd_991456 37710627835865048706695 := by
  unfold tailWord_991456
  simp only [CollatzResearch.WordTrace]
  refine ⟨18080685548065857024541111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24107580730754476032721481 18080685548065857024541111)
  ·
    refine ⟨27121028322098785536811667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18080685548065857024541111 27121028322098785536811667)
    ·
      refine ⟨40681542483148178305217501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27121028322098785536811667 40681542483148178305217501)
      ·
        refine ⟨15255578431180566864456563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40681542483148178305217501 15255578431180566864456563)
        ·
          refine ⟨22883367646770850296684845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15255578431180566864456563 22883367646770850296684845)
          ·
            refine ⟨8581262867539068861256817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22883367646770850296684845 8581262867539068861256817)
            ·
              refine ⟨6435947150654301645942613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8581262867539068861256817 6435947150654301645942613)
              ·
                refine ⟨37710627835865048706695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6435947150654301645942613 37710627835865048706695)
                ·
                  rfl

theorem cell22_991456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 9].length) (baseStart_991456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991456 prefixEnd_991456 := by exact prefixLift 991456
  have htrace : WordTrace (prefixWord ++ tailWord_991456) baseStart_991456 baseEnd_991456 := by
    simpa [prefixWord, tailWord_991456, baseEnd_991456] using wordTrace_append hprefix tailTrace_991456
  have hstable : (prefixWord ++ tailWord_991456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991456).length < 2 ^ (prefixWord ++ tailWord_991456).sum := by decide
  have hdescent : baseEnd_991456 < baseStart_991456 := by decide
  rcases family_descends (prefixWord ++ tailWord_991456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991473 : List Nat := [1, 2, 2, 2, 2, 1, 6, 6]
def baseStart_991473 : Nat := 118140960795 + 991473 * 2 ^ 59
def prefixEnd_991473 : Nat := 4983230072969 + 3 ^ 40 * 991473 * 2
def baseEnd_991473 : Nat := 37711274441133673409467

theorem tailTrace_991473 : CollatzResearch.WordTrace tailWord_991473 prefixEnd_991473 37711274441133673409467 := by
  unfold tailWord_991473
  simp only [CollatzResearch.WordTrace]
  refine ⟨36161991137070125952451073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24107994091380083968300715 36161991137070125952451073)
  ·
    refine ⟨27121493352802594464338305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36161991137070125952451073 27121493352802594464338305)
    ·
      refine ⟨20341120014601945848253729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27121493352802594464338305 20341120014601945848253729)
      ·
        refine ⟨15255840010951459386190297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20341120014601945848253729 15255840010951459386190297)
        ·
          refine ⟨11441880008213594539642723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15255840010951459386190297 11441880008213594539642723)
          ·
            refine ⟨17162820012320391809464085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11441880008213594539642723 17162820012320391809464085)
            ·
              refine ⟨804507188077518366068629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17162820012320391809464085 804507188077518366068629)
              ·
                refine ⟨37711274441133673409467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 804507188077518366068629 37711274441133673409467)
                ·
                  rfl

theorem cell22_991473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 6].length) (baseStart_991473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991473 prefixEnd_991473 := by exact prefixLift 991473
  have htrace : WordTrace (prefixWord ++ tailWord_991473) baseStart_991473 baseEnd_991473 := by
    simpa [prefixWord, tailWord_991473, baseEnd_991473] using wordTrace_append hprefix tailTrace_991473
  have hstable : (prefixWord ++ tailWord_991473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991473).length < 2 ^ (prefixWord ++ tailWord_991473).sum := by decide
  have hdescent : baseEnd_991473 < baseStart_991473 := by decide
  rcases family_descends (prefixWord ++ tailWord_991473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991488 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 5, 3]
def baseStart_991488 : Nat := 118140960795 + 991488 * 2 ^ 59
def prefixEnd_991488 : Nat := 4983230072969 + 3 ^ 40 * 991488 * 2
def baseEnd_991488 : Nat := 339406604776748021560157

theorem tailTrace_991488 : CollatzResearch.WordTrace tailWord_991488 prefixEnd_991488 339406604776748021560157 := by
  unfold tailWord_991488
  simp only [CollatzResearch.WordTrace]
  refine ⟨18081269116007891757123559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24108358821343855676164745 18081269116007891757123559)
  ·
    refine ⟨27121903674011837635685339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18081269116007891757123559 27121903674011837635685339)
    ·
      refine ⟨40682855511017756453528009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27121903674011837635685339 40682855511017756453528009)
      ·
        refine ⟨30512141633263317340146007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40682855511017756453528009 30512141633263317340146007)
        ·
          refine ⟨45768212449894976010219011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30512141633263317340146007 45768212449894976010219011)
          ·
            refine ⟨68652318674842464015328517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45768212449894976010219011 68652318674842464015328517)
            ·
              refine ⟨12872309751532962002874097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68652318674842464015328517 12872309751532962002874097)
              ·
                refine ⟨9654232313649721502155573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12872309751532962002874097 9654232313649721502155573)
                ·
                  refine ⟨905084279404661390827085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9654232313649721502155573 905084279404661390827085)
                  ·
                    refine ⟨339406604776748021560157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 905084279404661390827085 339406604776748021560157)
                    ·
                      rfl

theorem cell22_991488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 5, 3].length) (baseStart_991488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991488 prefixEnd_991488 := by exact prefixLift 991488
  have htrace : WordTrace (prefixWord ++ tailWord_991488) baseStart_991488 baseEnd_991488 := by
    simpa [prefixWord, tailWord_991488, baseEnd_991488] using wordTrace_append hprefix tailTrace_991488
  have hstable : (prefixWord ++ tailWord_991488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991488).length < 2 ^ (prefixWord ++ tailWord_991488).sum := by decide
  have hdescent : baseEnd_991488 < baseStart_991488 := by decide
  rcases family_descends (prefixWord ++ tailWord_991488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991490 : List Nat := [3, 4, 1, 1, 2, 3, 8]
def baseStart_991490 : Nat := 118140960795 + 991490 * 2 ^ 59
def prefixEnd_991490 : Nat := 4983230072969 + 3 ^ 40 * 991490 * 2
def baseEnd_991490 : Nat := 12570640348800766037413

theorem tailTrace_991490 : CollatzResearch.WordTrace tailWord_991490 prefixEnd_991490 12570640348800766037413 := by
  unfold tailWord_991490
  simp only [CollatzResearch.WordTrace]
  refine ⟨9040652794502134463954981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24108407452005691903879949 9040652794502134463954981)
  ·
    refine ⟨1695122398969150211991559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9040652794502134463954981 1695122398969150211991559)
    ·
      refine ⟨2542683598453725317987339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1695122398969150211991559 2542683598453725317987339)
      ·
        refine ⟨3814025397680587976981009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2542683598453725317987339 3814025397680587976981009)
        ·
          refine ⟨2860519048260440982735757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3814025397680587976981009 2860519048260440982735757)
          ·
            refine ⟨1072694643097665368525909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2860519048260440982735757 1072694643097665368525909)
            ·
              refine ⟨12570640348800766037413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1072694643097665368525909 12570640348800766037413)
              ·
                rfl

theorem cell22_991490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 8].length) (baseStart_991490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991490 prefixEnd_991490 := by exact prefixLift 991490
  have htrace : WordTrace (prefixWord ++ tailWord_991490) baseStart_991490 baseEnd_991490 := by
    simpa [prefixWord, tailWord_991490, baseEnd_991490] using wordTrace_append hprefix tailTrace_991490
  have hstable : (prefixWord ++ tailWord_991490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991490).length < 2 ^ (prefixWord ++ tailWord_991490).sum := by decide
  have hdescent : baseEnd_991490 < baseStart_991490 := by decide
  rcases family_descends (prefixWord ++ tailWord_991490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991505 : List Nat := [1, 2, 2, 1, 1, 5, 3, 1, 3, 3]
def baseStart_991505 : Nat := 118140960795 + 991505 * 2 ^ 59
def prefixEnd_991505 : Nat := 4983230072969 + 3 ^ 40 * 991505 * 2
def baseEnd_991505 : Nat := 339412424224165643885105

theorem tailTrace_991505 : CollatzResearch.WordTrace tailWord_991505 prefixEnd_991505 339412424224165643885105 := by
  unfold tailWord_991505
  simp only [CollatzResearch.WordTrace]
  refine ⟨36163158272954195417615969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24108772181969463611743979 36163158272954195417615969)
  ·
    refine ⟨27122368704715646563211977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36163158272954195417615969 27122368704715646563211977)
    ·
      refine ⟨20341776528536734922408983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27122368704715646563211977 20341776528536734922408983)
      ·
        refine ⟨30512664792805102383613475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20341776528536734922408983 30512664792805102383613475)
        ·
          refine ⟨45768997189207653575420213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30512664792805102383613475 45768997189207653575420213)
          ·
            refine ⟨4290843486488217522695645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45768997189207653575420213 4290843486488217522695645)
            ·
              refine ⟨1609066307433081571010867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4290843486488217522695645 1609066307433081571010867)
              ·
                refine ⟨2413599461149622356516301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1609066307433081571010867 2413599461149622356516301)
                ·
                  refine ⟨905099797931108383693613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2413599461149622356516301 905099797931108383693613)
                  ·
                    refine ⟨339412424224165643885105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 905099797931108383693613 339412424224165643885105)
                    ·
                      rfl

theorem cell22_991505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_991505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991505 prefixEnd_991505 := by exact prefixLift 991505
  have htrace : WordTrace (prefixWord ++ tailWord_991505) baseStart_991505 baseEnd_991505 := by
    simpa [prefixWord, tailWord_991505, baseEnd_991505] using wordTrace_append hprefix tailTrace_991505
  have hstable : (prefixWord ++ tailWord_991505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991505).length < 2 ^ (prefixWord ++ tailWord_991505).sum := by decide
  have hdescent : baseEnd_991505 < baseStart_991505 := by decide
  rcases family_descends (prefixWord ++ tailWord_991505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991556 : List Nat := [2, 3, 4, 1, 2, 1, 1, 4, 1, 3]
def baseStart_991556 : Nat := 118140960795 + 991556 * 2 ^ 59
def prefixEnd_991556 : Nat := 4983230072969 + 3 ^ 40 * 991556 * 2
def baseEnd_991556 : Nat := 339429882566418510859949

theorem tailTrace_991556 : CollatzResearch.WordTrace tailWord_991556 prefixEnd_991556 339429882566418510859949 := by
  unfold tailWord_991556
  simp only [CollatzResearch.WordTrace]
  refine ⟨18082509197884715563861261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24110012263846287418481681 18082509197884715563861261)
  ·
    refine ⟨6780940949206768336447973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18082509197884715563861261 6780940949206768336447973)
    ·
      refine ⟨1271426427976269063083995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6780940949206768336447973 1271426427976269063083995)
      ·
        refine ⟨1907139641964403594625993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1271426427976269063083995 1907139641964403594625993)
        ·
          refine ⟨1430354731473302695969495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1907139641964403594625993 1430354731473302695969495)
          ·
            refine ⟨2145532097209954043954243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430354731473302695969495 2145532097209954043954243)
            ·
              refine ⟨3218298145814931065931365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2145532097209954043954243 3218298145814931065931365)
              ·
                refine ⟨603430902340299574862131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3218298145814931065931365 603430902340299574862131)
                ·
                  refine ⟨905146353510449362293197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 603430902340299574862131 905146353510449362293197)
                  ·
                    refine ⟨339429882566418510859949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 905146353510449362293197 339429882566418510859949)
                    ·
                      rfl

theorem cell22_991556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_991556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991556 prefixEnd_991556 := by exact prefixLift 991556
  have htrace : WordTrace (prefixWord ++ tailWord_991556) baseStart_991556 baseEnd_991556 := by
    simpa [prefixWord, tailWord_991556, baseEnd_991556] using wordTrace_append hprefix tailTrace_991556
  have hstable : (prefixWord ++ tailWord_991556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991556).length < 2 ^ (prefixWord ++ tailWord_991556).sum := by decide
  have hdescent : baseEnd_991556 < baseStart_991556 := by decide
  rcases family_descends (prefixWord ++ tailWord_991556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991593 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 1, 6]
def baseStart_991593 : Nat := 118140960795 + 991593 * 2 ^ 59
def prefixEnd_991593 : Nat := 4983230072969 + 3 ^ 40 * 991593 * 2
def baseEnd_991593 : Nat := 339442548422562747684835

theorem tailTrace_991593 : CollatzResearch.WordTrace tailWord_991593 prefixEnd_991593 339442548422562747684835 := by
  unfold tailWord_991593
  simp only [CollatzResearch.WordTrace]
  refine ⟨36166367896635386446819433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24110911931090257631212955 36166367896635386446819433)
  ·
    refine ⟨27124775922476539835114575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36166367896635386446819433 27124775922476539835114575)
    ·
      refine ⟨40687163883714809752671863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27124775922476539835114575 40687163883714809752671863)
      ·
        refine ⟨61030745825572214629007795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40687163883714809752671863 61030745825572214629007795)
        ·
          refine ⟨91546118738358321943511693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61030745825572214629007795 91546118738358321943511693)
          ·
            refine ⟨34329794526884370728816885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91546118738358321943511693 34329794526884370728816885)
            ·
              refine ⟨3218418236895409755826583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34329794526884370728816885 3218418236895409755826583)
              ·
                refine ⟨4827627355343114633739875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3218418236895409755826583 4827627355343114633739875)
                ·
                  refine ⟨7241441033014671950609813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4827627355343114633739875 7241441033014671950609813)
                  ·
                    refine ⟨339442548422562747684835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7241441033014671950609813 339442548422562747684835)
                    ·
                      rfl

theorem cell22_991593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_991593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991593 prefixEnd_991593 := by exact prefixLift 991593
  have htrace : WordTrace (prefixWord ++ tailWord_991593) baseStart_991593 baseEnd_991593 := by
    simpa [prefixWord, tailWord_991593, baseEnd_991593] using wordTrace_append hprefix tailTrace_991593
  have hstable : (prefixWord ++ tailWord_991593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991593).length < 2 ^ (prefixWord ++ tailWord_991593).sum := by decide
  have hdescent : baseEnd_991593 < baseStart_991593 := by decide
  rcases family_descends (prefixWord ++ tailWord_991593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991597 : List Nat := [1, 5, 1, 1, 1, 2, 4, 3, 4]
def baseStart_991597 : Nat := 118140960795 + 991597 * 2 ^ 59
def prefixEnd_991597 : Nat := 4983230072969 + 3 ^ 40 * 991597 * 2
def baseEnd_991597 : Nat := 113147972568102690194941

theorem tailTrace_991597 : CollatzResearch.WordTrace tailWord_991597 prefixEnd_991597 113147972568102690194941 := by
  unfold tailWord_991597
  simp only [CollatzResearch.WordTrace]
  refine ⟨36166513788620895129965045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24111009192413930086643363 36166513788620895129965045)
  ·
    refine ⟨3390610667683208918434223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36166513788620895129965045 3390610667683208918434223)
    ·
      refine ⟨5085916001524813377651335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3390610667683208918434223 5085916001524813377651335)
      ·
        refine ⟨7628874002287220066477003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5085916001524813377651335 7628874002287220066477003)
        ·
          refine ⟨11443311003430830099715505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7628874002287220066477003 11443311003430830099715505)
          ·
            refine ⟨8582483252573122574786629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11443311003430830099715505 8582483252573122574786629)
            ·
              refine ⟨1609215609857460482772493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8582483252573122574786629 1609215609857460482772493)
              ·
                refine ⟨603455853696547681039685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1609215609857460482772493 603455853696547681039685)
                ·
                  refine ⟨113147972568102690194941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 603455853696547681039685 113147972568102690194941)
                  ·
                    rfl

theorem cell22_991597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_991597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991597 prefixEnd_991597 := by exact prefixLift 991597
  have htrace : WordTrace (prefixWord ++ tailWord_991597) baseStart_991597 baseEnd_991597 := by
    simpa [prefixWord, tailWord_991597, baseEnd_991597] using wordTrace_append hprefix tailTrace_991597
  have hstable : (prefixWord ++ tailWord_991597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991597).length < 2 ^ (prefixWord ++ tailWord_991597).sum := by decide
  have hdescent : baseEnd_991597 < baseStart_991597 := by decide
  rcases family_descends (prefixWord ++ tailWord_991597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991642 : List Nat := [3, 1, 1, 4, 1, 4, 2, 6]
def baseStart_991642 : Nat := 118140960795 + 991642 * 2 ^ 59
def prefixEnd_991642 : Nat := 4983230072969 + 3 ^ 40 * 991642 * 2
def baseEnd_991642 : Nat := 37717702458215883689965

theorem tailTrace_991642 : CollatzResearch.WordTrace tailWord_991642 prefixEnd_991642 37717702458215883689965 := by
  unfold tailWord_991642
  simp only [CollatzResearch.WordTrace]
  refine ⟨9042038768364466953838295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24112103382305245210235453 9042038768364466953838295)
  ·
    refine ⟨13563058152546700430757443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9042038768364466953838295 13563058152546700430757443)
    ·
      refine ⟨20344587228820050646136165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13563058152546700430757443 20344587228820050646136165)
      ·
        refine ⟨3814610105403759496150531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20344587228820050646136165 3814610105403759496150531)
        ·
          refine ⟨5721915158105639244225797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3814610105403759496150531 5721915158105639244225797)
          ·
            refine ⟨1072859092144807358292337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5721915158105639244225797 1072859092144807358292337)
            ·
              refine ⟨804644319108605518719253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072859092144807358292337 804644319108605518719253)
              ·
                refine ⟨37717702458215883689965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 804644319108605518719253 37717702458215883689965)
                ·
                  rfl

theorem cell22_991642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 6].length) (baseStart_991642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991642 prefixEnd_991642 := by exact prefixLift 991642
  have htrace : WordTrace (prefixWord ++ tailWord_991642) baseStart_991642 baseEnd_991642 := by
    simpa [prefixWord, tailWord_991642, baseEnd_991642] using wordTrace_append hprefix tailTrace_991642
  have hstable : (prefixWord ++ tailWord_991642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991642).length < 2 ^ (prefixWord ++ tailWord_991642).sum := by decide
  have hdescent : baseEnd_991642 < baseStart_991642 := by decide
  rcases family_descends (prefixWord ++ tailWord_991642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991653 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 9]
def baseStart_991653 : Nat := 118140960795 + 991653 * 2 ^ 59
def prefixEnd_991653 : Nat := 4983230072969 + 3 ^ 40 * 991653 * 2
def baseEnd_991653 : Nat := 113154362549580863728217

theorem tailTrace_991653 : CollatzResearch.WordTrace tailWord_991653 prefixEnd_991653 113154362549580863728217 := by
  unfold tailWord_991653
  simp only [CollatzResearch.WordTrace]
  refine ⟨36168556276418016694003613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24112370850945344462669075 36168556276418016694003613)
  ·
    refine ⟨13563208603656756260251355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36168556276418016694003613 13563208603656756260251355)
    ·
      refine ⟨20344812905485134390377033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13563208603656756260251355 20344812905485134390377033)
      ·
        refine ⟨15258609679113850792782775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20344812905485134390377033 15258609679113850792782775)
        ·
          refine ⟨22887914518670776189174163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15258609679113850792782775 22887914518670776189174163)
          ·
            refine ⟨34331871778006164283761245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22887914518670776189174163 34331871778006164283761245)
            ·
              refine ⟨12874451916752311606410467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34331871778006164283761245 12874451916752311606410467)
              ·
                refine ⟨19311677875128467409615701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12874451916752311606410467 19311677875128467409615701)
                ·
                  refine ⟨113154362549580863728217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19311677875128467409615701 113154362549580863728217)
                  ·
                    rfl

theorem cell22_991653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_991653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991653 prefixEnd_991653 := by exact prefixLift 991653
  have htrace : WordTrace (prefixWord ++ tailWord_991653) baseStart_991653 baseEnd_991653 := by
    simpa [prefixWord, tailWord_991653, baseEnd_991653] using wordTrace_append hprefix tailTrace_991653
  have hstable : (prefixWord ++ tailWord_991653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991653).length < 2 ^ (prefixWord ++ tailWord_991653).sum := by decide
  have hdescent : baseEnd_991653 < baseStart_991653 := by decide
  rcases family_descends (prefixWord ++ tailWord_991653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991683 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 2, 8]
def baseStart_991683 : Nat := 118140960795 + 991683 * 2 ^ 59
def prefixEnd_991683 : Nat := 4983230072969 + 3 ^ 40 * 991683 * 2
def baseEnd_991683 : Nat := 339473357261832512934559

theorem tailTrace_991683 : CollatzResearch.WordTrace tailWord_991683 prefixEnd_991683 339473357261832512934559 := by
  unfold tailWord_991683
  simp only [CollatzResearch.WordTrace]
  refine ⟨36169650466309331817595703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24113100310872887878397135 36169650466309331817595703)
  ·
    refine ⟨54254475699463997726393555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36169650466309331817595703 54254475699463997726393555)
    ·
      refine ⟨81381713549195996589590333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54254475699463997726393555 81381713549195996589590333)
      ·
        refine ⟨30518142580948498721096375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81381713549195996589590333 30518142580948498721096375)
        ·
          refine ⟨45777213871422748081644563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30518142580948498721096375 45777213871422748081644563)
          ·
            refine ⟨68665820807134122122466845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45777213871422748081644563 68665820807134122122466845)
            ·
              refine ⟨25749682802675295795925067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68665820807134122122466845 25749682802675295795925067)
              ·
                refine ⟨38624524204012943693887601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25749682802675295795925067 38624524204012943693887601)
                ·
                  refine ⟨28968393153009707770415701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38624524204012943693887601 28968393153009707770415701)
                  ·
                    refine ⟨339473357261832512934559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28968393153009707770415701 339473357261832512934559)
                    ·
                      rfl

theorem cell22_991683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 8].length) (baseStart_991683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991683 prefixEnd_991683 := by exact prefixLift 991683
  have htrace : WordTrace (prefixWord ++ tailWord_991683) baseStart_991683 baseEnd_991683 := by
    simpa [prefixWord, tailWord_991683, baseEnd_991683] using wordTrace_append hprefix tailTrace_991683
  have hstable : (prefixWord ++ tailWord_991683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991683).length < 2 ^ (prefixWord ++ tailWord_991683).sum := by decide
  have hdescent : baseEnd_991683 < baseStart_991683 := by decide
  rcases family_descends (prefixWord ++ tailWord_991683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991687 : List Nat := [1, 1, 4, 1, 1, 4, 4, 1, 5]
def baseStart_991687 : Nat := 118140960795 + 991687 * 2 ^ 59
def prefixEnd_991687 : Nat := 4983230072969 + 3 ^ 40 * 991687 * 2
def baseEnd_991687 : Nat := 113158242181192611944849

theorem tailTrace_991687 : CollatzResearch.WordTrace tailWord_991687 prefixEnd_991687 113158242181192611944849 := by
  unfold tailWord_991687
  simp only [CollatzResearch.WordTrace]
  refine ⟨36169796358294840500741315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24113197572196560333827543 36169796358294840500741315)
  ·
    refine ⟨54254694537442260751111973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36169796358294840500741315 54254694537442260751111973)
    ·
      refine ⟨10172755225770423890833495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54254694537442260751111973 10172755225770423890833495)
      ·
        refine ⟨15259132838655635836250243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10172755225770423890833495 15259132838655635836250243)
        ·
          refine ⟨22888699257983453754375365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15259132838655635836250243 22888699257983453754375365)
          ·
            refine ⟨4291631110871897578945381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22888699257983453754375365 4291631110871897578945381)
            ·
              refine ⟨804680833288480796052259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4291631110871897578945381 804680833288480796052259)
              ·
                refine ⟨1207021249932721194078389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804680833288480796052259 1207021249932721194078389)
                ·
                  refine ⟨113158242181192611944849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1207021249932721194078389 113158242181192611944849)
                  ·
                    rfl

theorem cell22_991687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 5].length) (baseStart_991687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991687 prefixEnd_991687 := by exact prefixLift 991687
  have htrace : WordTrace (prefixWord ++ tailWord_991687) baseStart_991687 baseEnd_991687 := by
    simpa [prefixWord, tailWord_991687, baseEnd_991687] using wordTrace_append hprefix tailTrace_991687
  have hstable : (prefixWord ++ tailWord_991687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991687).length < 2 ^ (prefixWord ++ tailWord_991687).sum := by decide
  have hdescent : baseEnd_991687 < baseStart_991687 := by decide
  rcases family_descends (prefixWord ++ tailWord_991687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991747 : List Nat := [1, 1, 1, 3, 2, 1, 3, 5, 2, 3]
def baseStart_991747 : Nat := 118140960795 + 991747 * 2 ^ 59
def prefixEnd_991747 : Nat := 4983230072969 + 3 ^ 40 * 991747 * 2
def baseEnd_991747 : Nat := 339495265769757679334363

theorem tailTrace_991747 : CollatzResearch.WordTrace tailWord_991747 prefixEnd_991747 339495265769757679334363 := by
  unfold tailWord_991747
  simp only [CollatzResearch.WordTrace]
  refine ⟨36171984738077470747925495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24114656492051647165283663 36171984738077470747925495)
  ·
    refine ⟨54257977107116206121888243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36171984738077470747925495 54257977107116206121888243)
    ·
      refine ⟨81386965660674309182832365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54257977107116206121888243 81386965660674309182832365)
      ·
        refine ⟨30520112122752865943562137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81386965660674309182832365 30520112122752865943562137)
        ·
          refine ⟨22890084092064649457671603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30520112122752865943562137 22890084092064649457671603)
          ·
            refine ⟨34335126138096974186507405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22890084092064649457671603 34335126138096974186507405)
            ·
              refine ⟨12875672301786365319940277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34335126138096974186507405 12875672301786365319940277)
              ·
                refine ⟨1207094278292471748744401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12875672301786365319940277 1207094278292471748744401)
                ·
                  refine ⟨905320708719353811558301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1207094278292471748744401 905320708719353811558301)
                  ·
                    refine ⟨339495265769757679334363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 905320708719353811558301 339495265769757679334363)
                    ·
                      rfl

theorem cell22_991747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 3].length) (baseStart_991747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991747 prefixEnd_991747 := by exact prefixLift 991747
  have htrace : WordTrace (prefixWord ++ tailWord_991747) baseStart_991747 baseEnd_991747 := by
    simpa [prefixWord, tailWord_991747, baseEnd_991747] using wordTrace_append hprefix tailTrace_991747
  have hstable : (prefixWord ++ tailWord_991747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991747).length < 2 ^ (prefixWord ++ tailWord_991747).sum := by decide
  have hdescent : baseEnd_991747 < baseStart_991747 := by decide
  rcases family_descends (prefixWord ++ tailWord_991747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991764 : List Nat := [2, 4, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_991764 : Nat := 118140960795 + 991764 * 2 ^ 59
def prefixEnd_991764 : Nat := 4983230072969 + 3 ^ 40 * 991764 * 2
def baseEnd_991764 : Nat := 339501085217175301659311

theorem tailTrace_991764 : CollatzResearch.WordTrace tailWord_991764 prefixEnd_991764 339501085217175301659311 := by
  unfold tailWord_991764
  simp only [CollatzResearch.WordTrace]
  refine ⟨18086302389507941325647173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24115069852677255100862897 18086302389507941325647173)
  ·
    refine ⟨3391181698032738998558845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18086302389507941325647173 3391181698032738998558845)
    ·
      refine ⟨1271693136762277124459567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3391181698032738998558845 1271693136762277124459567)
      ·
        refine ⟨1907539705143415686689351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1271693136762277124459567 1907539705143415686689351)
        ·
          refine ⟨2861309557715123530034027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1907539705143415686689351 2861309557715123530034027)
          ·
            refine ⟨4291964336572685295051041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2861309557715123530034027 4291964336572685295051041)
            ·
              refine ⟨3218973252429513971288281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4291964336572685295051041 3218973252429513971288281)
              ·
                refine ⟨2414229939322135478466211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3218973252429513971288281 2414229939322135478466211)
                ·
                  refine ⟨3621344908983203217699317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2414229939322135478466211 3621344908983203217699317)
                  ·
                    refine ⟨339501085217175301659311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3621344908983203217699317 339501085217175301659311)
                    ·
                      rfl

theorem cell22_991764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_991764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991764 prefixEnd_991764 := by exact prefixLift 991764
  have htrace : WordTrace (prefixWord ++ tailWord_991764) baseStart_991764 baseEnd_991764 := by
    simpa [prefixWord, tailWord_991764, baseEnd_991764] using wordTrace_append hprefix tailTrace_991764
  have hstable : (prefixWord ++ tailWord_991764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991764).length < 2 ^ (prefixWord ++ tailWord_991764).sum := by decide
  have hdescent : baseEnd_991764 < baseStart_991764 := by decide
  rcases family_descends (prefixWord ++ tailWord_991764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991792 : List Nat := [2, 1, 1, 1, 2, 3, 3, 3, 3, 3]
def baseStart_991792 : Nat := 118140960795 + 991792 * 2 ^ 59
def prefixEnd_991792 : Nat := 4983230072969 + 3 ^ 40 * 991792 * 2
def baseEnd_991792 : Nat := 339510670189392561959225

theorem tailTrace_991792 : CollatzResearch.WordTrace tailWord_991792 prefixEnd_991792 339510670189392561959225 := by
  unfold tailWord_991792
  simp only [CollatzResearch.WordTrace]
  refine ⟨18086813011457221716656815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24115750681942962288875753 18086813011457221716656815)
  ·
    refine ⟨27130219517185832574985223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18086813011457221716656815 27130219517185832574985223)
    ·
      refine ⟨40695329275778748862477835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27130219517185832574985223 40695329275778748862477835)
      ·
        refine ⟨61042993913668123293716753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40695329275778748862477835 61042993913668123293716753)
        ·
          refine ⟨45782245435251092470287565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61042993913668123293716753 45782245435251092470287565)
          ·
            refine ⟨17168342038219159676357837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45782245435251092470287565 17168342038219159676357837)
            ·
              refine ⟨6438128264332184878634189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17168342038219159676357837 6438128264332184878634189)
              ·
                refine ⟨2414298099124569329487821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6438128264332184878634189 2414298099124569329487821)
                ·
                  refine ⟨905361787171713498557933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2414298099124569329487821 905361787171713498557933)
                  ·
                    refine ⟨339510670189392561959225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 905361787171713498557933 339510670189392561959225)
                    ·
                      rfl

theorem cell22_991792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 3, 3].length) (baseStart_991792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991792 prefixEnd_991792 := by exact prefixLift 991792
  have htrace : WordTrace (prefixWord ++ tailWord_991792) baseStart_991792 baseEnd_991792 := by
    simpa [prefixWord, tailWord_991792, baseEnd_991792] using wordTrace_append hprefix tailTrace_991792
  have hstable : (prefixWord ++ tailWord_991792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991792).length < 2 ^ (prefixWord ++ tailWord_991792).sum := by decide
  have hdescent : baseEnd_991792 < baseStart_991792 := by decide
  rcases family_descends (prefixWord ++ tailWord_991792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991798 : List Nat := [5, 1, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_991798 : Nat := 118140960795 + 991798 * 2 ^ 59
def prefixEnd_991798 : Nat := 4983230072969 + 3 ^ 40 * 991798 * 2
def baseEnd_991798 : Nat := 339512724112010546309207

theorem tailTrace_991798 : CollatzResearch.WordTrace tailWord_991798 prefixEnd_991798 339512724112010546309207 := by
  unfold tailWord_991798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2260865303805794153627003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24115896573928470972021365 2260865303805794153627003)
  ·
    refine ⟨3391297955708691230440505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2260865303805794153627003 3391297955708691230440505)
    ·
      refine ⟨2543473466781518422830379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3391297955708691230440505 2543473466781518422830379)
      ·
        refine ⟨3815210200172277634245569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2543473466781518422830379 3815210200172277634245569)
        ·
          refine ⟨2861407650129208225684177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3815210200172277634245569 2861407650129208225684177)
          ·
            refine ⟨2146055737596906169263133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2861407650129208225684177 2146055737596906169263133)
            ·
              refine ⟨804770901598839813473675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2146055737596906169263133 804770901598839813473675)
              ·
                refine ⟨1207156352398259720210513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804770901598839813473675 1207156352398259720210513)
                ·
                  refine ⟨905367264298694790157885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1207156352398259720210513 905367264298694790157885)
                  ·
                    refine ⟨339512724112010546309207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 905367264298694790157885 339512724112010546309207)
                    ·
                      rfl

theorem cell22_991798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_991798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991798 prefixEnd_991798 := by exact prefixLift 991798
  have htrace : WordTrace (prefixWord ++ tailWord_991798) baseStart_991798 baseEnd_991798 := by
    simpa [prefixWord, tailWord_991798, baseEnd_991798] using wordTrace_append hprefix tailTrace_991798
  have hstable : (prefixWord ++ tailWord_991798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991798).length < 2 ^ (prefixWord ++ tailWord_991798).sum := by decide
  have hdescent : baseEnd_991798 < baseStart_991798 := by decide
  rcases family_descends (prefixWord ++ tailWord_991798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991809 : List Nat := [1, 2, 5, 1, 1, 2, 2, 2, 3, 3]
def baseStart_991809 : Nat := 118140960795 + 991809 * 2 ^ 59
def prefixEnd_991809 : Nat := 4983230072969 + 3 ^ 40 * 991809 * 2
def baseEnd_991809 : Nat := 339516489636810184284173

theorem tailTrace_991809 : CollatzResearch.WordTrace tailWord_991809 prefixEnd_991809 339516489636810184284173 := by
  unfold tailWord_991809
  simp only [CollatzResearch.WordTrace]
  refine ⟨36174246063852855336682481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24116164042568570224454987 36174246063852855336682481)
  ·
    refine ⟨27130684547889641502511861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36174246063852855336682481 27130684547889641502511861)
    ·
      refine ⟨2543501676364653890860487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27130684547889641502511861 2543501676364653890860487)
      ·
        refine ⟨3815252514546980836290731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2543501676364653890860487 3815252514546980836290731)
        ·
          refine ⟨5722878771820471254436097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3815252514546980836290731 5722878771820471254436097)
          ·
            refine ⟨4292159078865353440827073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5722878771820471254436097 4292159078865353440827073)
            ·
              refine ⟨3219119309149015080620305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4292159078865353440827073 3219119309149015080620305)
              ·
                refine ⟨2414339481861761310465229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3219119309149015080620305 2414339481861761310465229)
                ·
                  refine ⟨905377305698160491424461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2414339481861761310465229 905377305698160491424461)
                  ·
                    refine ⟨339516489636810184284173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 905377305698160491424461 339516489636810184284173)
                    ·
                      rfl

theorem cell22_991809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_991809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991809 prefixEnd_991809 := by exact prefixLift 991809
  have htrace : WordTrace (prefixWord ++ tailWord_991809) baseStart_991809 baseEnd_991809 := by
    simpa [prefixWord, tailWord_991809, baseEnd_991809] using wordTrace_append hprefix tailTrace_991809
  have hstable : (prefixWord ++ tailWord_991809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991809).length < 2 ^ (prefixWord ++ tailWord_991809).sum := by decide
  have hdescent : baseEnd_991809 < baseStart_991809 := by decide
  rcases family_descends (prefixWord ++ tailWord_991809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991856 : List Nat := [2, 1, 1, 1, 7, 2, 2, 1, 5]
def baseStart_991856 : Nat := 118140960795 + 991856 * 2 ^ 59
def prefixEnd_991856 : Nat := 4983230072969 + 3 ^ 40 * 991856 * 2
def baseEnd_991856 : Nat := 113177526232439242786343

theorem tailTrace_991856 : CollatzResearch.WordTrace tailWord_991856 prefixEnd_991856 113177526232439242786343 := by
  unfold tailWord_991856
  simp only [CollatzResearch.WordTrace]
  refine ⟨18087980147341291181821711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24117306863121721575762281 18087980147341291181821711)
  ·
    refine ⟨27131970221011936772732567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18087980147341291181821711 27131970221011936772732567)
    ·
      refine ⟨40697955331517905159098851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27131970221011936772732567 40697955331517905159098851)
      ·
        refine ⟨61046932997276857738648277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40697955331517905159098851 61046932997276857738648277)
        ·
          refine ⟨1430787492123676353249569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 61046932997276857738648277 1430787492123676353249569)
          ·
            refine ⟨1073090619092757264937177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1430787492123676353249569 1073090619092757264937177)
            ·
              refine ⟨804817964319567948702883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1073090619092757264937177 804817964319567948702883)
              ·
                refine ⟨1207226946479351923054325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804817964319567948702883 1207226946479351923054325)
                ·
                  refine ⟨113177526232439242786343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1207226946479351923054325 113177526232439242786343)
                  ·
                    rfl

theorem cell22_991856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 5].length) (baseStart_991856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991856 prefixEnd_991856 := by exact prefixLift 991856
  have htrace : WordTrace (prefixWord ++ tailWord_991856) baseStart_991856 baseEnd_991856 := by
    simpa [prefixWord, tailWord_991856, baseEnd_991856] using wordTrace_append hprefix tailTrace_991856
  have hstable : (prefixWord ++ tailWord_991856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991856).length < 2 ^ (prefixWord ++ tailWord_991856).sum := by decide
  have hdescent : baseEnd_991856 < baseStart_991856 := by decide
  rcases family_descends (prefixWord ++ tailWord_991856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991869 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_991869 : Nat := 118140960795 + 991869 * 2 ^ 59
def prefixEnd_991869 : Nat := 4983230072969 + 3 ^ 40 * 991869 * 2
def baseEnd_991869 : Nat := 339537028862990027783989

theorem tailTrace_991869 : CollatzResearch.WordTrace tailWord_991869 prefixEnd_991869 339537028862990027783989 := by
  unfold tailWord_991869
  simp only [CollatzResearch.WordTrace]
  refine ⟨36176434443635485583866661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24117622962423657055911107 36176434443635485583866661)
  ·
    refine ⟨6783081458181653546974999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36176434443635485583866661 6783081458181653546974999)
    ·
      refine ⟨10174622187272480320462499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6783081458181653546974999 10174622187272480320462499)
      ·
        refine ⟨15261933280908720480693749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10174622187272480320462499 15261933280908720480693749)
        ·
          refine ⟨1430806245085192545065039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15261933280908720480693749 1430806245085192545065039)
          ·
            refine ⟨2146209367627788817597559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430806245085192545065039 2146209367627788817597559)
            ·
              refine ⟨3219314051441683226396339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2146209367627788817597559 3219314051441683226396339)
              ·
                refine ⟨4828971077162524839594509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3219314051441683226396339 4828971077162524839594509)
                ·
                  refine ⟨1810864153935946814847941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4828971077162524839594509 1810864153935946814847941)
                  ·
                    refine ⟨339537028862990027783989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1810864153935946814847941 339537028862990027783989)
                    ·
                      rfl

theorem cell22_991869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_991869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991869 prefixEnd_991869 := by exact prefixLift 991869
  have htrace : WordTrace (prefixWord ++ tailWord_991869) baseStart_991869 baseEnd_991869 := by
    simpa [prefixWord, tailWord_991869, baseEnd_991869] using wordTrace_append hprefix tailTrace_991869
  have hstable : (prefixWord ++ tailWord_991869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991869).length < 2 ^ (prefixWord ++ tailWord_991869).sum := by decide
  have hdescent : baseEnd_991869 < baseStart_991869 := by decide
  rcases family_descends (prefixWord ++ tailWord_991869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991886 : List Nat := [4, 1, 1, 3, 1, 1, 5, 1, 1, 4]
def baseStart_991886 : Nat := 118140960795 + 991886 * 2 ^ 59
def prefixEnd_991886 : Nat := 4983230072969 + 3 ^ 40 * 991886 * 2
def baseEnd_991886 : Nat := 339542848310407650108937

theorem tailTrace_991886 : CollatzResearch.WordTrace tailWord_991886 prefixEnd_991886 339542848310407650108937 := by
  unfold tailWord_991886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4522131810571737185904439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24118036323049264991490341 4522131810571737185904439)
  ·
    refine ⟨6783197715857605778856659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4522131810571737185904439 6783197715857605778856659)
    ·
      refine ⟨10174796573786408668284989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6783197715857605778856659 10174796573786408668284989)
      ·
        refine ⟨3815548715169903250606871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10174796573786408668284989 3815548715169903250606871)
        ·
          refine ⟨5723323072754854875910307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3815548715169903250606871 5723323072754854875910307)
          ·
            refine ⟨8584984609132282313865461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5723323072754854875910307 8584984609132282313865461)
            ·
              refine ⟨804842307106151466924887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8584984609132282313865461 804842307106151466924887)
              ·
                refine ⟨1207263460659227200387331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804842307106151466924887 1207263460659227200387331)
                ·
                  refine ⟨1810895190988840800580997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1207263460659227200387331 1810895190988840800580997)
                  ·
                    refine ⟨339542848310407650108937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1810895190988840800580997 339542848310407650108937)
                    ·
                      rfl

theorem cell22_991886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_991886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991886 prefixEnd_991886 := by exact prefixLift 991886
  have htrace : WordTrace (prefixWord ++ tailWord_991886) baseStart_991886 baseEnd_991886 := by
    simpa [prefixWord, tailWord_991886, baseEnd_991886] using wordTrace_append hprefix tailTrace_991886
  have hstable : (prefixWord ++ tailWord_991886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991886).length < 2 ^ (prefixWord ++ tailWord_991886).sum := by decide
  have hdescent : baseEnd_991886 < baseStart_991886 := by decide
  rcases family_descends (prefixWord ++ tailWord_991886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991897 : List Nat := [1, 2, 1, 2, 1, 2, 3, 4, 2, 4]
def baseStart_991897 : Nat := 118140960795 + 991897 * 2 ^ 59
def prefixEnd_991897 : Nat := 4983230072969 + 3 ^ 40 * 991897 * 2
def baseEnd_991897 : Nat := 339546613835207288083903

theorem tailTrace_991897 : CollatzResearch.WordTrace tailWord_991897 prefixEnd_991897 339546613835207288083903 := by
  unfold tailWord_991897
  simp only [CollatzResearch.WordTrace]
  refine ⟨36177455687534046365885945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24118303791689364243923963 36177455687534046365885945)
  ·
    refine ⟨27133091765650534774414459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36177455687534046365885945 27133091765650534774414459)
    ·
      refine ⟨40699637648475802161621689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27133091765650534774414459 40699637648475802161621689)
      ·
        refine ⟨30524728236356851621216267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40699637648475802161621689 30524728236356851621216267)
        ·
          refine ⟨45787092354535277431824401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30524728236356851621216267 45787092354535277431824401)
          ·
            refine ⟨34340319265901458073868301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45787092354535277431824401 34340319265901458073868301)
            ·
              refine ⟨12877619724713046777700613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34340319265901458073868301 12877619724713046777700613)
              ·
                refine ⟨2414553698383696270818865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12877619724713046777700613 2414553698383696270818865)
                ·
                  refine ⟨1810915273787772203114149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2414553698383696270818865 1810915273787772203114149)
                  ·
                    refine ⟨339546613835207288083903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1810915273787772203114149 339546613835207288083903)
                    ·
                      rfl

theorem cell22_991897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_991897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991897 prefixEnd_991897 := by exact prefixLift 991897
  have htrace : WordTrace (prefixWord ++ tailWord_991897) baseStart_991897 baseEnd_991897 := by
    simpa [prefixWord, tailWord_991897, baseEnd_991897] using wordTrace_append hprefix tailTrace_991897
  have hstable : (prefixWord ++ tailWord_991897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991897).length < 2 ^ (prefixWord ++ tailWord_991897).sum := by decide
  have hdescent : baseEnd_991897 < baseStart_991897 := by decide
  rcases family_descends (prefixWord ++ tailWord_991897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991901 : List Nat := [1, 4, 2, 1, 1, 1, 6, 2, 4]
def baseStart_991901 : Nat := 118140960795 + 991901 * 2 ^ 59
def prefixEnd_991901 : Nat := 4983230072969 + 3 ^ 40 * 991901 * 2
def baseEnd_991901 : Nat := 113182661038984203661297

theorem tailTrace_991901 : CollatzResearch.WordTrace tailWord_991901 prefixEnd_991901 113182661038984203661297 := by
  unfold tailWord_991901
  simp only [CollatzResearch.WordTrace]
  refine ⟨36177601579519555049031557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24118401053013036699354371 36177601579519555049031557)
  ·
    refine ⟨6783300296159916571693417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36177601579519555049031557 6783300296159916571693417)
    ·
      refine ⟨5087475222119937428770063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6783300296159916571693417 5087475222119937428770063)
      ·
        refine ⟨7631212833179906143155095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5087475222119937428770063 7631212833179906143155095)
        ·
          refine ⟨11446819249769859214732643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7631212833179906143155095 11446819249769859214732643)
          ·
            refine ⟨17170228874654788822098965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11446819249769859214732643 17170228874654788822098965)
            ·
              refine ⟨804854478499443226035889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17170228874654788822098965 804854478499443226035889)
              ·
                refine ⟨603640858874582419526917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 804854478499443226035889 603640858874582419526917)
                ·
                  refine ⟨113182661038984203661297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 603640858874582419526917 113182661038984203661297)
                  ·
                    rfl

theorem cell22_991901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_991901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991901 prefixEnd_991901 := by exact prefixLift 991901
  have htrace : WordTrace (prefixWord ++ tailWord_991901) baseStart_991901 baseEnd_991901 := by
    simpa [prefixWord, tailWord_991901, baseEnd_991901] using wordTrace_append hprefix tailTrace_991901
  have hstable : (prefixWord ++ tailWord_991901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991901).length < 2 ^ (prefixWord ++ tailWord_991901).sum := by decide
  have hdescent : baseEnd_991901 < baseStart_991901 := by decide
  rcases family_descends (prefixWord ++ tailWord_991901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991937 : List Nat := [1, 2, 6, 2, 2, 1, 2, 1, 1, 4]
def baseStart_991937 : Nat := 118140960795 + 991937 * 2 ^ 59
def prefixEnd_991937 : Nat := 4983230072969 + 3 ^ 40 * 991937 * 2
def baseEnd_991937 : Nat := 339560306652660517083781

theorem tailTrace_991937 : CollatzResearch.WordTrace tailWord_991937 prefixEnd_991937 339560306652660517083781 := by
  unfold tailWord_991937
  simp only [CollatzResearch.WordTrace]
  refine ⟨36178914607389133197342065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24119276404926088798228043 36178914607389133197342065)
  ·
    refine ⟨27134185955541849898006549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36178914607389133197342065 27134185955541849898006549)
    ·
      refine ⟨1271914966666024213969057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27134185955541849898006549 1271914966666024213969057)
      ·
        refine ⟨953936224999518160476793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1271914966666024213969057 953936224999518160476793)
        ·
          refine ⟨715452168749638620357595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 953936224999518160476793 715452168749638620357595)
          ·
            refine ⟨1073178253124457930536393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715452168749638620357595 1073178253124457930536393)
            ·
              refine ⟨804883689843343447902295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1073178253124457930536393 804883689843343447902295)
              ·
                refine ⟨1207325534765015171853443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804883689843343447902295 1207325534765015171853443)
                ·
                  refine ⟨1810988302147522757780165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1207325534765015171853443 1810988302147522757780165)
                  ·
                    refine ⟨339560306652660517083781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1810988302147522757780165 339560306652660517083781)
                    ·
                      rfl

theorem cell22_991937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_991937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991937 prefixEnd_991937 := by exact prefixLift 991937
  have htrace : WordTrace (prefixWord ++ tailWord_991937) baseStart_991937 baseEnd_991937 := by
    simpa [prefixWord, tailWord_991937, baseEnd_991937] using wordTrace_append hprefix tailTrace_991937
  have hstable : (prefixWord ++ tailWord_991937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991937).length < 2 ^ (prefixWord ++ tailWord_991937).sum := by decide
  have hdescent : baseEnd_991937 < baseStart_991937 := by decide
  rcases family_descends (prefixWord ++ tailWord_991937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991961 : List Nat := [1, 2, 1, 2, 3, 2, 1, 6, 1, 3]
def baseStart_991961 : Nat := 118140960795 + 991961 * 2 ^ 59
def prefixEnd_991961 : Nat := 4983230072969 + 3 ^ 40 * 991961 * 2
def baseEnd_991961 : Nat := 339568522343132454483707

theorem tailTrace_991961 : CollatzResearch.WordTrace tailWord_991961 prefixEnd_991961 339568522343132454483707 := by
  unfold tailWord_991961
  simp only [CollatzResearch.WordTrace]
  refine ⟨36179789959302185296215737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24119859972868123530810491 36179789959302185296215737)
  ·
    refine ⟨27134842469476638972161803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36179789959302185296215737 27134842469476638972161803)
    ·
      refine ⟨40702263704214958458242705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27134842469476638972161803 40702263704214958458242705)
      ·
        refine ⟨30526697778161218843682029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40702263704214958458242705 30526697778161218843682029)
        ·
          refine ⟨11447511666810457066380761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30526697778161218843682029 11447511666810457066380761)
          ·
            refine ⟨8585633750107842799785571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11447511666810457066380761 8585633750107842799785571)
            ·
              refine ⟨12878450625161764199678357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8585633750107842799785571 12878450625161764199678357)
              ·
                refine ⟨603677373054457696859923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12878450625161764199678357 603677373054457696859923)
                ·
                  refine ⟨905516059581686545289885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 603677373054457696859923 905516059581686545289885)
                  ·
                    refine ⟨339568522343132454483707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 905516059581686545289885 339568522343132454483707)
                    ·
                      rfl

theorem cell22_991961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 1, 3].length) (baseStart_991961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_991961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_991961 prefixEnd_991961 := by exact prefixLift 991961
  have htrace : WordTrace (prefixWord ++ tailWord_991961) baseStart_991961 baseEnd_991961 := by
    simpa [prefixWord, tailWord_991961, baseEnd_991961] using wordTrace_append hprefix tailTrace_991961
  have hstable : (prefixWord ++ tailWord_991961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991961).length < 2 ^ (prefixWord ++ tailWord_991961).sum := by decide
  have hdescent : baseEnd_991961 < baseStart_991961 := by decide
  rcases family_descends (prefixWord ++ tailWord_991961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992079 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 9, 3]
def baseStart_992079 : Nat := 118140960795 + 992079 * 2 ^ 59
def prefixEnd_992079 : Nat := 4983230072969 + 3 ^ 40 * 992079 * 2
def baseEnd_992079 : Nat := 339608916154619480033345

theorem tailTrace_992079 : CollatzResearch.WordTrace tailWord_992079 prefixEnd_992079 339608916154619480033345 := by
  unfold tailWord_992079
  simp only [CollatzResearch.WordTrace]
  refine ⟨36184093772874691449011291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24122729181916460966007527 36184093772874691449011291)
  ·
    refine ⟨54276140659312037173516937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36184093772874691449011291 54276140659312037173516937)
    ·
      refine ⟨40707105494484027880137703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54276140659312037173516937 40707105494484027880137703)
      ·
        refine ⟨61060658241726041820206555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40707105494484027880137703 61060658241726041820206555)
        ·
          refine ⟨91590987362589062730309833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61060658241726041820206555 91590987362589062730309833)
          ·
            refine ⟨68693240521941797047732375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91590987362589062730309833 68693240521941797047732375)
            ·
              refine ⟨103039860782912695571598563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68693240521941797047732375 103039860782912695571598563)
              ·
                refine ⟨154559791174369043357397845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103039860782912695571598563 154559791174369043357397845)
                ·
                  refine ⟨905623776412318613422253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 154559791174369043357397845 905623776412318613422253)
                  ·
                    refine ⟨339608916154619480033345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 905623776412318613422253 339608916154619480033345)
                    ·
                      rfl

theorem cell22_992079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 3].length) (baseStart_992079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992079 prefixEnd_992079 := by exact prefixLift 992079
  have htrace : WordTrace (prefixWord ++ tailWord_992079) baseStart_992079 baseEnd_992079 := by
    simpa [prefixWord, tailWord_992079, baseEnd_992079] using wordTrace_append hprefix tailTrace_992079
  have hstable : (prefixWord ++ tailWord_992079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992079).length < 2 ^ (prefixWord ++ tailWord_992079).sum := by decide
  have hdescent : baseEnd_992079 < baseStart_992079 := by decide
  rcases family_descends (prefixWord ++ tailWord_992079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992081 : List Nat := [1, 2, 2, 1, 6, 2, 1, 7]
def baseStart_992081 : Nat := 118140960795 + 992081 * 2 ^ 59
def prefixEnd_992081 : Nat := 4983230072969 + 3 ^ 40 * 992081 * 2
def baseEnd_992081 : Nat := 37734400088388015720371

theorem tailTrace_992081 : CollatzResearch.WordTrace tailWord_992081 prefixEnd_992081 37734400088388015720371 := by
  unfold tailWord_992081
  simp only [CollatzResearch.WordTrace]
  refine ⟨36184166718867445790584097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24122777812578297193722731 36184166718867445790584097)
  ·
    refine ⟨27138125039150584342938073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36184166718867445790584097 27138125039150584342938073)
    ·
      refine ⟨20353593779362938257203555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27138125039150584342938073 20353593779362938257203555)
      ·
        refine ⟨30530390669044407385805333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20353593779362938257203555 30530390669044407385805333)
        ·
          refine ⟨1431112062611456596209625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30530390669044407385805333 1431112062611456596209625)
          ·
            refine ⟨1073334046958592447157219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1431112062611456596209625 1073334046958592447157219)
            ·
              refine ⟨1610001070437888670735829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073334046958592447157219 1610001070437888670735829)
              ·
                refine ⟨37734400088388015720371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1610001070437888670735829 37734400088388015720371)
                ·
                  rfl

theorem cell22_992081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 7].length) (baseStart_992081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992081 prefixEnd_992081 := by exact prefixLift 992081
  have htrace : WordTrace (prefixWord ++ tailWord_992081) baseStart_992081 baseEnd_992081 := by
    simpa [prefixWord, tailWord_992081, baseEnd_992081] using wordTrace_append hprefix tailTrace_992081
  have hstable : (prefixWord ++ tailWord_992081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992081).length < 2 ^ (prefixWord ++ tailWord_992081).sum := by decide
  have hdescent : baseEnd_992081 < baseStart_992081 := by decide
  rcases family_descends (prefixWord ++ tailWord_992081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992096 : List Nat := [2, 1, 1, 3, 3, 1, 3, 2, 3, 3]
def baseStart_992096 : Nat := 118140960795 + 992096 * 2 ^ 59
def prefixEnd_992096 : Nat := 4983230072969 + 3 ^ 40 * 992096 * 2
def baseEnd_992096 : Nat := 339614735602037102358293

theorem tailTrace_992096 : CollatzResearch.WordTrace tailWord_992096 prefixEnd_992096 339614735602037102358293 := by
  unfold tailWord_992096
  simp only [CollatzResearch.WordTrace]
  refine ⟨18092356906906551676190071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24123142542542068901586761 18092356906906551676190071)
  ·
    refine ⟨27138535360359827514285107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18092356906906551676190071 27138535360359827514285107)
    ·
      refine ⟨40707803040539741271427661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27138535360359827514285107 40707803040539741271427661)
      ·
        refine ⟨15265426140202402976785373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40707803040539741271427661 15265426140202402976785373)
        ·
          refine ⟨5724534802575901116294515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15265426140202402976785373 5724534802575901116294515)
          ·
            refine ⟨8586802203863851674441773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5724534802575901116294515 8586802203863851674441773)
            ·
              refine ⟨3220050826448944377915665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8586802203863851674441773 3220050826448944377915665)
              ·
                refine ⟨2415038119836708283436749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3220050826448944377915665 2415038119836708283436749)
                ·
                  refine ⟨905639294938765606288781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2415038119836708283436749 905639294938765606288781)
                  ·
                    refine ⟨339614735602037102358293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 905639294938765606288781 339614735602037102358293)
                    ·
                      rfl

theorem cell22_992096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 3, 3].length) (baseStart_992096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992096 prefixEnd_992096 := by exact prefixLift 992096
  have htrace : WordTrace (prefixWord ++ tailWord_992096) baseStart_992096 baseEnd_992096 := by
    simpa [prefixWord, tailWord_992096, baseEnd_992096] using wordTrace_append hprefix tailTrace_992096
  have hstable : (prefixWord ++ tailWord_992096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992096).length < 2 ^ (prefixWord ++ tailWord_992096).sum := by decide
  have hdescent : baseEnd_992096 < baseStart_992096 := by decide
  rcases family_descends (prefixWord ++ tailWord_992096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992098 : List Nat := [3, 3, 2, 1, 3, 1, 3, 6]
def baseStart_992098 : Nat := 118140960795 + 992098 * 2 ^ 59
def prefixEnd_992098 : Nat := 4983230072969 + 3 ^ 40 * 992098 * 2
def baseEnd_992098 : Nat := 37735046693656640423143

theorem tailTrace_992098 : CollatzResearch.WordTrace tailWord_992098 prefixEnd_992098 37735046693656640423143 := by
  unfold tailWord_992098
  simp only [CollatzResearch.WordTrace]
  refine ⟨9046196689951464423488237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24123191173203905129301965 9046196689951464423488237)
  ·
    refine ⟨3392323758731799158808089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9046196689951464423488237 3392323758731799158808089)
    ·
      refine ⟨2544242819048849369106067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3392323758731799158808089 2544242819048849369106067)
      ·
        refine ⟨3816364228573274053659101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2544242819048849369106067 3816364228573274053659101)
        ·
          refine ⟨1431136585714977770122163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3816364228573274053659101 1431136585714977770122163)
          ·
            refine ⟨2146704878572466655183245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431136585714977770122163 2146704878572466655183245)
            ·
              refine ⟨805014329464674995693717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2146704878572466655183245 805014329464674995693717)
              ·
                refine ⟨37735046693656640423143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 805014329464674995693717 37735046693656640423143)
                ·
                  rfl

theorem cell22_992098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 6].length) (baseStart_992098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992098 prefixEnd_992098 := by exact prefixLift 992098
  have htrace : WordTrace (prefixWord ++ tailWord_992098) baseStart_992098 baseEnd_992098 := by
    simpa [prefixWord, tailWord_992098, baseEnd_992098] using wordTrace_append hprefix tailTrace_992098
  have hstable : (prefixWord ++ tailWord_992098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992098).length < 2 ^ (prefixWord ++ tailWord_992098).sum := by decide
  have hdescent : baseEnd_992098 < baseStart_992098 := by decide
  rcases family_descends (prefixWord ++ tailWord_992098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992109 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 7]
def baseStart_992109 : Nat := 118140960795 + 992109 * 2 ^ 59
def prefixEnd_992109 : Nat := 4983230072969 + 3 ^ 40 * 992109 * 2
def baseEnd_992109 : Nat := 113206395255903133927751

theorem tailTrace_992109 : CollatzResearch.WordTrace tailWord_992109 prefixEnd_992109 113206395255903133927751 := by
  unfold tailWord_992109
  simp only [CollatzResearch.WordTrace]
  refine ⟨36185187962766006572603381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24123458641844004381735587 36185187962766006572603381)
  ·
    refine ⟨3392361371509313116181567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36185187962766006572603381 3392361371509313116181567)
    ·
      refine ⟨5088542057263969674272351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3392361371509313116181567 5088542057263969674272351)
      ·
        refine ⟨7632813085895954511408527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5088542057263969674272351 7632813085895954511408527)
        ·
          refine ⟨11449219628843931767112791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7632813085895954511408527 11449219628843931767112791)
          ·
            refine ⟨17173829443265897650669187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11449219628843931767112791 17173829443265897650669187)
            ·
              refine ⟨25760744164898846476003781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17173829443265897650669187 25760744164898846476003781)
              ·
                refine ⟨4830139530918533714250709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25760744164898846476003781 4830139530918533714250709)
                ·
                  refine ⟨113206395255903133927751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4830139530918533714250709 113206395255903133927751)
                  ·
                    rfl

theorem cell22_992109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_992109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992109 prefixEnd_992109 := by exact prefixLift 992109
  have htrace : WordTrace (prefixWord ++ tailWord_992109) baseStart_992109 baseEnd_992109 := by
    simpa [prefixWord, tailWord_992109, baseEnd_992109] using wordTrace_append hprefix tailTrace_992109
  have hstable : (prefixWord ++ tailWord_992109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992109).length < 2 ^ (prefixWord ++ tailWord_992109).sum := by decide
  have hdescent : baseEnd_992109 < baseStart_992109 := by decide
  rcases family_descends (prefixWord ++ tailWord_992109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992113 : List Nat := [1, 2, 2, 2, 1, 4, 1, 5, 1, 3]
def baseStart_992113 : Nat := 118140960795 + 992113 * 2 ^ 59
def prefixEnd_992113 : Nat := 4983230072969 + 3 ^ 40 * 992113 * 2
def baseEnd_992113 : Nat := 339620555049454724683241

theorem tailTrace_992113 : CollatzResearch.WordTrace tailWord_992113 prefixEnd_992113 339620555049454724683241 := by
  unfold tailWord_992113
  simp only [CollatzResearch.WordTrace]
  refine ⟨36185333854751515255748993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24123555903167676837165995 36185333854751515255748993)
  ·
    refine ⟨27139000391063636441811745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36185333854751515255748993 27139000391063636441811745)
    ·
      refine ⟨20354250293297727331358809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27139000391063636441811745 20354250293297727331358809)
      ·
        refine ⟨15265687719973295498519107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20354250293297727331358809 15265687719973295498519107)
        ·
          refine ⟨22898531579959943247778661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15265687719973295498519107 22898531579959943247778661)
          ·
            refine ⟨4293474671242489358958499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22898531579959943247778661 4293474671242489358958499)
            ·
              refine ⟨6440212006863734038437749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293474671242489358958499 6440212006863734038437749)
              ·
                refine ⟨603769875643475066103539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6440212006863734038437749 603769875643475066103539)
                ·
                  refine ⟨905654813465212599155309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 603769875643475066103539 905654813465212599155309)
                  ·
                    refine ⟨339620555049454724683241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 905654813465212599155309 339620555049454724683241)
                    ·
                      rfl

theorem cell22_992113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 1, 3].length) (baseStart_992113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992113 prefixEnd_992113 := by exact prefixLift 992113
  have htrace : WordTrace (prefixWord ++ tailWord_992113) baseStart_992113 baseEnd_992113 := by
    simpa [prefixWord, tailWord_992113, baseEnd_992113] using wordTrace_append hprefix tailTrace_992113
  have hstable : (prefixWord ++ tailWord_992113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992113).length < 2 ^ (prefixWord ++ tailWord_992113).sum := by decide
  have hdescent : baseEnd_992113 < baseStart_992113 := by decide
  rcases family_descends (prefixWord ++ tailWord_992113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992139 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 5, 4]
def baseStart_992139 : Nat := 118140960795 + 992139 * 2 ^ 59
def prefixEnd_992139 : Nat := 4983230072969 + 3 ^ 40 * 992139 * 2
def baseEnd_992139 : Nat := 339629455380799323533161

theorem tailTrace_992139 : CollatzResearch.WordTrace tailWord_992139 prefixEnd_992139 339629455380799323533161 := by
  unfold tailWord_992139
  simp only [CollatzResearch.WordTrace]
  refine ⟨36186282152657321696195471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24124188101771547797463647 36186282152657321696195471)
  ·
    refine ⟨54279423228985982544293207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36186282152657321696195471 54279423228985982544293207)
    ·
      refine ⟨81419134843478973816439811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54279423228985982544293207 81419134843478973816439811)
      ·
        refine ⟨122128702265218460724659717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81419134843478973816439811 122128702265218460724659717)
        ·
          refine ⟨22899131674728461385873697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122128702265218460724659717 22899131674728461385873697)
          ·
            refine ⟨17174348756046346039405273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22899131674728461385873697 17174348756046346039405273)
            ·
              refine ⟨12880761567034759529553955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17174348756046346039405273 12880761567034759529553955)
              ·
                refine ⟨19321142350552139294330933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12880761567034759529553955 19321142350552139294330933)
                ·
                  refine ⟨1811357095364263058843525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19321142350552139294330933 1811357095364263058843525)
                  ·
                    refine ⟨339629455380799323533161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1811357095364263058843525 339629455380799323533161)
                    ·
                      rfl

theorem cell22_992139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 4].length) (baseStart_992139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992139 prefixEnd_992139 := by exact prefixLift 992139
  have htrace : WordTrace (prefixWord ++ tailWord_992139) baseStart_992139 baseEnd_992139 := by
    simpa [prefixWord, tailWord_992139, baseEnd_992139] using wordTrace_append hprefix tailTrace_992139
  have hstable : (prefixWord ++ tailWord_992139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992139).length < 2 ^ (prefixWord ++ tailWord_992139).sum := by decide
  have hdescent : baseEnd_992139 < baseStart_992139 := by decide
  rcases family_descends (prefixWord ++ tailWord_992139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992169 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 3, 5]
def baseStart_992169 : Nat := 118140960795 + 992169 * 2 ^ 59
def prefixEnd_992169 : Nat := 4983230072969 + 3 ^ 40 * 992169 * 2
def baseEnd_992169 : Nat := 339639724993889245283069

theorem tailTrace_992169 : CollatzResearch.WordTrace tailWord_992169 prefixEnd_992169 339639724993889245283069 := by
  unfold tailWord_992169
  simp only [CollatzResearch.WordTrace]
  refine ⟨36187376342548636819787561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24124917561699091213191707 36187376342548636819787561)
  ·
    refine ⟨27140532256911477614840671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36187376342548636819787561 27140532256911477614840671)
    ·
      refine ⟨40710798385367216422261007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27140532256911477614840671 40710798385367216422261007)
      ·
        refine ⟨61066197578050824633391511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40710798385367216422261007 61066197578050824633391511)
        ·
          refine ⟨91599296367076236950087267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61066197578050824633391511 91599296367076236950087267)
          ·
            refine ⟨137398944550614355425130901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91599296367076236950087267 137398944550614355425130901)
            ·
              refine ⟨6440575525810047910553011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137398944550614355425130901 6440575525810047910553011)
              ·
                refine ⟨9660863288715071865829517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6440575525810047910553011 9660863288715071865829517)
                ·
                  refine ⟨3622823733268151949686069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9660863288715071865829517 3622823733268151949686069)
                  ·
                    refine ⟨339639724993889245283069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3622823733268151949686069 339639724993889245283069)
                    ·
                      rfl

theorem cell22_992169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_992169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992169 prefixEnd_992169 := by exact prefixLift 992169
  have htrace : WordTrace (prefixWord ++ tailWord_992169) baseStart_992169 baseEnd_992169 := by
    simpa [prefixWord, tailWord_992169, baseEnd_992169] using wordTrace_append hprefix tailTrace_992169
  have hstable : (prefixWord ++ tailWord_992169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992169).length < 2 ^ (prefixWord ++ tailWord_992169).sum := by decide
  have hdescent : baseEnd_992169 < baseStart_992169 := by decide
  rcases family_descends (prefixWord ++ tailWord_992169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992186 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 4, 3]
def baseStart_992186 : Nat := 118140960795 + 992186 * 2 ^ 59
def prefixEnd_992186 : Nat := 4983230072969 + 3 ^ 40 * 992186 * 2
def baseEnd_992186 : Nat := 339645544441306867608017

theorem tailTrace_992186 : CollatzResearch.WordTrace tailWord_992186 prefixEnd_992186 339645544441306867608017 := by
  unfold tailWord_992186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9046999095871762180789103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24125330922324699148770941 9046999095871762180789103)
  ·
    refine ⟨13570498643807643271183655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9046999095871762180789103 13570498643807643271183655)
    ·
      refine ⟨20355747965711464906775483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13570498643807643271183655 20355747965711464906775483)
      ·
        refine ⟨30533621948567197360163225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20355747965711464906775483 30533621948567197360163225)
        ·
          refine ⟨22900216461425398020122419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30533621948567197360163225 22900216461425398020122419)
          ·
            refine ⟨34350324692138097030183629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22900216461425398020122419 34350324692138097030183629)
            ·
              refine ⟨12881371759551786386318861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34350324692138097030183629 12881371759551786386318861)
              ·
                refine ⟨4830514409831919894869573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12881371759551786386318861 4830514409831919894869573)
                ·
                  refine ⟨905721451843484980288045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4830514409831919894869573 905721451843484980288045)
                  ·
                    refine ⟨339645544441306867608017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 905721451843484980288045 339645544441306867608017)
                    ·
                      rfl

theorem cell22_992186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_992186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992186 prefixEnd_992186 := by exact prefixLift 992186
  have htrace : WordTrace (prefixWord ++ tailWord_992186) baseStart_992186 baseEnd_992186 := by
    simpa [prefixWord, tailWord_992186, baseEnd_992186] using wordTrace_append hprefix tailTrace_992186
  have hstable : (prefixWord ++ tailWord_992186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992186).length < 2 ^ (prefixWord ++ tailWord_992186).sum := by decide
  have hdescent : baseEnd_992186 < baseStart_992186 := by decide
  rcases family_descends (prefixWord ++ tailWord_992186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992199 : List Nat := [1, 1, 4, 1, 1, 2, 3, 9]
def baseStart_992199 : Nat := 118140960795 + 992199 * 2 ^ 59
def prefixEnd_992199 : Nat := 4983230072969 + 3 ^ 40 * 992199 * 2
def baseEnd_992199 : Nat := 37738888289664351892553

theorem tailTrace_992199 : CollatzResearch.WordTrace tailWord_992199 prefixEnd_992199 37738888289664351892553 := by
  unfold tailWord_992199
  simp only [CollatzResearch.WordTrace]
  refine ⟨36188470532439951943379651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24125647021626634628919767 36188470532439951943379651)
  ·
    refine ⟨54282705798659927915069477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36188470532439951943379651 54282705798659927915069477)
    ·
      refine ⟨10178007337248736484075527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54282705798659927915069477 10178007337248736484075527)
      ·
        refine ⟨15267011005873104726113291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10178007337248736484075527 15267011005873104726113291)
        ·
          refine ⟨22900516508809657089169937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15267011005873104726113291 22900516508809657089169937)
          ·
            refine ⟨17175387381607242816877453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22900516508809657089169937 17175387381607242816877453)
            ·
              refine ⟨6440770268102716056329045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17175387381607242816877453 6440770268102716056329045)
              ·
                refine ⟨37738888289664351892553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6440770268102716056329045 37738888289664351892553)
                ·
                  rfl

theorem cell22_992199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 9].length) (baseStart_992199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992199 prefixEnd_992199 := by exact prefixLift 992199
  have htrace : WordTrace (prefixWord ++ tailWord_992199) baseStart_992199 baseEnd_992199 := by
    simpa [prefixWord, tailWord_992199, baseEnd_992199] using wordTrace_append hprefix tailTrace_992199
  have hstable : (prefixWord ++ tailWord_992199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992199).length < 2 ^ (prefixWord ++ tailWord_992199).sum := by decide
  have hdescent : baseEnd_992199 < baseStart_992199 := by decide
  rcases family_descends (prefixWord ++ tailWord_992199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992203 : List Nat := [1, 1, 1, 1, 3, 6, 1, 3, 2, 3]
def baseStart_992203 : Nat := 118140960795 + 992203 * 2 ^ 59
def prefixEnd_992203 : Nat := 4983230072969 + 3 ^ 40 * 992203 * 2
def baseEnd_992203 : Nat := 339651363888724489932965

theorem tailTrace_992203 : CollatzResearch.WordTrace tailWord_992203 prefixEnd_992203 339651363888724489932965 := by
  unfold tailWord_992203
  simp only [CollatzResearch.WordTrace]
  refine ⟨36188616424425460626525263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24125744282950307084350175 36188616424425460626525263)
  ·
    refine ⟨54282924636638190939787895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36188616424425460626525263 54282924636638190939787895)
    ·
      refine ⟨81424386954957286409681843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54282924636638190939787895 81424386954957286409681843)
      ·
        refine ⟨122136580432435929614522765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81424386954957286409681843 122136580432435929614522765)
        ·
          refine ⟨45801217662163473605446037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122136580432435929614522765 45801217662163473605446037)
          ·
            refine ⟨2146932077913912825255283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45801217662163473605446037 2146932077913912825255283)
            ·
              refine ⟨3220398116870869237882925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2146932077913912825255283 3220398116870869237882925)
              ·
                refine ⟨1207649293826575964206097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3220398116870869237882925 1207649293826575964206097)
                ·
                  refine ⟨905736970369931973154573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1207649293826575964206097 905736970369931973154573)
                  ·
                    refine ⟨339651363888724489932965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 905736970369931973154573 339651363888724489932965)
                    ·
                      rfl

theorem cell22_992203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 3].length) (baseStart_992203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992203 prefixEnd_992203 := by exact prefixLift 992203
  have htrace : WordTrace (prefixWord ++ tailWord_992203) baseStart_992203 baseEnd_992203 := by
    simpa [prefixWord, tailWord_992203, baseEnd_992203] using wordTrace_append hprefix tailTrace_992203
  have hstable : (prefixWord ++ tailWord_992203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992203).length < 2 ^ (prefixWord ++ tailWord_992203).sum := by decide
  have hdescent : baseEnd_992203 < baseStart_992203 := by decide
  rcases family_descends (prefixWord ++ tailWord_992203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992218 : List Nat := [3, 1, 1, 2, 4, 2, 2, 1, 2, 4]
def baseStart_992218 : Nat := 118140960795 + 992218 * 2 ^ 59
def prefixEnd_992218 : Nat := 4983230072969 + 3 ^ 40 * 992218 * 2
def baseEnd_992218 : Nat := 339656498695269450807919

theorem tailTrace_992218 : CollatzResearch.WordTrace tailWord_992218 prefixEnd_992218 339656498695269450807919 := by
  unfold tailWord_992218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9047290879842779547080327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24126109012914078792214205 9047290879842779547080327)
  ·
    refine ⟨13570936319764169320620491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9047290879842779547080327 13570936319764169320620491)
    ·
      refine ⟨20356404479646253980930737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13570936319764169320620491 20356404479646253980930737)
      ·
        refine ⟨15267303359734690485698053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20356404479646253980930737 15267303359734690485698053)
        ·
          refine ⟨2862619379950254466068385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15267303359734690485698053 2862619379950254466068385)
          ·
            refine ⟨2146964534962690849551289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2862619379950254466068385 2146964534962690849551289)
            ·
              refine ⟨1610223401222018137163467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2146964534962690849551289 1610223401222018137163467)
              ·
                refine ⟨2415335101833027205745201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1610223401222018137163467 2415335101833027205745201)
                ·
                  refine ⟨1811501326374770404308901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2415335101833027205745201 1811501326374770404308901)
                  ·
                    refine ⟨339656498695269450807919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1811501326374770404308901 339656498695269450807919)
                    ·
                      rfl

theorem cell22_992218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_992218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992218 prefixEnd_992218 := by exact prefixLift 992218
  have htrace : WordTrace (prefixWord ++ tailWord_992218) baseStart_992218 baseEnd_992218 := by
    simpa [prefixWord, tailWord_992218, baseEnd_992218] using wordTrace_append hprefix tailTrace_992218
  have hstable : (prefixWord ++ tailWord_992218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992218).length < 2 ^ (prefixWord ++ tailWord_992218).sum := by decide
  have hdescent : baseEnd_992218 < baseStart_992218 := by decide
  rcases family_descends (prefixWord ++ tailWord_992218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992261 : List Nat := [1, 3, 1, 1, 2, 3, 1, 5, 5]
def baseStart_992261 : Nat := 118140960795 + 992261 * 2 ^ 59
def prefixEnd_992261 : Nat := 4983230072969 + 3 ^ 40 * 992261 * 2
def baseEnd_992261 : Nat := 113223739491343890660929

theorem tailTrace_992261 : CollatzResearch.WordTrace tailWord_992261 prefixEnd_992261 113223739491343890660929 := by
  unfold tailWord_992261
  simp only [CollatzResearch.WordTrace]
  refine ⟨36190731858215336532136637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24127154572143557688091091 36190731858215336532136637)
  ·
    refine ⟨13571524446830751199551239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36190731858215336532136637 13571524446830751199551239)
    ·
      refine ⟨20357286670246126799326859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13571524446830751199551239 20357286670246126799326859)
      ·
        refine ⟨30535930005369190198990289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20357286670246126799326859 30535930005369190198990289)
        ·
          refine ⟨22901947504026892649242717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30535930005369190198990289 22901947504026892649242717)
          ·
            refine ⟨8588230314010084743466019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22901947504026892649242717 8588230314010084743466019)
            ·
              refine ⟨12882345471015127115199029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8588230314010084743466019 12882345471015127115199029)
              ·
                refine ⟨1207719887907668167049909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12882345471015127115199029 1207719887907668167049909)
                ·
                  refine ⟨113223739491343890660929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1207719887907668167049909 113223739491343890660929)
                  ·
                    rfl

theorem cell22_992261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_992261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992261 prefixEnd_992261 := by exact prefixLift 992261
  have htrace : WordTrace (prefixWord ++ tailWord_992261) baseStart_992261 baseEnd_992261 := by
    simpa [prefixWord, tailWord_992261, baseEnd_992261] using wordTrace_append hprefix tailTrace_992261
  have hstable : (prefixWord ++ tailWord_992261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992261).length < 2 ^ (prefixWord ++ tailWord_992261).sum := by decide
  have hdescent : baseEnd_992261 < baseStart_992261 := by decide
  rcases family_descends (prefixWord ++ tailWord_992261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992295 : List Nat := [1, 1, 7, 1, 1, 1, 3, 2, 5]
def baseStart_992295 : Nat := 118140960795 + 992295 * 2 ^ 59
def prefixEnd_992295 : Nat := 4983230072969 + 3 ^ 40 * 992295 * 2
def baseEnd_992295 : Nat := 113227619122955638877561

theorem tailTrace_992295 : CollatzResearch.WordTrace tailWord_992295 prefixEnd_992295 113227619122955638877561 := by
  unfold tailWord_992295
  simp only [CollatzResearch.WordTrace]
  refine ⟨36191971940092160338874339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24127981293394773559249559 36191971940092160338874339)
  ·
    refine ⟨54287957910138240508311509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36191971940092160338874339 54287957910138240508311509)
    ·
      refine ⟨1272374013518865011913551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 54287957910138240508311509 1272374013518865011913551)
      ·
        refine ⟨1908561020278297517870327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1272374013518865011913551 1908561020278297517870327)
        ·
          refine ⟨2862841530417446276805491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1908561020278297517870327 2862841530417446276805491)
          ·
            refine ⟨4294262295626169415208237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862841530417446276805491 4294262295626169415208237)
            ·
              refine ⟨1610348360859813530703089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4294262295626169415208237 1610348360859813530703089)
              ·
                refine ⟨1207761270644860148027317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1610348360859813530703089 1207761270644860148027317)
                ·
                  refine ⟨113227619122955638877561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1207761270644860148027317 113227619122955638877561)
                  ·
                    rfl

theorem cell22_992295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 5].length) (baseStart_992295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992295 prefixEnd_992295 := by exact prefixLift 992295
  have htrace : WordTrace (prefixWord ++ tailWord_992295) baseStart_992295 baseEnd_992295 := by
    simpa [prefixWord, tailWord_992295, baseEnd_992295] using wordTrace_append hprefix tailTrace_992295
  have hstable : (prefixWord ++ tailWord_992295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992295).length < 2 ^ (prefixWord ++ tailWord_992295).sum := by decide
  have hdescent : baseEnd_992295 < baseStart_992295 := by decide
  rcases family_descends (prefixWord ++ tailWord_992295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992336 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 6, 4]
def baseStart_992336 : Nat := 118140960795 + 992336 * 2 ^ 59
def prefixEnd_992336 : Nat := 4983230072969 + 3 ^ 40 * 992336 * 2
def baseEnd_992336 : Nat := 339696892506756476357557

theorem tailTrace_992336 : CollatzResearch.WordTrace tailWord_992336 prefixEnd_992336 339696892506756476357557 := by
  unfold tailWord_992336
  simp only [CollatzResearch.WordTrace]
  refine ⟨18096733666471812170558431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24128978221962416227411241 18096733666471812170558431)
  ·
    refine ⟨27145100499707718255837647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18096733666471812170558431 27145100499707718255837647)
    ·
      refine ⟨40717650749561577383756471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27145100499707718255837647 40717650749561577383756471)
      ·
        refine ⟨61076476124342366075634707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40717650749561577383756471 61076476124342366075634707)
        ·
          refine ⟨91614714186513549113452061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61076476124342366075634707 91614714186513549113452061)
          ·
            refine ⟨34355517819942580917544523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91614714186513549113452061 34355517819942580917544523)
            ·
              refine ⟨51533276729913871376316785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34355517819942580917544523 51533276729913871376316785)
              ·
                refine ⟨38649957547435403532237589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51533276729913871376316785 38649957547435403532237589)
                ·
                  refine ⟨1811716760036034540573637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38649957547435403532237589 1811716760036034540573637)
                  ·
                    refine ⟨339696892506756476357557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1811716760036034540573637 339696892506756476357557)
                    ·
                      rfl

theorem cell22_992336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_992336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992336 prefixEnd_992336 := by exact prefixLift 992336
  have htrace : WordTrace (prefixWord ++ tailWord_992336) baseStart_992336 baseEnd_992336 := by
    simpa [prefixWord, tailWord_992336, baseEnd_992336] using wordTrace_append hprefix tailTrace_992336
  have hstable : (prefixWord ++ tailWord_992336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992336).length < 2 ^ (prefixWord ++ tailWord_992336).sum := by decide
  have hdescent : baseEnd_992336 < baseStart_992336 := by decide
  rcases family_descends (prefixWord ++ tailWord_992336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992340 : List Nat := [2, 4, 1, 1, 1, 1, 5, 3, 4]
def baseStart_992340 : Nat := 118140960795 + 992340 * 2 ^ 59
def prefixEnd_992340 : Nat := 4983230072969 + 3 ^ 40 * 992340 * 2
def baseEnd_992340 : Nat := 113232753929500599752515

theorem tailTrace_992340 : CollatzResearch.WordTrace tailWord_992340 prefixEnd_992340 113232753929500599752515 := by
  unfold tailWord_992340
  simp only [CollatzResearch.WordTrace]
  refine ⟨18096806612464566512131237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24129075483286088682841649 18096806612464566512131237)
  ·
    refine ⟨3393151239837106221024607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18096806612464566512131237 3393151239837106221024607)
    ·
      refine ⟨5089726859755659331536911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3393151239837106221024607 5089726859755659331536911)
      ·
        refine ⟨7634590289633488997305367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5089726859755659331536911 7634590289633488997305367)
        ·
          refine ⟨11451885434450233495958051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7634590289633488997305367 11451885434450233495958051)
          ·
            refine ⟨17177828151675350243937077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11451885434450233495958051 17177828151675350243937077)
            ·
              refine ⟨1610421389219564085369101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17177828151675350243937077 1610421389219564085369101)
              ·
                refine ⟨603908020957336532013413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1610421389219564085369101 603908020957336532013413)
                ·
                  refine ⟨113232753929500599752515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 603908020957336532013413 113232753929500599752515)
                  ·
                    rfl

theorem cell22_992340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_992340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992340 prefixEnd_992340 := by exact prefixLift 992340
  have htrace : WordTrace (prefixWord ++ tailWord_992340) baseStart_992340 baseEnd_992340 := by
    simpa [prefixWord, tailWord_992340, baseEnd_992340] using wordTrace_append hprefix tailTrace_992340
  have hstable : (prefixWord ++ tailWord_992340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992340).length < 2 ^ (prefixWord ++ tailWord_992340).sum := by decide
  have hdescent : baseEnd_992340 < baseStart_992340 := by decide
  rcases family_descends (prefixWord ++ tailWord_992340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992396 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 9]
def baseStart_992396 : Nat := 118140960795 + 992396 * 2 ^ 59
def prefixEnd_992396 : Nat := 4983230072969 + 3 ^ 40 * 992396 * 2
def baseEnd_992396 : Nat := 113239143910978773285791

theorem tailTrace_992396 : CollatzResearch.WordTrace tailWord_992396 prefixEnd_992396 113239143910978773285791 := by
  unfold tailWord_992396
  simp only [CollatzResearch.WordTrace]
  refine ⟨18097827856363127294150521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24130437141817503058867361 18097827856363127294150521)
  ·
    refine ⟨13573370892272345470612891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18097827856363127294150521 13573370892272345470612891)
    ·
      refine ⟨20360056338408518205919337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13573370892272345470612891 20360056338408518205919337)
      ·
        refine ⟨15270042253806388654439503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20360056338408518205919337 15270042253806388654439503)
        ·
          refine ⟨22905063380709582981659255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15270042253806388654439503 22905063380709582981659255)
          ·
            refine ⟨34357595071064374472488883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22905063380709582981659255 34357595071064374472488883)
            ·
              refine ⟨51536392606596561708733325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34357595071064374472488883 51536392606596561708733325)
              ·
                refine ⟨19326147227473710640774997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51536392606596561708733325 19326147227473710640774997)
                ·
                  refine ⟨113239143910978773285791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19326147227473710640774997 113239143910978773285791)
                  ·
                    rfl

theorem cell22_992396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_992396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992396 prefixEnd_992396 := by exact prefixLift 992396
  have htrace : WordTrace (prefixWord ++ tailWord_992396) baseStart_992396 baseEnd_992396 := by
    simpa [prefixWord, tailWord_992396, baseEnd_992396] using wordTrace_append hprefix tailTrace_992396
  have hstable : (prefixWord ++ tailWord_992396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992396).length < 2 ^ (prefixWord ++ tailWord_992396).sum := by decide
  have hdescent : baseEnd_992396 < baseStart_992396 := by decide
  rcases family_descends (prefixWord ++ tailWord_992396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992417 : List Nat := [1, 2, 3, 3, 1, 1, 3, 4, 1, 3]
def baseStart_992417 : Nat := 118140960795 + 992417 * 2 ^ 59
def prefixEnd_992417 : Nat := 4983230072969 + 3 ^ 40 * 992417 * 2
def baseEnd_992417 : Nat := 339724620462099265082309

theorem tailTrace_992417 : CollatzResearch.WordTrace tailWord_992417 prefixEnd_992417 339724620462099265082309 := by
  unfold tailWord_992417
  simp only [CollatzResearch.WordTrace]
  refine ⟨36196421645650175174815505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24130947763766783449877003 36196421645650175174815505)
  ·
    refine ⟨27147316234237631381111629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36196421645650175174815505 27147316234237631381111629)
    ·
      refine ⟨10180243587839111767916861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27147316234237631381111629 10180243587839111767916861)
      ·
        refine ⟨3817591345439666912968823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10180243587839111767916861 3817591345439666912968823)
        ·
          refine ⟨5726387018159500369453235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3817591345439666912968823 5726387018159500369453235)
          ·
            refine ⟨8589580527239250554179853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5726387018159500369453235 8589580527239250554179853)
            ·
              refine ⟨3221092697714718957817445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8589580527239250554179853 3221092697714718957817445)
              ·
                refine ⟨603954880821509804590771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3221092697714718957817445 603954880821509804590771)
                ·
                  refine ⟨905932321232264706886157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 603954880821509804590771 905932321232264706886157)
                  ·
                    refine ⟨339724620462099265082309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 905932321232264706886157 339724620462099265082309)
                    ·
                      rfl

theorem cell22_992417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_992417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992417 prefixEnd_992417 := by exact prefixLift 992417
  have htrace : WordTrace (prefixWord ++ tailWord_992417) baseStart_992417 baseEnd_992417 := by
    simpa [prefixWord, tailWord_992417, baseEnd_992417] using wordTrace_append hprefix tailTrace_992417
  have hstable : (prefixWord ++ tailWord_992417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992417).length < 2 ^ (prefixWord ++ tailWord_992417).sum := by decide
  have hdescent : baseEnd_992417 < baseStart_992417 := by decide
  rcases family_descends (prefixWord ++ tailWord_992417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992488 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 3, 6]
def baseStart_992488 : Nat := 118140960795 + 992488 * 2 ^ 59
def prefixEnd_992488 : Nat := 4983230072969 + 3 ^ 40 * 992488 * 2
def baseEnd_992488 : Nat := 339748925213078746557091

theorem tailTrace_992488 : CollatzResearch.WordTrace tailWord_992488 prefixEnd_992488 339748925213078746557091 := by
  unfold tailWord_992488
  simp only [CollatzResearch.WordTrace]
  refine ⟨18099505614196477150325059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24132674152261969533766745 18099505614196477150325059)
  ·
    refine ⟨27149258421294715725487589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18099505614196477150325059 27149258421294715725487589)
    ·
      refine ⟨5090485953992759198528923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27149258421294715725487589 5090485953992759198528923)
      ·
        refine ⟨7635728930989138797793385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5090485953992759198528923 7635728930989138797793385)
        ·
          refine ⟨5726796698241854098345039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7635728930989138797793385 5726796698241854098345039)
          ·
            refine ⟨8590195047362781147517559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5726796698241854098345039 8590195047362781147517559)
            ·
              refine ⟨12885292571044171721276339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8590195047362781147517559 12885292571044171721276339)
              ·
                refine ⟨19327938856566257581914509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12885292571044171721276339 19327938856566257581914509)
                ·
                  refine ⟨7247977071212346593217941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19327938856566257581914509 7247977071212346593217941)
                  ·
                    refine ⟨339748925213078746557091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7247977071212346593217941 339748925213078746557091)
                    ·
                      rfl

theorem cell22_992488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_992488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992488 prefixEnd_992488 := by exact prefixLift 992488
  have htrace : WordTrace (prefixWord ++ tailWord_992488) baseStart_992488 baseEnd_992488 := by
    simpa [prefixWord, tailWord_992488, baseEnd_992488] using wordTrace_append hprefix tailTrace_992488
  have hstable : (prefixWord ++ tailWord_992488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992488).length < 2 ^ (prefixWord ++ tailWord_992488).sum := by decide
  have hdescent : baseEnd_992488 < baseStart_992488 := by decide
  rcases family_descends (prefixWord ++ tailWord_992488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992490 : List Nat := [3, 1, 3, 1, 1, 3, 3, 1, 1, 5]
def baseStart_992490 : Nat := 118140960795 + 992490 * 2 ^ 59
def prefixEnd_992490 : Nat := 4983230072969 + 3 ^ 40 * 992490 * 2
def baseEnd_992490 : Nat := 339749609853951408007085

theorem tailTrace_992490 : CollatzResearch.WordTrace tailWord_992490 prefixEnd_992490 339749609853951408007085 := by
  unfold tailWord_992490
  simp only [CollatzResearch.WordTrace]
  refine ⟨9049771043596427160555731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24132722782923805761481949 9049771043596427160555731)
  ·
    refine ⟨13574656565394640740833597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9049771043596427160555731 13574656565394640740833597)
    ·
      refine ⟨5090496212022990277812599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13574656565394640740833597 5090496212022990277812599)
      ·
        refine ⟨7635744318034485416718899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5090496212022990277812599 7635744318034485416718899)
        ·
          refine ⟨11453616477051728125078349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7635744318034485416718899 11453616477051728125078349)
          ·
            refine ⟨4295106178894398046904381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11453616477051728125078349 4295106178894398046904381)
            ·
              refine ⟨1610664817085399267589143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4295106178894398046904381 1610664817085399267589143)
              ·
                refine ⟨2415997225628098901383715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1610664817085399267589143 2415997225628098901383715)
                ·
                  refine ⟨3623995838442148352075573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2415997225628098901383715 3623995838442148352075573)
                  ·
                    refine ⟨339749609853951408007085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3623995838442148352075573 339749609853951408007085)
                    ·
                      rfl

theorem cell22_992490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_992490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992490 prefixEnd_992490 := by exact prefixLift 992490
  have htrace : WordTrace (prefixWord ++ tailWord_992490) baseStart_992490 baseEnd_992490 := by
    simpa [prefixWord, tailWord_992490, baseEnd_992490] using wordTrace_append hprefix tailTrace_992490
  have hstable : (prefixWord ++ tailWord_992490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992490).length < 2 ^ (prefixWord ++ tailWord_992490).sum := by decide
  have hdescent : baseEnd_992490 < baseStart_992490 := by decide
  rcases family_descends (prefixWord ++ tailWord_992490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992520 : List Nat := [2, 1, 3, 2, 4, 2, 8]
def baseStart_992520 : Nat := 118140960795 + 992520 * 2 ^ 59
def prefixEnd_992520 : Nat := 4983230072969 + 3 ^ 40 * 992520 * 2
def baseEnd_992520 : Nat := 12583699239520049250259

theorem tailTrace_992520 : CollatzResearch.WordTrace tailWord_992520 prefixEnd_992520 12583699239520049250259 := by
  unfold tailWord_992520
  simp only [CollatzResearch.WordTrace]
  refine ⟨18100089182138511882907507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24133452242851349177210009 18100089182138511882907507)
  ·
    refine ⟨27150133773207767824361261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18100089182138511882907507 27150133773207767824361261)
    ·
      refine ⟨10181300164952912934135473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27150133773207767824361261 10181300164952912934135473)
      ·
        refine ⟨7635975123714684700601605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10181300164952912934135473 7635975123714684700601605)
        ·
          refine ⟨1431745335696503381362801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7635975123714684700601605 1431745335696503381362801)
          ·
            refine ⟨1073809001772377536022101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1431745335696503381362801 1073809001772377536022101)
            ·
              refine ⟨12583699239520049250259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1073809001772377536022101 12583699239520049250259)
              ·
                rfl

theorem cell22_992520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 8].length) (baseStart_992520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992520 prefixEnd_992520 := by exact prefixLift 992520
  have htrace : WordTrace (prefixWord ++ tailWord_992520) baseStart_992520 baseEnd_992520 := by
    simpa [prefixWord, tailWord_992520, baseEnd_992520] using wordTrace_append hprefix tailTrace_992520
  have hstable : (prefixWord ++ tailWord_992520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992520).length < 2 ^ (prefixWord ++ tailWord_992520).sum := by decide
  have hdescent : baseEnd_992520 < baseStart_992520 := by decide
  rcases family_descends (prefixWord ++ tailWord_992520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992533 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 2, 6]
def baseStart_992533 : Nat := 118140960795 + 992533 * 2 ^ 59
def prefixEnd_992533 : Nat := 4983230072969 + 3 ^ 40 * 992533 * 2
def baseEnd_992533 : Nat := 339764329632713629181953

theorem tailTrace_992533 : CollatzResearch.WordTrace tailWord_992533 prefixEnd_992533 339764329632713629181953 := by
  unfold tailWord_992533
  simp only [CollatzResearch.WordTrace]
  refine ⟨36200652513229926986038253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24133768342153284657358835 36200652513229926986038253)
  ·
    refine ⟨13575244692461222619764345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36200652513229926986038253 13575244692461222619764345)
    ·
      refine ⟨10181433519345916964823259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13575244692461222619764345 10181433519345916964823259)
      ·
        refine ⟨15272150279018875447234889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10181433519345916964823259 15272150279018875447234889)
        ·
          refine ⟨11454112709264156585426167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15272150279018875447234889 11454112709264156585426167)
          ·
            refine ⟨17181169063896234878139251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11454112709264156585426167 17181169063896234878139251)
            ·
              refine ⟨25771753595844352317208877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17181169063896234878139251 25771753595844352317208877)
              ·
                refine ⟨9664407598441632118953329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25771753595844352317208877 9664407598441632118953329)
                ·
                  refine ⟨7248305698831224089214997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9664407598441632118953329 7248305698831224089214997)
                  ·
                    refine ⟨339764329632713629181953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7248305698831224089214997 339764329632713629181953)
                    ·
                      rfl

theorem cell22_992533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_992533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992533 prefixEnd_992533 := by exact prefixLift 992533
  have htrace : WordTrace (prefixWord ++ tailWord_992533) baseStart_992533 baseEnd_992533 := by
    simpa [prefixWord, tailWord_992533, baseEnd_992533] using wordTrace_append hprefix tailTrace_992533
  have hstable : (prefixWord ++ tailWord_992533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992533).length < 2 ^ (prefixWord ++ tailWord_992533).sum := by decide
  have hdescent : baseEnd_992533 < baseStart_992533 := by decide
  rcases family_descends (prefixWord ++ tailWord_992533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992541 : List Nat := [1, 4, 2, 3, 1, 3, 2, 1, 2, 3]
def baseStart_992541 : Nat := 118140960795 + 992541 * 2 ^ 59
def prefixEnd_992541 : Nat := 4983230072969 + 3 ^ 40 * 992541 * 2
def baseEnd_992541 : Nat := 339767068196204274981929

theorem tailTrace_992541 : CollatzResearch.WordTrace tailWord_992541 prefixEnd_992541 339767068196204274981929 := by
  unfold tailWord_992541
  simp only [CollatzResearch.WordTrace]
  refine ⟨36200944297200944352329477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24133962864800629568219651 36200944297200944352329477)
  ·
    refine ⟨6787677055725177066061777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36200944297200944352329477 6787677055725177066061777)
    ·
      refine ⟨5090757791793882799546333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6787677055725177066061777 5090757791793882799546333)
      ·
        refine ⟨1909034171922706049829875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5090757791793882799546333 1909034171922706049829875)
        ·
          refine ⟨2863551257884059074744813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909034171922706049829875 2863551257884059074744813)
          ·
            refine ⟨1073831721706522153029305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2863551257884059074744813 1073831721706522153029305)
            ·
              refine ⟨805373791279891614771979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1073831721706522153029305 805373791279891614771979)
              ·
                refine ⟨1208060686919837422157969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805373791279891614771979 1208060686919837422157969)
                ·
                  refine ⟨906045515189878066618477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1208060686919837422157969 906045515189878066618477)
                  ·
                    refine ⟨339767068196204274981929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 906045515189878066618477 339767068196204274981929)
                    ·
                      rfl

theorem cell22_992541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_992541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992541 prefixEnd_992541 := by exact prefixLift 992541
  have htrace : WordTrace (prefixWord ++ tailWord_992541) baseStart_992541 baseEnd_992541 := by
    simpa [prefixWord, tailWord_992541, baseEnd_992541] using wordTrace_append hprefix tailTrace_992541
  have hstable : (prefixWord ++ tailWord_992541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992541).length < 2 ^ (prefixWord ++ tailWord_992541).sum := by decide
  have hdescent : baseEnd_992541 < baseStart_992541 := by decide
  rcases family_descends (prefixWord ++ tailWord_992541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992625 : List Nat := [1, 2, 2, 2, 1, 2, 4, 2, 1, 5]
def baseStart_992625 : Nat := 118140960795 + 992625 * 2 ^ 59
def prefixEnd_992625 : Nat := 4983230072969 + 3 ^ 40 * 992625 * 2
def baseEnd_992625 : Nat := 339795823112856055881671

theorem tailTrace_992625 : CollatzResearch.WordTrace tailWord_992625 prefixEnd_992625 339795823112856055881671 := by
  unfold tailWord_992625
  simp only [CollatzResearch.WordTrace]
  refine ⟨36204008028896626698387329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24136005352597751132258219 36204008028896626698387329)
  ·
    refine ⟨27153006021672470023790497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36204008028896626698387329 27153006021672470023790497)
    ·
      refine ⟨20364754516254352517842873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27153006021672470023790497 20364754516254352517842873)
      ·
        refine ⟨15273565887190764388382155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20364754516254352517842873 15273565887190764388382155)
        ·
          refine ⟨22910348830786146582573233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15273565887190764388382155 22910348830786146582573233)
          ·
            refine ⟨17182761623089609936929925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22910348830786146582573233 17182761623089609936929925)
            ·
              refine ⟨3221767804329301863174361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17182761623089609936929925 3221767804329301863174361)
              ·
                refine ⟨2416325853246976397380771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3221767804329301863174361 2416325853246976397380771)
                ·
                  refine ⟨3624488779870464596071157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416325853246976397380771 3624488779870464596071157)
                  ·
                    refine ⟨339795823112856055881671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3624488779870464596071157 339795823112856055881671)
                    ·
                      rfl

theorem cell22_992625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_992625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992625 prefixEnd_992625 := by exact prefixLift 992625
  have htrace : WordTrace (prefixWord ++ tailWord_992625) baseStart_992625 baseEnd_992625 := by
    simpa [prefixWord, tailWord_992625, baseEnd_992625] using wordTrace_append hprefix tailTrace_992625
  have hstable : (prefixWord ++ tailWord_992625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992625).length < 2 ^ (prefixWord ++ tailWord_992625).sum := by decide
  have hdescent : baseEnd_992625 < baseStart_992625 := by decide
  rcases family_descends (prefixWord ++ tailWord_992625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992629 : List Nat := [1, 3, 4, 1, 3, 1, 1, 3, 1, 4]
def baseStart_992629 : Nat := 118140960795 + 992629 * 2 ^ 59
def prefixEnd_992629 : Nat := 4983230072969 + 3 ^ 40 * 992629 * 2
def baseEnd_992629 : Nat := 339797192394601378781659

theorem tailTrace_992629 : CollatzResearch.WordTrace tailWord_992629 prefixEnd_992629 339797192394601378781659 := by
  unfold tailWord_992629
  simp only [CollatzResearch.WordTrace]
  refine ⟨36204153920882135381532941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24136102613921423587688627 36204153920882135381532941)
  ·
    refine ⟨13576557720330800768074853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36204153920882135381532941 13576557720330800768074853)
    ·
      refine ⟨2545604572562025144014035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13576557720330800768074853 2545604572562025144014035)
      ·
        refine ⟨3818406858843037716021053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2545604572562025144014035 3818406858843037716021053)
        ·
          refine ⟨1431902572066139143507895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3818406858843037716021053 1431902572066139143507895)
          ·
            refine ⟨2147853858099208715261843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431902572066139143507895 2147853858099208715261843)
            ·
              refine ⟨3221780787148813072892765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2147853858099208715261843 3221780787148813072892765)
              ·
                refine ⟨1208167795180804902334787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3221780787148813072892765 1208167795180804902334787)
                ·
                  refine ⟨1812251692771207353502181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1208167795180804902334787 1812251692771207353502181)
                  ·
                    refine ⟨339797192394601378781659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1812251692771207353502181 339797192394601378781659)
                    ·
                      rfl

theorem cell22_992629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_992629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992629 prefixEnd_992629 := by exact prefixLift 992629
  have htrace : WordTrace (prefixWord ++ tailWord_992629) baseStart_992629 baseEnd_992629 := by
    simpa [prefixWord, tailWord_992629, baseEnd_992629] using wordTrace_append hprefix tailTrace_992629
  have hstable : (prefixWord ++ tailWord_992629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992629).length < 2 ^ (prefixWord ++ tailWord_992629).sum := by decide
  have hdescent : baseEnd_992629 < baseStart_992629 := by decide
  rcases family_descends (prefixWord ++ tailWord_992629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992640 : List Nat := [2, 1, 1, 2, 1, 2, 1, 6, 2, 4]
def baseStart_992640 : Nat := 118140960795 + 992640 * 2 ^ 59
def prefixEnd_992640 : Nat := 4983230072969 + 3 ^ 40 * 992640 * 2
def baseEnd_992640 : Nat := 339800957919401016756625

theorem tailTrace_992640 : CollatzResearch.WordTrace tailWord_992640 prefixEnd_992640 339800957919401016756625 := by
  unfold tailWord_992640
  simp only [CollatzResearch.WordTrace]
  refine ⟨18102277561921142130091687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24136370082561522840122249 18102277561921142130091687)
  ·
    refine ⟨27153416342881713195137531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18102277561921142130091687 27153416342881713195137531)
    ·
      refine ⟨40730124514322569792706297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27153416342881713195137531 40730124514322569792706297)
      ·
        refine ⟨30547593385741927344529723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40730124514322569792706297 30547593385741927344529723)
        ·
          refine ⟨45821390078612891016794585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30547593385741927344529723 45821390078612891016794585)
          ·
            refine ⟨34366042558959668262595939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45821390078612891016794585 34366042558959668262595939)
            ·
              refine ⟨51549063838439502393893909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34366042558959668262595939 51549063838439502393893909)
              ·
                refine ⟨2416362367426851674713777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51549063838439502393893909 2416362367426851674713777)
                ·
                  refine ⟨1812271775570138756035333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2416362367426851674713777 1812271775570138756035333)
                  ·
                    refine ⟨339800957919401016756625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1812271775570138756035333 339800957919401016756625)
                    ·
                      rfl

theorem cell22_992640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_992640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992640 prefixEnd_992640 := by exact prefixLift 992640
  have htrace : WordTrace (prefixWord ++ tailWord_992640) baseStart_992640 baseEnd_992640 := by
    simpa [prefixWord, tailWord_992640, baseEnd_992640] using wordTrace_append hprefix tailTrace_992640
  have hstable : (prefixWord ++ tailWord_992640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992640).length < 2 ^ (prefixWord ++ tailWord_992640).sum := by decide
  have hdescent : baseEnd_992640 < baseStart_992640 := by decide
  rcases family_descends (prefixWord ++ tailWord_992640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992704 : List Nat := [2, 1, 1, 2, 3, 1, 2, 6, 1, 3]
def baseStart_992704 : Nat := 118140960795 + 992704 * 2 ^ 59
def prefixEnd_992704 : Nat := 4983230072969 + 3 ^ 40 * 992704 * 2
def baseEnd_992704 : Nat := 339822866427326183156429

theorem tailTrace_992704 : CollatzResearch.WordTrace tailWord_992704 prefixEnd_992704 339822866427326183156429 := by
  unfold tailWord_992704
  simp only [CollatzResearch.WordTrace]
  refine ⟨18103444697805211595256583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24137926263740282127008777 18103444697805211595256583)
  ·
    refine ⟨27155167046707817392884875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18103444697805211595256583 27155167046707817392884875)
    ·
      refine ⟨40732750570061726089327313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27155167046707817392884875 40732750570061726089327313)
      ·
        refine ⟨30549562927546294566995485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40732750570061726089327313 30549562927546294566995485)
        ·
          refine ⟨11456086097829860462623307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30549562927546294566995485 11456086097829860462623307)
          ·
            refine ⟨17184129146744790693934961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11456086097829860462623307 17184129146744790693934961)
            ·
              refine ⟨12888096860058593020451221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17184129146744790693934961 12888096860058593020451221)
              ·
                refine ⟨604129540315246547833651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12888096860058593020451221 604129540315246547833651)
                ·
                  refine ⟨906194310472869821750477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 604129540315246547833651 906194310472869821750477)
                  ·
                    refine ⟨339822866427326183156429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 906194310472869821750477 339822866427326183156429)
                    ·
                      rfl

theorem cell22_992704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 1, 3].length) (baseStart_992704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992704 prefixEnd_992704 := by exact prefixLift 992704
  have htrace : WordTrace (prefixWord ++ tailWord_992704) baseStart_992704 baseEnd_992704 := by
    simpa [prefixWord, tailWord_992704, baseEnd_992704] using wordTrace_append hprefix tailTrace_992704
  have hstable : (prefixWord ++ tailWord_992704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992704).length < 2 ^ (prefixWord ++ tailWord_992704).sum := by decide
  have hdescent : baseEnd_992704 < baseStart_992704 := by decide
  rcases family_descends (prefixWord ++ tailWord_992704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992715 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 2, 5]
def baseStart_992715 : Nat := 118140960795 + 992715 * 2 ^ 59
def prefixEnd_992715 : Nat := 4983230072969 + 3 ^ 40 * 992715 * 2
def baseEnd_992715 : Nat := 339826631952125821131395

theorem tailTrace_992715 : CollatzResearch.WordTrace tailWord_992715 prefixEnd_992715 339826631952125821131395 := by
  unfold tailWord_992715
  simp only [CollatzResearch.WordTrace]
  refine ⟨36207290598570572069163599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24138193732380381379442399 36207290598570572069163599)
  ·
    refine ⟨54310935897855858103745399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36207290598570572069163599 54310935897855858103745399)
    ·
      refine ⟨81466403846783787155618099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54310935897855858103745399 81466403846783787155618099)
      ·
        refine ⟨122199605770175680733427149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81466403846783787155618099 122199605770175680733427149)
        ·
          refine ⟨45824852163815880275035181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122199605770175680733427149 45824852163815880275035181)
          ·
            refine ⟨17184319561430955103138193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45824852163815880275035181 17184319561430955103138193)
            ·
              refine ⟨12888239671073216327353645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17184319561430955103138193 12888239671073216327353645)
              ·
                refine ⟨4833089876652456122757617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12888239671073216327353645 4833089876652456122757617)
                ·
                  refine ⟨3624817407489342092068213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4833089876652456122757617 3624817407489342092068213)
                  ·
                    refine ⟨339826631952125821131395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3624817407489342092068213 339826631952125821131395)
                    ·
                      rfl

theorem cell22_992715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 5].length) (baseStart_992715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992715 prefixEnd_992715 := by exact prefixLift 992715
  have htrace : WordTrace (prefixWord ++ tailWord_992715) baseStart_992715 baseEnd_992715 := by
    simpa [prefixWord, tailWord_992715, baseEnd_992715] using wordTrace_append hprefix tailTrace_992715
  have hstable : (prefixWord ++ tailWord_992715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992715).length < 2 ^ (prefixWord ++ tailWord_992715).sum := by decide
  have hdescent : baseEnd_992715 < baseStart_992715 := by decide
  rcases family_descends (prefixWord ++ tailWord_992715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992766 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_992766 : Nat := 118140960795 + 992766 * 2 ^ 59
def prefixEnd_992766 : Nat := 4983230072969 + 3 ^ 40 * 992766 * 2
def baseEnd_992766 : Nat := 339844090294378688106239

theorem tailTrace_992766 : CollatzResearch.WordTrace tailWord_992766 prefixEnd_992766 339844090294378688106239 := by
  unfold tailWord_992766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4526143840173225972408769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24139433814257205186180101 4526143840173225972408769)
  ·
    refine ⟨3394607880129919479306577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4526143840173225972408769 3394607880129919479306577)
    ·
      refine ⟨2545955910097439609479933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3394607880129919479306577 2545955910097439609479933)
      ·
        refine ⟨954733466286539853554975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2545955910097439609479933 954733466286539853554975)
        ·
          refine ⟨1432100199429809780332463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954733466286539853554975 1432100199429809780332463)
          ·
            refine ⟨2148150299144714670498695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432100199429809780332463 2148150299144714670498695)
            ·
              refine ⟨3222225448717072005748043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148150299144714670498695 3222225448717072005748043)
              ·
                refine ⟨4833338173075608008622065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3222225448717072005748043 4833338173075608008622065)
                ·
                  refine ⟨3625003629806706006466549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4833338173075608008622065 3625003629806706006466549)
                  ·
                    refine ⟨339844090294378688106239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3625003629806706006466549 339844090294378688106239)
                    ·
                      rfl

theorem cell22_992766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_992766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992766 prefixEnd_992766 := by exact prefixLift 992766
  have htrace : WordTrace (prefixWord ++ tailWord_992766) baseStart_992766 baseEnd_992766 := by
    simpa [prefixWord, tailWord_992766, baseEnd_992766] using wordTrace_append hprefix tailTrace_992766
  have hstable : (prefixWord ++ tailWord_992766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992766).length < 2 ^ (prefixWord ++ tailWord_992766).sum := by decide
  have hdescent : baseEnd_992766 < baseStart_992766 := by decide
  rcases family_descends (prefixWord ++ tailWord_992766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992777 : List Nat := [1, 2, 1, 1, 3, 1, 6, 1, 1, 5]
def baseStart_992777 : Nat := 118140960795 + 992777 * 2 ^ 59
def prefixEnd_992777 : Nat := 4983230072969 + 3 ^ 40 * 992777 * 2
def baseEnd_992777 : Nat := 339847855819178326081205

theorem tailTrace_992777 : CollatzResearch.WordTrace tailWord_992777 prefixEnd_992777 339847855819178326081205 := by
  unfold tailWord_992777
  simp only [CollatzResearch.WordTrace]
  refine ⟨36209551924345956657920585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24139701282897304438613723 36209551924345956657920585)
  ·
    refine ⟨27157163943259467493440439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36209551924345956657920585 27157163943259467493440439)
    ·
      refine ⟨40735745914889201240160659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27157163943259467493440439 40735745914889201240160659)
      ·
        refine ⟨61103618872333801860240989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40735745914889201240160659 61103618872333801860240989)
        ·
          refine ⟨22913857077125175697590371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61103618872333801860240989 22913857077125175697590371)
          ·
            refine ⟨34370785615687763546385557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22913857077125175697590371 34370785615687763546385557)
            ·
              refine ⟨1611130575735363916236823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34370785615687763546385557 1611130575735363916236823)
              ·
                refine ⟨2416695863603045874355235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611130575735363916236823 2416695863603045874355235)
                ·
                  refine ⟨3625043795404568811532853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416695863603045874355235 3625043795404568811532853)
                  ·
                    refine ⟨339847855819178326081205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3625043795404568811532853 339847855819178326081205)
                    ·
                      rfl

theorem cell22_992777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 5].length) (baseStart_992777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992777 prefixEnd_992777 := by exact prefixLift 992777
  have htrace : WordTrace (prefixWord ++ tailWord_992777) baseStart_992777 baseEnd_992777 := by
    simpa [prefixWord, tailWord_992777, baseEnd_992777] using wordTrace_append hprefix tailTrace_992777
  have hstable : (prefixWord ++ tailWord_992777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992777).length < 2 ^ (prefixWord ++ tailWord_992777).sum := by decide
  have hdescent : baseEnd_992777 < baseStart_992777 := by decide
  rcases family_descends (prefixWord ++ tailWord_992777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992828 : List Nat := [2, 2, 2, 2, 4, 1, 3, 1, 2, 3]
def baseStart_992828 : Nat := 118140960795 + 992828 * 2 ^ 59
def prefixEnd_992828 : Nat := 4983230072969 + 3 ^ 40 * 992828 * 2
def baseEnd_992828 : Nat := 339865314161431193056049

theorem tailTrace_992828 : CollatzResearch.WordTrace tailWord_992828 prefixEnd_992828 339865314161431193056049 := by
  unfold tailWord_992828
  simp only [CollatzResearch.WordTrace]
  refine ⟨18105706023580596184013569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24140941364774128245351425 18105706023580596184013569)
  ·
    refine ⟨13579279517685447138010177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18105706023580596184013569 13579279517685447138010177)
    ·
      refine ⟨10184459638264085353507633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13579279517685447138010177 10184459638264085353507633)
      ·
        refine ⟨7638344728698064015130725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10184459638264085353507633 7638344728698064015130725)
        ·
          refine ⟨1432189636630887002837011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7638344728698064015130725 1432189636630887002837011)
          ·
            refine ⟨2148284454946330504255517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432189636630887002837011 2148284454946330504255517)
            ·
              refine ⟨805606670604873939095819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2148284454946330504255517 805606670604873939095819)
              ·
                refine ⟨1208410005907310908643729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805606670604873939095819 1208410005907310908643729)
                ·
                  refine ⟨906307504430483181482797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1208410005907310908643729 906307504430483181482797)
                  ·
                    refine ⟨339865314161431193056049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 906307504430483181482797 339865314161431193056049)
                    ·
                      rfl

theorem cell22_992828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_992828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992828 prefixEnd_992828 := by exact prefixLift 992828
  have htrace : WordTrace (prefixWord ++ tailWord_992828) baseStart_992828 baseEnd_992828 := by
    simpa [prefixWord, tailWord_992828, baseEnd_992828] using wordTrace_append hprefix tailTrace_992828
  have hstable : (prefixWord ++ tailWord_992828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992828).length < 2 ^ (prefixWord ++ tailWord_992828).sum := by decide
  have hdescent : baseEnd_992828 < baseStart_992828 := by decide
  rcases family_descends (prefixWord ++ tailWord_992828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992852 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 9]
def baseStart_992852 : Nat := 118140960795 + 992852 * 2 ^ 59
def prefixEnd_992852 : Nat := 4983230072969 + 3 ^ 40 * 992852 * 2
def baseEnd_992852 : Nat := 113291176617301043485325

theorem tailTrace_992852 : CollatzResearch.WordTrace tailWord_992852 prefixEnd_992852 113291176617301043485325 := by
  unfold tailWord_992852
  simp only [CollatzResearch.WordTrace]
  refine ⟨18106143699537122233450405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24141524932716162977933873 18106143699537122233450405)
  ·
    refine ⟨3394901943663210418771951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18106143699537122233450405 3394901943663210418771951)
    ·
      refine ⟨5092352915494815628157927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3394901943663210418771951 5092352915494815628157927)
      ·
        refine ⟨7638529373242223442236891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5092352915494815628157927 7638529373242223442236891)
        ·
          refine ⟨11457794059863335163355337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7638529373242223442236891 11457794059863335163355337)
          ·
            refine ⟨8593345544897501372516503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11457794059863335163355337 8593345544897501372516503)
            ·
              refine ⟨12890018317346252058774755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8593345544897501372516503 12890018317346252058774755)
              ·
                refine ⟨19335027476019378088162133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12890018317346252058774755 19335027476019378088162133)
                ·
                  refine ⟨113291176617301043485325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19335027476019378088162133 113291176617301043485325)
                  ·
                    rfl

theorem cell22_992852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_992852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992852 prefixEnd_992852 := by exact prefixLift 992852
  have htrace : WordTrace (prefixWord ++ tailWord_992852) baseStart_992852 baseEnd_992852 := by
    simpa [prefixWord, tailWord_992852, baseEnd_992852] using wordTrace_append hprefix tailTrace_992852
  have hstable : (prefixWord ++ tailWord_992852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992852).length < 2 ^ (prefixWord ++ tailWord_992852).sum := by decide
  have hdescent : baseEnd_992852 < baseStart_992852 := by decide
  rcases family_descends (prefixWord ++ tailWord_992852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992886 : List Nat := [5, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_992886 : Nat := 118140960795 + 992886 * 2 ^ 59
def prefixEnd_992886 : Nat := 4983230072969 + 3 ^ 40 * 992886 * 2
def baseEnd_992886 : Nat := 113295056248912791701957

theorem tailTrace_992886 : CollatzResearch.WordTrace tailWord_992886 prefixEnd_992886 113295056248912791701957 := by
  unfold tailWord_992886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2263345467559441767102407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24142351653967378849092341 2263345467559441767102407)
  ·
    refine ⟨3395018201339162650653611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2263345467559441767102407 3395018201339162650653611)
    ·
      refine ⟨5092527302008743975980417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3395018201339162650653611 5092527302008743975980417)
      ·
        refine ⟨3819395476506557981985313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5092527302008743975980417 3819395476506557981985313)
        ·
          refine ⟨2864546607379918486488985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3819395476506557981985313 2864546607379918486488985)
          ·
            refine ⟨2148409955534938864866739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2864546607379918486488985 2148409955534938864866739)
            ·
              refine ⟨3222614933302408297300109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148409955534938864866739 3222614933302408297300109)
              ·
                refine ⟨1208480599988403111487541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3222614933302408297300109 1208480599988403111487541)
                ·
                  refine ⟨113295056248912791701957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1208480599988403111487541 113295056248912791701957)
                  ·
                    rfl

theorem cell22_992886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_992886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992886 prefixEnd_992886 := by exact prefixLift 992886
  have htrace : WordTrace (prefixWord ++ tailWord_992886) baseStart_992886 baseEnd_992886 := by
    simpa [prefixWord, tailWord_992886, baseEnd_992886] using wordTrace_append hprefix tailTrace_992886
  have hstable : (prefixWord ++ tailWord_992886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992886).length < 2 ^ (prefixWord ++ tailWord_992886).sum := by decide
  have hdescent : baseEnd_992886 < baseStart_992886 := by decide
  rcases family_descends (prefixWord ++ tailWord_992886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992946 : List Nat := [3, 2, 1, 1, 1, 2, 4, 3, 2, 3]
def baseStart_992946 : Nat := 118140960795 + 992946 * 2 ^ 59
def prefixEnd_992946 : Nat := 4983230072969 + 3 ^ 40 * 992946 * 2
def baseEnd_992946 : Nat := 339905707972918218605687

theorem tailTrace_992946 : CollatzResearch.WordTrace tailWord_992946 prefixEnd_992946 339905707972918218605687 := by
  unfold tailWord_992946
  simp only [CollatzResearch.WordTrace]
  refine ⟨9053928965183424630205673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24143810573822465680548461 9053928965183424630205673)
  ·
    refine ⟨6790446723887568472654255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9053928965183424630205673 6790446723887568472654255)
    ·
      refine ⟨10185670085831352708981383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6790446723887568472654255 10185670085831352708981383)
      ·
        refine ⟨15278505128747029063472075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10185670085831352708981383 15278505128747029063472075)
        ·
          refine ⟨22917757693120543595208113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15278505128747029063472075 22917757693120543595208113)
          ·
            refine ⟨17188318269840407696406085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22917757693120543595208113 17188318269840407696406085)
            ·
              refine ⟨3222809675595076443076141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17188318269840407696406085 3222809675595076443076141)
              ·
                refine ⟨1208553628348153666153553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3222809675595076443076141 1208553628348153666153553)
                ·
                  refine ⟨906415221261115249615165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1208553628348153666153553 906415221261115249615165)
                  ·
                    refine ⟨339905707972918218605687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 906415221261115249615165 339905707972918218605687)
                    ·
                      rfl

theorem cell22_992946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_992946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992946 prefixEnd_992946 := by exact prefixLift 992946
  have htrace : WordTrace (prefixWord ++ tailWord_992946) baseStart_992946 baseEnd_992946 := by
    simpa [prefixWord, tailWord_992946, baseEnd_992946] using wordTrace_append hprefix tailTrace_992946
  have hstable : (prefixWord ++ tailWord_992946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992946).length < 2 ^ (prefixWord ++ tailWord_992946).sum := by decide
  have hdescent : baseEnd_992946 < baseStart_992946 := by decide
  rcases family_descends (prefixWord ++ tailWord_992946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992959 : List Nat := [1, 1, 2, 2, 2, 3, 5, 6]
def baseStart_992959 : Nat := 118140960795 + 992959 * 2 ^ 59
def prefixEnd_992959 : Nat := 4983230072969 + 3 ^ 40 * 992959 * 2
def baseEnd_992959 : Nat := 37767795348732279781183

theorem tailTrace_992959 : CollatzResearch.WordTrace tailWord_992959 prefixEnd_992959 37767795348732279781183 := by
  unfold tailWord_992959
  simp only [CollatzResearch.WordTrace]
  refine ⟨36216190009686601741045931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24144126673124401160697287 36216190009686601741045931)
  ·
    refine ⟨54324285014529902611568897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36216190009686601741045931 54324285014529902611568897)
    ·
      refine ⟨40743213760897426958676673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54324285014529902611568897 40743213760897426958676673)
      ·
        refine ⟨30557410320673070219007505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40743213760897426958676673 30557410320673070219007505)
        ·
          refine ⟨22918057740504802664255629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30557410320673070219007505 22918057740504802664255629)
          ·
            refine ⟨8594271652689300999095861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22918057740504802664255629 8594271652689300999095861)
            ·
              refine ⟨805712967439621968665237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8594271652689300999095861 805712967439621968665237)
              ·
                refine ⟨37767795348732279781183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 805712967439621968665237 37767795348732279781183)
                ·
                  rfl

theorem cell22_992959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 6].length) (baseStart_992959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992959 prefixEnd_992959 := by exact prefixLift 992959
  have htrace : WordTrace (prefixWord ++ tailWord_992959) baseStart_992959 baseEnd_992959 := by
    simpa [prefixWord, tailWord_992959, baseEnd_992959] using wordTrace_append hprefix tailTrace_992959
  have hstable : (prefixWord ++ tailWord_992959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992959).length < 2 ^ (prefixWord ++ tailWord_992959).sum := by decide
  have hdescent : baseEnd_992959 < baseStart_992959 := by decide
  rcases family_descends (prefixWord ++ tailWord_992959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992980 : List Nat := [2, 4, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_992980 : Nat := 118140960795 + 992980 * 2 ^ 59
def prefixEnd_992980 : Nat := 4983230072969 + 3 ^ 40 * 992980 * 2
def baseEnd_992980 : Nat := 339917346867753463255583

theorem tailTrace_992980 : CollatzResearch.WordTrace tailWord_992980 prefixEnd_992980 339917346867753463255583 := by
  unfold tailWord_992980
  simp only [CollatzResearch.WordTrace]
  refine ⟨18108477971305261163780197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24144637295073681551706929 18108477971305261163780197)
  ·
    refine ⟨3395339619619736468208787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18108477971305261163780197 3395339619619736468208787)
    ·
      refine ⟨5093009429429604702313181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3395339619619736468208787 5093009429429604702313181)
      ·
        refine ⟨1909878536036101763367443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5093009429429604702313181 1909878536036101763367443)
        ·
          refine ⟨2864817804054152645051165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909878536036101763367443 2864817804054152645051165)
          ·
            refine ⟨1074306676520307241894187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2864817804054152645051165 1074306676520307241894187)
            ·
              refine ⟨1611460014780460862841281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074306676520307241894187 1611460014780460862841281)
              ·
                refine ⟨1208595011085345647130961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1611460014780460862841281 1208595011085345647130961)
                ·
                  refine ⟨906446258314009235348221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1208595011085345647130961 906446258314009235348221)
                  ·
                    refine ⟨339917346867753463255583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 906446258314009235348221 339917346867753463255583)
                    ·
                      rfl

theorem cell22_992980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_992980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992980 prefixEnd_992980 := by exact prefixLift 992980
  have htrace : WordTrace (prefixWord ++ tailWord_992980) baseStart_992980 baseEnd_992980 := by
    simpa [prefixWord, tailWord_992980, baseEnd_992980] using wordTrace_append hprefix tailTrace_992980
  have hstable : (prefixWord ++ tailWord_992980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992980).length < 2 ^ (prefixWord ++ tailWord_992980).sum := by decide
  have hdescent : baseEnd_992980 < baseStart_992980 := by decide
  rcases family_descends (prefixWord ++ tailWord_992980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992991 : List Nat := [1, 1, 2, 3, 2, 2, 4, 1, 3, 3]
def baseStart_992991 : Nat := 118140960795 + 992991 * 2 ^ 59
def prefixEnd_992991 : Nat := 4983230072969 + 3 ^ 40 * 992991 * 2
def baseEnd_992991 : Nat := 339921112392553101230549

theorem tailTrace_992991 : CollatzResearch.WordTrace tailWord_992991 prefixEnd_992991 339921112392553101230549 := by
  unfold tailWord_992991
  simp only [CollatzResearch.WordTrace]
  refine ⟨36217357145570671206210827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24144904763713780804140551 36217357145570671206210827)
  ·
    refine ⟨54326035718356006809316241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36217357145570671206210827 54326035718356006809316241)
    ·
      refine ⟨40744526788767005106987181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54326035718356006809316241 40744526788767005106987181)
      ·
        refine ⟨15279197545787626915120193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40744526788767005106987181 15279197545787626915120193)
        ·
          refine ⟨11459398159340720186340145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15279197545787626915120193 11459398159340720186340145)
          ·
            refine ⟨8594548619505540139755109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11459398159340720186340145 8594548619505540139755109)
            ·
              refine ⟨1611477866157288776204083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8594548619505540139755109 1611477866157288776204083)
              ·
                refine ⟨2417216799235933164306125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611477866157288776204083 2417216799235933164306125)
                ·
                  refine ⟨906456299713474936614797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2417216799235933164306125 906456299713474936614797)
                  ·
                    refine ⟨339921112392553101230549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 906456299713474936614797 339921112392553101230549)
                    ·
                      rfl

theorem cell22_992991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 3].length) (baseStart_992991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_992991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_992991 prefixEnd_992991 := by exact prefixLift 992991
  have htrace : WordTrace (prefixWord ++ tailWord_992991) baseStart_992991 baseEnd_992991 := by
    simpa [prefixWord, tailWord_992991, baseEnd_992991] using wordTrace_append hprefix tailTrace_992991
  have hstable : (prefixWord ++ tailWord_992991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992991).length < 2 ^ (prefixWord ++ tailWord_992991).sum := by decide
  have hdescent : baseEnd_992991 < baseStart_992991 := by decide
  rcases family_descends (prefixWord ++ tailWord_992991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993004 : List Nat := [2, 2, 1, 1, 2, 2, 2, 5, 5]
def baseStart_993004 : Nat := 118140960795 + 993004 * 2 ^ 59
def prefixEnd_993004 : Nat := 4983230072969 + 3 ^ 40 * 993004 * 2
def baseEnd_993004 : Nat := 113308520852741800218503

theorem tailTrace_993004 : CollatzResearch.WordTrace tailWord_993004 prefixEnd_993004 113308520852741800218503 := by
  unfold tailWord_993004
  simp only [CollatzResearch.WordTrace]
  refine ⟨18108915647261787213217033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24145220863015716284289377 18108915647261787213217033)
  ·
    refine ⟨13581686735446340409912775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18108915647261787213217033 13581686735446340409912775)
    ·
      refine ⟨20372530103169510614869163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13581686735446340409912775 20372530103169510614869163)
      ·
        refine ⟨30558795154754265922303745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20372530103169510614869163 30558795154754265922303745)
        ·
          refine ⟨22919096366065699441727809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30558795154754265922303745 22919096366065699441727809)
          ·
            refine ⟨17189322274549274581295857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22919096366065699441727809 17189322274549274581295857)
            ·
              refine ⟨12891991705911955935971893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17189322274549274581295857 12891991705911955935971893)
              ·
                refine ⟨1208624222429245868997365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12891991705911955935971893 1208624222429245868997365)
                ·
                  refine ⟨113308520852741800218503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1208624222429245868997365 113308520852741800218503)
                  ·
                    rfl

theorem cell22_993004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_993004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993004 prefixEnd_993004 := by exact prefixLift 993004
  have htrace : WordTrace (prefixWord ++ tailWord_993004) baseStart_993004 baseEnd_993004 := by
    simpa [prefixWord, tailWord_993004, baseEnd_993004] using wordTrace_append hprefix tailTrace_993004
  have hstable : (prefixWord ++ tailWord_993004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993004).length < 2 ^ (prefixWord ++ tailWord_993004).sum := by decide
  have hdescent : baseEnd_993004 < baseStart_993004 := by decide
  rcases family_descends (prefixWord ++ tailWord_993004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993068 : List Nat := [2, 2, 1, 1, 1, 7, 1, 2, 1, 4]
def baseStart_993068 : Nat := 118140960795 + 993068 * 2 ^ 59
def prefixEnd_993068 : Nat := 4983230072969 + 3 ^ 40 * 993068 * 2
def baseEnd_993068 : Nat := 339947471066150567055313

theorem tailTrace_993068 : CollatzResearch.WordTrace tailWord_993068 prefixEnd_993068 339947471066150567055313 := by
  unfold tailWord_993068
  simp only [CollatzResearch.WordTrace]
  refine ⟨18110082783145856678381929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24146777044194475571175905 18110082783145856678381929)
  ·
    refine ⟨13582562087359392508786447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18110082783145856678381929 13582562087359392508786447)
    ·
      refine ⟨20373843131039088763179671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13582562087359392508786447 20373843131039088763179671)
      ·
        refine ⟨30560764696558633144769507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20373843131039088763179671 30560764696558633144769507)
        ·
          refine ⟨45841147044837949717154261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30560764696558633144769507 45841147044837949717154261)
          ·
            refine ⟨1074401883863389446495803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 45841147044837949717154261 1074401883863389446495803)
            ·
              refine ⟨1611602825795084169743705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074401883863389446495803 1611602825795084169743705)
              ·
                refine ⟨1208702119346313127307779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1611602825795084169743705 1208702119346313127307779)
                ·
                  refine ⟨1813053179019469690961669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1208702119346313127307779 1813053179019469690961669)
                  ·
                    refine ⟨339947471066150567055313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1813053179019469690961669 339947471066150567055313)
                    ·
                      rfl

theorem cell22_993068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_993068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993068 prefixEnd_993068 := by exact prefixLift 993068
  have htrace : WordTrace (prefixWord ++ tailWord_993068) baseStart_993068 baseEnd_993068 := by
    simpa [prefixWord, tailWord_993068, baseEnd_993068] using wordTrace_append hprefix tailTrace_993068
  have hstable : (prefixWord ++ tailWord_993068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993068).length < 2 ^ (prefixWord ++ tailWord_993068).sum := by decide
  have hdescent : baseEnd_993068 < baseStart_993068 := by decide
  rcases family_descends (prefixWord ++ tailWord_993068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993085 : List Nat := [1, 4, 1, 4, 1, 2, 3, 1, 1, 4]
def baseStart_993085 : Nat := 118140960795 + 993085 * 2 ^ 59
def prefixEnd_993085 : Nat := 4983230072969 + 3 ^ 40 * 993085 * 2
def baseEnd_993085 : Nat := 339953290513568189380261

theorem tailTrace_993085 : CollatzResearch.WordTrace tailWord_993085 prefixEnd_993085 339953290513568189380261 := by
  unfold tailWord_993085
  simp only [CollatzResearch.WordTrace]
  refine ⟨36220785607230125260132709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24147190404820083506755139 36220785607230125260132709)
  ·
    refine ⟨6791397301355648486274883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36220785607230125260132709 6791397301355648486274883)
    ·
      refine ⟨10187095952033472729412325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6791397301355648486274883 10187095952033472729412325)
      ·
        refine ⟨1910080491006276136764811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10187095952033472729412325 1910080491006276136764811)
        ·
          refine ⟨2865120736509414205147217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1910080491006276136764811 2865120736509414205147217)
          ·
            refine ⟨2148840552382060653860413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2865120736509414205147217 2148840552382060653860413)
            ·
              refine ⟨805815207143272745197655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2148840552382060653860413 805815207143272745197655)
              ·
                refine ⟨1208722810714909117796483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805815207143272745197655 1208722810714909117796483)
                ·
                  refine ⟨1813084216072363676694725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1208722810714909117796483 1813084216072363676694725)
                  ·
                    refine ⟨339953290513568189380261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1813084216072363676694725 339953290513568189380261)
                    ·
                      rfl

theorem cell22_993085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_993085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993085 prefixEnd_993085 := by exact prefixLift 993085
  have htrace : WordTrace (prefixWord ++ tailWord_993085) baseStart_993085 baseEnd_993085 := by
    simpa [prefixWord, tailWord_993085, baseEnd_993085] using wordTrace_append hprefix tailTrace_993085
  have hstable : (prefixWord ++ tailWord_993085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993085).length < 2 ^ (prefixWord ++ tailWord_993085).sum := by decide
  have hdescent : baseEnd_993085 < baseStart_993085 := by decide
  rcases family_descends (prefixWord ++ tailWord_993085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993096 : List Nat := [2, 1, 3, 1, 1, 4, 2, 2, 2, 4]
def baseStart_993096 : Nat := 118140960795 + 993096 * 2 ^ 59
def prefixEnd_993096 : Nat := 4983230072969 + 3 ^ 40 * 993096 * 2
def baseEnd_993096 : Nat := 339957056038367827355227

theorem tailTrace_993096 : CollatzResearch.WordTrace tailWord_993096 prefixEnd_993096 339957056038367827355227 := by
  unfold tailWord_993096
  simp only [CollatzResearch.WordTrace]
  refine ⟨18110593405095137069391571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24147457873460182759188761 18110593405095137069391571)
  ·
    refine ⟨27165890107642705604087357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18110593405095137069391571 27165890107642705604087357)
    ·
      refine ⟨10187208790366014601532759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27165890107642705604087357 10187208790366014601532759)
      ·
        refine ⟨15280813185549021902299139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10187208790366014601532759 15280813185549021902299139)
        ·
          refine ⟨22921219778323532853448709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15280813185549021902299139 22921219778323532853448709)
          ·
            refine ⟨4297728708435662410021633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22921219778323532853448709 4297728708435662410021633)
            ·
              refine ⟨3223296531326746807516225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4297728708435662410021633 3223296531326746807516225)
              ·
                refine ⟨2417472398495060105637169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3223296531326746807516225 2417472398495060105637169)
                ·
                  refine ⟨1813104298871295079227877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2417472398495060105637169 1813104298871295079227877)
                  ·
                    refine ⟨339957056038367827355227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1813104298871295079227877 339957056038367827355227)
                    ·
                      rfl

theorem cell22_993096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_993096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993096 prefixEnd_993096 := by exact prefixLift 993096
  have htrace : WordTrace (prefixWord ++ tailWord_993096) baseStart_993096 baseEnd_993096 := by
    simpa [prefixWord, tailWord_993096, baseEnd_993096] using wordTrace_append hprefix tailTrace_993096
  have hstable : (prefixWord ++ tailWord_993096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993096).length < 2 ^ (prefixWord ++ tailWord_993096).sum := by decide
  have hdescent : baseEnd_993096 < baseStart_993096 := by decide
  rcases family_descends (prefixWord ++ tailWord_993096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993098 : List Nat := [3, 1, 2, 1, 1, 1, 6, 2, 2, 3]
def baseStart_993098 : Nat := 118140960795 + 993098 * 2 ^ 59
def prefixEnd_993098 : Nat := 4983230072969 + 3 ^ 40 * 993098 * 2
def baseEnd_993098 : Nat := 339957740679240488805221

theorem tailTrace_993098 : CollatzResearch.WordTrace tailWord_993098 prefixEnd_993098 339957740679240488805221 := by
  unfold tailWord_993098
  simp only [CollatzResearch.WordTrace]
  refine ⟨9055314939045757120088987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24147506504122018986903965 9055314939045757120088987)
  ·
    refine ⟨13582972408568635680133481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9055314939045757120088987 13582972408568635680133481)
    ·
      refine ⟨10187229306426476760100111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13582972408568635680133481 10187229306426476760100111)
      ·
        refine ⟨15280843959639715140150167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10187229306426476760100111 15280843959639715140150167)
        ·
          refine ⟨22921265939459572710225251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15280843959639715140150167 22921265939459572710225251)
          ·
            refine ⟨34381898909189359065337877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22921265939459572710225251 34381898909189359065337877)
            ·
              refine ⟨1611651511368251206187713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34381898909189359065337877 1611651511368251206187713)
              ·
                refine ⟨1208738633526188404640785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1611651511368251206187713 1208738633526188404640785)
                ·
                  refine ⟨906553975144641303480589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1208738633526188404640785 906553975144641303480589)
                  ·
                    refine ⟨339957740679240488805221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 906553975144641303480589 339957740679240488805221)
                    ·
                      rfl

theorem cell22_993098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_993098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993098 prefixEnd_993098 := by exact prefixLift 993098
  have htrace : WordTrace (prefixWord ++ tailWord_993098) baseStart_993098 baseEnd_993098 := by
    simpa [prefixWord, tailWord_993098, baseEnd_993098] using wordTrace_append hprefix tailTrace_993098
  have hstable : (prefixWord ++ tailWord_993098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993098).length < 2 ^ (prefixWord ++ tailWord_993098).sum := by decide
  have hdescent : baseEnd_993098 < baseStart_993098 := by decide
  rcases family_descends (prefixWord ++ tailWord_993098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993139 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 7]
def baseStart_993139 : Nat := 118140960795 + 993139 * 2 ^ 59
def prefixEnd_993139 : Nat := 4983230072969 + 3 ^ 40 * 993139 * 2
def baseEnd_993139 : Nat := 113323925272376682843365

theorem tailTrace_993139 : CollatzResearch.WordTrace tailWord_993139 prefixEnd_993139 113323925272376682843365 := by
  unfold tailWord_993139
  simp only [CollatzResearch.WordTrace]
  refine ⟨36222755149034492482598471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24148503432689661655065647 36222755149034492482598471)
  ·
    refine ⟨54334132723551738723897707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36222755149034492482598471 54334132723551738723897707)
    ·
      refine ⟨81501199085327608085846561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54334132723551738723897707 81501199085327608085846561)
      ·
        refine ⟨61125899313995706064384921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81501199085327608085846561 61125899313995706064384921)
        ·
          refine ⟨45844424485496779548288691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61125899313995706064384921 45844424485496779548288691)
          ·
            refine ⟨68766636728245169322433037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45844424485496779548288691 68766636728245169322433037)
            ·
              refine ⟨25787488773091938495912389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68766636728245169322433037 25787488773091938495912389)
              ·
                refine ⟨4835154144954738467983573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25787488773091938495912389 4835154144954738467983573)
                ·
                  refine ⟨113323925272376682843365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4835154144954738467983573 113323925272376682843365)
                  ·
                    rfl

theorem cell22_993139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 7].length) (baseStart_993139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993139 prefixEnd_993139 := by exact prefixLift 993139
  have htrace : WordTrace (prefixWord ++ tailWord_993139) baseStart_993139 baseEnd_993139 := by
    simpa [prefixWord, tailWord_993139, baseEnd_993139] using wordTrace_append hprefix tailTrace_993139
  have hstable : (prefixWord ++ tailWord_993139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993139).length < 2 ^ (prefixWord ++ tailWord_993139).sum := by decide
  have hdescent : baseEnd_993139 < baseStart_993139 := by decide
  rcases family_descends (prefixWord ++ tailWord_993139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993160 : List Nat := [2, 1, 3, 3, 3, 1, 2, 1, 3, 3]
def baseStart_993160 : Nat := 118140960795 + 993160 * 2 ^ 59
def prefixEnd_993160 : Nat := 4983230072969 + 3 ^ 40 * 993160 * 2
def baseEnd_993160 : Nat := 339978964546292993755031

theorem tailTrace_993160 : CollatzResearch.WordTrace tailWord_993160 prefixEnd_993160 339978964546292993755031 := by
  unfold tailWord_993160
  simp only [CollatzResearch.WordTrace]
  refine ⟨18111760540979206534556467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24149014054638942046075289 18111760540979206534556467)
  ·
    refine ⟨27167640811468809801834701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18111760540979206534556467 27167640811468809801834701)
    ·
      refine ⟨10187865304300803675688013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27167640811468809801834701 10187865304300803675688013)
      ·
        refine ⟨3820449489112801378383005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10187865304300803675688013 3820449489112801378383005)
        ·
          refine ⟨1432668558417300516893627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3820449489112801378383005 1432668558417300516893627)
          ·
            refine ⟨2149002837625950775340441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432668558417300516893627 2149002837625950775340441)
            ·
              refine ⟨1611752128219463081505331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2149002837625950775340441 1611752128219463081505331)
              ·
                refine ⟨2417628192329194622257997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611752128219463081505331 2417628192329194622257997)
                ·
                  refine ⟨906610572123447983346749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2417628192329194622257997 906610572123447983346749)
                  ·
                    refine ⟨339978964546292993755031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 906610572123447983346749 339978964546292993755031)
                    ·
                      rfl

theorem cell22_993160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_993160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993160 prefixEnd_993160 := by exact prefixLift 993160
  have htrace : WordTrace (prefixWord ++ tailWord_993160) baseStart_993160 baseEnd_993160 := by
    simpa [prefixWord, tailWord_993160, baseEnd_993160] using wordTrace_append hprefix tailTrace_993160
  have hstable : (prefixWord ++ tailWord_993160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993160).length < 2 ^ (prefixWord ++ tailWord_993160).sum := by decide
  have hdescent : baseEnd_993160 < baseStart_993160 := by decide
  rcases family_descends (prefixWord ++ tailWord_993160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993173 : List Nat := [1, 3, 2, 1, 1, 3, 5, 1, 5]
def baseStart_993173 : Nat := 118140960795 + 993173 * 2 ^ 59
def prefixEnd_993173 : Nat := 4983230072969 + 3 ^ 40 * 993173 * 2
def baseEnd_993173 : Nat := 113327804903988431059997

theorem tailTrace_993173 : CollatzResearch.WordTrace tailWord_993173 prefixEnd_993173 113327804903988431059997 := by
  unfold tailWord_993173
  simp only [CollatzResearch.WordTrace]
  refine ⟨36223995230911316289336173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24149330153940877526224115 36223995230911316289336173)
  ·
    refine ⟨13583998211591743608501065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36223995230911316289336173 13583998211591743608501065)
    ·
      refine ⟨10187998658693807706375799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13583998211591743608501065 10187998658693807706375799)
      ·
        refine ⟨15281997988040711559563699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10187998658693807706375799 15281997988040711559563699)
        ·
          refine ⟨22922996982061067339345549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15281997988040711559563699 22922996982061067339345549)
          ·
            refine ⟨8596123868272900252254581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22922996982061067339345549 8596123868272900252254581)
            ·
              refine ⟨805886612650584398648867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8596123868272900252254581 805886612650584398648867)
              ·
                refine ⟨1208829918975876597973301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805886612650584398648867 1208829918975876597973301)
                ·
                  refine ⟨113327804903988431059997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1208829918975876597973301 113327804903988431059997)
                  ·
                    rfl

theorem cell22_993173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_993173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993173 prefixEnd_993173 := by exact prefixLift 993173
  have htrace : WordTrace (prefixWord ++ tailWord_993173) baseStart_993173 baseEnd_993173 := by
    simpa [prefixWord, tailWord_993173, baseEnd_993173] using wordTrace_append hprefix tailTrace_993173
  have hstable : (prefixWord ++ tailWord_993173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993173).length < 2 ^ (prefixWord ++ tailWord_993173).sum := by decide
  have hdescent : baseEnd_993173 < baseStart_993173 := by decide
  rcases family_descends (prefixWord ++ tailWord_993173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993231 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 4, 4]
def baseStart_993231 : Nat := 118140960795 + 993231 * 2 ^ 59
def prefixEnd_993231 : Nat := 4983230072969 + 3 ^ 40 * 993231 * 2
def baseEnd_993231 : Nat := 340003269297272475229813

theorem tailTrace_993231 : CollatzResearch.WordTrace tailWord_993231 prefixEnd_993231 340003269297272475229813 := by
  unfold tailWord_993231
  simp only [CollatzResearch.WordTrace]
  refine ⟨36226110664701192194947547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24150740443134128129965031 36226110664701192194947547)
  ·
    refine ⟨54339165997051788292421321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36226110664701192194947547 54339165997051788292421321)
    ·
      refine ⟨40754374497788841219315991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54339165997051788292421321 40754374497788841219315991)
      ·
        refine ⟨61131561746683261828973987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40754374497788841219315991 61131561746683261828973987)
        ·
          refine ⟨91697342620024892743460981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61131561746683261828973987 91697342620024892743460981)
          ·
            refine ⟨8596625870627333694699467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91697342620024892743460981 8596625870627333694699467)
            ·
              refine ⟨12894938805941000542049201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8596625870627333694699467 12894938805941000542049201)
              ·
                refine ⟨9671204104455750406536901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12894938805941000542049201 9671204104455750406536901)
                ·
                  refine ⟨1813350769585453201225669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9671204104455750406536901 1813350769585453201225669)
                  ·
                    refine ⟨340003269297272475229813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1813350769585453201225669 340003269297272475229813)
                    ·
                      rfl

theorem cell22_993231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_993231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993231 prefixEnd_993231 := by exact prefixLift 993231
  have htrace : WordTrace (prefixWord ++ tailWord_993231) baseStart_993231 baseEnd_993231 := by
    simpa [prefixWord, tailWord_993231, baseEnd_993231] using wordTrace_append hprefix tailTrace_993231
  have hstable : (prefixWord ++ tailWord_993231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993231).length < 2 ^ (prefixWord ++ tailWord_993231).sum := by decide
  have hdescent : baseEnd_993231 < baseStart_993231 := by decide
  rcases family_descends (prefixWord ++ tailWord_993231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993276 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 1, 8]
def baseStart_993276 : Nat := 118140960795 + 993276 * 2 ^ 59
def prefixEnd_993276 : Nat := 4983230072969 + 3 ^ 40 * 993276 * 2
def baseEnd_993276 : Nat := 340018673716907357854675

theorem tailTrace_993276 : CollatzResearch.WordTrace tailWord_993276 prefixEnd_993276 340018673716907357854675 := by
  unfold tailWord_993276
  simp only [CollatzResearch.WordTrace]
  refine ⟨18113875974769082440167841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24151834633025443253557121 18113875974769082440167841)
  ·
    refine ⟨13585406981076811830125881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18113875974769082440167841 13585406981076811830125881)
    ·
      refine ⟨10189055235807608872594411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13585406981076811830125881 10189055235807608872594411)
      ·
        refine ⟨15283582853711413308891617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10189055235807608872594411 15283582853711413308891617)
        ·
          refine ⟨11462687140283559981668713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15283582853711413308891617 11462687140283559981668713)
          ·
            refine ⟨8597015355212669986251535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11462687140283559981668713 8597015355212669986251535)
            ·
              refine ⟨12895523032819004979377303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8597015355212669986251535 12895523032819004979377303)
              ·
                refine ⟨19343284549228507469065955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12895523032819004979377303 19343284549228507469065955)
                ·
                  refine ⟨29014926823842761203598933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19343284549228507469065955 29014926823842761203598933)
                  ·
                    refine ⟨340018673716907357854675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29014926823842761203598933 340018673716907357854675)
                    ·
                      rfl

theorem cell22_993276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_993276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993276 prefixEnd_993276 := by exact prefixLift 993276
  have htrace : WordTrace (prefixWord ++ tailWord_993276) baseStart_993276 baseEnd_993276 := by
    simpa [prefixWord, tailWord_993276, baseEnd_993276] using wordTrace_append hprefix tailTrace_993276
  have hstable : (prefixWord ++ tailWord_993276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993276).length < 2 ^ (prefixWord ++ tailWord_993276).sum := by decide
  have hdescent : baseEnd_993276 < baseStart_993276 := by decide
  rcases family_descends (prefixWord ++ tailWord_993276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993385 : List Nat := [1, 2, 1, 1, 1, 5, 2, 4, 2, 3]
def baseStart_993385 : Nat := 118140960795 + 993385 * 2 ^ 59
def prefixEnd_993385 : Nat := 4983230072969 + 3 ^ 40 * 993385 * 2
def baseEnd_993385 : Nat := 340055986644467406879341

theorem tailTrace_993385 : CollatzResearch.WordTrace tailWord_993385 prefixEnd_993385 340055986644467406879341 := by
  unfold tailWord_993385
  simp only [CollatzResearch.WordTrace]
  refine ⟨36231727506143276496053609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24154485004095517664035739 36231727506143276496053609)
  ·
    refine ⟨27173795629607457372040207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36231727506143276496053609 27173795629607457372040207)
    ·
      refine ⟨40760693444411186058060311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27173795629607457372040207 40760693444411186058060311)
      ·
        refine ⟨61141040166616779087090467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40760693444411186058060311 61141040166616779087090467)
        ·
          refine ⟨91711560249925168630635701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61141040166616779087090467 91711560249925168630635701)
          ·
            refine ⟨8597958773430484559122097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91711560249925168630635701 8597958773430484559122097)
            ·
              refine ⟨6448469080072863419341573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8597958773430484559122097 6448469080072863419341573)
              ·
                refine ⟨1209087952513661891126545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6448469080072863419341573 1209087952513661891126545)
                ·
                  refine ⟨906815964385246418344909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1209087952513661891126545 906815964385246418344909)
                  ·
                    refine ⟨340055986644467406879341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 906815964385246418344909 340055986644467406879341)
                    ·
                      rfl

theorem cell22_993385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 3].length) (baseStart_993385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993385 prefixEnd_993385 := by exact prefixLift 993385
  have htrace : WordTrace (prefixWord ++ tailWord_993385) baseStart_993385 baseEnd_993385 := by
    simpa [prefixWord, tailWord_993385, baseEnd_993385] using wordTrace_append hprefix tailTrace_993385
  have hstable : (prefixWord ++ tailWord_993385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993385).length < 2 ^ (prefixWord ++ tailWord_993385).sum := by decide
  have hdescent : baseEnd_993385 < baseStart_993385 := by decide
  rcases family_descends (prefixWord ++ tailWord_993385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993438 : List Nat := [4, 3, 1, 1, 4, 1, 2, 2, 4]
def baseStart_993438 : Nat := 118140960795 + 993438 * 2 ^ 59
def prefixEnd_993438 : Nat := 4983230072969 + 3 ^ 40 * 993438 * 2
def baseEnd_993438 : Nat := 113358043209197645101393

theorem tailTrace_993438 : CollatzResearch.WordTrace tailWord_993438 prefixEnd_993438 113358043209197645101393 := by
  unfold tailWord_993438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4529207571868908318466621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24155773716634177698488645 4529207571868908318466621)
  ·
    refine ⟨1698452839450840619424983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4529207571868908318466621 1698452839450840619424983)
    ·
      refine ⟨2547679259176260929137475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1698452839450840619424983 2547679259176260929137475)
      ·
        refine ⟨3821518888764391393706213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2547679259176260929137475 3821518888764391393706213)
        ·
          refine ⟨716534791643323386319915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3821518888764391393706213 716534791643323386319915)
          ·
            refine ⟨1074802187464985079479873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716534791643323386319915 1074802187464985079479873)
            ·
              refine ⟨806101640598738809609905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1074802187464985079479873 806101640598738809609905)
              ·
                refine ⟨604576230449054107207429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 806101640598738809609905 604576230449054107207429)
                ·
                  refine ⟨113358043209197645101393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 604576230449054107207429 113358043209197645101393)
                  ·
                    rfl

theorem cell22_993438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_993438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993438 prefixEnd_993438 := by exact prefixLift 993438
  have htrace : WordTrace (prefixWord ++ tailWord_993438) baseStart_993438 baseEnd_993438 := by
    simpa [prefixWord, tailWord_993438, baseEnd_993438] using wordTrace_append hprefix tailTrace_993438
  have hstable : (prefixWord ++ tailWord_993438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993438).length < 2 ^ (prefixWord ++ tailWord_993438).sum := by decide
  have hdescent : baseEnd_993438 < baseStart_993438 := by decide
  rcases family_descends (prefixWord ++ tailWord_993438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993494 : List Nat := [5, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_993494 : Nat := 118140960795 + 993494 * 2 ^ 59
def prefixEnd_993494 : Nat := 4983230072969 + 3 ^ 40 * 993494 * 2
def baseEnd_993494 : Nat := 113364433190675818634669

theorem tailTrace_993494 : CollatzResearch.WordTrace tailWord_993494 prefixEnd_993494 113364433190675818634669 := by
  unfold tailWord_993494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2264731441421774256985721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24157135375165592074514357 2264731441421774256985721)
  ·
    refine ⟨1698548581066330692739291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2264731441421774256985721 1698548581066330692739291)
    ·
      refine ⟨2547822871599496039108937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1698548581066330692739291 2547822871599496039108937)
      ·
        refine ⟨1910867153699622029331703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2547822871599496039108937 1910867153699622029331703)
        ·
          refine ⟨2866300730549433043997555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1910867153699622029331703 2866300730549433043997555)
          ·
            refine ⟨4299451095824149565996333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2866300730549433043997555 4299451095824149565996333)
            ·
              refine ⟨1612294160934056087248625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4299451095824149565996333 1612294160934056087248625)
              ·
                refine ⟨1209220620700542065436469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1612294160934056087248625 1209220620700542065436469)
                ·
                  refine ⟨113364433190675818634669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1209220620700542065436469 113364433190675818634669)
                  ·
                    rfl

theorem cell22_993494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_993494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993494 prefixEnd_993494 := by exact prefixLift 993494
  have htrace : WordTrace (prefixWord ++ tailWord_993494) baseStart_993494 baseEnd_993494 := by
    simpa [prefixWord, tailWord_993494, baseEnd_993494] using wordTrace_append hprefix tailTrace_993494
  have hstable : (prefixWord ++ tailWord_993494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993494).length < 2 ^ (prefixWord ++ tailWord_993494).sum := by decide
  have hdescent : baseEnd_993494 < baseStart_993494 := by decide
  rcases family_descends (prefixWord ++ tailWord_993494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993505 : List Nat := [1, 2, 3, 1, 3, 1, 4, 1, 6]
def baseStart_993505 : Nat := 118140960795 + 993505 * 2 ^ 59
def prefixEnd_993505 : Nat := 4983230072969 + 3 ^ 40 * 993505 * 2
def baseEnd_993505 : Nat := 113365688365609031292991

theorem tailTrace_993505 : CollatzResearch.WordTrace tailWord_993505 prefixEnd_993505 113365688365609031292991 := by
  unfold tailWord_993505
  simp only [CollatzResearch.WordTrace]
  refine ⟨36236104265708536990421969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24157402843805691326947979 36236104265708536990421969)
  ·
    refine ⟨27177078199281402742816477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36236104265708536990421969 27177078199281402742816477)
    ·
      refine ⟨10191404324730526028556179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27177078199281402742816477 10191404324730526028556179)
      ·
        refine ⟨15287106487095789042834269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10191404324730526028556179 15287106487095789042834269)
        ·
          refine ⟨5732664932660920891062851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15287106487095789042834269 5732664932660920891062851)
          ·
            refine ⟨8598997398991381336594277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5732664932660920891062851 8598997398991381336594277)
            ·
              refine ⟨1612312012310884000611427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8598997398991381336594277 1612312012310884000611427)
              ·
                refine ⟨2418468018466326000917141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1612312012310884000611427 2418468018466326000917141)
                ·
                  refine ⟨113365688365609031292991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2418468018466326000917141 113365688365609031292991)
                  ·
                    rfl

theorem cell22_993505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 6].length) (baseStart_993505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993505 prefixEnd_993505 := by exact prefixLift 993505
  have htrace : WordTrace (prefixWord ++ tailWord_993505) baseStart_993505 baseEnd_993505 := by
    simpa [prefixWord, tailWord_993505, baseEnd_993505] using wordTrace_append hprefix tailTrace_993505
  have hstable : (prefixWord ++ tailWord_993505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993505).length < 2 ^ (prefixWord ++ tailWord_993505).sum := by decide
  have hdescent : baseEnd_993505 < baseStart_993505 := by decide
  rcases family_descends (prefixWord ++ tailWord_993505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993535 : List Nat := [1, 1, 2, 2, 1, 4, 2, 3, 2, 4]
def baseStart_993535 : Nat := 118140960795 + 993535 * 2 ^ 59
def prefixEnd_993535 : Nat := 4983230072969 + 3 ^ 40 * 993535 * 2
def baseEnd_993535 : Nat := 340107334709917015628881

theorem tailTrace_993535 : CollatzResearch.WordTrace tailWord_993535 prefixEnd_993535 340107334709917015628881 := by
  unfold tailWord_993535
  simp only [CollatzResearch.WordTrace]
  refine ⟨36237198455599852114014059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24158132303733234742676039 36237198455599852114014059)
  ·
    refine ⟨54355797683399778171021089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36237198455599852114014059 54355797683399778171021089)
    ·
      refine ⟨40766848262549833628265817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54355797683399778171021089 40766848262549833628265817)
      ·
        refine ⟨30575136196912375221199363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40766848262549833628265817 30575136196912375221199363)
        ·
          refine ⟨45862704295368562831799045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30575136196912375221199363 45862704295368562831799045)
          ·
            refine ⟨8599257055381605530962321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45862704295368562831799045 8599257055381605530962321)
            ·
              refine ⟨6449442791536204148221741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8599257055381605530962321 6449442791536204148221741)
              ·
                refine ⟨2418541046826076555583153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6449442791536204148221741 2418541046826076555583153)
                ·
                  refine ⟨1813905785119557416687365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2418541046826076555583153 1813905785119557416687365)
                  ·
                    refine ⟨340107334709917015628881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1813905785119557416687365 340107334709917015628881)
                    ·
                      rfl

theorem cell22_993535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_993535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993535 prefixEnd_993535 := by exact prefixLift 993535
  have htrace : WordTrace (prefixWord ++ tailWord_993535) baseStart_993535 baseEnd_993535 := by
    simpa [prefixWord, tailWord_993535, baseEnd_993535] using wordTrace_append hprefix tailTrace_993535
  have hstable : (prefixWord ++ tailWord_993535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993535).length < 2 ^ (prefixWord ++ tailWord_993535).sum := by decide
  have hdescent : baseEnd_993535 < baseStart_993535 := by decide
  rcases family_descends (prefixWord ++ tailWord_993535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993575 : List Nat := [1, 1, 8, 1, 2, 1, 1, 2, 1, 4]
def baseStart_993575 : Nat := 118140960795 + 993575 * 2 ^ 59
def prefixEnd_993575 : Nat := 4983230072969 + 3 ^ 40 * 993575 * 2
def baseEnd_993575 : Nat := 340121027527370244628759

theorem tailTrace_993575 : CollatzResearch.WordTrace tailWord_993575 prefixEnd_993575 340121027527370244628759 := by
  unfold tailWord_993575
  simp only [CollatzResearch.WordTrace]
  refine ⟨36238657375454938945470179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24159104916969959296980119 36238657375454938945470179)
  ·
    refine ⟨54357986063182408418205269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36238657375454938945470179 54357986063182408418205269)
    ·
      refine ⟨637007649177918848650843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 54357986063182408418205269 637007649177918848650843)
      ·
        refine ⟨955511473766878272976265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637007649177918848650843 955511473766878272976265)
        ·
          refine ⟨716633605325158704732199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 955511473766878272976265 716633605325158704732199)
          ·
            refine ⟨1074950407987738057098299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716633605325158704732199 1074950407987738057098299)
            ·
              refine ⟨1612425611981607085647449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074950407987738057098299 1612425611981607085647449)
              ·
                refine ⟨1209319208986205314235587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1612425611981607085647449 1209319208986205314235587)
                ·
                  refine ⟨1813978813479307971353381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1209319208986205314235587 1813978813479307971353381)
                  ·
                    refine ⟨340121027527370244628759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1813978813479307971353381 340121027527370244628759)
                    ·
                      rfl

theorem cell22_993575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_993575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993575 prefixEnd_993575 := by exact prefixLift 993575
  have htrace : WordTrace (prefixWord ++ tailWord_993575) baseStart_993575 baseEnd_993575 := by
    simpa [prefixWord, tailWord_993575, baseEnd_993575] using wordTrace_append hprefix tailTrace_993575
  have hstable : (prefixWord ++ tailWord_993575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993575).length < 2 ^ (prefixWord ++ tailWord_993575).sum := by decide
  have hdescent : baseEnd_993575 < baseStart_993575 := by decide
  rcases family_descends (prefixWord ++ tailWord_993575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993599 : List Nat := [1, 1, 2, 2, 4, 1, 2, 5, 1, 3]
def baseStart_993599 : Nat := 118140960795 + 993599 * 2 ^ 59
def prefixEnd_993599 : Nat := 4983230072969 + 3 ^ 40 * 993599 * 2
def baseEnd_993599 : Nat := 340129243217842182028685

theorem tailTrace_993599 : CollatzResearch.WordTrace tailWord_993599 prefixEnd_993599 340129243217842182028685 := by
  unfold tailWord_993599
  simp only [CollatzResearch.WordTrace]
  refine ⟨36239532727367991044343851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24159688484911994029562567 36239532727367991044343851)
  ·
    refine ⟨54359299091051986566515777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36239532727367991044343851 54359299091051986566515777)
    ·
      refine ⟨40769474318288989924886833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54359299091051986566515777 40769474318288989924886833)
      ·
        refine ⟨30577105738716742443665125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40769474318288989924886833 30577105738716742443665125)
        ·
          refine ⟨5733207326009389208187211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30577105738716742443665125 5733207326009389208187211)
          ·
            refine ⟨8599810989014083812280817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5733207326009389208187211 8599810989014083812280817)
            ·
              refine ⟨6449858241760562859210613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8599810989014083812280817 6449858241760562859210613)
              ·
                refine ⟨604674210165052768050995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6449858241760562859210613 604674210165052768050995)
                ·
                  refine ⟨907011315247579152076493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 604674210165052768050995 907011315247579152076493)
                  ·
                    refine ⟨340129243217842182028685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 907011315247579152076493 340129243217842182028685)
                    ·
                      rfl

theorem cell22_993599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 1, 3].length) (baseStart_993599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993599 prefixEnd_993599 := by exact prefixLift 993599
  have htrace : WordTrace (prefixWord ++ tailWord_993599) baseStart_993599 baseEnd_993599 := by
    simpa [prefixWord, tailWord_993599, baseEnd_993599] using wordTrace_append hprefix tailTrace_993599
  have hstable : (prefixWord ++ tailWord_993599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993599).length < 2 ^ (prefixWord ++ tailWord_993599).sum := by decide
  have hdescent : baseEnd_993599 < baseStart_993599 := by decide
  rcases family_descends (prefixWord ++ tailWord_993599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993612 : List Nat := [2, 2, 1, 3, 2, 1, 4, 2, 5]
def baseStart_993612 : Nat := 118140960795 + 993612 * 2 ^ 59
def prefixEnd_993612 : Nat := 4983230072969 + 3 ^ 40 * 993612 * 2
def baseEnd_993612 : Nat := 113377897794504827151215

theorem tailTrace_993612 : CollatzResearch.WordTrace tailWord_993612 prefixEnd_993612 113377897794504827151215 := by
  unfold tailWord_993612
  simp only [CollatzResearch.WordTrace]
  refine ⟨18120003438160447132283545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24160004584213929509711393 18120003438160447132283545)
  ·
    refine ⟨13590002578620335349212659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18120003438160447132283545 13590002578620335349212659)
    ·
      refine ⟨20385003867930503023818989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13590002578620335349212659 20385003867930503023818989)
      ·
        refine ⟨7644376450473938633932121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20385003867930503023818989 7644376450473938633932121)
        ·
          refine ⟨5733282337855453975449091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7644376450473938633932121 5733282337855453975449091)
          ·
            refine ⟨8599923506783180963173637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5733282337855453975449091 8599923506783180963173637)
            ·
              refine ⟨1612485657521846430595057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8599923506783180963173637 1612485657521846430595057)
              ·
                refine ⟨1209364243141384822946293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1612485657521846430595057 1209364243141384822946293)
                ·
                  refine ⟨113377897794504827151215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1209364243141384822946293 113377897794504827151215)
                  ·
                    rfl

theorem cell22_993612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_993612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993612 prefixEnd_993612 := by exact prefixLift 993612
  have htrace : WordTrace (prefixWord ++ tailWord_993612) baseStart_993612 baseEnd_993612 := by
    simpa [prefixWord, tailWord_993612, baseEnd_993612] using wordTrace_append hprefix tailTrace_993612
  have hstable : (prefixWord ++ tailWord_993612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993612).length < 2 ^ (prefixWord ++ tailWord_993612).sum := by decide
  have hdescent : baseEnd_993612 < baseStart_993612 := by decide
  rcases family_descends (prefixWord ++ tailWord_993612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993616 : List Nat := [2, 1, 1, 1, 1, 6, 4, 2, 1, 3]
def baseStart_993616 : Nat := 118140960795 + 993616 * 2 ^ 59
def prefixEnd_993616 : Nat := 4983230072969 + 3 ^ 40 * 993616 * 2
def baseEnd_993616 : Nat := 340135062665259804353633

theorem tailTrace_993616 : CollatzResearch.WordTrace tailWord_993616 prefixEnd_993616 340135062665259804353633 := by
  unfold tailWord_993616
  simp only [CollatzResearch.WordTrace]
  refine ⟨18120076384153201473856351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24160101845537601965141801 18120076384153201473856351)
  ·
    refine ⟨27180114576229802210784527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18120076384153201473856351 27180114576229802210784527)
    ·
      refine ⟨40770171864344703316176791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27180114576229802210784527 40770171864344703316176791)
      ·
        refine ⟨61155257796517054974265187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40770171864344703316176791 61155257796517054974265187)
        ·
          refine ⟨91732886694775582461397781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61155257796517054974265187 91732886694775582461397781)
          ·
            refine ⟨4299979063817605427878021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91732886694775582461397781 4299979063817605427878021)
            ·
              refine ⟨806246074465801017727129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4299979063817605427878021 806246074465801017727129)
              ·
                refine ⟨604684555849350763295347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 806246074465801017727129 604684555849350763295347)
                ·
                  refine ⟨907026833774026144943021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 604684555849350763295347 907026833774026144943021)
                  ·
                    refine ⟨340135062665259804353633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 907026833774026144943021 340135062665259804353633)
                    ·
                      rfl

theorem cell22_993616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 1, 3].length) (baseStart_993616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993616 prefixEnd_993616 := by exact prefixLift 993616
  have htrace : WordTrace (prefixWord ++ tailWord_993616) baseStart_993616 baseEnd_993616 := by
    simpa [prefixWord, tailWord_993616, baseEnd_993616] using wordTrace_append hprefix tailTrace_993616
  have hstable : (prefixWord ++ tailWord_993616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993616).length < 2 ^ (prefixWord ++ tailWord_993616).sum := by decide
  have hdescent : baseEnd_993616 < baseStart_993616 := by decide
  rcases family_descends (prefixWord ++ tailWord_993616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993655 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 3, 5]
def baseStart_993655 : Nat := 118140960795 + 993655 * 2 ^ 59
def prefixEnd_993655 : Nat := 4983230072969 + 3 ^ 40 * 993655 * 2
def baseEnd_993655 : Nat := 340148413162276702628513

theorem tailTrace_993655 : CollatzResearch.WordTrace tailWord_993655 prefixEnd_993655 340148413162276702628513 := by
  unfold tailWord_993655
  simp only [CollatzResearch.WordTrace]
  refine ⟨36241575215165112608382419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24161050143443408405588279 36241575215165112608382419)
  ·
    refine ⟨54362362822747668912573629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36241575215165112608382419 54362362822747668912573629)
    ·
      refine ⟨20385886058530375842215111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54362362822747668912573629 20385886058530375842215111)
      ·
        refine ⟨30578829087795563763322667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20385886058530375842215111 30578829087795563763322667)
        ·
          refine ⟨45868243631693345644984001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30578829087795563763322667 45868243631693345644984001)
          ·
            refine ⟨34401182723770009233738001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45868243631693345644984001 34401182723770009233738001)
            ·
              refine ⟨25800887042827506925303501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34401182723770009233738001 25800887042827506925303501)
              ·
                refine ⟨9675332641060315096988813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25800887042827506925303501 9675332641060315096988813)
                ·
                  refine ⟨3628249740397618161370805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9675332641060315096988813 3628249740397618161370805)
                  ·
                    refine ⟨340148413162276702628513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3628249740397618161370805 340148413162276702628513)
                    ·
                      rfl

theorem cell22_993655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_993655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993655 prefixEnd_993655 := by exact prefixLift 993655
  have htrace : WordTrace (prefixWord ++ tailWord_993655) baseStart_993655 baseEnd_993655 := by
    simpa [prefixWord, tailWord_993655, baseEnd_993655] using wordTrace_append hprefix tailTrace_993655
  have hstable : (prefixWord ++ tailWord_993655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993655).length < 2 ^ (prefixWord ++ tailWord_993655).sum := by decide
  have hdescent : baseEnd_993655 < baseStart_993655 := by decide
  rcases family_descends (prefixWord ++ tailWord_993655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993659 : List Nat := [1, 1, 1, 1, 1, 7, 4, 1, 1, 4]
def baseStart_993659 : Nat := 118140960795 + 993659 * 2 ^ 59
def prefixEnd_993659 : Nat := 4983230072969 + 3 ^ 40 * 993659 * 2
def baseEnd_993659 : Nat := 340149782444022025528501

theorem tailTrace_993659 : CollatzResearch.WordTrace tailWord_993659 prefixEnd_993659 340149782444022025528501 := by
  unfold tailWord_993659
  simp only [CollatzResearch.WordTrace]
  refine ⟨36241721107150621291528031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24161147404767080861018687 36241721107150621291528031)
  ·
    refine ⟨54362581660725931937292047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36241721107150621291528031 54362581660725931937292047)
    ·
      refine ⟨81543872491088897905938071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54362581660725931937292047 81543872491088897905938071)
      ·
        refine ⟨122315808736633346858907107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81543872491088897905938071 122315808736633346858907107)
        ·
          refine ⟨183473713104950020288360661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122315808736633346858907107 183473713104950020288360661)
          ·
            refine ⟨4300165150897266100508453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 183473713104950020288360661 4300165150897266100508453)
            ·
              refine ⟨806280965793237393845335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4300165150897266100508453 806280965793237393845335)
              ·
                refine ⟨1209421448689856090768003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806280965793237393845335 1209421448689856090768003)
                ·
                  refine ⟨1814132173034784136152005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1209421448689856090768003 1814132173034784136152005)
                  ·
                    refine ⟨340149782444022025528501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1814132173034784136152005 340149782444022025528501)
                    ·
                      rfl

theorem cell22_993659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 1, 4].length) (baseStart_993659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993659 prefixEnd_993659 := by exact prefixLift 993659
  have htrace : WordTrace (prefixWord ++ tailWord_993659) baseStart_993659 baseEnd_993659 := by
    simpa [prefixWord, tailWord_993659, baseEnd_993659] using wordTrace_append hprefix tailTrace_993659
  have hstable : (prefixWord ++ tailWord_993659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993659).length < 2 ^ (prefixWord ++ tailWord_993659).sum := by decide
  have hdescent : baseEnd_993659 < baseStart_993659 := by decide
  rcases family_descends (prefixWord ++ tailWord_993659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993685 : List Nat := [1, 3, 2, 1, 1, 2, 1, 11]
def baseStart_993685 : Nat := 118140960795 + 993685 * 2 ^ 59
def prefixEnd_993685 : Nat := 4983230072969 + 3 ^ 40 * 993685 * 2
def baseEnd_993685 : Nat := 37795409197262958264269

theorem tailTrace_993685 : CollatzResearch.WordTrace tailWord_993685 prefixEnd_993685 37795409197262958264269 := by
  unfold tailWord_993685
  simp only [CollatzResearch.WordTrace]
  refine ⟨36242669405056427731974509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24161779603370951821316339 36242669405056427731974509)
  ·
    refine ⟨13591001026896160399490441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36242669405056427731974509 13591001026896160399490441)
    ·
      refine ⟨10193250770172120299617831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13591001026896160399490441 10193250770172120299617831)
      ·
        refine ⟨15289876155258180449426747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10193250770172120299617831 15289876155258180449426747)
        ·
          refine ⟨22934814232887270674140121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15289876155258180449426747 22934814232887270674140121)
          ·
            refine ⟨17201110674665453005605091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22934814232887270674140121 17201110674665453005605091)
            ·
              refine ⟨25801666011998179508407637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17201110674665453005605091 25801666011998179508407637)
              ·
                refine ⟨37795409197262958264269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 25801666011998179508407637 37795409197262958264269)
                ·
                  rfl

theorem cell22_993685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 11].length) (baseStart_993685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993685 prefixEnd_993685 := by exact prefixLift 993685
  have htrace : WordTrace (prefixWord ++ tailWord_993685) baseStart_993685 baseEnd_993685 := by
    simpa [prefixWord, tailWord_993685, baseEnd_993685] using wordTrace_append hprefix tailTrace_993685
  have hstable : (prefixWord ++ tailWord_993685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993685).length < 2 ^ (prefixWord ++ tailWord_993685).sum := by decide
  have hdescent : baseEnd_993685 < baseStart_993685 := by decide
  rcases family_descends (prefixWord ++ tailWord_993685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993704 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 1, 6]
def baseStart_993704 : Nat := 118140960795 + 993704 * 2 ^ 59
def prefixEnd_993704 : Nat := 4983230072969 + 3 ^ 40 * 993704 * 2
def baseEnd_993704 : Nat := 340165186863656908153363

theorem tailTrace_993704 : CollatzResearch.WordTrace tailWord_993704 prefixEnd_993704 340165186863656908153363 := by
  unfold tailWord_993704
  simp only [CollatzResearch.WordTrace]
  refine ⟨18121681195993796988458083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24162241594658395984610777 18121681195993796988458083)
  ·
    refine ⟨27182521793990695482687125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18121681195993796988458083 27182521793990695482687125)
    ·
      refine ⟨1274180709093313850750959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27182521793990695482687125 1274180709093313850750959)
      ·
        refine ⟨1911271063639970776126439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1274180709093313850750959 1911271063639970776126439)
        ·
          refine ⟨2866906595459956164189659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1911271063639970776126439 2866906595459956164189659)
          ·
            refine ⟨4300359893189934246284489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2866906595459956164189659 4300359893189934246284489)
            ·
              refine ⟨3225269919892450684713367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4300359893189934246284489 3225269919892450684713367)
              ·
                refine ⟨4837904879838676027070051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3225269919892450684713367 4837904879838676027070051)
                ·
                  refine ⟨7256857319758014040605077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4837904879838676027070051 7256857319758014040605077)
                  ·
                    refine ⟨340165186863656908153363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7256857319758014040605077 340165186863656908153363)
                    ·
                      rfl

theorem cell22_993704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_993704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993704 prefixEnd_993704 := by exact prefixLift 993704
  have htrace : WordTrace (prefixWord ++ tailWord_993704) baseStart_993704 baseEnd_993704 := by
    simpa [prefixWord, tailWord_993704, baseEnd_993704] using wordTrace_append hprefix tailTrace_993704
  have hstable : (prefixWord ++ tailWord_993704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993704).length < 2 ^ (prefixWord ++ tailWord_993704).sum := by decide
  have hdescent : baseEnd_993704 < baseStart_993704 := by decide
  rcases family_descends (prefixWord ++ tailWord_993704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993715 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 3, 8]
def baseStart_993715 : Nat := 118140960795 + 993715 * 2 ^ 59
def prefixEnd_993715 : Nat := 4983230072969 + 3 ^ 40 * 993715 * 2
def baseEnd_993715 : Nat := 340168952388456546128329

theorem tailTrace_993715 : CollatzResearch.WordTrace tailWord_993715 prefixEnd_993715 340168952388456546128329 := by
  unfold tailWord_993715
  simp only [CollatzResearch.WordTrace]
  refine ⟨36243763594947742855566599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24162509063298495237044399 36243763594947742855566599)
  ·
    refine ⟨54365645392421614283349899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36243763594947742855566599 54365645392421614283349899)
    ·
      refine ⟨81548468088632421425024849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54365645392421614283349899 81548468088632421425024849)
      ·
        refine ⟨61161351066474316068768637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81548468088632421425024849 61161351066474316068768637)
        ·
          refine ⟨22935506649927868525788239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61161351066474316068768637 22935506649927868525788239)
          ·
            refine ⟨34403259974891802788682359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22935506649927868525788239 34403259974891802788682359)
            ·
              refine ⟨51604889962337704183023539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34403259974891802788682359 51604889962337704183023539)
              ·
                refine ⟨77407334943506556274535309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51604889962337704183023539 77407334943506556274535309)
                ·
                  refine ⟨29027750603814958602950741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77407334943506556274535309 29027750603814958602950741)
                  ·
                    refine ⟨340168952388456546128329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29027750603814958602950741 340168952388456546128329)
                    ·
                      rfl

theorem cell22_993715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 8].length) (baseStart_993715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993715 prefixEnd_993715 := by exact prefixLift 993715
  have htrace : WordTrace (prefixWord ++ tailWord_993715) baseStart_993715 baseEnd_993715 := by
    simpa [prefixWord, tailWord_993715, baseEnd_993715] using wordTrace_append hprefix tailTrace_993715
  have hstable : (prefixWord ++ tailWord_993715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993715).length < 2 ^ (prefixWord ++ tailWord_993715).sum := by decide
  have hdescent : baseEnd_993715 < baseStart_993715 := by decide
  rcases family_descends (prefixWord ++ tailWord_993715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993740 : List Nat := [2, 2, 1, 4, 4, 1, 2, 1, 2, 3]
def baseStart_993740 : Nat := 118140960795 + 993740 * 2 ^ 59
def prefixEnd_993740 : Nat := 4983230072969 + 3 ^ 40 * 993740 * 2
def baseEnd_993740 : Nat := 340177510399364814253253

theorem tailTrace_993740 : CollatzResearch.WordTrace tailWord_993740 prefixEnd_993740 340177510399364814253253 := by
  unfold tailWord_993740
  simp only [CollatzResearch.WordTrace]
  refine ⟨18122337709928586062613337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24163116946571448083484449 18122337709928586062613337)
  ·
    refine ⟨13591753282446439546960003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18122337709928586062613337 13591753282446439546960003)
    ·
      refine ⟨20387629923669659320440005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13591753282446439546960003 20387629923669659320440005)
      ·
        refine ⟨3822680610688061122582501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20387629923669659320440005 3822680610688061122582501)
        ·
          refine ⟨716752614504011460484219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3822680610688061122582501 716752614504011460484219)
          ·
            refine ⟨1075128921756017190726329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716752614504011460484219 1075128921756017190726329)
            ·
              refine ⟨806346691317012893044747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1075128921756017190726329 806346691317012893044747)
              ·
                refine ⟨1209520036975519339567121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806346691317012893044747 1209520036975519339567121)
                ·
                  refine ⟨907140027731639504675341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1209520036975519339567121 907140027731639504675341)
                  ·
                    refine ⟨340177510399364814253253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 907140027731639504675341 340177510399364814253253)
                    ·
                      rfl

theorem cell22_993740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 2, 3].length) (baseStart_993740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993740 prefixEnd_993740 := by exact prefixLift 993740
  have htrace : WordTrace (prefixWord ++ tailWord_993740) baseStart_993740 baseEnd_993740 := by
    simpa [prefixWord, tailWord_993740, baseEnd_993740] using wordTrace_append hprefix tailTrace_993740
  have hstable : (prefixWord ++ tailWord_993740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993740).length < 2 ^ (prefixWord ++ tailWord_993740).sum := by decide
  have hdescent : baseEnd_993740 < baseStart_993740 := by decide
  rcases family_descends (prefixWord ++ tailWord_993740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993807 : List Nat := [1, 1, 2, 1, 1, 1, 2, 7, 1, 5]
def baseStart_993807 : Nat := 118140960795 + 993807 * 2 ^ 59
def prefixEnd_993807 : Nat := 4983230072969 + 3 ^ 40 * 993807 * 2
def baseEnd_993807 : Nat := 340200445868598972828047

theorem tailTrace_993807 : CollatzResearch.WordTrace tailWord_993807 prefixEnd_993807 340200445868598972828047 := by
  unfold tailWord_993807
  simp only [CollatzResearch.WordTrace]
  refine ⟨36247119110614442567915675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24164746073742961711943783 36247119110614442567915675)
  ·
    refine ⟨54370678665921663851873513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36247119110614442567915675 54370678665921663851873513)
    ·
      refine ⟨40778008999441247888905135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54370678665921663851873513 40778008999441247888905135)
      ·
        refine ⟨61167013499161871833357703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40778008999441247888905135 61167013499161871833357703)
        ·
          refine ⟨91750520248742807750036555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61167013499161871833357703 91750520248742807750036555)
          ·
            refine ⟨137625780373114211625054833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91750520248742807750036555 137625780373114211625054833)
            ·
              refine ⟨103219335279835658718791125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137625780373114211625054833 103219335279835658718791125)
              ·
                refine ⟨2419203170621148251221667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 103219335279835658718791125 2419203170621148251221667)
                ·
                  refine ⟨3628804755931722376832501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419203170621148251221667 3628804755931722376832501)
                  ·
                    refine ⟨340200445868598972828047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3628804755931722376832501 340200445868598972828047)
                    ·
                      rfl

theorem cell22_993807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_993807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993807 prefixEnd_993807 := by exact prefixLift 993807
  have htrace : WordTrace (prefixWord ++ tailWord_993807) baseStart_993807 baseEnd_993807 := by
    simpa [prefixWord, tailWord_993807, baseEnd_993807] using wordTrace_append hprefix tailTrace_993807
  have hstable : (prefixWord ++ tailWord_993807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993807).length < 2 ^ (prefixWord ++ tailWord_993807).sum := by decide
  have hdescent : baseEnd_993807 < baseStart_993807 := by decide
  rcases family_descends (prefixWord ++ tailWord_993807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993828 : List Nat := [2, 3, 1, 5, 1, 1, 1, 3, 1, 4]
def baseStart_993828 : Nat := 118140960795 + 993828 * 2 ^ 59
def prefixEnd_993828 : Nat := 4983230072969 + 3 ^ 40 * 993828 * 2
def baseEnd_993828 : Nat := 340207634597761918052983

theorem tailTrace_993828 : CollatzResearch.WordTrace tailWord_993828 prefixEnd_993828 340207634597761918052983 := by
  unfold tailWord_993828
  simp only [CollatzResearch.WordTrace]
  refine ⟨18123942521769181577215069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24165256695692242102953425 18123942521769181577215069)
  ·
    refine ⟨6796478445663443091455651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18123942521769181577215069 6796478445663443091455651)
    ·
      refine ⟨10194717668495164637183477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6796478445663443091455651 10194717668495164637183477)
      ·
        refine ⟨955754781421421684735951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10194717668495164637183477 955754781421421684735951)
        ·
          refine ⟨1433632172132132527103927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955754781421421684735951 1433632172132132527103927)
          ·
            refine ⟨2150448258198198790655891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433632172132132527103927 2150448258198198790655891)
            ·
              refine ⟨3225672387297298185983837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2150448258198198790655891 3225672387297298185983837)
              ·
                refine ⟨1209627145236486819743939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3225672387297298185983837 1209627145236486819743939)
                ·
                  refine ⟨1814440717854730229615909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1209627145236486819743939 1814440717854730229615909)
                  ·
                    refine ⟨340207634597761918052983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1814440717854730229615909 340207634597761918052983)
                    ·
                      rfl

theorem cell22_993828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_993828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993828 prefixEnd_993828 := by exact prefixLift 993828
  have htrace : WordTrace (prefixWord ++ tailWord_993828) baseStart_993828 baseEnd_993828 := by
    simpa [prefixWord, tailWord_993828, baseEnd_993828] using wordTrace_append hprefix tailTrace_993828
  have hstable : (prefixWord ++ tailWord_993828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993828).length < 2 ^ (prefixWord ++ tailWord_993828).sum := by decide
  have hdescent : baseEnd_993828 < baseStart_993828 := by decide
  rcases family_descends (prefixWord ++ tailWord_993828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993841 : List Nat := [1, 2, 2, 3, 1, 1, 5, 2, 2, 3]
def baseStart_993841 : Nat := 118140960795 + 993841 * 2 ^ 59
def prefixEnd_993841 : Nat := 4983230072969 + 3 ^ 40 * 993841 * 2
def baseEnd_993841 : Nat := 340212084763434217477943

theorem tailTrace_993841 : CollatzResearch.WordTrace tailWord_993841 prefixEnd_993841 340212084763434217477943 := by
  unfold tailWord_993841
  simp only [CollatzResearch.WordTrace]
  refine ⟨36248359192491266374653377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24165572794994177583102251 36248359192491266374653377)
  ·
    refine ⟨27186269394368449780990033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36248359192491266374653377 27186269394368449780990033)
    ·
      refine ⟨20389702045776337335742525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27186269394368449780990033 20389702045776337335742525)
      ·
        refine ⟨7646138267166126500903447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20389702045776337335742525 7646138267166126500903447)
        ·
          refine ⟨11469207400749189751355171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7646138267166126500903447 11469207400749189751355171)
          ·
            refine ⟨17203811101123784627032757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11469207400749189751355171 17203811101123784627032757)
            ·
              refine ⟨1612857290730354808784321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17203811101123784627032757 1612857290730354808784321)
              ·
                refine ⟨1209642968047766106588241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1612857290730354808784321 1209642968047766106588241)
                ·
                  refine ⟨907232226035824579941181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1209642968047766106588241 907232226035824579941181)
                  ·
                    refine ⟨340212084763434217477943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 907232226035824579941181 340212084763434217477943)
                    ·
                      rfl

theorem cell22_993841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_993841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993841 prefixEnd_993841 := by exact prefixLift 993841
  have htrace : WordTrace (prefixWord ++ tailWord_993841) baseStart_993841 baseEnd_993841 := by
    simpa [prefixWord, tailWord_993841, baseEnd_993841] using wordTrace_append hprefix tailTrace_993841
  have hstable : (prefixWord ++ tailWord_993841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993841).length < 2 ^ (prefixWord ++ tailWord_993841).sum := by decide
  have hdescent : baseEnd_993841 < baseStart_993841 := by decide
  rcases family_descends (prefixWord ++ tailWord_993841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993867 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 2, 6]
def baseStart_993867 : Nat := 118140960795 + 993867 * 2 ^ 59
def prefixEnd_993867 : Nat := 4983230072969 + 3 ^ 40 * 993867 * 2
def baseEnd_993867 : Nat := 340220985094778816327863

theorem tailTrace_993867 : CollatzResearch.WordTrace tailWord_993867 prefixEnd_993867 340220985094778816327863 := by
  unfold tailWord_993867
  simp only [CollatzResearch.WordTrace]
  refine ⟨36249307490397072815099855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24166204993598048543399903 36249307490397072815099855)
  ·
    refine ⟨54373961235595609222649783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36249307490397072815099855 54373961235595609222649783)
    ·
      refine ⟨81560941853393413833974675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54373961235595609222649783 81560941853393413833974675)
      ·
        refine ⟨122341412780090120750962013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81560941853393413833974675 122341412780090120750962013)
        ·
          refine ⟨45878029792533795281610755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122341412780090120750962013 45878029792533795281610755)
          ·
            refine ⟨68817044688800692922416133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45878029792533795281610755 68817044688800692922416133)
            ·
              refine ⟨12903195879150129922953025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68817044688800692922416133 12903195879150129922953025)
              ·
                refine ⟨9677396909362597442214769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12903195879150129922953025 9677396909362597442214769)
                ·
                  refine ⟨7258047682021948081661077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9677396909362597442214769 7258047682021948081661077)
                  ·
                    refine ⟨340220985094778816327863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7258047682021948081661077 340220985094778816327863)
                    ·
                      rfl

theorem cell22_993867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 6].length) (baseStart_993867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993867 prefixEnd_993867 := by exact prefixLift 993867
  have htrace : WordTrace (prefixWord ++ tailWord_993867) baseStart_993867 baseEnd_993867 := by
    simpa [prefixWord, tailWord_993867, baseEnd_993867] using wordTrace_append hprefix tailTrace_993867
  have hstable : (prefixWord ++ tailWord_993867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993867).length < 2 ^ (prefixWord ++ tailWord_993867).sum := by decide
  have hdescent : baseEnd_993867 < baseStart_993867 := by decide
  rcases family_descends (prefixWord ++ tailWord_993867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993916 : List Nat := [2, 2, 2, 1, 1, 2, 6, 1, 5]
def baseStart_993916 : Nat := 118140960795 + 993916 * 2 ^ 59
def prefixEnd_993916 : Nat := 4983230072969 + 3 ^ 40 * 993916 * 2
def baseEnd_993916 : Nat := 113412586265386340617571

theorem tailTrace_993916 : CollatzResearch.WordTrace tailWord_993916 prefixEnd_993916 113412586265386340617571 := by
  unfold tailWord_993916
  simp only [CollatzResearch.WordTrace]
  refine ⟨18125547333609777091816801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24167396444813036122422401 18125547333609777091816801)
  ·
    refine ⟨13594160500207332818862601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18125547333609777091816801 13594160500207332818862601)
    ·
      refine ⟨10195620375155499614146951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13594160500207332818862601 10195620375155499614146951)
      ·
        refine ⟨15293430562733249421220427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10195620375155499614146951 15293430562733249421220427)
        ·
          refine ⟨22940145844099874131830641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15293430562733249421220427 22940145844099874131830641)
          ·
            refine ⟨17205109383074905598872981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22940145844099874131830641 17205109383074905598872981)
            ·
              refine ⟨806489502331636199947171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17205109383074905598872981 806489502331636199947171)
              ·
                refine ⟨1209734253497454299920757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806489502331636199947171 1209734253497454299920757)
                ·
                  refine ⟨113412586265386340617571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1209734253497454299920757 113412586265386340617571)
                  ·
                    rfl

theorem cell22_993916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_993916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_993916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_993916 prefixEnd_993916 := by exact prefixLift 993916
  have htrace : WordTrace (prefixWord ++ tailWord_993916) baseStart_993916 baseEnd_993916 := by
    simpa [prefixWord, tailWord_993916, baseEnd_993916] using wordTrace_append hprefix tailTrace_993916
  have hstable : (prefixWord ++ tailWord_993916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993916).length < 2 ^ (prefixWord ++ tailWord_993916).sum := by decide
  have hdescent : baseEnd_993916 < baseStart_993916 := by decide
  rcases family_descends (prefixWord ++ tailWord_993916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994038 : List Nat := [5, 1, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_994038 : Nat := 118140960795 + 994038 * 2 ^ 59
def prefixEnd_994038 : Nat := 4983230072969 + 3 ^ 40 * 994038 * 2
def baseEnd_994038 : Nat := 340279521889391370302339

theorem tailTrace_994038 : CollatzResearch.WordTrace tailWord_994038 prefixEnd_994038 340279521889391370302339 := by
  unfold tailWord_994038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2265971523298598063723423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24170362915185046013049845 2265971523298598063723423)
  ·
    refine ⟨3398957284947897095585135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2265971523298598063723423 3398957284947897095585135)
    ·
      refine ⟨5098435927421845643377703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3398957284947897095585135 5098435927421845643377703)
      ·
        refine ⟨7647653891132768465066555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5098435927421845643377703 7647653891132768465066555)
        ·
          refine ⟨11471480836699152697599833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7647653891132768465066555 11471480836699152697599833)
          ·
            refine ⟨8603610627524364523199875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11471480836699152697599833 8603610627524364523199875)
            ·
              refine ⟨12905415941286546784799813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8603610627524364523199875 12905415941286546784799813)
              ·
                refine ⟨2419765488991227522149965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12905415941286546784799813 2419765488991227522149965)
                ·
                  refine ⟨907412058371710320806237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2419765488991227522149965 907412058371710320806237)
                  ·
                    refine ⟨340279521889391370302339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 907412058371710320806237 340279521889391370302339)
                    ·
                      rfl

theorem cell22_994038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_994038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994038 prefixEnd_994038 := by exact prefixLift 994038
  have htrace : WordTrace (prefixWord ++ tailWord_994038) baseStart_994038 baseEnd_994038 := by
    simpa [prefixWord, tailWord_994038, baseEnd_994038] using wordTrace_append hprefix tailTrace_994038
  have hstable : (prefixWord ++ tailWord_994038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994038).length < 2 ^ (prefixWord ++ tailWord_994038).sum := by decide
  have hdescent : baseEnd_994038 < baseStart_994038 := by decide
  rcases family_descends (prefixWord ++ tailWord_994038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994081 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 3, 4]
def baseStart_994081 : Nat := 118140960795 + 994081 * 2 ^ 59
def prefixEnd_994081 : Nat := 4983230072969 + 3 ^ 40 * 994081 * 2
def baseEnd_994081 : Nat := 340294241668153591477207

theorem tailTrace_994081 : CollatzResearch.WordTrace tailWord_994081 prefixEnd_994081 340294241668153591477207 := by
  unfold tailWord_994081
  simp only [CollatzResearch.WordTrace]
  refine ⟨36257112711621787363390097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24171408474414524908926731 36257112711621787363390097)
  ·
    refine ⟨27192834533716340522542573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36257112711621787363390097 27192834533716340522542573)
    ·
      refine ⟨10197312950143627695953465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27192834533716340522542573 10197312950143627695953465)
      ·
        refine ⟨7647984712607720771965099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10197312950143627695953465 7647984712607720771965099)
        ·
          refine ⟨11471977068911581157947649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7647984712607720771965099 11471977068911581157947649)
          ·
            refine ⟨8603982801683685868460737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11471977068911581157947649 8603982801683685868460737)
            ·
              refine ⟨6452987101262764401345553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8603982801683685868460737 6452987101262764401345553)
              ·
                refine ⟨4839740325947073301009165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6452987101262764401345553 4839740325947073301009165)
                ·
                  refine ⟨1814902622230152487878437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4839740325947073301009165 1814902622230152487878437)
                  ·
                    refine ⟨340294241668153591477207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1814902622230152487878437 340294241668153591477207)
                    ·
                      rfl

theorem cell22_994081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_994081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994081 prefixEnd_994081 := by exact prefixLift 994081
  have htrace : WordTrace (prefixWord ++ tailWord_994081) baseStart_994081 baseEnd_994081 := by
    simpa [prefixWord, tailWord_994081, baseEnd_994081] using wordTrace_append hprefix tailTrace_994081
  have hstable : (prefixWord ++ tailWord_994081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994081).length < 2 ^ (prefixWord ++ tailWord_994081).sum := by decide
  have hdescent : baseEnd_994081 < baseStart_994081 := by decide
  rcases family_descends (prefixWord ++ tailWord_994081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994111 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 3, 5]
def baseStart_994111 : Nat := 118140960795 + 994111 * 2 ^ 59
def prefixEnd_994111 : Nat := 4983230072969 + 3 ^ 40 * 994111 * 2
def baseEnd_994111 : Nat := 340304511281243513227115

theorem tailTrace_994111 : CollatzResearch.WordTrace tailWord_994111 prefixEnd_994111 340304511281243513227115 := by
  unfold tailWord_994111
  simp only [CollatzResearch.WordTrace]
  refine ⟨36258206901513102486982187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24172137934342068324654791 36258206901513102486982187)
  ·
    refine ⟨54387310352269653730473281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36258206901513102486982187 54387310352269653730473281)
    ·
      refine ⟨40790482764202240297854961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54387310352269653730473281 40790482764202240297854961)
      ·
        refine ⟨30592862073151680223391221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40790482764202240297854961 30592862073151680223391221)
        ·
          refine ⟨2868080819357970020942927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30592862073151680223391221 2868080819357970020942927)
          ·
            refine ⟨4302121229036955031414391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2868080819357970020942927 4302121229036955031414391)
            ·
              refine ⟨6453181843555432547121587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4302121229036955031414391 6453181843555432547121587)
              ·
                refine ⟨9679772765333148820682381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6453181843555432547121587 9679772765333148820682381)
                ·
                  refine ⟨3629914786999930807755893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9679772765333148820682381 3629914786999930807755893)
                  ·
                    refine ⟨340304511281243513227115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3629914786999930807755893 340304511281243513227115)
                    ·
                      rfl

theorem cell22_994111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_994111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994111 prefixEnd_994111 := by exact prefixLift 994111
  have htrace : WordTrace (prefixWord ++ tailWord_994111) baseStart_994111 baseEnd_994111 := by
    simpa [prefixWord, tailWord_994111, baseEnd_994111] using wordTrace_append hprefix tailTrace_994111
  have hstable : (prefixWord ++ tailWord_994111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994111).length < 2 ^ (prefixWord ++ tailWord_994111).sum := by decide
  have hdescent : baseEnd_994111 < baseStart_994111 := by decide
  rcases family_descends (prefixWord ++ tailWord_994111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994128 : List Nat := [2, 1, 1, 1, 1, 4, 3, 4, 2, 3]
def baseStart_994128 : Nat := 118140960795 + 994128 * 2 ^ 59
def prefixEnd_994128 : Nat := 4983230072969 + 3 ^ 40 * 994128 * 2
def baseEnd_994128 : Nat := 340310330728661135552063

theorem tailTrace_994128 : CollatzResearch.WordTrace tailWord_994128 prefixEnd_994128 340310330728661135552063 := by
  unfold tailWord_994128
  simp only [CollatzResearch.WordTrace]
  refine ⟨18129413471225757195175519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24172551294967676260234025 18129413471225757195175519)
  ·
    refine ⟨27194120206838635792763279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18129413471225757195175519 27194120206838635792763279)
    ·
      refine ⟨40791180310257953689144919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27194120206838635792763279 40791180310257953689144919)
      ·
        refine ⟨61186770465386930533717379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40791180310257953689144919 61186770465386930533717379)
        ·
          refine ⟨91780155698080395800576069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61186770465386930533717379 91780155698080395800576069)
          ·
            refine ⟨17208779193390074212608013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91780155698080395800576069 17208779193390074212608013)
            ·
              refine ⟨6453292197521277829728005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17208779193390074212608013 6453292197521277829728005)
              ·
                refine ⟨1209992287035239593074001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6453292197521277829728005 1209992287035239593074001)
                ·
                  refine ⟨907494215276429694805501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1209992287035239593074001 907494215276429694805501)
                  ·
                    refine ⟨340310330728661135552063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 907494215276429694805501 340310330728661135552063)
                    ·
                      rfl

theorem cell22_994128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 2, 3].length) (baseStart_994128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994128 prefixEnd_994128 := by exact prefixLift 994128
  have htrace : WordTrace (prefixWord ++ tailWord_994128) baseStart_994128 baseEnd_994128 := by
    simpa [prefixWord, tailWord_994128, baseEnd_994128] using wordTrace_append hprefix tailTrace_994128
  have hstable : (prefixWord ++ tailWord_994128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994128).length < 2 ^ (prefixWord ++ tailWord_994128).sum := by decide
  have hdescent : baseEnd_994128 < baseStart_994128 := by decide
  rcases family_descends (prefixWord ++ tailWord_994128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994231 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 8]
def baseStart_994231 : Nat := 118140960795 + 994231 * 2 ^ 59
def prefixEnd_994231 : Nat := 4983230072969 + 3 ^ 40 * 994231 * 2
def baseEnd_994231 : Nat := 113448529911201066742249

theorem tailTrace_994231 : CollatzResearch.WordTrace tailWord_994231 prefixEnd_994231 113448529911201066742249 := by
  unfold tailWord_994231
  simp only [CollatzResearch.WordTrace]
  refine ⟨36262583661078362981350547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24175055774052241987567031 36262583661078362981350547)
  ·
    refine ⟨54393875491617544472025821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36262583661078362981350547 54393875491617544472025821)
    ·
      refine ⟨20397703309356579177009683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54393875491617544472025821 20397703309356579177009683)
      ·
        refine ⟨30596554964034868765514525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20397703309356579177009683 30596554964034868765514525)
        ·
          refine ⟨11473708111513075787067947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30596554964034868765514525 11473708111513075787067947)
          ·
            refine ⟨17210562167269613680601921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11473708111513075787067947 17210562167269613680601921)
            ·
              refine ⟨12907921625452210260451441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17210562167269613680601921 12907921625452210260451441)
              ·
                refine ⟨9680941219089157695338581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12907921625452210260451441 9680941219089157695338581)
                ·
                  refine ⟨113448529911201066742249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9680941219089157695338581 113448529911201066742249)
                  ·
                    rfl

theorem cell22_994231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 8].length) (baseStart_994231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994231 prefixEnd_994231 := by exact prefixLift 994231
  have htrace : WordTrace (prefixWord ++ tailWord_994231) baseStart_994231 baseEnd_994231 := by
    simpa [prefixWord, tailWord_994231, baseEnd_994231] using wordTrace_append hprefix tailTrace_994231
  have hstable : (prefixWord ++ tailWord_994231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994231).length < 2 ^ (prefixWord ++ tailWord_994231).sum := by decide
  have hdescent : baseEnd_994231 < baseStart_994231 := by decide
  rcases family_descends (prefixWord ++ tailWord_994231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994263 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 6, 3]
def baseStart_994263 : Nat := 118140960795 + 994263 * 2 ^ 59
def prefixEnd_994263 : Nat := 4983230072969 + 3 ^ 40 * 994263 * 2
def baseEnd_994263 : Nat := 340356543987565783426649

theorem tailTrace_994263 : CollatzResearch.WordTrace tailWord_994263 prefixEnd_994263 340356543987565783426649 := by
  unfold tailWord_994263
  simp only [CollatzResearch.WordTrace]
  refine ⟨36263750796962432446515443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24175833864641621631010295 36263750796962432446515443)
  ·
    refine ⟨54395626195443648669773165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36263750796962432446515443 54395626195443648669773165)
    ·
      refine ⟨20398359823291368251164937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54395626195443648669773165 20398359823291368251164937)
      ·
        refine ⟨15298769867468526188373703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20398359823291368251164937 15298769867468526188373703)
        ·
          refine ⟨22948154801202789282560555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15298769867468526188373703 22948154801202789282560555)
          ·
            refine ⟨34422232201804183923840833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22948154801202789282560555 34422232201804183923840833)
            ·
              refine ⟨25816674151353137942880625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34422232201804183923840833 25816674151353137942880625)
              ·
                refine ⟨19362505613514853457160469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25816674151353137942880625 19362505613514853457160469)
                ·
                  refine ⟨907617450633508755804397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19362505613514853457160469 907617450633508755804397)
                  ·
                    refine ⟨340356543987565783426649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 907617450633508755804397 340356543987565783426649)
                    ·
                      rfl

theorem cell22_994263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_994263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994263 prefixEnd_994263 := by exact prefixLift 994263
  have htrace : WordTrace (prefixWord ++ tailWord_994263) baseStart_994263 baseEnd_994263 := by
    simpa [prefixWord, tailWord_994263, baseEnd_994263] using wordTrace_append hprefix tailTrace_994263
  have hstable : (prefixWord ++ tailWord_994263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994263).length < 2 ^ (prefixWord ++ tailWord_994263).sum := by decide
  have hdescent : baseEnd_994263 < baseStart_994263 := by decide
  rcases family_descends (prefixWord ++ tailWord_994263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994292 : List Nat := [2, 6, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_994292 : Nat := 118140960795 + 994292 * 2 ^ 59
def prefixEnd_994292 : Nat := 4983230072969 + 3 ^ 40 * 994292 * 2
def baseEnd_994292 : Nat := 340366471280219374451561

theorem tailTrace_994292 : CollatzResearch.WordTrace tailWord_994292 prefixEnd_994292 340366471280219374451561 := by
  unfold tailWord_994292
  simp only [CollatzResearch.WordTrace]
  refine ⟨18132404256928685199660565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24176539009238246932880753 18132404256928685199660565)
  ·
    refine ⟨849956449543532118734089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18132404256928685199660565 849956449543532118734089)
    ·
      refine ⟨637467337157649089050567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 849956449543532118734089 637467337157649089050567)
      ·
        refine ⟨956201005736473633575851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637467337157649089050567 956201005736473633575851)
        ·
          refine ⟨1434301508604710450363777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956201005736473633575851 1434301508604710450363777)
          ·
            refine ⟨1075726131453532837772833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1434301508604710450363777 1075726131453532837772833)
            ·
              refine ⟨806794598590149628329625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1075726131453532837772833 806794598590149628329625)
              ·
                refine ⟨605095948942612221247219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 806794598590149628329625 605095948942612221247219)
                ·
                  refine ⟨907643923413918331870829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 605095948942612221247219 907643923413918331870829)
                  ·
                    refine ⟨340366471280219374451561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 907643923413918331870829 340366471280219374451561)
                    ·
                      rfl

theorem cell22_994292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_994292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994292 prefixEnd_994292 := by exact prefixLift 994292
  have htrace : WordTrace (prefixWord ++ tailWord_994292) baseStart_994292 baseEnd_994292 := by
    simpa [prefixWord, tailWord_994292, baseEnd_994292] using wordTrace_append hprefix tailTrace_994292
  have hstable : (prefixWord ++ tailWord_994292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994292).length < 2 ^ (prefixWord ++ tailWord_994292).sum := by decide
  have hdescent : baseEnd_994292 < baseStart_994292 := by decide
  rcases family_descends (prefixWord ++ tailWord_994292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994325 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 5, 3]
def baseStart_994325 : Nat := 118140960795 + 994325 * 2 ^ 59
def prefixEnd_994325 : Nat := 4983230072969 + 3 ^ 40 * 994325 * 2
def baseEnd_994325 : Nat := 340377767854618288376459

theorem tailTrace_994325 : CollatzResearch.WordTrace tailWord_994325 prefixEnd_994325 340377767854618288376459 := by
  unfold tailWord_994325
  simp only [CollatzResearch.WordTrace]
  refine ⟨36266012122737817035272429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24177341415158544690181619 36266012122737817035272429)
  ·
    refine ⟨13599754546026681388227161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36266012122737817035272429 13599754546026681388227161)
    ·
      refine ⟨10199815909520011041170371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13599754546026681388227161 10199815909520011041170371)
      ·
        refine ⟨15299723864280016561755557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10199815909520011041170371 15299723864280016561755557)
        ·
          refine ⟨2868698224552503105329167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15299723864280016561755557 2868698224552503105329167)
          ·
            refine ⟨4303047336828754657993751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2868698224552503105329167 4303047336828754657993751)
            ·
              refine ⟨6454571005243131986990627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4303047336828754657993751 6454571005243131986990627)
              ·
                refine ⟨9681856507864697980485941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6454571005243131986990627 9681856507864697980485941)
                ·
                  refine ⟨907674047612315435670557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9681856507864697980485941 907674047612315435670557)
                  ·
                    refine ⟨340377767854618288376459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 907674047612315435670557 340377767854618288376459)
                    ·
                      rfl

theorem cell22_994325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_994325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994325 prefixEnd_994325 := by exact prefixLift 994325
  have htrace : WordTrace (prefixWord ++ tailWord_994325) baseStart_994325 baseEnd_994325 := by
    simpa [prefixWord, tailWord_994325, baseEnd_994325] using wordTrace_append hprefix tailTrace_994325
  have hstable : (prefixWord ++ tailWord_994325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994325).length < 2 ^ (prefixWord ++ tailWord_994325).sum := by decide
  have hdescent : baseEnd_994325 < baseStart_994325 := by decide
  rcases family_descends (prefixWord ++ tailWord_994325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994353 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 4, 5]
def baseStart_994353 : Nat := 118140960795 + 994353 * 2 ^ 59
def prefixEnd_994353 : Nat := 4983230072969 + 3 ^ 40 * 994353 * 2
def baseEnd_994353 : Nat := 340387352826835548676373

theorem tailTrace_994353 : CollatzResearch.WordTrace tailWord_994353 prefixEnd_994353 340387352826835548676373 := by
  unfold tailWord_994353
  simp only [CollatzResearch.WordTrace]
  refine ⟨36267033366636377817291713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24178022244424251878194475 36267033366636377817291713)
  ·
    refine ⟨27200275024977283362968785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36267033366636377817291713 27200275024977283362968785)
    ·
      refine ⟨20400206268732962522226589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27200275024977283362968785 20400206268732962522226589)
      ·
        refine ⟨7650077350774860945834971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20400206268732962522226589 7650077350774860945834971)
        ·
          refine ⟨11475116026162291418752457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7650077350774860945834971 11475116026162291418752457)
          ·
            refine ⟨8606337019621718564064343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11475116026162291418752457 8606337019621718564064343)
            ·
              refine ⟨12909505529432577846096515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8606337019621718564064343 12909505529432577846096515)
              ·
                refine ⟨19364258294148866769144773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12909505529432577846096515 19364258294148866769144773)
                ·
                  refine ⟨3630798430152912519214645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19364258294148866769144773 3630798430152912519214645)
                  ·
                    refine ⟨340387352826835548676373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3630798430152912519214645 340387352826835548676373)
                    ·
                      rfl

theorem cell22_994353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_994353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994353 prefixEnd_994353 := by exact prefixLift 994353
  have htrace : WordTrace (prefixWord ++ tailWord_994353) baseStart_994353 baseEnd_994353 := by
    simpa [prefixWord, tailWord_994353, baseEnd_994353] using wordTrace_append hprefix tailTrace_994353
  have hstable : (prefixWord ++ tailWord_994353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994353).length < 2 ^ (prefixWord ++ tailWord_994353).sum := by decide
  have hdescent : baseEnd_994353 < baseStart_994353 := by decide
  rcases family_descends (prefixWord ++ tailWord_994353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994385 : List Nat := [1, 2, 2, 1, 3, 1, 3, 4, 1, 4]
def baseStart_994385 : Nat := 118140960795 + 994385 * 2 ^ 59
def prefixEnd_994385 : Nat := 4983230072969 + 3 ^ 40 * 994385 * 2
def baseEnd_994385 : Nat := 340398307080798131876275

theorem tailTrace_994385 : CollatzResearch.WordTrace tailWord_994385 prefixEnd_994385 340398307080798131876275 := by
  unfold tailWord_994385
  simp only [CollatzResearch.WordTrace]
  refine ⟨36268200502520447282456609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24178800335013631521637739 36268200502520447282456609)
  ·
    refine ⟨27201150376890335461842457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36268200502520447282456609 27201150376890335461842457)
    ·
      refine ⟨20400862782667751596381843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27201150376890335461842457 20400862782667751596381843)
      ·
        refine ⟨30601294174001627394572765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20400862782667751596381843 30601294174001627394572765)
        ·
          refine ⟨11475485315250610272964787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30601294174001627394572765 11475485315250610272964787)
          ·
            refine ⟨17213227972875915409447181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11475485315250610272964787 17213227972875915409447181)
            ·
              refine ⟨6454960489828468278542693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17213227972875915409447181 6454960489828468278542693)
              ·
                refine ⟨1210305091842837802226755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6454960489828468278542693 1210305091842837802226755)
                ·
                  refine ⟨1815457637764256703340133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1210305091842837802226755 1815457637764256703340133)
                  ·
                    refine ⟨340398307080798131876275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1815457637764256703340133 340398307080798131876275)
                    ·
                      rfl

theorem cell22_994385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_994385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994385 prefixEnd_994385 := by exact prefixLift 994385
  have htrace : WordTrace (prefixWord ++ tailWord_994385) baseStart_994385 baseEnd_994385 := by
    simpa [prefixWord, tailWord_994385, baseEnd_994385] using wordTrace_append hprefix tailTrace_994385
  have hstable : (prefixWord ++ tailWord_994385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994385).length < 2 ^ (prefixWord ++ tailWord_994385).sum := by decide
  have hdescent : baseEnd_994385 < baseStart_994385 := by decide
  rcases family_descends (prefixWord ++ tailWord_994385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994415 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 4, 3]
def baseStart_994415 : Nat := 118140960795 + 994415 * 2 ^ 59
def prefixEnd_994415 : Nat := 4983230072969 + 3 ^ 40 * 994415 * 2
def baseEnd_994415 : Nat := 340408576693888053626183

theorem tailTrace_994415 : CollatzResearch.WordTrace tailWord_994415 prefixEnd_994415 340408576693888053626183 := by
  unfold tailWord_994415
  simp only [CollatzResearch.WordTrace]
  refine ⟨36269294692411762406048699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24179529794941174937365799 36269294692411762406048699)
  ·
    refine ⟨54403942038617643609073049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36269294692411762406048699 54403942038617643609073049)
    ·
      refine ⟨40802956528963232706804787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54403942038617643609073049 40802956528963232706804787)
      ·
        refine ⟨61204434793444849060207181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40802956528963232706804787 61204434793444849060207181)
        ·
          refine ⟨22951663047541818397577693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61204434793444849060207181 22951663047541818397577693)
          ·
            refine ⟨8606873642828181899091635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22951663047541818397577693 8606873642828181899091635)
            ·
              refine ⟨12910310464242272848637453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8606873642828181899091635 12910310464242272848637453)
              ·
                refine ⟨4841366424090852318239045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12910310464242272848637453 4841366424090852318239045)
                ·
                  refine ⟨907756204517034809669821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4841366424090852318239045 907756204517034809669821)
                  ·
                    refine ⟨340408576693888053626183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 907756204517034809669821 340408576693888053626183)
                    ·
                      rfl

theorem cell22_994415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 3].length) (baseStart_994415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994415 prefixEnd_994415 := by exact prefixLift 994415
  have htrace : WordTrace (prefixWord ++ tailWord_994415) baseStart_994415 baseEnd_994415 := by
    simpa [prefixWord, tailWord_994415, baseEnd_994415] using wordTrace_append hprefix tailTrace_994415
  have hstable : (prefixWord ++ tailWord_994415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994415).length < 2 ^ (prefixWord ++ tailWord_994415).sum := by decide
  have hdescent : baseEnd_994415 < baseStart_994415 := by decide
  rcases family_descends (prefixWord ++ tailWord_994415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994443 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 2, 7]
def baseStart_994443 : Nat := 118140960795 + 994443 * 2 ^ 59
def prefixEnd_994443 : Nat := 4983230072969 + 3 ^ 40 * 994443 * 2
def baseEnd_994443 : Nat := 340418161666105313926097

theorem tailTrace_994443 : CollatzResearch.WordTrace tailWord_994443 prefixEnd_994443 340418161666105313926097 := by
  unfold tailWord_994443
  simp only [CollatzResearch.WordTrace]
  refine ⟨36270315936310323188067983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24180210624206882125378655 36270315936310323188067983)
  ·
    refine ⟨54405473904465484782101975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36270315936310323188067983 54405473904465484782101975)
    ·
      refine ⟨81608210856698227173152963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54405473904465484782101975 81608210856698227173152963)
      ·
        refine ⟨122412316285047340759729445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81608210856698227173152963 122412316285047340759729445)
        ·
          refine ⟨22952309303446376392449271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122412316285047340759729445 22952309303446376392449271)
          ·
            refine ⟨34428463955169564588673907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22952309303446376392449271 34428463955169564588673907)
            ·
              refine ⟨51642695932754346883010861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34428463955169564588673907 51642695932754346883010861)
              ·
                refine ⟨19366010974782880081129073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51642695932754346883010861 19366010974782880081129073)
                ·
                  refine ⟨14524508231087160060846805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19366010974782880081129073 14524508231087160060846805)
                  ·
                    refine ⟨340418161666105313926097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14524508231087160060846805 340418161666105313926097)
                    ·
                      rfl

theorem cell22_994443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 7].length) (baseStart_994443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994443 prefixEnd_994443 := by exact prefixLift 994443
  have htrace : WordTrace (prefixWord ++ tailWord_994443) baseStart_994443 baseEnd_994443 := by
    simpa [prefixWord, tailWord_994443, baseEnd_994443] using wordTrace_append hprefix tailTrace_994443
  have hstable : (prefixWord ++ tailWord_994443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994443).length < 2 ^ (prefixWord ++ tailWord_994443).sum := by decide
  have hdescent : baseEnd_994443 < baseStart_994443 := by decide
  rcases family_descends (prefixWord ++ tailWord_994443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994466 : List Nat := [3, 3, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_994466 : Nat := 118140960795 + 994466 * 2 ^ 59
def prefixEnd_994466 : Nat := 4983230072969 + 3 ^ 40 * 994466 * 2
def baseEnd_994466 : Nat := 340426035036140920601027

theorem tailTrace_994466 : CollatzResearch.WordTrace tailWord_994466 prefixEnd_994466 340426035036140920601027 := by
  unfold tailWord_994466
  simp only [CollatzResearch.WordTrace]
  refine ⟨9067788703806749529038813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24180769876817998744103501 9067788703806749529038813)
  ·
    refine ⟨3400420763927531073389555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9067788703806749529038813 3400420763927531073389555)
    ·
      refine ⟨5100631145891296610084333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3400420763927531073389555 5100631145891296610084333)
      ·
        refine ⟨1912736679709236228781625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5100631145891296610084333 1912736679709236228781625)
        ·
          refine ⟨1434552509781927171586219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1912736679709236228781625 1434552509781927171586219)
          ·
            refine ⟨2151828764672890757379329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1434552509781927171586219 2151828764672890757379329)
            ·
              refine ⟨1613871573504668068034497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2151828764672890757379329 1613871573504668068034497)
              ·
                refine ⟨1210403680128501051025873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1613871573504668068034497 1210403680128501051025873)
                ·
                  refine ⟨907802760096375788269405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1210403680128501051025873 907802760096375788269405)
                  ·
                    refine ⟨340426035036140920601027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 907802760096375788269405 340426035036140920601027)
                    ·
                      rfl

theorem cell22_994466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_994466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994466 prefixEnd_994466 := by exact prefixLift 994466
  have htrace : WordTrace (prefixWord ++ tailWord_994466) baseStart_994466 baseEnd_994466 := by
    simpa [prefixWord, tailWord_994466, baseEnd_994466] using wordTrace_append hprefix tailTrace_994466
  have hstable : (prefixWord ++ tailWord_994466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994466).length < 2 ^ (prefixWord ++ tailWord_994466).sum := by decide
  have hdescent : baseEnd_994466 < baseStart_994466 := by decide
  rcases family_descends (prefixWord ++ tailWord_994466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994494 : List Nat := [4, 2, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_994494 : Nat := 118140960795 + 994494 * 2 ^ 59
def prefixEnd_994494 : Nat := 4983230072969 + 3 ^ 40 * 994494 * 2
def baseEnd_994494 : Nat := 340435620008358180900941

theorem tailTrace_994494 : CollatzResearch.WordTrace tailWord_994494 prefixEnd_994494 340435620008358180900941 := by
  unfold tailWord_994494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4534022007390694862271817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24181450706083705932116357 4534022007390694862271817)
  ·
    refine ⟨3400516505543021146703863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4534022007390694862271817 3400516505543021146703863)
    ·
      refine ⟨5100774758314531720055795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3400516505543021146703863 5100774758314531720055795)
      ·
        refine ⟨7651162137471797580083693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5100774758314531720055795 7651162137471797580083693)
        ·
          refine ⟨2869185801551924092531385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7651162137471797580083693 2869185801551924092531385)
          ·
            refine ⟨2151889351163943069398539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2869185801551924092531385 2151889351163943069398539)
            ·
              refine ⟨3227834026745914604097809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151889351163943069398539 3227834026745914604097809)
              ·
                refine ⟨2420875520059435953073357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3227834026745914604097809 2420875520059435953073357)
                ·
                  refine ⟨907828320022288482402509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2420875520059435953073357 907828320022288482402509)
                  ·
                    refine ⟨340435620008358180900941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 907828320022288482402509 340435620008358180900941)
                    ·
                      rfl

theorem cell22_994494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_994494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994494 prefixEnd_994494 := by exact prefixLift 994494
  have htrace : WordTrace (prefixWord ++ tailWord_994494) baseStart_994494 baseEnd_994494 := by
    simpa [prefixWord, tailWord_994494, baseEnd_994494] using wordTrace_append hprefix tailTrace_994494
  have hstable : (prefixWord ++ tailWord_994494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994494).length < 2 ^ (prefixWord ++ tailWord_994494).sum := by decide
  have hdescent : baseEnd_994494 < baseStart_994494 := by decide
  rcases family_descends (prefixWord ++ tailWord_994494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994498 : List Nat := [3, 5, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_994498 : Nat := 118140960795 + 994498 * 2 ^ 59
def prefixEnd_994498 : Nat := 4983230072969 + 3 ^ 40 * 994498 * 2
def baseEnd_994498 : Nat := 340436989290103503800929

theorem tailTrace_994498 : CollatzResearch.WordTrace tailWord_994498 prefixEnd_994498 340436989290103503800929 := by
  unfold tailWord_994498
  simp only [CollatzResearch.WordTrace]
  refine ⟨9068080487777766895330037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24181547967407378387546765 9068080487777766895330037)
  ·
    refine ⟨850132545729165646437191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9068080487777766895330037 850132545729165646437191)
    ·
      refine ⟨1275198818593748469655787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 850132545729165646437191 1275198818593748469655787)
      ·
        refine ⟨1912798227890622704483681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1275198818593748469655787 1912798227890622704483681)
        ·
          refine ⟨1434598670917967028362761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1912798227890622704483681 1434598670917967028362761)
          ·
            refine ⟨1075949003188475271272071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1434598670917967028362761 1075949003188475271272071)
            ·
              refine ⟨1613923504782712906908107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075949003188475271272071 1613923504782712906908107)
              ·
                refine ⟨2420885257174069360362161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1613923504782712906908107 2420885257174069360362161)
                ·
                  refine ⟨1815663942880552020271621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2420885257174069360362161 1815663942880552020271621)
                  ·
                    refine ⟨340436989290103503800929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1815663942880552020271621 340436989290103503800929)
                    ·
                      rfl

theorem cell22_994498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_994498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994498 prefixEnd_994498 := by exact prefixLift 994498
  have htrace : WordTrace (prefixWord ++ tailWord_994498) baseStart_994498 baseEnd_994498 := by
    simpa [prefixWord, tailWord_994498, baseEnd_994498] using wordTrace_append hprefix tailTrace_994498
  have hstable : (prefixWord ++ tailWord_994498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994498).length < 2 ^ (prefixWord ++ tailWord_994498).sum := by decide
  have hdescent : baseEnd_994498 < baseStart_994498 := by decide
  rcases family_descends (prefixWord ++ tailWord_994498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994565 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 1, 6]
def baseStart_994565 : Nat := 118140960795 + 994565 * 2 ^ 59
def prefixEnd_994565 : Nat := 4983230072969 + 3 ^ 40 * 994565 * 2
def baseEnd_994565 : Nat := 340459924759337662375723

theorem tailTrace_994565 : CollatzResearch.WordTrace tailWord_994565 prefixEnd_994565 340459924759337662375723 := by
  unfold tailWord_994565
  simp only [CollatzResearch.WordTrace]
  refine ⟨36274765641868338024009149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24183177094578892016006099 36274765641868338024009149)
  ·
    refine ⟨13603037115700626759003431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36274765641868338024009149 13603037115700626759003431)
    ·
      refine ⟨20404555673550940138505147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13603037115700626759003431 20404555673550940138505147)
      ·
        refine ⟨30606833510326410207757721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20404555673550940138505147 30606833510326410207757721)
        ·
          refine ⟨22955125132744807655818291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30606833510326410207757721 22955125132744807655818291)
          ·
            refine ⟨34432687699117211483727437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22955125132744807655818291 34432687699117211483727437)
            ·
              refine ⟨12912257887168954306397789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34432687699117211483727437 12912257887168954306397789)
              ·
                refine ⟨4842096707688357864899171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12912257887168954306397789 4842096707688357864899171)
                ·
                  refine ⟨7263145061532536797348757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4842096707688357864899171 7263145061532536797348757)
                  ·
                    refine ⟨340459924759337662375723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7263145061532536797348757 340459924759337662375723)
                    ·
                      rfl

theorem cell22_994565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_994565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994565 prefixEnd_994565 := by exact prefixLift 994565
  have htrace : WordTrace (prefixWord ++ tailWord_994565) baseStart_994565 baseEnd_994565 := by
    simpa [prefixWord, tailWord_994565, baseEnd_994565] using wordTrace_append hprefix tailTrace_994565
  have hstable : (prefixWord ++ tailWord_994565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994565).length < 2 ^ (prefixWord ++ tailWord_994565).sum := by decide
  have hdescent : baseEnd_994565 < baseStart_994565 := by decide
  rcases family_descends (prefixWord ++ tailWord_994565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994586 : List Nat := [3, 1, 1, 3, 3, 2, 3, 2, 4]
def baseStart_994586 : Nat := 118140960795 + 994586 * 2 ^ 59
def prefixEnd_994586 : Nat := 4983230072969 + 3 ^ 40 * 994586 * 2
def baseEnd_994586 : Nat := 113489037829500202533553

theorem tailTrace_994586 : CollatzResearch.WordTrace tailWord_994586 prefixEnd_994586 113489037829500202533553 := by
  unfold tailWord_994586
  simp only [CollatzResearch.WordTrace]
  refine ⟨9068882893698064652630903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24183687716528172407015741 9068882893698064652630903)
  ·
    refine ⟨13603324340547096978946355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9068882893698064652630903 13603324340547096978946355)
    ·
      refine ⟨20404986510820645468419533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13603324340547096978946355 20404986510820645468419533)
      ·
        refine ⟨7651869941557742050657325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20404986510820645468419533 7651869941557742050657325)
        ·
          refine ⟨2869451228084153268996497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7651869941557742050657325 2869451228084153268996497)
          ·
            refine ⟨2152088421063114951747373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2869451228084153268996497 2152088421063114951747373)
            ·
              refine ⟨807033157898668106905265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2152088421063114951747373 807033157898668106905265)
              ·
                refine ⟨605274868424001080178949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 807033157898668106905265 605274868424001080178949)
                ·
                  refine ⟨113489037829500202533553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 605274868424001080178949 113489037829500202533553)
                  ·
                    rfl

theorem cell22_994586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_994586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994586 prefixEnd_994586 := by exact prefixLift 994586
  have htrace : WordTrace (prefixWord ++ tailWord_994586) baseStart_994586 baseEnd_994586 := by
    simpa [prefixWord, tailWord_994586, baseEnd_994586] using wordTrace_append hprefix tailTrace_994586
  have hstable : (prefixWord ++ tailWord_994586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994586).length < 2 ^ (prefixWord ++ tailWord_994586).sum := by decide
  have hdescent : baseEnd_994586 < baseStart_994586 := by decide
  rcases family_descends (prefixWord ++ tailWord_994586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994597 : List Nat := [1, 3, 1, 2, 4, 2, 2, 7]
def baseStart_994597 : Nat := 118140960795 + 994597 * 2 ^ 59
def prefixEnd_994597 : Nat := 4983230072969 + 3 ^ 40 * 994597 * 2
def baseEnd_994597 : Nat := 37830097668144471730625

theorem tailTrace_994597 : CollatzResearch.WordTrace tailWord_994597 prefixEnd_994597 37830097668144471730625 := by
  unfold tailWord_994597
  simp only [CollatzResearch.WordTrace]
  refine ⟨36275932777752407489174045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24183955185168271659449363 36275932777752407489174045)
  ·
    refine ⟨13603474791657152808440267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36275932777752407489174045 13603474791657152808440267)
    ·
      refine ⟨20405212187485729212660401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13603474791657152808440267 20405212187485729212660401)
      ·
        refine ⟨15303909140614296909495301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20405212187485729212660401 15303909140614296909495301)
        ·
          refine ⟨2869482963865180670530369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15303909140614296909495301 2869482963865180670530369)
          ·
            refine ⟨2152112222898885502897777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2869482963865180670530369 2152112222898885502897777)
            ·
              refine ⟨1614084167174164127173333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2152112222898885502897777 1614084167174164127173333)
              ·
                refine ⟨37830097668144471730625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1614084167174164127173333 37830097668144471730625)
                ·
                  rfl

theorem cell22_994597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 7].length) (baseStart_994597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994597 prefixEnd_994597 := by exact prefixLift 994597
  have htrace : WordTrace (prefixWord ++ tailWord_994597) baseStart_994597 baseEnd_994597 := by
    simpa [prefixWord, tailWord_994597, baseEnd_994597] using wordTrace_append hprefix tailTrace_994597
  have hstable : (prefixWord ++ tailWord_994597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994597).length < 2 ^ (prefixWord ++ tailWord_994597).sum := by decide
  have hdescent : baseEnd_994597 < baseStart_994597 := by decide
  rcases family_descends (prefixWord ++ tailWord_994597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994637 : List Nat := [1, 6, 1, 3, 2, 1, 2, 2, 4]
def baseStart_994637 : Nat := 118140960795 + 994637 * 2 ^ 59
def prefixEnd_994637 : Nat := 4983230072969 + 3 ^ 40 * 994637 * 2
def baseEnd_994637 : Nat := 113494857276917824858501

theorem tailTrace_994637 : CollatzResearch.WordTrace tailWord_994637 prefixEnd_994637 113494857276917824858501 := by
  unfold tailWord_994637
  simp only [CollatzResearch.WordTrace]
  refine ⟨36277391697607494320630165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24184927798404996213753443 36277391697607494320630165)
  ·
    refine ⟨1700502735825351296279539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36277391697607494320630165 1700502735825351296279539)
    ·
      refine ⟨2550754103738026944419309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1700502735825351296279539 2550754103738026944419309)
      ·
        refine ⟨956532788901760104157241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2550754103738026944419309 956532788901760104157241)
        ·
          refine ⟨717399591676320078117931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 956532788901760104157241 717399591676320078117931)
          ·
            refine ⟨1076099387514480117176897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717399591676320078117931 1076099387514480117176897)
            ·
              refine ⟨807074540635860087882673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1076099387514480117176897 807074540635860087882673)
              ·
                refine ⟨605305905476895065912005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 807074540635860087882673 605305905476895065912005)
                ·
                  refine ⟨113494857276917824858501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 605305905476895065912005 113494857276917824858501)
                  ·
                    rfl

theorem cell22_994637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_994637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994637 prefixEnd_994637 := by exact prefixLift 994637
  have htrace : WordTrace (prefixWord ++ tailWord_994637) baseStart_994637 baseEnd_994637 := by
    simpa [prefixWord, tailWord_994637, baseEnd_994637] using wordTrace_append hprefix tailTrace_994637
  have hstable : (prefixWord ++ tailWord_994637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994637).length < 2 ^ (prefixWord ++ tailWord_994637).sum := by decide
  have hdescent : baseEnd_994637 < baseStart_994637 := by decide
  rcases family_descends (prefixWord ++ tailWord_994637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994672 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 3, 4]
def baseStart_994672 : Nat := 118140960795 + 994672 * 2 ^ 59
def prefixEnd_994672 : Nat := 4983230072969 + 3 ^ 40 * 994672 * 2
def baseEnd_994672 : Nat := 340496553046025049950395

theorem tailTrace_994672 : CollatzResearch.WordTrace tailWord_994672 prefixEnd_994672 340496553046025049950395 := by
  unfold tailWord_994672
  simp only [CollatzResearch.WordTrace]
  refine ⟨18139334126240347649077135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24185778834987130198769513 18139334126240347649077135)
  ·
    refine ⟨27209001189360521473615703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18139334126240347649077135 27209001189360521473615703)
    ·
      refine ⟨40813501784040782210423555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27209001189360521473615703 40813501784040782210423555)
      ·
        refine ⟨61220252676061173315635333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40813501784040782210423555 61220252676061173315635333)
        ·
          refine ⟨11478797376761469996681625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61220252676061173315635333 11478797376761469996681625)
          ·
            refine ⟨8609098032571102497511219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11478797376761469996681625 8609098032571102497511219)
            ·
              refine ⟨12913647048856653746266829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8609098032571102497511219 12913647048856653746266829)
              ·
                refine ⟨4842617643321245154850061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12913647048856653746266829 4842617643321245154850061)
                ·
                  refine ⟨1815981616245466933068773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4842617643321245154850061 1815981616245466933068773)
                  ·
                    refine ⟨340496553046025049950395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1815981616245466933068773 340496553046025049950395)
                    ·
                      rfl

theorem cell22_994672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_994672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994672 prefixEnd_994672 := by exact prefixLift 994672
  have htrace : WordTrace (prefixWord ++ tailWord_994672) baseStart_994672 baseEnd_994672 := by
    simpa [prefixWord, tailWord_994672, baseEnd_994672] using wordTrace_append hprefix tailTrace_994672
  have hstable : (prefixWord ++ tailWord_994672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994672).length < 2 ^ (prefixWord ++ tailWord_994672).sum := by decide
  have hdescent : baseEnd_994672 < baseStart_994672 := by decide
  rcases family_descends (prefixWord ++ tailWord_994672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994719 : List Nat := [1, 1, 2, 5, 1, 2, 3, 1, 1, 5]
def baseStart_994719 : Nat := 118140960795 + 994719 * 2 ^ 59
def prefixEnd_994719 : Nat := 4983230072969 + 3 ^ 40 * 994719 * 2
def baseEnd_994719 : Nat := 340512642106532594025251

theorem tailTrace_994719 : CollatzResearch.WordTrace tailWord_994719 prefixEnd_994719 340512642106532594025251 := by
  unfold tailWord_994719
  simp only [CollatzResearch.WordTrace]
  refine ⟨36280382483310422325115211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24186921655540281550076807 36280382483310422325115211)
  ·
    refine ⟨54420573724965633487672817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36280382483310422325115211 54420573724965633487672817)
    ·
      refine ⟨40815430293724225115754613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54420573724965633487672817 40815430293724225115754613)
      ·
        refine ⟨3826446590036646104601995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40815430293724225115754613 3826446590036646104601995)
        ·
          refine ⟨5739669885054969156902993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3826446590036646104601995 5739669885054969156902993)
          ·
            refine ⟨4304752413791226867677245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5739669885054969156902993 4304752413791226867677245)
            ·
              refine ⟨1614282155171710075378967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4304752413791226867677245 1614282155171710075378967)
              ·
                refine ⟨2421423232757565113068451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614282155171710075378967 2421423232757565113068451)
                ·
                  refine ⟨3632134849136347669602677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2421423232757565113068451 3632134849136347669602677)
                  ·
                    refine ⟨340512642106532594025251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3632134849136347669602677 340512642106532594025251)
                    ·
                      rfl

theorem cell22_994719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 5].length) (baseStart_994719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994719 prefixEnd_994719 := by exact prefixLift 994719
  have htrace : WordTrace (prefixWord ++ tailWord_994719) baseStart_994719 baseEnd_994719 := by
    simpa [prefixWord, tailWord_994719, baseEnd_994719] using wordTrace_append hprefix tailTrace_994719
  have hstable : (prefixWord ++ tailWord_994719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994719).length < 2 ^ (prefixWord ++ tailWord_994719).sum := by decide
  have hdescent : baseEnd_994719 < baseStart_994719 := by decide
  rcases family_descends (prefixWord ++ tailWord_994719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
