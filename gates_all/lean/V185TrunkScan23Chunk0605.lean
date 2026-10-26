import V185TrunkScan23Chunk0604

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3577236 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_3577236 : Nat := 118140960795 + 3577236 * 2 ^ 59
def prefixEnd_3577236 : Nat := 4983230072969 + 3 ^ 40 * 3577236 * 2
def baseEnd_3577236 : Nat := 612280494189023760466199

theorem tailTrace_3577236 : CollatzResearch.WordTrace tailWord_3577236 prefixEnd_3577236 612280494189023760466199 := by
  unfold tailWord_3577236
  simp only [CollatzResearch.WordTrace]
  refine ⟨65236257834146195057115781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86981677112194926742821041 65236257834146195057115781)
  ·
    refine ⟨12231798343902411573209209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65236257834146195057115781 12231798343902411573209209)
    ·
      refine ⟨9173848757926808679906907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12231798343902411573209209 9173848757926808679906907)
      ·
        refine ⟨13760773136890213019860361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9173848757926808679906907 13760773136890213019860361)
        ·
          refine ⟨10320579852667659764895271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13760773136890213019860361 10320579852667659764895271)
          ·
            refine ⟨15480869779001489647342907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10320579852667659764895271 15480869779001489647342907)
            ·
              refine ⟨23221304668502234471014361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15480869779001489647342907 23221304668502234471014361)
              ·
                refine ⟨17415978501376675853260771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23221304668502234471014361 17415978501376675853260771)
                ·
                  refine ⟨26123967752065013779891157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17415978501376675853260771 26123967752065013779891157)
                  ·
                    refine ⟨612280494189023760466199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26123967752065013779891157 612280494189023760466199)
                    ·
                      rfl

theorem cell23_3577236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_3577236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577236 prefixEnd_3577236 := by exact prefixLift 3577236
  have htrace : WordTrace (prefixWord ++ tailWord_3577236) baseStart_3577236 baseEnd_3577236 := by
    simpa [prefixWord, tailWord_3577236, baseEnd_3577236] using wordTrace_append hprefix tailTrace_3577236
  have hstable : (prefixWord ++ tailWord_3577236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577236).length < 2 ^ (prefixWord ++ tailWord_3577236).sum := by decide
  have hdescent : baseEnd_3577236 < baseStart_3577236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577273 : List Nat := [1, 2, 1, 4, 4, 1, 1, 2, 2, 1, 4]
def baseStart_3577273 : Nat := 118140960795 + 3577273 * 2 ^ 59
def prefixEnd_3577273 : Nat := 4983230072969 + 3 ^ 40 * 3577273 * 2
def baseEnd_3577273 : Nat := 1836860481351287636635927

theorem tailTrace_3577273 : CollatzResearch.WordTrace tailWord_3577273 prefixEnd_3577273 1836860481351287636635927 := by
  unfold tailWord_3577273
  simp only [CollatzResearch.WordTrace]
  refine ⟨130473865169158345433328473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86982576779438896955552315 130473865169158345433328473)
  ·
    refine ⟨97855398876868759074996355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130473865169158345433328473 97855398876868759074996355)
    ·
      refine ⟨146783098315303138612494533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97855398876868759074996355 146783098315303138612494533)
      ·
        refine ⟨27521830934119338489842725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146783098315303138612494533 27521830934119338489842725)
        ·
          refine ⟨5160343300147375966845511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27521830934119338489842725 5160343300147375966845511)
          ·
            refine ⟨7740514950221063950268267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5160343300147375966845511 7740514950221063950268267)
            ·
              refine ⟨11610772425331595925402401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7740514950221063950268267 11610772425331595925402401)
              ·
                refine ⟨8708079318998696944051801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11610772425331595925402401 8708079318998696944051801)
                ·
                  refine ⟨6531059489249022708038851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8708079318998696944051801 6531059489249022708038851)
                  ·
                    refine ⟨9796589233873534062058277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6531059489249022708038851 9796589233873534062058277)
                    ·
                      refine ⟨1836860481351287636635927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9796589233873534062058277 1836860481351287636635927)
                      ·
                        rfl

theorem cell23_3577273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_3577273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577273 prefixEnd_3577273 := by exact prefixLift 3577273
  have htrace : WordTrace (prefixWord ++ tailWord_3577273) baseStart_3577273 baseEnd_3577273 := by
    simpa [prefixWord, tailWord_3577273, baseEnd_3577273] using wordTrace_append hprefix tailTrace_3577273
  have hstable : (prefixWord ++ tailWord_3577273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577273).length < 2 ^ (prefixWord ++ tailWord_3577273).sum := by decide
  have hdescent : baseEnd_3577273 < baseStart_3577273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577283 : List Nat := [1, 1, 1, 3, 1, 1, 4, 6, 1, 4]
def baseStart_3577283 : Nat := 118140960795 + 3577283 * 2 ^ 59
def prefixEnd_3577283 : Nat := 4983230072969 + 3 ^ 40 * 3577283 * 2
def baseEnd_3577283 : Nat := 612288538719277532503627

theorem tailTrace_3577283 : CollatzResearch.WordTrace tailWord_3577283 prefixEnd_3577283 612288538719277532503627 := by
  unfold tailWord_3577283
  simp only [CollatzResearch.WordTrace]
  refine ⟨130474229899122117141192503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86982819932748078094128335 130474229899122117141192503)
  ·
    refine ⟨195711344848683175711788755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130474229899122117141192503 195711344848683175711788755)
    ·
      refine ⟨293567017273024763567683133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195711344848683175711788755 293567017273024763567683133)
      ·
        refine ⟨110087631477384286337881175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293567017273024763567683133 110087631477384286337881175)
        ·
          refine ⟨165131447216076429506821763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110087631477384286337881175 165131447216076429506821763)
          ·
            refine ⟨247697170824114644260232645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165131447216076429506821763 247697170824114644260232645)
            ·
              refine ⟨46443219529521495798793621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247697170824114644260232645 46443219529521495798793621)
              ·
                refine ⟨2177025915446320115568451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46443219529521495798793621 2177025915446320115568451)
                ·
                  refine ⟨3265538873169480173352677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2177025915446320115568451 3265538873169480173352677)
                  ·
                    refine ⟨612288538719277532503627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3265538873169480173352677 612288538719277532503627)
                    ·
                      rfl

theorem cell23_3577283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 1, 4].length) (baseStart_3577283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577283 prefixEnd_3577283 := by exact prefixLift 3577283
  have htrace : WordTrace (prefixWord ++ tailWord_3577283) baseStart_3577283 baseEnd_3577283 := by
    simpa [prefixWord, tailWord_3577283, baseEnd_3577283] using wordTrace_append hprefix tailTrace_3577283
  have hstable : (prefixWord ++ tailWord_3577283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577283).length < 2 ^ (prefixWord ++ tailWord_3577283).sum := by decide
  have hdescent : baseEnd_3577283 < baseStart_3577283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577334 : List Nat := [5, 1, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_3577334 : Nat := 118140960795 + 3577334 * 2 ^ 59
def prefixEnd_3577334 : Nat := 4983230072969 + 3 ^ 40 * 3577334 * 2
def baseEnd_3577334 : Nat := 612297267890403965991049

theorem tailTrace_3577334 : CollatzResearch.WordTrace tailWord_3577334 prefixEnd_3577334 612297267890403965991049 := by
  unfold tailWord_3577334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8154755626371084553206191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86984060014624901900866037 8154755626371084553206191)
  ·
    refine ⟨12232133439556626829809287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8154755626371084553206191 12232133439556626829809287)
    ·
      refine ⟨18348200159334940244713931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12232133439556626829809287 18348200159334940244713931)
      ·
        refine ⟨27522300239002410367070897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18348200159334940244713931 27522300239002410367070897)
        ·
          refine ⟨20641725179251807775303173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27522300239002410367070897 20641725179251807775303173)
          ·
            refine ⟨3870323471109713957869345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20641725179251807775303173 3870323471109713957869345)
            ·
              refine ⟨2902742603332285468402009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3870323471109713957869345 2902742603332285468402009)
              ·
                refine ⟨2177056952499214101301507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2902742603332285468402009 2177056952499214101301507)
                ·
                  refine ⟨3265585428748821151952261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2177056952499214101301507 3265585428748821151952261)
                  ·
                    refine ⟨612297267890403965991049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3265585428748821151952261 612297267890403965991049)
                    ·
                      rfl

theorem cell23_3577334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_3577334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577334 prefixEnd_3577334 := by exact prefixLift 3577334
  have htrace : WordTrace (prefixWord ++ tailWord_3577334) baseStart_3577334 baseEnd_3577334 := by
    simpa [prefixWord, tailWord_3577334, baseEnd_3577334] using wordTrace_append hprefix tailTrace_3577334
  have hstable : (prefixWord ++ tailWord_3577334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577334).length < 2 ^ (prefixWord ++ tailWord_3577334).sum := by decide
  have hdescent : baseEnd_3577334 < baseStart_3577334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577373 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 4, 4]
def baseStart_3577373 : Nat := 118140960795 + 3577373 * 2 ^ 59
def prefixEnd_3577373 : Nat := 4983230072969 + 3 ^ 40 * 3577373 * 2
def baseEnd_3577373 : Nat := 612303943138912415128489

theorem tailTrace_3577373 : CollatzResearch.WordTrace tailWord_3577373 prefixEnd_3577373 612303943138912415128489 := by
  unfold tailWord_3577373
  simp only [CollatzResearch.WordTrace]
  refine ⟨130477512468796062511968773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86985008312530708341312515 130477512468796062511968773)
  ·
    refine ⟨24464533587899261720994145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130477512468796062511968773 24464533587899261720994145)
    ·
      refine ⟨18348400190924446290745609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24464533587899261720994145 18348400190924446290745609)
      ·
        refine ⟨13761300143193334718059207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18348400190924446290745609 13761300143193334718059207)
        ·
          refine ⟨20641950214790002077088811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13761300143193334718059207 20641950214790002077088811)
          ·
            refine ⟨30962925322185003115633217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20641950214790002077088811 30962925322185003115633217)
            ·
              refine ⟨23222193991638752336724913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30962925322185003115633217 23222193991638752336724913)
              ·
                refine ⟨17416645493729064252543685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23222193991638752336724913 17416645493729064252543685)
                ·
                  refine ⟨3265621030074199547351941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17416645493729064252543685 3265621030074199547351941)
                  ·
                    refine ⟨612303943138912415128489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3265621030074199547351941 612303943138912415128489)
                    ·
                      rfl

theorem cell23_3577373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_3577373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577373 prefixEnd_3577373 := by exact prefixLift 3577373
  have htrace : WordTrace (prefixWord ++ tailWord_3577373) baseStart_3577373 baseEnd_3577373 := by
    simpa [prefixWord, tailWord_3577373, baseEnd_3577373] using wordTrace_append hprefix tailTrace_3577373
  have hstable : (prefixWord ++ tailWord_3577373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577373).length < 2 ^ (prefixWord ++ tailWord_3577373).sum := by decide
  have hdescent : baseEnd_3577373 < baseStart_3577373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577386 : List Nat := [3, 1, 4, 1, 1, 1, 12]
def baseStart_3577386 : Nat := 118140960795 + 3577386 * 2 ^ 59
def prefixEnd_3577386 : Nat := 4983230072969 + 3 ^ 40 * 3577386 * 2
def baseEnd_3577386 : Nat := 22678006230435132031147

theorem tailTrace_3577386 : CollatzResearch.WordTrace tailWord_3577386 prefixEnd_3577386 22678006230435132031147 := by
  unfold tailWord_3577386
  simp only [CollatzResearch.WordTrace]
  refine ⟨32619496654437241433048003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86985324411832643821461341 32619496654437241433048003)
  ·
    refine ⟨48929244981655862149572005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32619496654437241433048003 48929244981655862149572005)
    ·
      refine ⟨9174233434060474153044751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48929244981655862149572005 9174233434060474153044751)
      ·
        refine ⟨13761350151090711229567127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9174233434060474153044751 13761350151090711229567127)
        ·
          refine ⟨20642025226636066844350691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13761350151090711229567127 20642025226636066844350691)
          ·
            refine ⟨30963037839954100266526037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20642025226636066844350691 30963037839954100266526037)
            ·
              refine ⟨22678006230435132031147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 30963037839954100266526037 22678006230435132031147)
              ·
                rfl

theorem cell23_3577386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 12].length) (baseStart_3577386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577386 prefixEnd_3577386 := by exact prefixLift 3577386
  have htrace : WordTrace (prefixWord ++ tailWord_3577386) baseStart_3577386 baseEnd_3577386 := by
    simpa [prefixWord, tailWord_3577386, baseEnd_3577386] using wordTrace_append hprefix tailTrace_3577386
  have hstable : (prefixWord ++ tailWord_3577386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577386).length < 2 ^ (prefixWord ++ tailWord_3577386).sum := by decide
  have hdescent : baseEnd_3577386 < baseStart_3577386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577390 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 4, 4]
def baseStart_3577390 : Nat := 118140960795 + 3577390 * 2 ^ 59
def prefixEnd_3577390 : Nat := 4983230072969 + 3 ^ 40 * 3577390 * 2
def baseEnd_3577390 : Nat := 612306852862621226290963

theorem tailTrace_3577390 : CollatzResearch.WordTrace tailWord_3577390 prefixEnd_3577390 612306852862621226290963 := by
  unfold tailWord_3577390
  simp only [CollatzResearch.WordTrace]
  refine ⟨16309766563716809301917203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86985421673156316276891749 16309766563716809301917203)
  ·
    refine ⟨24464649845575213952875805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16309766563716809301917203 24464649845575213952875805)
    ·
      refine ⟨9174243692090705232328427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24464649845575213952875805 9174243692090705232328427)
      ·
        refine ⟨13761365538136057848492641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9174243692090705232328427 13761365538136057848492641)
        ·
          refine ⟨10321024153602043386369481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13761365538136057848492641 10321024153602043386369481)
          ·
            refine ⟨7740768115201532539777111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10321024153602043386369481 7740768115201532539777111)
            ·
              refine ⟨11611152172802298809665667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7740768115201532539777111 11611152172802298809665667)
              ·
                refine ⟨17416728259203448214498501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11611152172802298809665667 17416728259203448214498501)
                ·
                  refine ⟨3265636548600646540218469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17416728259203448214498501 3265636548600646540218469)
                  ·
                    refine ⟨612306852862621226290963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3265636548600646540218469 612306852862621226290963)
                    ·
                      rfl

theorem cell23_3577390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_3577390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577390 prefixEnd_3577390 := by exact prefixLift 3577390
  have htrace : WordTrace (prefixWord ++ tailWord_3577390) baseStart_3577390 baseEnd_3577390 := by
    simpa [prefixWord, tailWord_3577390, baseEnd_3577390] using wordTrace_append hprefix tailTrace_3577390
  have hstable : (prefixWord ++ tailWord_3577390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577390).length < 2 ^ (prefixWord ++ tailWord_3577390).sum := by decide
  have hdescent : baseEnd_3577390 < baseStart_3577390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577397 : List Nat := [1, 3, 3, 1, 1, 4, 2, 1, 3, 2, 2]
def baseStart_3577397 : Nat := 118140960795 + 3577397 * 2 ^ 59
def prefixEnd_3577397 : Nat := 4983230072969 + 3 ^ 40 * 3577397 * 2
def baseEnd_3577397 : Nat := 1836924152952445151485357

theorem tailTrace_3577397 : CollatzResearch.WordTrace tailWord_3577397 prefixEnd_3577397 1836924152952445151485357 := by
  unfold tailWord_3577397
  simp only [CollatzResearch.WordTrace]
  refine ⟨130478387820709114610842445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86985591880472743073894963 130478387820709114610842445)
  ·
    refine ⟨48929395432765917979065917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130478387820709114610842445 48929395432765917979065917)
    ·
      refine ⟨18348523287287219242149719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48929395432765917979065917 18348523287287219242149719)
      ·
        refine ⟨27522784930930828863224579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18348523287287219242149719 27522784930930828863224579)
        ·
          refine ⟨41284177396396243294836869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27522784930930828863224579 41284177396396243294836869)
          ·
            refine ⟨7740783261824295617781913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41284177396396243294836869 7740783261824295617781913)
            ·
              refine ⟨5805587446368221713336435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7740783261824295617781913 5805587446368221713336435)
              ·
                refine ⟨8708381169552332570004653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5805587446368221713336435 8708381169552332570004653)
                ·
                  refine ⟨3265642938582124713751745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8708381169552332570004653 3265642938582124713751745)
                  ·
                    refine ⟨2449232203936593535313809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3265642938582124713751745 2449232203936593535313809)
                    ·
                      refine ⟨1836924152952445151485357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2449232203936593535313809 1836924152952445151485357)
                      ·
                        rfl

theorem cell23_3577397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_3577397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577397 prefixEnd_3577397 := by exact prefixLift 3577397
  have htrace : WordTrace (prefixWord ++ tailWord_3577397) baseStart_3577397 baseEnd_3577397 := by
    simpa [prefixWord, tailWord_3577397, baseEnd_3577397] using wordTrace_append hprefix tailTrace_3577397
  have hstable : (prefixWord ++ tailWord_3577397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577397).length < 2 ^ (prefixWord ++ tailWord_3577397).sum := by decide
  have hdescent : baseEnd_3577397 < baseStart_3577397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577414 : List Nat := [6, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_3577414 : Nat := 118140960795 + 3577414 * 2 ^ 59
def prefixEnd_3577414 : Nat := 4983230072969 + 3 ^ 40 * 3577414 * 2
def baseEnd_3577414 : Nat := 1836932882123571584972779

theorem tailTrace_3577414 : CollatzResearch.WordTrace tailWord_3577414 prefixEnd_3577414 1836932882123571584972779 := by
  unfold tailWord_3577414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4077468995676485203569103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86986005241098351009474197 4077468995676485203569103)
  ·
    refine ⟨6116203493514727805353655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4077468995676485203569103 6116203493514727805353655)
    ·
      refine ⟨9174305240272091708030483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6116203493514727805353655 9174305240272091708030483)
      ·
        refine ⟨13761457860408137562045725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9174305240272091708030483 13761457860408137562045725)
        ·
          refine ⟨5160546697653051585767147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13761457860408137562045725 5160546697653051585767147)
          ·
            refine ⟨7740820046479577378650721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5160546697653051585767147 7740820046479577378650721)
            ·
              refine ⟨5805615034859683033988041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7740820046479577378650721 5805615034859683033988041)
              ·
                refine ⟨4354211276144762275491031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5805615034859683033988041 4354211276144762275491031)
                ·
                  refine ⟨6531316914217143413236547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4354211276144762275491031 6531316914217143413236547)
                  ·
                    refine ⟨9796975371325715119854821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6531316914217143413236547 9796975371325715119854821)
                    ·
                      refine ⟨1836932882123571584972779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9796975371325715119854821 1836932882123571584972779)
                      ·
                        rfl

theorem cell23_3577414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_3577414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577414 prefixEnd_3577414 := by exact prefixLift 3577414
  have htrace : WordTrace (prefixWord ++ tailWord_3577414) baseStart_3577414 baseEnd_3577414 := by
    simpa [prefixWord, tailWord_3577414, baseEnd_3577414] using wordTrace_append hprefix tailTrace_3577414
  have hstable : (prefixWord ++ tailWord_3577414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577414).length < 2 ^ (prefixWord ++ tailWord_3577414).sum := by decide
  have hdescent : baseEnd_3577414 < baseStart_3577414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577437 : List Nat := [1, 4, 4, 2, 2, 1, 9]
def baseStart_3577437 : Nat := 118140960795 + 3577437 * 2 ^ 59
def prefixEnd_3577437 : Nat := 4983230072969 + 3 ^ 40 * 3577437 * 2
def baseEnd_3577437 : Nat := 22678329533069444382533

theorem tailTrace_3577437 : CollatzResearch.WordTrace tailWord_3577437 prefixEnd_3577437 22678329533069444382533 := by
  unfold tailWord_3577437
  simp only [CollatzResearch.WordTrace]
  refine ⟨130479846740564201442298565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86986564493709467628199043 130479846740564201442298565)
  ·
    refine ⟨24464971263855787770430981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130479846740564201442298565 24464971263855787770430981)
    ·
      refine ⟨4587182111972960206955809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24464971263855787770430981 4587182111972960206955809)
      ·
        refine ⟨3440386583979720155216857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4587182111972960206955809 3440386583979720155216857)
        ·
          refine ⟨2580289937984790116412643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3440386583979720155216857 2580289937984790116412643)
          ·
            refine ⟨3870434906977185174618965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2580289937984790116412643 3870434906977185174618965)
            ·
              refine ⟨22678329533069444382533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3870434906977185174618965 22678329533069444382533)
              ·
                rfl

theorem cell23_3577437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 9].length) (baseStart_3577437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577437 prefixEnd_3577437 := by exact prefixLift 3577437
  have htrace : WordTrace (prefixWord ++ tailWord_3577437) baseStart_3577437 baseEnd_3577437 := by
    simpa [prefixWord, tailWord_3577437, baseEnd_3577437] using wordTrace_append hprefix tailTrace_3577437
  have hstable : (prefixWord ++ tailWord_3577437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577437).length < 2 ^ (prefixWord ++ tailWord_3577437).sum := by decide
  have hdescent : baseEnd_3577437 < baseStart_3577437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577473 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_3577473 : Nat := 118140960795 + 3577473 * 2 ^ 59
def prefixEnd_3577473 : Nat := 4983230072969 + 3 ^ 40 * 3577473 * 2
def baseEnd_3577473 : Nat := 1836963177482186854135007

theorem tailTrace_3577473 : CollatzResearch.WordTrace tailWord_3577473 prefixEnd_3577473 1836963177482186854135007 := by
  unfold tailWord_3577473
  simp only [CollatzResearch.WordTrace]
  refine ⟨130481159768433779590609073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86987439845622519727072715 130481159768433779590609073)
  ·
    refine ⟨97860869826325334692956805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130481159768433779590609073 97860869826325334692956805)
    ·
      refine ⟨18348913092436000254929401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97860869826325334692956805 18348913092436000254929401)
      ·
        refine ⟨13761684819327000191197051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18348913092436000254929401 13761684819327000191197051)
        ·
          refine ⟨20642527228990500286795577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13761684819327000191197051 20642527228990500286795577)
          ·
            refine ⟨15481895421742875215096683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20642527228990500286795577 15481895421742875215096683)
            ·
              refine ⟨23222843132614312822645025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15481895421742875215096683 23222843132614312822645025)
              ·
                refine ⟨17417132349460734616983769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23222843132614312822645025 17417132349460734616983769)
                ·
                  refine ⟨13062849262095550962737827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17417132349460734616983769 13062849262095550962737827)
                  ·
                    refine ⟨19594273893143326444106741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13062849262095550962737827 19594273893143326444106741)
                    ·
                      refine ⟨1836963177482186854135007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19594273893143326444106741 1836963177482186854135007)
                      ·
                        rfl

theorem cell23_3577473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_3577473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577473 prefixEnd_3577473 := by exact prefixLift 3577473
  have htrace : WordTrace (prefixWord ++ tailWord_3577473) baseStart_3577473 baseEnd_3577473 := by
    simpa [prefixWord, tailWord_3577473, baseEnd_3577473] using wordTrace_append hprefix tailTrace_3577473
  have hstable : (prefixWord ++ tailWord_3577473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577473).length < 2 ^ (prefixWord ++ tailWord_3577473).sum := by decide
  have hdescent : baseEnd_3577473 < baseStart_3577473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577504 : List Nat := [2, 1, 1, 4, 3, 2, 2, 2, 2, 2, 2]
def baseStart_3577504 : Nat := 118140960795 + 3577504 * 2 ^ 59
def prefixEnd_3577504 : Nat := 4983230072969 + 3 ^ 40 * 3577504 * 2
def baseEnd_3577504 : Nat := 1836979095382476232847365

theorem tailTrace_3577504 : CollatzResearch.WordTrace tailWord_3577504 prefixEnd_3577504 1836979095382476232847365 := by
  unfold tailWord_3577504
  simp only [CollatzResearch.WordTrace]
  refine ⟨65241145215660735942493783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86988193620880981256658377 65241145215660735942493783)
  ·
    refine ⟨97861717823491103913740675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65241145215660735942493783 97861717823491103913740675)
    ·
      refine ⟨146792576735236655870611013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97861717823491103913740675 146792576735236655870611013)
      ·
        refine ⟨27523608137856872975739565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146792576735236655870611013 27523608137856872975739565)
        ·
          refine ⟨10321353051696327365902337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27523608137856872975739565 10321353051696327365902337)
          ·
            refine ⟨7741014788772245524426753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10321353051696327365902337 7741014788772245524426753)
            ·
              refine ⟨5805761091579184143320065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7741014788772245524426753 5805761091579184143320065)
              ·
                refine ⟨4354320818684388107490049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5805761091579184143320065 4354320818684388107490049)
                ·
                  refine ⟨3265740614013291080617537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4354320818684388107490049 3265740614013291080617537)
                  ·
                    refine ⟨2449305460509968310463153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3265740614013291080617537 2449305460509968310463153)
                    ·
                      refine ⟨1836979095382476232847365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2449305460509968310463153 1836979095382476232847365)
                      ·
                        rfl

theorem cell23_3577504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_3577504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577504 prefixEnd_3577504 := by exact prefixLift 3577504
  have htrace : WordTrace (prefixWord ++ tailWord_3577504) baseStart_3577504 baseEnd_3577504 := by
    simpa [prefixWord, tailWord_3577504, baseEnd_3577504] using wordTrace_append hprefix tailTrace_3577504
  have hstable : (prefixWord ++ tailWord_3577504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577504).length < 2 ^ (prefixWord ++ tailWord_3577504).sum := by decide
  have hdescent : baseEnd_3577504 < baseStart_3577504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577543 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_3577543 : Nat := 118140960795 + 3577543 * 2 ^ 59
def prefixEnd_3577543 : Nat := 4983230072969 + 3 ^ 40 * 3577543 * 2
def baseEnd_3577543 : Nat := 1836999121128001580259685

theorem tailTrace_3577543 : CollatzResearch.WordTrace tailWord_3577543 prefixEnd_3577543 1836999121128001580259685 := by
  unfold tailWord_3577543
  simp only [CollatzResearch.WordTrace]
  refine ⟨130483712878180181545657283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86989141918786787697104855 130483712878180181545657283)
  ·
    refine ⟨195725569317270272318485925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130483712878180181545657283 195725569317270272318485925)
    ·
      refine ⟨36698544246988176059716111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195725569317270272318485925 36698544246988176059716111)
      ·
        refine ⟨55047816370482264089574167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36698544246988176059716111 55047816370482264089574167)
        ·
          refine ⟨82571724555723396134361251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55047816370482264089574167 82571724555723396134361251)
          ·
            refine ⟨123857586833585094201541877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82571724555723396134361251 123857586833585094201541877)
            ·
              refine ⟨11611648765648602581394551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123857586833585094201541877 11611648765648602581394551)
              ·
                refine ⟨17417473148472903872091827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11611648765648602581394551 17417473148472903872091827)
                ·
                  refine ⟨26126209722709355808137741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17417473148472903872091827 26126209722709355808137741)
                  ·
                    refine ⟨9797328646016008428051653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26126209722709355808137741 9797328646016008428051653)
                    ·
                      refine ⟨1836999121128001580259685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9797328646016008428051653 1836999121128001580259685)
                      ·
                        rfl

theorem cell23_3577543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_3577543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577543 prefixEnd_3577543 := by exact prefixLift 3577543
  have htrace : WordTrace (prefixWord ++ tailWord_3577543) baseStart_3577543 baseEnd_3577543 := by
    simpa [prefixWord, tailWord_3577543, baseEnd_3577543] using wordTrace_append hprefix tailTrace_3577543
  have hstable : (prefixWord ++ tailWord_3577543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577543).length < 2 ^ (prefixWord ++ tailWord_3577543).sum := by decide
  have hdescent : baseEnd_3577543 < baseStart_3577543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577560 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 4, 4, 2]
def baseStart_3577560 : Nat := 118140960795 + 3577560 * 2 ^ 59
def prefixEnd_3577560 : Nat := 4983230072969 + 3 ^ 40 * 3577560 * 2
def baseEnd_3577560 : Nat := 1837007850299128013747107

theorem tailTrace_3577560 : CollatzResearch.WordTrace tailWord_3577560 prefixEnd_3577560 1837007850299128013747107 := by
  unfold tailWord_3577560
  simp only [CollatzResearch.WordTrace]
  refine ⟨65242166459559296724513067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86989555279412395632684089 65242166459559296724513067)
  ·
    refine ⟨97863249689338945086769601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65242166459559296724513067 97863249689338945086769601)
    ·
      refine ⟨73397437267004208815077201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97863249689338945086769601 73397437267004208815077201)
      ·
        refine ⟨55048077950253156611307901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73397437267004208815077201 55048077950253156611307901)
        ·
          refine ⟨20643029231344933729240463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55048077950253156611307901 20643029231344933729240463)
          ·
            refine ⟨30964543847017400593860695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20643029231344933729240463 30964543847017400593860695)
            ·
              refine ⟨46446815770526100890791043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30964543847017400593860695 46446815770526100890791043)
              ·
                refine ⟨69670223655789151336186565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46446815770526100890791043 69670223655789151336186565)
                ·
                  refine ⟨13063166935460465875534981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69670223655789151336186565 13063166935460465875534981)
                  ·
                    refine ⟨2449343800398837351662809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13063166935460465875534981 2449343800398837351662809)
                    ·
                      refine ⟨1837007850299128013747107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2449343800398837351662809 1837007850299128013747107)
                      ·
                        rfl

theorem cell23_3577560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_3577560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577560 prefixEnd_3577560 := by exact prefixLift 3577560
  have htrace : WordTrace (prefixWord ++ tailWord_3577560) baseStart_3577560 baseEnd_3577560 := by
    simpa [prefixWord, tailWord_3577560, baseEnd_3577560] using wordTrace_append hprefix tailTrace_3577560
  have hstable : (prefixWord ++ tailWord_3577560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577560).length < 2 ^ (prefixWord ++ tailWord_3577560).sum := by decide
  have hdescent : baseEnd_3577560 < baseStart_3577560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577573 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 2, 1, 6]
def baseStart_3577573 : Nat := 118140960795 + 3577573 * 2 ^ 59
def prefixEnd_3577573 : Nat := 4983230072969 + 3 ^ 40 * 3577573 * 2
def baseEnd_3577573 : Nat := 1837014525547636462884547

theorem tailTrace_3577573 : CollatzResearch.WordTrace tailWord_3577573 prefixEnd_3577573 1837014525547636462884547 := by
  unfold tailWord_3577573
  simp only [CollatzResearch.WordTrace]
  refine ⟨130484807068071496669249373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86989871378714331112832915 130484807068071496669249373)
  ·
    refine ⟨48931802650526811250968515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130484807068071496669249373 48931802650526811250968515)
    ·
      refine ⟨73397703975790216876452773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48931802650526811250968515 73397703975790216876452773)
      ·
        refine ⟨13762069495460665664334895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73397703975790216876452773 13762069495460665664334895)
        ·
          refine ⟨20643104243190998496502343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13762069495460665664334895 20643104243190998496502343)
          ·
            refine ⟨30964656364786497744753515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20643104243190998496502343 30964656364786497744753515)
            ·
              refine ⟨46446984547179746617130273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30964656364786497744753515 46446984547179746617130273)
              ·
                refine ⟨34835238410384809962847705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46446984547179746617130273 34835238410384809962847705)
                ·
                  refine ⟨26126428807788607472135779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34835238410384809962847705 26126428807788607472135779)
                  ·
                    refine ⟨39189643211682911208203669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26126428807788607472135779 39189643211682911208203669)
                    ·
                      refine ⟨1837014525547636462884547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39189643211682911208203669 1837014525547636462884547)
                      ·
                        rfl

theorem cell23_3577573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_3577573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577573 prefixEnd_3577573 := by exact prefixLift 3577573
  have htrace : WordTrace (prefixWord ++ tailWord_3577573) baseStart_3577573 baseEnd_3577573 := by
    simpa [prefixWord, tailWord_3577573, baseEnd_3577573] using wordTrace_append hprefix tailTrace_3577573
  have hstable : (prefixWord ++ tailWord_3577573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577573).length < 2 ^ (prefixWord ++ tailWord_3577573).sum := by decide
  have hdescent : baseEnd_3577573 < baseStart_3577573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577604 : List Nat := [2, 3, 2, 2, 1, 2, 3, 3, 1, 4]
def baseStart_3577604 : Nat := 118140960795 + 3577604 * 2 ^ 59
def prefixEnd_3577604 : Nat := 4983230072969 + 3 ^ 40 * 3577604 * 2
def baseEnd_3577604 : Nat := 612343481149308613865635

theorem tailTrace_3577604 : CollatzResearch.WordTrace tailWord_3577604 prefixEnd_3577604 612343481149308613865635 := by
  unfold tailWord_3577604
  simp only [CollatzResearch.WordTrace]
  refine ⟨65242968865479594481813933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86990625153972792642418577 65242968865479594481813933)
  ·
    refine ⟨24466113324554847930680225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65242968865479594481813933 24466113324554847930680225)
    ·
      refine ⟨18349584993416135948010169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24466113324554847930680225 18349584993416135948010169)
      ·
        refine ⟨13762188745062101961007627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18349584993416135948010169 13762188745062101961007627)
        ·
          refine ⟨20643283117593152941511441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13762188745062101961007627 20643283117593152941511441)
          ·
            refine ⟨15482462338194864706133581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20643283117593152941511441 15482462338194864706133581)
            ·
              refine ⟨5805923376823074264800093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15482462338194864706133581 5805923376823074264800093)
              ·
                refine ⟨2177221266308652849300035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5805923376823074264800093 2177221266308652849300035)
                ·
                  refine ⟨3265831899462979273950053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2177221266308652849300035 3265831899462979273950053)
                  ·
                    refine ⟨612343481149308613865635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3265831899462979273950053 612343481149308613865635)
                    ·
                      rfl

theorem cell23_3577604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_3577604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577604 prefixEnd_3577604 := by exact prefixLift 3577604
  have htrace : WordTrace (prefixWord ++ tailWord_3577604) baseStart_3577604 baseEnd_3577604 := by
    simpa [prefixWord, tailWord_3577604, baseEnd_3577604] using wordTrace_append hprefix tailTrace_3577604
  have hstable : (prefixWord ++ tailWord_3577604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577604).length < 2 ^ (prefixWord ++ tailWord_3577604).sum := by decide
  have hdescent : baseEnd_3577604 < baseStart_3577604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577660 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 6, 4]
def baseStart_3577660 : Nat := 118140960795 + 3577660 * 2 ^ 59
def prefixEnd_3577660 : Nat := 4983230072969 + 3 ^ 40 * 3577660 * 2
def baseEnd_3577660 : Nat := 612353066121525874165549

theorem tailTrace_3577660 : CollatzResearch.WordTrace tailWord_3577660 prefixEnd_3577660 612353066121525874165549 := by
  unfold tailWord_3577660
  simp only [CollatzResearch.WordTrace]
  refine ⟨65243990109378155263833217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86991986812504207018444289 65243990109378155263833217)
  ·
    refine ⟨48932992582033616447874913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65243990109378155263833217 48932992582033616447874913)
    ·
      refine ⟨36699744436525212335906185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48932992582033616447874913 36699744436525212335906185)
      ·
        refine ⟨27524808327393909251929639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36699744436525212335906185 27524808327393909251929639)
        ·
          refine ⟨41287212491090863877894459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27524808327393909251929639 41287212491090863877894459)
          ·
            refine ⟨61930818736636295816841689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41287212491090863877894459 61930818736636295816841689)
            ·
              refine ⟨46448114052477221862631267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61930818736636295816841689 46448114052477221862631267)
              ·
                refine ⟨69672171078715832793946901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46448114052477221862631267 69672171078715832793946901)
                ·
                  refine ⟨3265883019314804662216261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69672171078715832793946901 3265883019314804662216261)
                  ·
                    refine ⟨612353066121525874165549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3265883019314804662216261 612353066121525874165549)
                    ·
                      rfl

theorem cell23_3577660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_3577660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577660 prefixEnd_3577660 := by exact prefixLift 3577660
  have htrace : WordTrace (prefixWord ++ tailWord_3577660) baseStart_3577660 baseEnd_3577660 := by
    simpa [prefixWord, tailWord_3577660, baseEnd_3577660] using wordTrace_append hprefix tailTrace_3577660
  have hstable : (prefixWord ++ tailWord_3577660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577660).length < 2 ^ (prefixWord ++ tailWord_3577660).sum := by decide
  have hdescent : baseEnd_3577660 < baseStart_3577660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577717 : List Nat := [1, 3, 4, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_3577717 : Nat := 118140960795 + 3577717 * 2 ^ 59
def prefixEnd_3577717 : Nat := 4983230072969 + 3 ^ 40 * 3577717 * 2
def baseEnd_3577717 : Nat := 1837088466761883899483885

theorem tailTrace_3577717 : CollatzResearch.WordTrace tailWord_3577717 prefixEnd_3577717 1837088466761883899483885 := by
  unfold tailWord_3577717
  simp only [CollatzResearch.WordTrace]
  refine ⟨130490059179549809262491405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86993372786366539508327603 130490059179549809262491405)
  ·
    refine ⟨48933772192331178473434277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130490059179549809262491405 48933772192331178473434277)
    ·
      refine ⟨9175082286062095963768927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48933772192331178473434277 9175082286062095963768927)
      ·
        refine ⟨13762623429093143945653391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9175082286062095963768927 13762623429093143945653391)
        ·
          refine ⟨20643935143639715918480087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13762623429093143945653391 20643935143639715918480087)
          ·
            refine ⟨30965902715459573877720131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20643935143639715918480087 30965902715459573877720131)
            ·
              refine ⟨46448854073189360816580197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30965902715459573877720131 46448854073189360816580197)
              ·
                refine ⟨8709160138723005153108787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46448854073189360816580197 8709160138723005153108787)
                ·
                  refine ⟨13063740208084507729663181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8709160138723005153108787 13063740208084507729663181)
                  ·
                    refine ⟨4898902578031690398623693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13063740208084507729663181 4898902578031690398623693)
                    ·
                      refine ⟨1837088466761883899483885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4898902578031690398623693 1837088466761883899483885)
                      ·
                        rfl

theorem cell23_3577717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_3577717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577717 prefixEnd_3577717 := by exact prefixLift 3577717
  have htrace : WordTrace (prefixWord ++ tailWord_3577717) baseStart_3577717 baseEnd_3577717 := by
    simpa [prefixWord, tailWord_3577717, baseEnd_3577717] using wordTrace_append hprefix tailTrace_3577717
  have hstable : (prefixWord ++ tailWord_3577717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577717).length < 2 ^ (prefixWord ++ tailWord_3577717).sum := by decide
  have hdescent : baseEnd_3577717 < baseStart_3577717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577718 : List Nat := [5, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4]
def baseStart_3577718 : Nat := 118140960795 + 3577718 * 2 ^ 59
def prefixEnd_3577718 : Nat := 4983230072969 + 3 ^ 40 * 3577718 * 2
def baseEnd_3577718 : Nat := 1837088980242538395571381

theorem tailTrace_3577718 : CollatzResearch.WordTrace tailWord_3577718 prefixEnd_3577718 1837088980242538395571381 := by
  unfold tailWord_3577718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8155630978284136652079863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86993397101697457622185205 8155630978284136652079863)
  ·
    refine ⟨12233446467426204978119795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8155630978284136652079863 12233446467426204978119795)
    ·
      refine ⟨18350169701139307467179693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12233446467426204978119795 18350169701139307467179693)
      ·
        refine ⟨6881313637927240300192385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18350169701139307467179693 6881313637927240300192385)
        ·
          refine ⟨5160985228445430225144289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6881313637927240300192385 5160985228445430225144289)
          ·
            refine ⟨3870738921334072668858217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5160985228445430225144289 3870738921334072668858217)
            ·
              refine ⟨2903054191000554501643663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3870738921334072668858217 2903054191000554501643663)
              ·
                refine ⟨4354581286500831752465495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2903054191000554501643663 4354581286500831752465495)
                ·
                  refine ⟨6531871929751247628698243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4354581286500831752465495 6531871929751247628698243)
                  ·
                    refine ⟨9797807894626871443047365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6531871929751247628698243 9797807894626871443047365)
                    ·
                      refine ⟨1837088980242538395571381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9797807894626871443047365 1837088980242538395571381)
                      ·
                        rfl

theorem cell23_3577718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_3577718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577718 prefixEnd_3577718 := by exact prefixLift 3577718
  have htrace : WordTrace (prefixWord ++ tailWord_3577718) baseStart_3577718 baseEnd_3577718 := by
    simpa [prefixWord, tailWord_3577718, baseEnd_3577718] using wordTrace_append hprefix tailTrace_3577718
  have hstable : (prefixWord ++ tailWord_3577718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577718).length < 2 ^ (prefixWord ++ tailWord_3577718).sum := by decide
  have hdescent : baseEnd_3577718 < baseStart_3577718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577751 : List Nat := [1, 1, 3, 3, 1, 4, 3, 1, 2, 1, 3]
def baseStart_3577751 : Nat := 118140960795 + 3577751 * 2 ^ 59
def prefixEnd_3577751 : Nat := 4983230072969 + 3 ^ 40 * 3577751 * 2
def baseEnd_3577751 : Nat := 1837105925104136766458729

theorem tailTrace_3577751 : CollatzResearch.WordTrace tailWord_3577751 prefixEnd_3577751 1837105925104136766458729 := by
  unfold tailWord_3577751
  simp only [CollatzResearch.WordTrace]
  refine ⟨130491299261426633069229107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86994199507617755379486071 130491299261426633069229107)
  ·
    refine ⟨195736948892139949603843661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130491299261426633069229107 195736948892139949603843661)
    ·
      refine ⟨73401355834552481101441373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195736948892139949603843661 73401355834552481101441373)
      ·
        refine ⟨27525508437957180413040515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73401355834552481101441373 27525508437957180413040515)
        ·
          refine ⟨41288262656935770619560773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27525508437957180413040515 41288262656935770619560773)
          ·
            refine ⟨7741549248175456991167645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41288262656935770619560773 7741549248175456991167645)
            ·
              refine ⟨2903080968065796371687867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7741549248175456991167645 2903080968065796371687867)
              ·
                refine ⟨4354621452098694557531801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2903080968065796371687867 4354621452098694557531801)
                ·
                  refine ⟨3265966089074020918148851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4354621452098694557531801 3265966089074020918148851)
                  ·
                    refine ⟨4898949133611031377223277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3265966089074020918148851 4898949133611031377223277)
                    ·
                      refine ⟨1837105925104136766458729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4898949133611031377223277 1837105925104136766458729)
                      ·
                        rfl

theorem cell23_3577751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_3577751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577751 prefixEnd_3577751 := by exact prefixLift 3577751
  have htrace : WordTrace (prefixWord ++ tailWord_3577751) baseStart_3577751 baseEnd_3577751 := by
    simpa [prefixWord, tailWord_3577751, baseEnd_3577751] using wordTrace_append hprefix tailTrace_3577751
  have hstable : (prefixWord ++ tailWord_3577751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577751).length < 2 ^ (prefixWord ++ tailWord_3577751).sum := by decide
  have hdescent : baseEnd_3577751 < baseStart_3577751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577758 : List Nat := [4, 3, 1, 3, 2, 1, 2, 7]
def baseStart_3577758 : Nat := 118140960795 + 3577758 * 2 ^ 59
def prefixEnd_3577758 : Nat := 4983230072969 + 3 ^ 40 * 3577758 * 2
def baseEnd_3577758 : Nat := 68041093313656231076711

theorem tailTrace_3577758 : CollatzResearch.WordTrace tailWord_3577758 prefixEnd_3577758 68041093313656231076711 := by
  unfold tailWord_3577758
  simp only [CollatzResearch.WordTrace]
  refine ⟨16311444321550159158091741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86994369714934182176489285 16311444321550159158091741)
  ·
    refine ⟨6116791620581309684284403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16311444321550159158091741 6116791620581309684284403)
    ·
      refine ⟨9175187430871964526426605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6116791620581309684284403 9175187430871964526426605)
      ·
        refine ⟨3440695286576986697409977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9175187430871964526426605 3440695286576986697409977)
        ·
          refine ⟨2580521464932740023057483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3440695286576986697409977 2580521464932740023057483)
          ·
            refine ⟨3870782197399110034586225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2580521464932740023057483 3870782197399110034586225)
            ·
              refine ⟨2903086648049332525939669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3870782197399110034586225 2903086648049332525939669)
              ·
                refine ⟨68041093313656231076711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2903086648049332525939669 68041093313656231076711)
                ·
                  rfl

theorem cell23_3577758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 7].length) (baseStart_3577758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577758 prefixEnd_3577758 := by exact prefixLift 3577758
  have htrace : WordTrace (prefixWord ++ tailWord_3577758) baseStart_3577758 baseEnd_3577758 := by
    simpa [prefixWord, tailWord_3577758, baseEnd_3577758] using wordTrace_append hprefix tailTrace_3577758
  have hstable : (prefixWord ++ tailWord_3577758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577758).length < 2 ^ (prefixWord ++ tailWord_3577758).sum := by decide
  have hdescent : baseEnd_3577758 < baseStart_3577758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577760 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 5]
def baseStart_3577760 : Nat := 118140960795 + 3577760 * 2 ^ 59
def prefixEnd_3577760 : Nat := 4983230072969 + 3 ^ 40 * 3577760 * 2
def baseEnd_3577760 : Nat := 1837110546430027231246187

theorem tailTrace_3577760 : CollatzResearch.WordTrace tailWord_3577760 prefixEnd_3577760 1837110546430027231246187 := by
  unfold tailWord_3577760
  simp only [CollatzResearch.WordTrace]
  refine ⟨65245813759197013803153367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86994418345596018404204489 65245813759197013803153367)
  ·
    refine ⟨97868720638795520704730051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65245813759197013803153367 97868720638795520704730051)
    ·
      refine ⟨146803080958193281057095077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97868720638795520704730051 146803080958193281057095077)
      ·
        refine ⟨27525577679661240198205327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146803080958193281057095077 27525577679661240198205327)
        ·
          refine ⟨41288366519491860297307991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27525577679661240198205327 41288366519491860297307991)
          ·
            refine ⟨61932549779237790445961987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41288366519491860297307991 61932549779237790445961987)
            ·
              refine ⟨92898824668856685668942981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61932549779237790445961987 92898824668856685668942981)
              ·
                refine ⟨17418529625410628562926809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92898824668856685668942981 17418529625410628562926809)
                ·
                  refine ⟨13063897219057971422195107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17418529625410628562926809 13063897219057971422195107)
                  ·
                    refine ⟨19595845828586957133292661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13063897219057971422195107 19595845828586957133292661)
                    ·
                      refine ⟨1837110546430027231246187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19595845828586957133292661 1837110546430027231246187)
                      ·
                        rfl

theorem cell23_3577760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_3577760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577760 prefixEnd_3577760 := by exact prefixLift 3577760
  have htrace : WordTrace (prefixWord ++ tailWord_3577760) baseStart_3577760 baseEnd_3577760 := by
    simpa [prefixWord, tailWord_3577760, baseEnd_3577760] using wordTrace_append hprefix tailTrace_3577760
  have hstable : (prefixWord ++ tailWord_3577760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577760).length < 2 ^ (prefixWord ++ tailWord_3577760).sum := by decide
  have hdescent : baseEnd_3577760 < baseStart_3577760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577777 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 2, 1, 5]
def baseStart_3577777 : Nat := 118140960795 + 3577777 * 2 ^ 59
def prefixEnd_3577777 : Nat := 4983230072969 + 3 ^ 40 * 3577777 * 2
def baseEnd_3577777 : Nat := 1837119275601153664733609

theorem tailTrace_3577777 : CollatzResearch.WordTrace tailWord_3577777 prefixEnd_3577777 1837119275601153664733609 := by
  unfold tailWord_3577777
  simp only [CollatzResearch.WordTrace]
  refine ⟨130492247559332439509675585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86994831706221626339783723 130492247559332439509675585)
  ·
    refine ⟨97869185669499329632256689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130492247559332439509675585 97869185669499329632256689)
    ·
      refine ⟨73401889252124497224192517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97869185669499329632256689 73401889252124497224192517)
      ·
        refine ⟨13762854234773343229536097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73401889252124497224192517 13762854234773343229536097)
        ·
          refine ⟨10322140676080007422152073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13762854234773343229536097 10322140676080007422152073)
          ·
            refine ⟨7741605507060005566614055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10322140676080007422152073 7741605507060005566614055)
            ·
              refine ⟨11612408260590008349921083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7741605507060005566614055 11612408260590008349921083)
              ·
                refine ⟨17418612390885012524881625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11612408260590008349921083 17418612390885012524881625)
                ·
                  refine ⟨13063959293163759393661219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17418612390885012524881625 13063959293163759393661219)
                  ·
                    refine ⟨19595938939745639090491829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13063959293163759393661219 19595938939745639090491829)
                    ·
                      refine ⟨1837119275601153664733609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19595938939745639090491829 1837119275601153664733609)
                      ·
                        rfl

theorem cell23_3577777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_3577777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577777 prefixEnd_3577777 := by exact prefixLift 3577777
  have htrace : WordTrace (prefixWord ++ tailWord_3577777) baseStart_3577777 baseEnd_3577777 := by
    simpa [prefixWord, tailWord_3577777, baseEnd_3577777] using wordTrace_append hprefix tailTrace_3577777
  have hstable : (prefixWord ++ tailWord_3577777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577777).length < 2 ^ (prefixWord ++ tailWord_3577777).sum := by decide
  have hdescent : baseEnd_3577777 < baseStart_3577777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577827 : List Nat := [1, 1, 1, 6, 1, 2, 1, 3, 2, 5]
def baseStart_3577827 : Nat := 118140960795 + 3577827 * 2 ^ 59
def prefixEnd_3577827 : Nat := 4983230072969 + 3 ^ 40 * 3577827 * 2
def baseEnd_3577827 : Nat := 612381649877959489702793

theorem tailTrace_3577827 : CollatzResearch.WordTrace tailWord_3577827 prefixEnd_3577827 612381649877959489702793 := by
  unfold tailWord_3577827
  simp only [CollatzResearch.WordTrace]
  refine ⟨130494071209151298048995735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86996047472767532032663823 130494071209151298048995735)
  ·
    refine ⟨195741106813726947073493603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130494071209151298048995735 195741106813726947073493603)
    ·
      refine ⟨293611660220590420610240405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195741106813726947073493603 293611660220590420610240405)
      ·
        refine ⟨13763046572840175966105019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 293611660220590420610240405 13763046572840175966105019)
        ·
          refine ⟨20644569859260263949157529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13763046572840175966105019 20644569859260263949157529)
          ·
            refine ⟨15483427394445197961868147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20644569859260263949157529 15483427394445197961868147)
            ·
              refine ⟨23225141091667796942802221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15483427394445197961868147 23225141091667796942802221)
              ·
                refine ⟨8709427909375423853550833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23225141091667796942802221 8709427909375423853550833)
                ·
                  refine ⟨6532070932031567890163125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8709427909375423853550833 6532070932031567890163125)
                  ·
                    refine ⟨612381649877959489702793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6532070932031567890163125 612381649877959489702793)
                    ·
                      rfl

theorem cell23_3577827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 5].length) (baseStart_3577827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577827 prefixEnd_3577827 := by exact prefixLift 3577827
  have htrace : WordTrace (prefixWord ++ tailWord_3577827) baseStart_3577827 baseEnd_3577827 := by
    simpa [prefixWord, tailWord_3577827, baseEnd_3577827] using wordTrace_append hprefix tailTrace_3577827
  have hstable : (prefixWord ++ tailWord_3577827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577827).length < 2 ^ (prefixWord ++ tailWord_3577827).sum := by decide
  have hdescent : baseEnd_3577827 < baseStart_3577827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577847 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 5, 6, 2]
def baseStart_3577847 : Nat := 118140960795 + 3577847 * 2 ^ 59
def prefixEnd_3577847 : Nat := 4983230072969 + 3 ^ 40 * 3577847 * 2
def baseEnd_3577847 : Nat := 1837155219246968390858287

theorem tailTrace_3577847 : CollatzResearch.WordTrace tailWord_3577847 prefixEnd_3577847 1837155219246968390858287 := by
  unfold tailWord_3577847
  simp only [CollatzResearch.WordTrace]
  refine ⟨130494800669078841464723795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86996533779385894309815863 130494800669078841464723795)
  ·
    refine ⟨195742201003618262197085693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130494800669078841464723795 195742201003618262197085693)
    ·
      refine ⟨73403325376356848323907135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195742201003618262197085693 73403325376356848323907135)
      ·
        refine ⟨110104988064535272485860703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73403325376356848323907135 110104988064535272485860703)
        ·
          refine ⟨165157482096802908728791055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110104988064535272485860703 165157482096802908728791055)
          ·
            refine ⟨247736223145204363093186583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165157482096802908728791055 247736223145204363093186583)
            ·
              refine ⟨371604334717806544639779875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247736223145204363093186583 371604334717806544639779875)
              ·
                refine ⟨557406502076709816959669813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371604334717806544639779875 557406502076709816959669813)
                ·
                  refine ⟨52256859569691545339969045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 557406502076709816959669813 52256859569691545339969045)
                  ·
                    refine ⟨2449540292329291187811049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52256859569691545339969045 2449540292329291187811049)
                    ·
                      refine ⟨1837155219246968390858287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2449540292329291187811049 1837155219246968390858287)
                      ·
                        rfl

theorem cell23_3577847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 6, 2].length) (baseStart_3577847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577847 prefixEnd_3577847 := by exact prefixLift 3577847
  have htrace : WordTrace (prefixWord ++ tailWord_3577847) baseStart_3577847 baseEnd_3577847 := by
    simpa [prefixWord, tailWord_3577847, baseEnd_3577847] using wordTrace_append hprefix tailTrace_3577847
  have hstable : (prefixWord ++ tailWord_3577847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577847).length < 2 ^ (prefixWord ++ tailWord_3577847).sum := by decide
  have hdescent : baseEnd_3577847 < baseStart_3577847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577854 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3577854 : Nat := 118140960795 + 3577854 * 2 ^ 59
def prefixEnd_3577854 : Nat := 4983230072969 + 3 ^ 40 * 3577854 * 2
def baseEnd_3577854 : Nat := 1837158813611549863470755

theorem tailTrace_3577854 : CollatzResearch.WordTrace tailWord_3577854 prefixEnd_3577854 1837158813611549863470755 := by
  unfold tailWord_3577854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16311881997506685207528577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86996703986702321106819077 16311881997506685207528577)
  ·
    refine ⟨12233911498130013905646433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16311881997506685207528577 12233911498130013905646433)
    ·
      refine ⟨9175433623597510429234825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12233911498130013905646433 9175433623597510429234825)
      ·
        refine ⟨6881575217698132821926119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9175433623597510429234825 6881575217698132821926119)
        ·
          refine ⟨10322362826547199232889179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6881575217698132821926119 10322362826547199232889179)
          ·
            refine ⟨15483544239820798849333769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10322362826547199232889179 15483544239820798849333769)
            ·
              refine ⟨11612658179865599137000327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15483544239820798849333769 11612658179865599137000327)
              ·
                refine ⟨17418987269798398705500491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11612658179865599137000327 17418987269798398705500491)
                ·
                  refine ⟨26128480904697598058250737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17418987269798398705500491 26128480904697598058250737)
                  ·
                    refine ⟨19596360678523198543688053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26128480904697598058250737 19596360678523198543688053)
                    ·
                      refine ⟨1837158813611549863470755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19596360678523198543688053 1837158813611549863470755)
                      ·
                        rfl

theorem cell23_3577854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3577854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577854 prefixEnd_3577854 := by exact prefixLift 3577854
  have htrace : WordTrace (prefixWord ++ tailWord_3577854) baseStart_3577854 baseEnd_3577854 := by
    simpa [prefixWord, tailWord_3577854, baseEnd_3577854] using wordTrace_append hprefix tailTrace_3577854
  have hstable : (prefixWord ++ tailWord_3577854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577854).length < 2 ^ (prefixWord ++ tailWord_3577854).sum := by decide
  have hdescent : baseEnd_3577854 < baseStart_3577854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577864 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 2, 4, 2]
def baseStart_3577864 : Nat := 118140960795 + 3577864 * 2 ^ 59
def prefixEnd_3577864 : Nat := 4983230072969 + 3 ^ 40 * 3577864 * 2
def baseEnd_3577864 : Nat := 1837163948418094824345709

theorem tailTrace_3577864 : CollatzResearch.WordTrace tailWord_3577864 prefixEnd_3577864 1837163948418094824345709 := by
  unfold tailWord_3577864
  simp only [CollatzResearch.WordTrace]
  refine ⟨65247710355008626684046323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86996947140011502245395097 65247710355008626684046323)
  ·
    refine ⟨97871565532512940026069485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65247710355008626684046323 97871565532512940026069485)
    ·
      refine ⟨36701837074692352509776057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97871565532512940026069485 36701837074692352509776057)
      ·
        refine ⟨27526377806019264382332043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36701837074692352509776057 27526377806019264382332043)
        ·
          refine ⟨41289566709028896573498065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27526377806019264382332043 41289566709028896573498065)
          ·
            refine ⟨30967175031771672430123549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41289566709028896573498065 30967175031771672430123549)
            ·
              refine ⟨11612690636914377161296331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30967175031771672430123549 11612690636914377161296331)
              ·
                refine ⟨17419035955371565741944497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11612690636914377161296331 17419035955371565741944497)
                ·
                  refine ⟨13064276966528674306458373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17419035955371565741944497 13064276966528674306458373)
                  ·
                    refine ⟨2449551931224126432460945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13064276966528674306458373 2449551931224126432460945)
                    ·
                      refine ⟨1837163948418094824345709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2449551931224126432460945 1837163948418094824345709)
                      ·
                        rfl

theorem cell23_3577864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_3577864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577864 prefixEnd_3577864 := by exact prefixLift 3577864
  have htrace : WordTrace (prefixWord ++ tailWord_3577864) baseStart_3577864 baseEnd_3577864 := by
    simpa [prefixWord, tailWord_3577864, baseEnd_3577864] using wordTrace_append hprefix tailTrace_3577864
  have hstable : (prefixWord ++ tailWord_3577864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577864).length < 2 ^ (prefixWord ++ tailWord_3577864).sum := by decide
  have hdescent : baseEnd_3577864 < baseStart_3577864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577867 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 3]
def baseStart_3577867 : Nat := 118140960795 + 3577867 * 2 ^ 59
def prefixEnd_3577867 : Nat := 4983230072969 + 3 ^ 40 * 3577867 * 2
def baseEnd_3577867 : Nat := 1837165488860058312608195

theorem tailTrace_3577867 : CollatzResearch.WordTrace tailWord_3577867 prefixEnd_3577867 1837165488860058312608195 := by
  unfold tailWord_3577867
  simp only [CollatzResearch.WordTrace]
  refine ⟨130495530129006384880451855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86997020086004256586967903 130495530129006384880451855)
  ·
    refine ⟨195743295193509577320677783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130495530129006384880451855 195743295193509577320677783)
    ·
      refine ⟨293614942790264365981016675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195743295193509577320677783 293614942790264365981016675)
      ·
        refine ⟨440422414185396548971525013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293614942790264365981016675 440422414185396548971525013)
        ·
          refine ⟨20644800664940463233040235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 440422414185396548971525013 20644800664940463233040235)
          ·
            refine ⟨30967200997410694849560353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20644800664940463233040235 30967200997410694849560353)
            ·
              refine ⟨23225400748058021137170265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30967200997410694849560353 23225400748058021137170265)
              ·
                refine ⟨17419050561043515852877699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23225400748058021137170265 17419050561043515852877699)
                ·
                  refine ⟨26128575841565273779316549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17419050561043515852877699 26128575841565273779316549)
                  ·
                    refine ⟨4899107970293488833621853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26128575841565273779316549 4899107970293488833621853)
                    ·
                      refine ⟨1837165488860058312608195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4899107970293488833621853 1837165488860058312608195)
                      ·
                        rfl

theorem cell23_3577867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 3].length) (baseStart_3577867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577867 prefixEnd_3577867 := by exact prefixLift 3577867
  have htrace : WordTrace (prefixWord ++ tailWord_3577867) baseStart_3577867 baseEnd_3577867 := by
    simpa [prefixWord, tailWord_3577867, baseEnd_3577867] using wordTrace_append hprefix tailTrace_3577867
  have hstable : (prefixWord ++ tailWord_3577867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577867).length < 2 ^ (prefixWord ++ tailWord_3577867).sum := by decide
  have hdescent : baseEnd_3577867 < baseStart_3577867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577884 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_3577884 : Nat := 118140960795 + 3577884 * 2 ^ 59
def prefixEnd_3577884 : Nat := 4983230072969 + 3 ^ 40 * 3577884 * 2
def baseEnd_3577884 : Nat := 1837174218031184746095617

theorem tailTrace_3577884 : CollatzResearch.WordTrace tailWord_3577884 prefixEnd_3577884 1837174218031184746095617 := by
  unfold tailWord_3577884
  simp only [CollatzResearch.WordTrace]
  refine ⟨65248075084972398391910353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86997433446629864522547137 65248075084972398391910353)
  ·
    refine ⟨48936056313729298793932765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65248075084972398391910353 48936056313729298793932765)
    ·
      refine ⟨18351021117648487047724787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48936056313729298793932765 18351021117648487047724787)
      ·
        refine ⟨27526531676472730571587181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18351021117648487047724787 27526531676472730571587181)
        ·
          refine ⟨10322449378677273964345193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27526531676472730571587181 10322449378677273964345193)
          ·
            refine ⟨7741837034007955473258895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10322449378677273964345193 7741837034007955473258895)
            ·
              refine ⟨11612755551011933209888343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7741837034007955473258895 11612755551011933209888343)
              ·
                refine ⟨17419133326517899814832515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11612755551011933209888343 17419133326517899814832515)
                ·
                  refine ⟨26128699989776849722248773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17419133326517899814832515 26128699989776849722248773)
                  ·
                    refine ⟨4899131248083159322921645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26128699989776849722248773 4899131248083159322921645)
                    ·
                      refine ⟨1837174218031184746095617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4899131248083159322921645 1837174218031184746095617)
                      ·
                        rfl

theorem cell23_3577884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_3577884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577884 prefixEnd_3577884 := by exact prefixLift 3577884
  have htrace : WordTrace (prefixWord ++ tailWord_3577884) baseStart_3577884 baseEnd_3577884 := by
    simpa [prefixWord, tailWord_3577884, baseEnd_3577884] using wordTrace_append hprefix tailTrace_3577884
  have hstable : (prefixWord ++ tailWord_3577884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577884).length < 2 ^ (prefixWord ++ tailWord_3577884).sum := by decide
  have hdescent : baseEnd_3577884 < baseStart_3577884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577891 : List Nat := [1, 1, 1, 4, 3, 1, 4, 3, 1, 4]
def baseStart_3577891 : Nat := 118140960795 + 3577891 * 2 ^ 59
def prefixEnd_3577891 : Nat := 4983230072969 + 3 ^ 40 * 3577891 * 2
def baseEnd_3577891 : Nat := 612392604131922072902695

theorem tailTrace_3577891 : CollatzResearch.WordTrace tailWord_3577891 prefixEnd_3577891 612392604131922072902695 := by
  unfold tailWord_3577891
  simp only [CollatzResearch.WordTrace]
  refine ⟨130496405480919436979325527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86997603653946291319550351 130496405480919436979325527)
  ·
    refine ⟨195744608221379155468988291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130496405480919436979325527 195744608221379155468988291)
    ·
      refine ⟨293616912332068733203482437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195744608221379155468988291 293616912332068733203482437)
      ·
        refine ⟨55053171062262887475652957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293616912332068733203482437 55053171062262887475652957)
        ·
          refine ⟨20644939148348582803369859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55053171062262887475652957 20644939148348582803369859)
          ·
            refine ⟨30967408722522874205054789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20644939148348582803369859 30967408722522874205054789)
            ·
              refine ⟨5806389135473038913447773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30967408722522874205054789 5806389135473038913447773)
              ·
                refine ⟨2177395925802389592542915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5806389135473038913447773 2177395925802389592542915)
                ·
                  refine ⟨3266093888703584388814373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2177395925802389592542915 3266093888703584388814373)
                  ·
                    refine ⟨612392604131922072902695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3266093888703584388814373 612392604131922072902695)
                    ·
                      rfl

theorem cell23_3577891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 1, 4].length) (baseStart_3577891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577891 prefixEnd_3577891 := by exact prefixLift 3577891
  have htrace : WordTrace (prefixWord ++ tailWord_3577891) baseStart_3577891 baseEnd_3577891 := by
    simpa [prefixWord, tailWord_3577891, baseEnd_3577891] using wordTrace_append hprefix tailTrace_3577891
  have hstable : (prefixWord ++ tailWord_3577891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577891).length < 2 ^ (prefixWord ++ tailWord_3577891).sum := by decide
  have hdescent : baseEnd_3577891 < baseStart_3577891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577904 : List Nat := [2, 1, 1, 1, 2, 7, 1, 2, 6]
def baseStart_3577904 : Nat := 118140960795 + 3577904 * 2 ^ 59
def prefixEnd_3577904 : Nat := 4983230072969 + 3 ^ 40 * 3577904 * 2
def baseEnd_3577904 : Nat := 204131609738252740871725

theorem tailTrace_3577904 : CollatzResearch.WordTrace tailWord_3577904 prefixEnd_3577904 204131609738252740871725 := by
  unfold tailWord_3577904
  simp only [CollatzResearch.WordTrace]
  refine ⟨65248439814936170099774383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86997919753248226799699177 65248439814936170099774383)
  ·
    refine ⟨97872659722404255149661575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65248439814936170099774383 97872659722404255149661575)
    ·
      refine ⟨146808989583606382724492363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97872659722404255149661575 146808989583606382724492363)
      ·
        refine ⟨220213484375409574086738545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146808989583606382724492363 220213484375409574086738545)
        ·
          refine ⟨165160113281557180565053909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220213484375409574086738545 165160113281557180565053909)
          ·
            refine ⟨3870940155036496419493451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 165160113281557180565053909 3870940155036496419493451)
            ·
              refine ⟨5806410232554744629240177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3870940155036496419493451 5806410232554744629240177)
              ·
                refine ⟨4354807674416058471930133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5806410232554744629240177 4354807674416058471930133)
                ·
                  refine ⟨204131609738252740871725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4354807674416058471930133 204131609738252740871725)
                  ·
                    rfl

theorem cell23_3577904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 6].length) (baseStart_3577904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577904 prefixEnd_3577904 := by exact prefixLift 3577904
  have htrace : WordTrace (prefixWord ++ tailWord_3577904) baseStart_3577904 baseEnd_3577904 := by
    simpa [prefixWord, tailWord_3577904, baseEnd_3577904] using wordTrace_append hprefix tailTrace_3577904
  have hstable : (prefixWord ++ tailWord_3577904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577904).length < 2 ^ (prefixWord ++ tailWord_3577904).sum := by decide
  have hdescent : baseEnd_3577904 < baseStart_3577904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577908 : List Nat := [2, 5, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_3577908 : Nat := 118140960795 + 3577908 * 2 ^ 59
def prefixEnd_3577908 : Nat := 4983230072969 + 3 ^ 40 * 3577908 * 2
def baseEnd_3577908 : Nat := 612395513855630884065169

theorem tailTrace_3577908 : CollatzResearch.WordTrace tailWord_3577908 prefixEnd_3577908 612395513855630884065169 := by
  unfold tailWord_3577908
  simp only [CollatzResearch.WordTrace]
  refine ⟨65248512760928924441347189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86998017014571899255129585 65248512760928924441347189)
  ·
    refine ⟨6117048071337086666376299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65248512760928924441347189 6117048071337086666376299)
    ·
      refine ⟨9175572107005629999564449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6117048071337086666376299 9175572107005629999564449)
      ·
        refine ⟨6881679080254222499673337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9175572107005629999564449 6881679080254222499673337)
        ·
          refine ⟨5161259310190666874755003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6881679080254222499673337 5161259310190666874755003)
          ·
            refine ⟨7741888965286000312132505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5161259310190666874755003 7741888965286000312132505)
            ·
              refine ⟨5806416723964500234099379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7741888965286000312132505 5806416723964500234099379)
              ·
                refine ⟨8709625085946750351149069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5806416723964500234099379 8709625085946750351149069)
                ·
                  refine ⟨3266109407230031381680901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8709625085946750351149069 3266109407230031381680901)
                  ·
                    refine ⟨612395513855630884065169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3266109407230031381680901 612395513855630884065169)
                    ·
                      rfl

theorem cell23_3577908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_3577908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577908 prefixEnd_3577908 := by exact prefixLift 3577908
  have htrace : WordTrace (prefixWord ++ tailWord_3577908) baseStart_3577908 baseEnd_3577908 := by
    simpa [prefixWord, tailWord_3577908, baseEnd_3577908] using wordTrace_append hprefix tailTrace_3577908
  have hstable : (prefixWord ++ tailWord_3577908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577908).length < 2 ^ (prefixWord ++ tailWord_3577908).sum := by decide
  have hdescent : baseEnd_3577908 < baseStart_3577908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577921 : List Nat := [1, 2, 5, 1, 2, 2, 3, 1, 6]
def baseStart_3577921 : Nat := 118140960795 + 3577921 * 2 ^ 59
def prefixEnd_3577921 : Nat := 4983230072969 + 3 ^ 40 * 3577921 * 2
def baseEnd_3577921 : Nat := 204132579646155677925883

theorem tailTrace_3577921 : CollatzResearch.WordTrace tailWord_3577921 prefixEnd_3577921 204132579646155677925883 := by
  unfold tailWord_3577921
  simp only [CollatzResearch.WordTrace]
  refine ⟨130497499670810752102917617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86998333113873834735278411 130497499670810752102917617)
  ·
    refine ⟨97873124753108064077188213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130497499670810752102917617 97873124753108064077188213)
    ·
      refine ⟨9175605445603881007236395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97873124753108064077188213 9175605445603881007236395)
      ·
        refine ⟨13763408168405821510854593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9175605445603881007236395 13763408168405821510854593)
        ·
          refine ⟨10322556126304366133140945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13763408168405821510854593 10322556126304366133140945)
          ·
            refine ⟨7741917094728274599855709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10322556126304366133140945 7741917094728274599855709)
            ·
              refine ⟨2903218910523102974945891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7741917094728274599855709 2903218910523102974945891)
              ·
                refine ⟨4354828365784654462418837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2903218910523102974945891 4354828365784654462418837)
                ·
                  refine ⟨204132579646155677925883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4354828365784654462418837 204132579646155677925883)
                  ·
                    rfl

theorem cell23_3577921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 6].length) (baseStart_3577921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577921 prefixEnd_3577921 := by exact prefixLift 3577921
  have htrace : WordTrace (prefixWord ++ tailWord_3577921) baseStart_3577921 baseEnd_3577921 := by
    simpa [prefixWord, tailWord_3577921, baseEnd_3577921] using wordTrace_append hprefix tailTrace_3577921
  have hstable : (prefixWord ++ tailWord_3577921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577921).length < 2 ^ (prefixWord ++ tailWord_3577921).sum := by decide
  have hdescent : baseEnd_3577921 < baseStart_3577921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577934 : List Nat := [4, 1, 1, 1, 1, 4, 1, 4, 1, 5]
def baseStart_3577934 : Nat := 118140960795 + 3577934 * 2 ^ 59
def prefixEnd_3577934 : Nat := 4983230072969 + 3 ^ 40 * 3577934 * 2
def baseEnd_3577934 : Nat := 612399964021303183490129

theorem tailTrace_3577934 : CollatzResearch.WordTrace tailWord_3577934 prefixEnd_3577934 612399964021303183490129 := by
  unfold tailWord_3577934
  simp only [CollatzResearch.WordTrace]
  refine ⟨16312246727470456915392607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86998649213175770215427237 16312246727470456915392607)
  ·
    refine ⟨24468370091205685373088911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16312246727470456915392607 24468370091205685373088911)
    ·
      refine ⟨36702555136808528059633367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24468370091205685373088911 36702555136808528059633367)
      ·
        refine ⟨55053832705212792089450051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36702555136808528059633367 55053832705212792089450051)
        ·
          refine ⟨82580749057819188134175077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55053832705212792089450051 82580749057819188134175077)
          ·
            refine ⟨15483890448341097775157827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82580749057819188134175077 15483890448341097775157827)
            ·
              refine ⟨23225835672511646662736741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15483890448341097775157827 23225835672511646662736741)
              ·
                refine ⟨4354844188595933749263139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23225835672511646662736741 4354844188595933749263139)
                ·
                  refine ⟨6532266282893900623894709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4354844188595933749263139 6532266282893900623894709)
                  ·
                    refine ⟨612399964021303183490129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6532266282893900623894709 612399964021303183490129)
                    ·
                      rfl

theorem cell23_3577934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_3577934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577934 prefixEnd_3577934 := by exact prefixLift 3577934
  have htrace : WordTrace (prefixWord ++ tailWord_3577934) baseStart_3577934 baseEnd_3577934 := by
    simpa [prefixWord, tailWord_3577934, baseEnd_3577934] using wordTrace_append hprefix tailTrace_3577934
  have hstable : (prefixWord ++ tailWord_3577934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577934).length < 2 ^ (prefixWord ++ tailWord_3577934).sum := by decide
  have hdescent : baseEnd_3577934 < baseStart_3577934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577942 : List Nat := [5, 2, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_3577942 : Nat := 118140960795 + 3577942 * 2 ^ 59
def prefixEnd_3577942 : Nat := 4983230072969 + 3 ^ 40 * 3577942 * 2
def baseEnd_3577942 : Nat := 612401333303048506390117

theorem tailTrace_3577942 : CollatzResearch.WordTrace tailWord_3577942 prefixEnd_3577942 612401333303048506390117 := by
  unfold tailWord_3577942
  simp only [CollatzResearch.WordTrace]
  refine ⟨8156141600233417043089505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86998843735823115126288053 8156141600233417043089505)
  ·
    refine ⟨6117106200175062782317129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8156141600233417043089505 6117106200175062782317129)
    ·
      refine ⟨4587829650131297086737847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6117106200175062782317129 4587829650131297086737847)
      ·
        refine ⟨6881744475196945630106771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4587829650131297086737847 6881744475196945630106771)
        ·
          refine ⟨10322616712795418445160157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6881744475196945630106771 10322616712795418445160157)
          ·
            refine ⟨3870981267298281916935059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10322616712795418445160157 3870981267298281916935059)
            ·
              refine ⟨5806471900947422875402589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3870981267298281916935059 5806471900947422875402589)
              ·
                refine ⟨2177426962855283578275971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5806471900947422875402589 2177426962855283578275971)
                ·
                  refine ⟨3266140444282925367413957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2177426962855283578275971 3266140444282925367413957)
                  ·
                    refine ⟨612401333303048506390117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3266140444282925367413957 612401333303048506390117)
                    ·
                      rfl

theorem cell23_3577942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_3577942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577942 prefixEnd_3577942 := by exact prefixLift 3577942
  have htrace : WordTrace (prefixWord ++ tailWord_3577942) baseStart_3577942 baseEnd_3577942 := by
    simpa [prefixWord, tailWord_3577942, baseEnd_3577942] using wordTrace_append hprefix tailTrace_3577942
  have hstable : (prefixWord ++ tailWord_3577942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577942).length < 2 ^ (prefixWord ++ tailWord_3577942).sum := by decide
  have hdescent : baseEnd_3577942 < baseStart_3577942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577964 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 4, 4]
def baseStart_3577964 : Nat := 118140960795 + 3577964 * 2 ^ 59
def prefixEnd_3577964 : Nat := 4983230072969 + 3 ^ 40 * 3577964 * 2
def baseEnd_3577964 : Nat := 612405098827848144365083

theorem tailTrace_3577964 : CollatzResearch.WordTrace tailWord_3577964 prefixEnd_3577964 612405098827848144365083 := by
  unfold tailWord_3577964
  simp only [CollatzResearch.WordTrace]
  refine ⟨65249534004827485223366473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86999378673103313631155297 65249534004827485223366473)
  ·
    refine ⟨48937150503620613917524855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65249534004827485223366473 48937150503620613917524855)
    ·
      refine ⟨73405725755430920876287283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48937150503620613917524855 73405725755430920876287283)
      ·
        refine ⟨110108588633146381314430925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73405725755430920876287283 110108588633146381314430925)
        ·
          refine ⟨41290720737429892992911597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110108588633146381314430925 41290720737429892992911597)
          ·
            refine ⟨15484020276536209872341849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41290720737429892992911597 15484020276536209872341849)
            ·
              refine ⟨11613015207402157404256387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15484020276536209872341849 11613015207402157404256387)
              ·
                refine ⟨17419522811103236106384581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11613015207402157404256387 17419522811103236106384581)
                ·
                  refine ⟨3266160527081856769947109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17419522811103236106384581 3266160527081856769947109)
                  ·
                    refine ⟨612405098827848144365083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3266160527081856769947109 612405098827848144365083)
                    ·
                      rfl

theorem cell23_3577964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_3577964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577964 prefixEnd_3577964 := by exact prefixLift 3577964
  have htrace : WordTrace (prefixWord ++ tailWord_3577964) baseStart_3577964 baseEnd_3577964 := by
    simpa [prefixWord, tailWord_3577964, baseEnd_3577964] using wordTrace_append hprefix tailTrace_3577964
  have hstable : (prefixWord ++ tailWord_3577964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577964).length < 2 ^ (prefixWord ++ tailWord_3577964).sum := by decide
  have hdescent : baseEnd_3577964 < baseStart_3577964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577965 : List Nat := [1, 5, 1, 1, 2, 1, 5, 2, 1, 1, 3]
def baseStart_3577965 : Nat := 118140960795 + 3577965 * 2 ^ 59
def prefixEnd_3577965 : Nat := 4983230072969 + 3 ^ 40 * 3577965 * 2
def baseEnd_3577965 : Nat := 1837215809964198929182745

theorem tailTrace_3577965 : CollatzResearch.WordTrace tailWord_3577965 prefixEnd_3577965 1837215809964198929182745 := by
  unfold tailWord_3577965
  simp only [CollatzResearch.WordTrace]
  refine ⟨130499104482651347617519349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86999402988434231745012899 130499104482651347617519349)
  ·
    refine ⟨12234291045248563839142439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130499104482651347617519349 12234291045248563839142439)
    ·
      refine ⟨18351436567872845758713659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12234291045248563839142439 18351436567872845758713659)
      ·
        refine ⟨27527154851809268638070489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18351436567872845758713659 27527154851809268638070489)
        ·
          refine ⟨20645366138856951478552867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27527154851809268638070489 20645366138856951478552867)
          ·
            refine ⟨30968049208285427217829301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20645366138856951478552867 30968049208285427217829301)
            ·
              refine ⟨2903254613276758801671497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30968049208285427217829301 2903254613276758801671497)
              ·
                refine ⟨2177440959957569101253623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2903254613276758801671497 2177440959957569101253623)
                ·
                  refine ⟨3266161439936353651880435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2177440959957569101253623 3266161439936353651880435)
                  ·
                    refine ⟨4899242159904530477820653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3266161439936353651880435 4899242159904530477820653)
                    ·
                      refine ⟨1837215809964198929182745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4899242159904530477820653 1837215809964198929182745)
                      ·
                        rfl

theorem cell23_3577965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_3577965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577965 prefixEnd_3577965 := by exact prefixLift 3577965
  have htrace : WordTrace (prefixWord ++ tailWord_3577965) baseStart_3577965 baseEnd_3577965 := by
    simpa [prefixWord, tailWord_3577965, baseEnd_3577965] using wordTrace_append hprefix tailTrace_3577965
  have hstable : (prefixWord ++ tailWord_3577965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577965).length < 2 ^ (prefixWord ++ tailWord_3577965).sum := by decide
  have hdescent : baseEnd_3577965 < baseStart_3577965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577967 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 6]
def baseStart_3577967 : Nat := 118140960795 + 3577967 * 2 ^ 59
def prefixEnd_3577967 : Nat := 4983230072969 + 3 ^ 40 * 3577967 * 2
def baseEnd_3577967 : Nat := 1837216836925507921357735

theorem tailTrace_3577967 : CollatzResearch.WordTrace tailWord_3577967 prefixEnd_3577967 1837216836925507921357735 := by
  unfold tailWord_3577967
  simp only [CollatzResearch.WordTrace]
  refine ⟨130499177428644101959092155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86999451619096067972728103 130499177428644101959092155)
  ·
    refine ⟨195748766142966152938638233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130499177428644101959092155 195748766142966152938638233)
    ·
      refine ⟨146811574607224614703978675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195748766142966152938638233 146811574607224614703978675)
      ·
        refine ⟨220217361910836922055968013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146811574607224614703978675 220217361910836922055968013)
        ·
          refine ⟨82581510716563845770988005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220217361910836922055968013 82581510716563845770988005)
          ·
            refine ⟨15484033259355721082060251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82581510716563845770988005 15484033259355721082060251)
            ·
              refine ⟨23226049889033581623090377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15484033259355721082060251 23226049889033581623090377)
              ·
                refine ⟨17419537416775186217317783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23226049889033581623090377 17419537416775186217317783)
                ·
                  refine ⟨26129306125162779325976675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17419537416775186217317783 26129306125162779325976675)
                  ·
                    refine ⟨39193959187744168988965013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26129306125162779325976675 39193959187744168988965013)
                    ·
                      refine ⟨1837216836925507921357735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39193959187744168988965013 1837216836925507921357735)
                      ·
                        rfl

theorem cell23_3577967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_3577967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577967 prefixEnd_3577967 := by exact prefixLift 3577967
  have htrace : WordTrace (prefixWord ++ tailWord_3577967) baseStart_3577967 baseEnd_3577967 := by
    simpa [prefixWord, tailWord_3577967, baseEnd_3577967] using wordTrace_append hprefix tailTrace_3577967
  have hstable : (prefixWord ++ tailWord_3577967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577967).length < 2 ^ (prefixWord ++ tailWord_3577967).sum := by decide
  have hdescent : baseEnd_3577967 < baseStart_3577967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577977 : List Nat := [1, 2, 1, 3, 4, 1, 1, 10]
def baseStart_3577977 : Nat := 118140960795 + 3577977 * 2 ^ 59
def prefixEnd_3577977 : Nat := 4983230072969 + 3 ^ 40 * 3577977 * 2
def baseEnd_3577977 : Nat := 68045258212298254897507

theorem tailTrace_3577977 : CollatzResearch.WordTrace tailWord_3577977 prefixEnd_3577977 68045258212298254897507 := by
  unfold tailWord_3577977
  simp only [CollatzResearch.WordTrace]
  refine ⟨130499542158607873666956185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86999694772405249111304123 130499542158607873666956185)
  ·
    refine ⟨97874656618955905250217139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130499542158607873666956185 97874656618955905250217139)
    ·
      refine ⟨146811984928433857875325709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97874656618955905250217139 146811984928433857875325709)
      ·
        refine ⟨55054494348162696703247141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146811984928433857875325709 55054494348162696703247141)
        ·
          refine ⟨10322717690280505631858839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55054494348162696703247141 10322717690280505631858839)
          ·
            refine ⟨15484076535420758447788259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10322717690280505631858839 15484076535420758447788259)
            ·
              refine ⟨23226114803131137671682389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15484076535420758447788259 23226114803131137671682389)
              ·
                refine ⟨68045258212298254897507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23226114803131137671682389 68045258212298254897507)
                ·
                  rfl

theorem cell23_3577977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 10].length) (baseStart_3577977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577977 prefixEnd_3577977 := by exact prefixLift 3577977
  have htrace : WordTrace (prefixWord ++ tailWord_3577977) baseStart_3577977 baseEnd_3577977 := by
    simpa [prefixWord, tailWord_3577977, baseEnd_3577977] using wordTrace_append hprefix tailTrace_3577977
  have hstable : (prefixWord ++ tailWord_3577977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577977).length < 2 ^ (prefixWord ++ tailWord_3577977).sum := by decide
  have hdescent : baseEnd_3577977 < baseStart_3577977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577981 : List Nat := [1, 4, 1, 1, 3, 3, 1, 3, 2, 4]
def baseStart_3577981 : Nat := 118140960795 + 3577981 * 2 ^ 59
def prefixEnd_3577981 : Nat := 4983230072969 + 3 ^ 40 * 3577981 * 2
def baseEnd_3577981 : Nat := 612408008551556955527557

theorem tailTrace_3577981 : CollatzResearch.WordTrace tailWord_3577981 prefixEnd_3577981 612408008551556955527557 := by
  unfold tailWord_3577981
  simp only [CollatzResearch.WordTrace]
  refine ⟨130499688050593382350101797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86999792033728921566734531 130499688050593382350101797)
  ·
    refine ⟨24468691509486259190644087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130499688050593382350101797 24468691509486259190644087)
    ·
      refine ⟨36703037264229388785966131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24468691509486259190644087 36703037264229388785966131)
      ·
        refine ⟨55054555896344083178949197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36703037264229388785966131 55054555896344083178949197)
        ·
          refine ⟨20645458461129031192105949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55054555896344083178949197 20645458461129031192105949)
          ·
            refine ⟨7742046922923386697039731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20645458461129031192105949 7742046922923386697039731)
            ·
              refine ⟨11613070384385080045559597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7742046922923386697039731 11613070384385080045559597)
              ·
                refine ⟨4354901394144405017084849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11613070384385080045559597 4354901394144405017084849)
                ·
                  refine ⟨3266176045608303762813637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4354901394144405017084849 3266176045608303762813637)
                  ·
                    refine ⟨612408008551556955527557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3266176045608303762813637 612408008551556955527557)
                    ·
                      rfl

theorem cell23_3577981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_3577981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577981 prefixEnd_3577981 := by exact prefixLift 3577981
  have htrace : WordTrace (prefixWord ++ tailWord_3577981) baseStart_3577981 baseEnd_3577981 := by
    simpa [prefixWord, tailWord_3577981, baseEnd_3577981] using wordTrace_append hprefix tailTrace_3577981
  have hstable : (prefixWord ++ tailWord_3577981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577981).length < 2 ^ (prefixWord ++ tailWord_3577981).sum := by decide
  have hdescent : baseEnd_3577981 < baseStart_3577981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577991 : List Nat := [1, 1, 4, 2, 1, 1, 5, 2, 1, 2, 3]
def baseStart_3577991 : Nat := 118140960795 + 3577991 * 2 ^ 59
def prefixEnd_3577991 : Nat := 4983230072969 + 3 ^ 40 * 3577991 * 2
def baseEnd_3577991 : Nat := 1837229160461215827457625

theorem tailTrace_3577991 : CollatzResearch.WordTrace tailWord_3577991 prefixEnd_3577991 1837229160461215827457625 := by
  unfold tailWord_3577991
  simp only [CollatzResearch.WordTrace]
  refine ⟨130500052780557154057965827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87000035187038102705310551 130500052780557154057965827)
  ·
    refine ⟨195750079170835731086948741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130500052780557154057965827 195750079170835731086948741)
    ·
      refine ⟨36703139844531699578802889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195750079170835731086948741 36703139844531699578802889)
      ·
        refine ⟨27527354883398774684102167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36703139844531699578802889 27527354883398774684102167)
        ·
          refine ⟨41291032325098162026153251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27527354883398774684102167 41291032325098162026153251)
          ·
            refine ⟨61936548487647243039229877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41291032325098162026153251 61936548487647243039229877)
            ·
              refine ⟨5806551420716929034927801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61936548487647243039229877 5806551420716929034927801)
              ·
                refine ⟨4354913565537696776195851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5806551420716929034927801 4354913565537696776195851)
                ·
                  refine ⟨6532370348306545164293777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4354913565537696776195851 6532370348306545164293777)
                  ·
                    refine ⟨4899277761229908873220333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6532370348306545164293777 4899277761229908873220333)
                    ·
                      refine ⟨1837229160461215827457625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4899277761229908873220333 1837229160461215827457625)
                      ·
                        rfl

theorem cell23_3577991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_3577991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577991 prefixEnd_3577991 := by exact prefixLift 3577991
  have htrace : WordTrace (prefixWord ++ tailWord_3577991) baseStart_3577991 baseEnd_3577991 := by
    simpa [prefixWord, tailWord_3577991, baseEnd_3577991] using wordTrace_append hprefix tailTrace_3577991
  have hstable : (prefixWord ++ tailWord_3577991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577991).length < 2 ^ (prefixWord ++ tailWord_3577991).sum := by decide
  have hdescent : baseEnd_3577991 < baseStart_3577991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578008 : List Nat := [2, 1, 2, 4, 4, 1, 1, 1, 1, 1, 5]
def baseStart_3578008 : Nat := 118140960795 + 3578008 * 2 ^ 59
def prefixEnd_3578008 : Nat := 4983230072969 + 3 ^ 40 * 3578008 * 2
def baseEnd_3578008 : Nat := 1837237889632342260945047

theorem tailTrace_3578008 : CollatzResearch.WordTrace tailWord_3578008 prefixEnd_3578008 1837237889632342260945047 := by
  unfold tailWord_3578008
  simp only [CollatzResearch.WordTrace]
  refine ⟨65250336410747782980667339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87000448547663710640889785 65250336410747782980667339)
  ·
    refine ⟨97875504616121674471001009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65250336410747782980667339 97875504616121674471001009)
    ·
      refine ⟨73406628462091255853250757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97875504616121674471001009 73406628462091255853250757)
      ·
        refine ⟨13763742836642110472484517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73406628462091255853250757 13763742836642110472484517)
        ·
          refine ⟨2580701781870395713590847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13763742836642110472484517 2580701781870395713590847)
          ·
            refine ⟨3871052672805593570386271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2580701781870395713590847 3871052672805593570386271)
            ·
              refine ⟨5806579009208390355579407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3871052672805593570386271 5806579009208390355579407)
              ·
                refine ⟨8709868513812585533369111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5806579009208390355579407 8709868513812585533369111)
                ·
                  refine ⟨13064802770718878300053667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8709868513812585533369111 13064802770718878300053667)
                  ·
                    refine ⟨19597204156078317450080501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13064802770718878300053667 19597204156078317450080501)
                    ·
                      refine ⟨1837237889632342260945047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19597204156078317450080501 1837237889632342260945047)
                      ·
                        rfl

theorem cell23_3578008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_3578008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578008 prefixEnd_3578008 := by exact prefixLift 3578008
  have htrace : WordTrace (prefixWord ++ tailWord_3578008) baseStart_3578008 baseEnd_3578008 := by
    simpa [prefixWord, tailWord_3578008, baseEnd_3578008] using wordTrace_append hprefix tailTrace_3578008
  have hstable : (prefixWord ++ tailWord_3578008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578008).length < 2 ^ (prefixWord ++ tailWord_3578008).sum := by decide
  have hdescent : baseEnd_3578008 < baseStart_3578008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578074 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4]
def baseStart_3578074 : Nat := 118140960795 + 3578074 * 2 ^ 59
def prefixEnd_3578074 : Nat := 4983230072969 + 3 ^ 40 * 3578074 * 2
def baseEnd_3578074 : Nat := 1837271779355539002719743

theorem tailTrace_3578074 : CollatzResearch.WordTrace tailWord_3578074 prefixEnd_3578074 1837271779355539002719743 := by
  unfold tailWord_3578074
  simp only [CollatzResearch.WordTrace]
  refine ⟨32625770009814114808309319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87002053359504306155491517 32625770009814114808309319)
  ·
    refine ⟨48938655014721172212463979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32625770009814114808309319 48938655014721172212463979)
    ·
      refine ⟨73407982522081758318695969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48938655014721172212463979 73407982522081758318695969)
      ·
        refine ⟨55055986891561318739021977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73407982522081758318695969 55055986891561318739021977)
        ·
          refine ⟨41291990168670989054266483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55055986891561318739021977 41291990168670989054266483)
          ·
            refine ⟨61937985253006483581399725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41291990168670989054266483 61937985253006483581399725)
            ·
              refine ⟨23226744469877431343024897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61937985253006483581399725 23226744469877431343024897)
              ·
                refine ⟨17420058352408073507268673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23226744469877431343024897 17420058352408073507268673)
                ·
                  refine ⟨13065043764306055130451505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17420058352408073507268673 13065043764306055130451505)
                  ·
                    refine ⟨9798782823229541347838629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13065043764306055130451505 9798782823229541347838629)
                    ·
                      refine ⟨1837271779355539002719743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9798782823229541347838629 1837271779355539002719743)
                      ·
                        rfl

theorem cell23_3578074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_3578074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578074 prefixEnd_3578074 := by exact prefixLift 3578074
  have htrace : WordTrace (prefixWord ++ tailWord_3578074) baseStart_3578074 baseEnd_3578074 := by
    simpa [prefixWord, tailWord_3578074, baseEnd_3578074] using wordTrace_append hprefix tailTrace_3578074
  have hstable : (prefixWord ++ tailWord_3578074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578074).length < 2 ^ (prefixWord ++ tailWord_3578074).sum := by decide
  have hdescent : baseEnd_3578074 < baseStart_3578074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578124 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 1, 2, 5]
def baseStart_3578124 : Nat := 118140960795 + 3578124 * 2 ^ 59
def prefixEnd_3578124 : Nat := 4983230072969 + 3 ^ 40 * 3578124 * 2
def baseEnd_3578124 : Nat := 1837297453388263807094513

theorem tailTrace_3578124 : CollatzResearch.WordTrace tailWord_3578124 prefixEnd_3578124 1837297453388263807094513 := by
  unfold tailWord_3578124
  simp only [CollatzResearch.WordTrace]
  refine ⟨65252451844537658886278713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87003269126050211848371617 65252451844537658886278713)
  ·
    refine ⟨48939338883403244164709035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65252451844537658886278713 48939338883403244164709035)
    ·
      refine ⟨73409008325104866247063553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48939338883403244164709035 73409008325104866247063553)
      ·
        refine ⟨55056756243828649685297665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73409008325104866247063553 55056756243828649685297665)
        ·
          refine ⟨41292567182871487263973249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55056756243828649685297665 41292567182871487263973249)
          ·
            refine ⟨30969425387153615447979937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41292567182871487263973249 30969425387153615447979937)
            ·
              refine ⟨23227069040365211585984953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30969425387153615447979937 23227069040365211585984953)
              ·
                refine ⟨17420301780273908689488715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23227069040365211585984953 17420301780273908689488715)
                ·
                  refine ⟨26130452670410863034233073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17420301780273908689488715 26130452670410863034233073)
                  ·
                    refine ⟨19597839502808147275674805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26130452670410863034233073 19597839502808147275674805)
                    ·
                      refine ⟨1837297453388263807094513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19597839502808147275674805 1837297453388263807094513)
                      ·
                        rfl

theorem cell23_3578124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_3578124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578124 prefixEnd_3578124 := by exact prefixLift 3578124
  have htrace : WordTrace (prefixWord ++ tailWord_3578124) baseStart_3578124 baseEnd_3578124 := by
    simpa [prefixWord, tailWord_3578124, baseEnd_3578124] using wordTrace_append hprefix tailTrace_3578124
  have hstable : (prefixWord ++ tailWord_3578124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578124).length < 2 ^ (prefixWord ++ tailWord_3578124).sum := by decide
  have hdescent : baseEnd_3578124 < baseStart_3578124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578221 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_3578221 : Nat := 118140960795 + 3578221 * 2 ^ 59
def prefixEnd_3578221 : Nat := 4983230072969 + 3 ^ 40 * 3578221 * 2
def baseEnd_3578221 : Nat := 612449087003916642527189

theorem tailTrace_3578221 : CollatzResearch.WordTrace tailWord_3578221 prefixEnd_3578221 612449087003916642527189 := by
  unfold tailWord_3578221
  simp only [CollatzResearch.WordTrace]
  refine ⟨130508441569723903338838517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87005627713149268892559011 130508441569723903338838517)
  ·
    refine ⟨12235166397161615938016111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130508441569723903338838517 12235166397161615938016111)
    ·
      refine ⟨18352749595742423907024167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12235166397161615938016111 18352749595742423907024167)
      ·
        refine ⟨27529124393613635860536251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18352749595742423907024167 27529124393613635860536251)
        ·
          refine ⟨41293686590420453790804377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27529124393613635860536251 41293686590420453790804377)
          ·
            refine ⟨30970264942815340343103283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41293686590420453790804377 30970264942815340343103283)
            ·
              refine ⟨46455397414223010514654925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30970264942815340343103283 46455397414223010514654925)
              ·
                refine ⟨17420774030333628942995597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46455397414223010514654925 17420774030333628942995597)
                ·
                  refine ⟨6532790261375110853623349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17420774030333628942995597 6532790261375110853623349)
                  ·
                    refine ⟨612449087003916642527189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6532790261375110853623349 612449087003916642527189)
                    ·
                      rfl

theorem cell23_3578221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_3578221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578221 prefixEnd_3578221 := by exact prefixLift 3578221
  have htrace : WordTrace (prefixWord ++ tailWord_3578221) baseStart_3578221 baseEnd_3578221 := by
    simpa [prefixWord, tailWord_3578221, baseEnd_3578221] using wordTrace_append hprefix tailTrace_3578221
  have hstable : (prefixWord ++ tailWord_3578221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578221).length < 2 ^ (prefixWord ++ tailWord_3578221).sum := by decide
  have hdescent : baseEnd_3578221 < baseStart_3578221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578235 : List Nat := [1, 1, 1, 1, 1, 7, 1, 5, 1, 1, 3]
def baseStart_3578235 : Nat := 118140960795 + 3578235 * 2 ^ 59
def prefixEnd_3578235 : Nat := 4983230072969 + 3 ^ 40 * 3578235 * 2
def baseEnd_3578235 : Nat := 1837354449740912872806503

theorem tailTrace_3578235 : CollatzResearch.WordTrace tailWord_3578235 prefixEnd_3578235 1837354449740912872806503 := by
  unfold tailWord_3578235
  simp only [CollatzResearch.WordTrace]
  refine ⟨130508952191673183729848159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87005968127782122486565439 130508952191673183729848159)
  ·
    refine ⟨195763428287509775594772239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130508952191673183729848159 195763428287509775594772239)
    ·
      refine ⟨293645142431264663392158359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195763428287509775594772239 293645142431264663392158359)
      ·
        refine ⟨440467713646896995088237539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293645142431264663392158359 440467713646896995088237539)
        ·
          refine ⟨660701570470345492632356309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440467713646896995088237539 660701570470345492632356309)
          ·
            refine ⟨15485193057898722483570851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 660701570470345492632356309 15485193057898722483570851)
            ·
              refine ⟨23227789586848083725356277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15485193057898722483570851 23227789586848083725356277)
              ·
                refine ⟨2177605273767007849252151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23227789586848083725356277 2177605273767007849252151)
                ·
                  refine ⟨3266407910650511773878227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2177605273767007849252151 3266407910650511773878227)
                  ·
                    refine ⟨4899611865975767660817341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3266407910650511773878227 4899611865975767660817341)
                    ·
                      refine ⟨1837354449740912872806503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4899611865975767660817341 1837354449740912872806503)
                      ·
                        rfl

theorem cell23_3578235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 1, 1, 3].length) (baseStart_3578235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578235 prefixEnd_3578235 := by exact prefixLift 3578235
  have htrace : WordTrace (prefixWord ++ tailWord_3578235) baseStart_3578235 baseEnd_3578235 := by
    simpa [prefixWord, tailWord_3578235, baseEnd_3578235] using wordTrace_append hprefix tailTrace_3578235
  have hstable : (prefixWord ++ tailWord_3578235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578235).length < 2 ^ (prefixWord ++ tailWord_3578235).sum := by decide
  have hdescent : baseEnd_3578235 < baseStart_3578235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578242 : List Nat := [3, 4, 2, 1, 2, 2, 1, 2, 6]
def baseStart_3578242 : Nat := 118140960795 + 3578242 * 2 ^ 59
def prefixEnd_3578242 : Nat := 4983230072969 + 3 ^ 40 * 3578242 * 2
def baseEnd_3578242 : Nat := 204150893789499371713219

theorem tailTrace_3578242 : CollatzResearch.WordTrace tailWord_3578242 prefixEnd_3578242 204150893789499371713219 := by
  unfold tailWord_3578242
  simp only [CollatzResearch.WordTrace]
  refine ⟨32627301875661955981338245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87006138335098549283568653 32627301875661955981338245)
  ·
    refine ⟨6117619101686616746500921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32627301875661955981338245 6117619101686616746500921)
    ·
      refine ⟨4588214326264962559875691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6117619101686616746500921 4588214326264962559875691)
      ·
        refine ⟨6882321489397443839813537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4588214326264962559875691 6882321489397443839813537)
        ·
          refine ⟨5161741117048082879860153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6882321489397443839813537 5161741117048082879860153)
          ·
            refine ⟨3871305837786062159895115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5161741117048082879860153 3871305837786062159895115)
            ·
              refine ⟨5806958756679093239842673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3871305837786062159895115 5806958756679093239842673)
              ·
                refine ⟨4355219067509319929882005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5806958756679093239842673 4355219067509319929882005)
                ·
                  refine ⟨204150893789499371713219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4355219067509319929882005 204150893789499371713219)
                  ·
                    rfl

theorem cell23_3578242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_3578242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578242 prefixEnd_3578242 := by exact prefixLift 3578242
  have htrace : WordTrace (prefixWord ++ tailWord_3578242) baseStart_3578242 baseEnd_3578242 := by
    simpa [prefixWord, tailWord_3578242, baseEnd_3578242] using wordTrace_append hprefix tailTrace_3578242
  have hstable : (prefixWord ++ tailWord_3578242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578242).length < 2 ^ (prefixWord ++ tailWord_3578242).sum := by decide
  have hdescent : baseEnd_3578242 < baseStart_3578242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578271 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 6]
def baseStart_3578271 : Nat := 118140960795 + 3578271 * 2 ^ 59
def prefixEnd_3578271 : Nat := 4983230072969 + 3 ^ 40 * 3578271 * 2
def baseEnd_3578271 : Nat := 1837372935044474731956337

theorem tailTrace_3578271 : CollatzResearch.WordTrace tailWord_3578271 prefixEnd_3578271 1837372935044474731956337 := by
  unfold tailWord_3578271
  simp only [CollatzResearch.WordTrace]
  refine ⟨130510265219542761878158667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87006843479695174585439111 130510265219542761878158667)
  ·
    refine ⟨195765397829314142817238001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130510265219542761878158667 195765397829314142817238001)
    ·
      refine ⟨146824048371985607112928501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195765397829314142817238001 146824048371985607112928501)
      ·
        refine ⟨13764754534873650666837047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146824048371985607112928501 13764754534873650666837047)
        ·
          refine ⟨20647131802310476000255571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13764754534873650666837047 20647131802310476000255571)
          ·
            refine ⟨30970697703465714000383357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20647131802310476000255571 30970697703465714000383357)
            ·
              refine ⟨11614011638799642750143759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30970697703465714000383357 11614011638799642750143759)
              ·
                refine ⟨17421017458199464125215639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11614011638799642750143759 17421017458199464125215639)
                ·
                  refine ⟨26131526187299196187823459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17421017458199464125215639 26131526187299196187823459)
                  ·
                    refine ⟨39197289280948794281735189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26131526187299196187823459 39197289280948794281735189)
                    ·
                      refine ⟨1837372935044474731956337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39197289280948794281735189 1837372935044474731956337)
                      ·
                        rfl

theorem cell23_3578271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_3578271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578271 prefixEnd_3578271 := by exact prefixLift 3578271
  have htrace : WordTrace (prefixWord ++ tailWord_3578271) baseStart_3578271 baseEnd_3578271 := by
    simpa [prefixWord, tailWord_3578271, baseEnd_3578271] using wordTrace_append hprefix tailTrace_3578271
  have hstable : (prefixWord ++ tailWord_3578271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578271).length < 2 ^ (prefixWord ++ tailWord_3578271).sum := by decide
  have hdescent : baseEnd_3578271 < baseStart_3578271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578275 : List Nat := [1, 1, 1, 4, 1, 4, 2, 2, 3, 2, 2]
def baseStart_3578275 : Nat := 118140960795 + 3578275 * 2 ^ 59
def prefixEnd_3578275 : Nat := 4983230072969 + 3 ^ 40 * 3578275 * 2
def baseEnd_3578275 : Nat := 1837374988967092716306319

theorem tailTrace_3578275 : CollatzResearch.WordTrace tailWord_3578275 prefixEnd_3578275 1837374988967092716306319 := by
  unfold tailWord_3578275
  simp only [CollatzResearch.WordTrace]
  refine ⟨130510411111528270561304279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87006940741018847040869519 130510411111528270561304279)
  ·
    refine ⟨195765616667292405841956419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130510411111528270561304279 195765616667292405841956419)
    ·
      refine ⟨293648425000938608762934629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195765616667292405841956419 293648425000938608762934629)
      ·
        refine ⟨55059079687675989143050243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293648425000938608762934629 55059079687675989143050243)
        ·
          refine ⟨82588619531513983714575365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55059079687675989143050243 82588619531513983714575365)
          ·
            refine ⟨15485366162158871946482881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82588619531513983714575365 15485366162158871946482881)
            ·
              refine ⟨11614024621619153959862161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15485366162158871946482881 11614024621619153959862161)
              ·
                refine ⟨8710518466214365469896621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11614024621619153959862161 8710518466214365469896621)
                ·
                  refine ⟨3266444424830387051211233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8710518466214365469896621 3266444424830387051211233)
                  ·
                    refine ⟨2449833318622790288408425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3266444424830387051211233 2449833318622790288408425)
                    ·
                      refine ⟨1837374988967092716306319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2449833318622790288408425 1837374988967092716306319)
                      ·
                        rfl

theorem cell23_3578275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_3578275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578275 prefixEnd_3578275 := by exact prefixLift 3578275
  have htrace : WordTrace (prefixWord ++ tailWord_3578275) baseStart_3578275 baseEnd_3578275 := by
    simpa [prefixWord, tailWord_3578275, baseEnd_3578275] using wordTrace_append hprefix tailTrace_3578275
  have hstable : (prefixWord ++ tailWord_3578275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578275).length < 2 ^ (prefixWord ++ tailWord_3578275).sum := by decide
  have hdescent : baseEnd_3578275 < baseStart_3578275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578318 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2]
def baseStart_3578318 : Nat := 118140960795 + 3578318 * 2 ^ 59
def prefixEnd_3578318 : Nat := 4983230072969 + 3 ^ 40 * 3578318 * 2
def baseEnd_3578318 : Nat := 1837397068635236048068621

theorem tailTrace_3578318 : CollatzResearch.WordTrace tailWord_3578318 prefixEnd_3578318 1837397068635236048068621 := by
  unfold tailWord_3578318
  simp only [CollatzResearch.WordTrace]
  refine ⟨16313997431296561113139951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87007986300248325936746405 16313997431296561113139951)
  ·
    refine ⟨24470996146944841669709927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16313997431296561113139951 24470996146944841669709927)
    ·
      refine ⟨36706494220417262504564891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24470996146944841669709927 36706494220417262504564891)
      ·
        refine ⟨55059741330625893756847337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36706494220417262504564891 55059741330625893756847337)
        ·
          refine ⟨41294805997969420317635503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55059741330625893756847337 41294805997969420317635503)
          ·
            refine ⟨61942208996954130476453255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41294805997969420317635503 61942208996954130476453255)
            ·
              refine ⟨92913313495431195714679883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61942208996954130476453255 92913313495431195714679883)
              ·
                refine ⟨139369970243146793572019825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92913313495431195714679883 139369970243146793572019825)
                ·
                  refine ⟨104527477682360095179014869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139369970243146793572019825 104527477682360095179014869)
                  ·
                    refine ⟨2449862758180314730758161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 104527477682360095179014869 2449862758180314730758161)
                    ·
                      refine ⟨1837397068635236048068621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2449862758180314730758161 1837397068635236048068621)
                      ·
                        rfl

theorem cell23_3578318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_3578318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578318 prefixEnd_3578318 := by exact prefixLift 3578318
  have htrace : WordTrace (prefixWord ++ tailWord_3578318) baseStart_3578318 baseEnd_3578318 := by
    simpa [prefixWord, tailWord_3578318, baseEnd_3578318] using wordTrace_append hprefix tailTrace_3578318
  have hstable : (prefixWord ++ tailWord_3578318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578318).length < 2 ^ (prefixWord ++ tailWord_3578318).sum := by decide
  have hdescent : baseEnd_3578318 < baseStart_3578318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578335 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 3, 3, 2]
def baseStart_3578335 : Nat := 118140960795 + 3578335 * 2 ^ 59
def prefixEnd_3578335 : Nat := 4983230072969 + 3 ^ 40 * 3578335 * 2
def baseEnd_3578335 : Nat := 1837405797806362481556043

theorem tailTrace_3578335 : CollatzResearch.WordTrace tailWord_3578335 prefixEnd_3578335 1837405797806362481556043 := by
  unfold tailWord_3578335
  simp only [CollatzResearch.WordTrace]
  refine ⟨130512599491310900808488459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87008399660873933872325639 130512599491310900808488459)
  ·
    refine ⟨195768899236966351212732689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130512599491310900808488459 195768899236966351212732689)
    ·
      refine ⟨146826674427724763409549517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195768899236966351212732689 146826674427724763409549517)
      ·
        refine ⟨55060002910396786278581069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146826674427724763409549517 55060002910396786278581069)
        ·
          refine ⟨20647501091398794854467901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55060002910396786278581069 20647501091398794854467901)
          ·
            refine ⟨7742812909274548070425463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20647501091398794854467901 7742812909274548070425463)
            ·
              refine ⟨11614219363911822105638195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7742812909274548070425463 11614219363911822105638195)
              ·
                refine ⟨17421329045867733158457293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11614219363911822105638195 17421329045867733158457293)
                ·
                  refine ⟨6532998392200399934421485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17421329045867733158457293 6532998392200399934421485)
                  ·
                    refine ⟨2449874397075149975408057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6532998392200399934421485 2449874397075149975408057)
                    ·
                      refine ⟨1837405797806362481556043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2449874397075149975408057 1837405797806362481556043)
                      ·
                        rfl

theorem cell23_3578335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_3578335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578335 prefixEnd_3578335 := by exact prefixLift 3578335
  have htrace : WordTrace (prefixWord ++ tailWord_3578335) baseStart_3578335 baseEnd_3578335 := by
    simpa [prefixWord, tailWord_3578335, baseEnd_3578335] using wordTrace_append hprefix tailTrace_3578335
  have hstable : (prefixWord ++ tailWord_3578335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578335).length < 2 ^ (prefixWord ++ tailWord_3578335).sum := by decide
  have hdescent : baseEnd_3578335 < baseStart_3578335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578352 : List Nat := [2, 1, 1, 1, 3, 3, 5, 1, 1, 3, 2]
def baseStart_3578352 : Nat := 118140960795 + 3578352 * 2 ^ 59
def prefixEnd_3578352 : Nat := 4983230072969 + 3 ^ 40 * 3578352 * 2
def baseEnd_3578352 : Nat := 1837414526977488915043465

theorem tailTrace_3578352 : CollatzResearch.WordTrace tailWord_3578352 prefixEnd_3578352 1837414526977488915043465 := by
  unfold tailWord_3578352
  simp only [CollatzResearch.WordTrace]
  refine ⟨65256609766124656355928655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87008813021499541807904873 65256609766124656355928655)
  ·
    refine ⟨97884914649186984533892983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65256609766124656355928655 97884914649186984533892983)
    ·
      refine ⟨146827371973780476800839475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97884914649186984533892983 146827371973780476800839475)
      ·
        refine ⟨220241057960670715201259213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146827371973780476800839475 220241057960670715201259213)
        ·
          refine ⟨82590396735251518200472205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220241057960670715201259213 82590396735251518200472205)
          ·
            refine ⟨30971398775719319325177077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82590396735251518200472205 30971398775719319325177077)
            ·
              refine ⟨2903568635223686186735351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30971398775719319325177077 2903568635223686186735351)
              ·
                refine ⟨4355352952835529280103027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2903568635223686186735351 4355352952835529280103027)
                ·
                  refine ⟨6533029429253293920154541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4355352952835529280103027 6533029429253293920154541)
                  ·
                    refine ⟨2449886035969985220057953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6533029429253293920154541 2449886035969985220057953)
                    ·
                      refine ⟨1837414526977488915043465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2449886035969985220057953 1837414526977488915043465)
                      ·
                        rfl

theorem cell23_3578352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 1, 3, 2].length) (baseStart_3578352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578352 prefixEnd_3578352 := by exact prefixLift 3578352
  have htrace : WordTrace (prefixWord ++ tailWord_3578352) baseStart_3578352 baseEnd_3578352 := by
    simpa [prefixWord, tailWord_3578352, baseEnd_3578352] using wordTrace_append hprefix tailTrace_3578352
  have hstable : (prefixWord ++ tailWord_3578352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578352).length < 2 ^ (prefixWord ++ tailWord_3578352).sum := by decide
  have hdescent : baseEnd_3578352 < baseStart_3578352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578358 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_3578358 : Nat := 118140960795 + 3578358 * 2 ^ 59
def prefixEnd_3578358 : Nat := 4983230072969 + 3 ^ 40 * 3578358 * 2
def baseEnd_3578358 : Nat := 612472535953805297189479

theorem tailTrace_3578358 : CollatzResearch.WordTrace tailWord_3578358 prefixEnd_3578358 612472535953805297189479 := by
  unfold tailWord_3578358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8157089898139223483535983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87008958913485050491050485 8157089898139223483535983)
  ·
    refine ⟨12235634847208835225303975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8157089898139223483535983 12235634847208835225303975)
    ·
      refine ⟨18353452270813252837955963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12235634847208835225303975 18353452270813252837955963)
      ·
        refine ⟨27530178406219879256933945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18353452270813252837955963 27530178406219879256933945)
        ·
          refine ⟨20647633804664909442700459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27530178406219879256933945 20647633804664909442700459)
          ·
            refine ⟨30971450706997364164050689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20647633804664909442700459 30971450706997364164050689)
            ·
              refine ⟨23228588030248023123038017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30971450706997364164050689 23228588030248023123038017)
              ·
                refine ⟨17421441022686017342278513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23228588030248023123038017 17421441022686017342278513)
                ·
                  refine ⟨13066080767014513006708885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17421441022686017342278513 13066080767014513006708885)
                  ·
                    refine ⟨612472535953805297189479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13066080767014513006708885 612472535953805297189479)
                    ·
                      rfl

theorem cell23_3578358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_3578358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578358 prefixEnd_3578358 := by exact prefixLift 3578358
  have htrace : WordTrace (prefixWord ++ tailWord_3578358) baseStart_3578358 baseEnd_3578358 := by
    simpa [prefixWord, tailWord_3578358, baseEnd_3578358] using wordTrace_append hprefix tailTrace_3578358
  have hstable : (prefixWord ++ tailWord_3578358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578358).length < 2 ^ (prefixWord ++ tailWord_3578358).sum := by decide
  have hdescent : baseEnd_3578358 < baseStart_3578358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578371 : List Nat := [1, 1, 1, 3, 2, 1, 4, 3, 7]
def baseStart_3578371 : Nat := 118140960795 + 3578371 * 2 ^ 59
def prefixEnd_3578371 : Nat := 4983230072969 + 3 ^ 40 * 3578371 * 2
def baseEnd_3578371 : Nat := 204158253678880482300653

theorem tailTrace_3578371 : CollatzResearch.WordTrace tailWord_3578371 prefixEnd_3578371 204158253678880482300653 := by
  unfold tailWord_3578371
  simp only [CollatzResearch.WordTrace]
  refine ⟨130513912519180478956798967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87009275012786985971199311 130513912519180478956798967)
  ·
    refine ⟨195770868778770718435198451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130513912519180478956798967 195770868778770718435198451)
    ·
      refine ⟨293656303168156077652797677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195770868778770718435198451 293656303168156077652797677)
      ·
        refine ⟨110121113688058529119799129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293656303168156077652797677 110121113688058529119799129)
        ·
          refine ⟨82590835266043896839849347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110121113688058529119799129 82590835266043896839849347)
          ·
            refine ⟨123886252899065845259774021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82590835266043896839849347 123886252899065845259774021)
            ·
              refine ⟨23228672418574845986207629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123886252899065845259774021 23228672418574845986207629)
              ·
                refine ⟨8710752156965567244827861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23228672418574845986207629 8710752156965567244827861)
                ·
                  refine ⟨204158253678880482300653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8710752156965567244827861 204158253678880482300653)
                  ·
                    rfl

theorem cell23_3578371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 7].length) (baseStart_3578371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578371 prefixEnd_3578371 := by exact prefixLift 3578371
  have htrace : WordTrace (prefixWord ++ tailWord_3578371) baseStart_3578371 baseEnd_3578371 := by
    simpa [prefixWord, tailWord_3578371, baseEnd_3578371] using wordTrace_append hprefix tailTrace_3578371
  have hstable : (prefixWord ++ tailWord_3578371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578371).length < 2 ^ (prefixWord ++ tailWord_3578371).sum := by decide
  have hdescent : baseEnd_3578371 < baseStart_3578371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578378 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_3578378 : Nat := 118140960795 + 3578378 * 2 ^ 59
def prefixEnd_3578378 : Nat := 4983230072969 + 3 ^ 40 * 3578378 * 2
def baseEnd_3578378 : Nat := 1837427877474505813318345

theorem tailTrace_3578378 : CollatzResearch.WordTrace tailWord_3578378 prefixEnd_3578378 1837427877474505813318345 := by
  unfold tailWord_3578378
  simp only [CollatzResearch.WordTrace]
  refine ⟨32628541957538779788075947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87009445220103412768202525 32628541957538779788075947)
  ·
    refine ⟨48942812936308169682113921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32628541957538779788075947 48942812936308169682113921)
    ·
      refine ⟨36707109702231127261585441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48942812936308169682113921 36707109702231127261585441)
      ·
        refine ⟨27530332276673345446189081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36707109702231127261585441 27530332276673345446189081)
        ·
          refine ⟨20647749207505009084641811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27530332276673345446189081 20647749207505009084641811)
          ·
            refine ⟨30971623811257513626962717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20647749207505009084641811 30971623811257513626962717)
            ·
              refine ⟨11614358929221567610111019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30971623811257513626962717 11614358929221567610111019)
              ·
                refine ⟨17421538393832351415166529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11614358929221567610111019 17421538393832351415166529)
                ·
                  refine ⟨13066153795374263561374897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17421538393832351415166529 13066153795374263561374897)
                  ·
                    refine ⟨9799615346530697671031173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13066153795374263561374897 9799615346530697671031173)
                    ·
                      refine ⟨1837427877474505813318345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9799615346530697671031173 1837427877474505813318345)
                      ·
                        rfl

theorem cell23_3578378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_3578378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578378 prefixEnd_3578378 := by exact prefixLift 3578378
  have htrace : WordTrace (prefixWord ++ tailWord_3578378) baseStart_3578378 baseEnd_3578378 := by
    simpa [prefixWord, tailWord_3578378, baseEnd_3578378] using wordTrace_append hprefix tailTrace_3578378
  have hstable : (prefixWord ++ tailWord_3578378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578378).length < 2 ^ (prefixWord ++ tailWord_3578378).sum := by decide
  have hdescent : baseEnd_3578378 < baseStart_3578378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578382 : List Nat := [4, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2]
def baseStart_3578382 : Nat := 118140960795 + 3578382 * 2 ^ 59
def prefixEnd_3578382 : Nat := 4983230072969 + 3 ^ 40 * 3578382 * 2
def baseEnd_3578382 : Nat := 1837429931397123797668327

theorem tailTrace_3578382 : CollatzResearch.WordTrace tailWord_3578382 prefixEnd_3578382 1837429931397123797668327 := by
  unfold tailWord_3578382
  simp only [CollatzResearch.WordTrace]
  refine ⟨16314289215267578479431175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87009542481427085223632933 16314289215267578479431175)
  ·
    refine ⟨24471433822901367719146763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16314289215267578479431175 24471433822901367719146763)
    ·
      refine ⟨36707150734352051578720145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24471433822901367719146763 36707150734352051578720145)
      ·
        refine ⟨27530363050764038684040109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36707150734352051578720145 27530363050764038684040109)
        ·
          refine ⟨10323886144036514506515041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27530363050764038684040109 10323886144036514506515041)
          ·
            refine ⟨7742914608027385879886281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10323886144036514506515041 7742914608027385879886281)
            ·
              refine ⟨5807185956020539409914711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7742914608027385879886281 5807185956020539409914711)
              ·
                refine ⟨8710778934030809114872067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5807185956020539409914711 8710778934030809114872067)
                ·
                  refine ⟨13066168401046213672308101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8710778934030809114872067 13066168401046213672308101)
                  ·
                    refine ⟨2449906575196165063557769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13066168401046213672308101 2449906575196165063557769)
                    ·
                      refine ⟨1837429931397123797668327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2449906575196165063557769 1837429931397123797668327)
                      ·
                        rfl

theorem cell23_3578382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_3578382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578382 prefixEnd_3578382 := by exact prefixLift 3578382
  have htrace : WordTrace (prefixWord ++ tailWord_3578382) baseStart_3578382 baseEnd_3578382 := by
    simpa [prefixWord, tailWord_3578382, baseEnd_3578382] using wordTrace_append hprefix tailTrace_3578382
  have hstable : (prefixWord ++ tailWord_3578382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578382).length < 2 ^ (prefixWord ++ tailWord_3578382).sum := by decide
  have hdescent : baseEnd_3578382 < baseStart_3578382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578411 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 5]
def baseStart_3578411 : Nat := 118140960795 + 3578411 * 2 ^ 59
def prefixEnd_3578411 : Nat := 4983230072969 + 3 ^ 40 * 3578411 * 2
def baseEnd_3578411 : Nat := 1837444822336104184205693

theorem tailTrace_3578411 : CollatzResearch.WordTrace tailWord_3578411 prefixEnd_3578411 1837444822336104184205693 := by
  unfold tailWord_3578411
  simp only [CollatzResearch.WordTrace]
  refine ⟨130515371439035565788255087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87010247626023710525503391 130515371439035565788255087)
  ·
    refine ⟨195773057158553348682382631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130515371439035565788255087 195773057158553348682382631)
    ·
      refine ⟨293659585737830023023573947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195773057158553348682382631 293659585737830023023573947)
      ·
        refine ⟨440489378606745034535360921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293659585737830023023573947 440489378606745034535360921)
        ·
          refine ⟨330367033955058775901520691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440489378606745034535360921 330367033955058775901520691)
          ·
            refine ⟨495550550932588163852281037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330367033955058775901520691 495550550932588163852281037)
            ·
              refine ⟨185831456599720561444605389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 495550550932588163852281037 185831456599720561444605389)
              ·
                refine ⟨69686796224895210541727021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185831456599720561444605389 69686796224895210541727021)
                ·
                  refine ⟨26132548584335703953147633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69686796224895210541727021 26132548584335703953147633)
                  ·
                    refine ⟨19599411438251777964860725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26132548584335703953147633 19599411438251777964860725)
                    ·
                      refine ⟨1837444822336104184205693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19599411438251777964860725 1837444822336104184205693)
                      ·
                        rfl

theorem cell23_3578411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 5].length) (baseStart_3578411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578411 prefixEnd_3578411 := by exact prefixLift 3578411
  have htrace : WordTrace (prefixWord ++ tailWord_3578411) baseStart_3578411 baseEnd_3578411 := by
    simpa [prefixWord, tailWord_3578411, baseEnd_3578411] using wordTrace_append hprefix tailTrace_3578411
  have hstable : (prefixWord ++ tailWord_3578411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578411).length < 2 ^ (prefixWord ++ tailWord_3578411).sum := by decide
  have hdescent : baseEnd_3578411 < baseStart_3578411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578418 : List Nat := [3, 2, 1, 1, 2, 1, 2, 4, 2, 5]
def baseStart_3578418 : Nat := 118140960795 + 3578418 * 2 ^ 59
def prefixEnd_3578418 : Nat := 4983230072969 + 3 ^ 40 * 3578418 * 2
def baseEnd_3578418 : Nat := 612482805566895218939387

theorem tailTrace_3578418 : CollatzResearch.WordTrace tailWord_3578418 prefixEnd_3578418 612482805566895218939387 := by
  unfold tailWord_3578418
  simp only [CollatzResearch.WordTrace]
  refine ⟨32628906687502551495939977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87010417833340137322506605 32628906687502551495939977)
  ·
    refine ⟨24471680015626913621954983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32628906687502551495939977 24471680015626913621954983)
    ·
      refine ⟨36707520023440370432932475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24471680015626913621954983 36707520023440370432932475)
      ·
        refine ⟨55061280035160555649398713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36707520023440370432932475 55061280035160555649398713)
        ·
          refine ⟨41295960026370416737049035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55061280035160555649398713 41295960026370416737049035)
          ·
            refine ⟨61943940039555625105573553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41295960026370416737049035 61943940039555625105573553)
            ·
              refine ⟨46457955029666718829180165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61943940039555625105573553 46457955029666718829180165)
              ·
                refine ⟨8710866568062509780471281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46457955029666718829180165 8710866568062509780471281)
                ·
                  refine ⟨6533149926046882335353461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8710866568062509780471281 6533149926046882335353461)
                  ·
                    refine ⟨612482805566895218939387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6533149926046882335353461 612482805566895218939387)
                    ·
                      rfl

theorem cell23_3578418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_3578418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578418 prefixEnd_3578418 := by exact prefixLift 3578418
  have htrace : WordTrace (prefixWord ++ tailWord_3578418) baseStart_3578418 baseEnd_3578418 := by
    simpa [prefixWord, tailWord_3578418, baseEnd_3578418] using wordTrace_append hprefix tailTrace_3578418
  have hstable : (prefixWord ++ tailWord_3578418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578418).length < 2 ^ (prefixWord ++ tailWord_3578418).sum := by decide
  have hdescent : baseEnd_3578418 < baseStart_3578418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578422 : List Nat := [5, 1, 2, 1, 2, 1, 2, 4, 5]
def baseStart_3578422 : Nat := 118140960795 + 3578422 * 2 ^ 59
def prefixEnd_3578422 : Nat := 4983230072969 + 3 ^ 40 * 3578422 * 2
def baseEnd_3578422 : Nat := 204161163402589293463127

theorem tailTrace_3578422 : CollatzResearch.WordTrace tailWord_3578422 prefixEnd_3578422 204161163402589293463127 := by
  unfold tailWord_3578422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8157235790124732166681595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87010515094663809777937013 8157235790124732166681595)
  ·
    refine ⟨12235853685187098250022393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8157235790124732166681595 12235853685187098250022393)
    ·
      refine ⟨9176890263890323687516795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12235853685187098250022393 9176890263890323687516795)
      ·
        refine ⟨13765335395835485531275193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9176890263890323687516795 13765335395835485531275193)
        ·
          refine ⟨10324001546876614148456395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13765335395835485531275193 10324001546876614148456395)
          ·
            refine ⟨15486002320314921222684593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10324001546876614148456395 15486002320314921222684593)
            ·
              refine ⟨11614501740236190917013445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15486002320314921222684593 11614501740236190917013445)
              ·
                refine ⟨2177719076294285796940021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11614501740236190917013445 2177719076294285796940021)
                ·
                  refine ⟨204161163402589293463127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2177719076294285796940021 204161163402589293463127)
                  ·
                    rfl

theorem cell23_3578422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_3578422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578422 prefixEnd_3578422 := by exact prefixLift 3578422
  have htrace : WordTrace (prefixWord ++ tailWord_3578422) baseStart_3578422 baseEnd_3578422 := by
    simpa [prefixWord, tailWord_3578422, baseEnd_3578422] using wordTrace_append hprefix tailTrace_3578422
  have hstable : (prefixWord ++ tailWord_3578422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578422).length < 2 ^ (prefixWord ++ tailWord_3578422).sum := by decide
  have hdescent : baseEnd_3578422 < baseStart_3578422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578448 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 5, 4]
def baseStart_3578448 : Nat := 118140960795 + 3578448 * 2 ^ 59
def prefixEnd_3578448 : Nat := 4983230072969 + 3 ^ 40 * 3578448 * 2
def baseEnd_3578448 : Nat := 612487940373440179814341

theorem tailTrace_3578448 : CollatzResearch.WordTrace tailWord_3578448 prefixEnd_3578448 612487940373440179814341 := by
  unfold tailWord_3578448
  simp only [CollatzResearch.WordTrace]
  refine ⟨65258360469950760553675999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87011147293267680738234665 65258360469950760553675999)
  ·
    refine ⟨97887540704926140830513999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65258360469950760553675999 97887540704926140830513999)
    ·
      refine ⟨146831311057389211245770999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97887540704926140830513999 146831311057389211245770999)
      ·
        refine ⟨220246966586083816868656499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146831311057389211245770999 220246966586083816868656499)
        ·
          refine ⟨330370449879125725302984749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220246966586083816868656499 330370449879125725302984749)
          ·
            refine ⟨123888918704672146988619281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330370449879125725302984749 123888918704672146988619281)
            ·
              refine ⟨92916689028504110241464461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123888918704672146988619281 92916689028504110241464461)
              ·
                refine ⟨34843758385689041340549173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92916689028504110241464461 34843758385689041340549173)
                ·
                  refine ⟨3266602348658347625676485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34843758385689041340549173 3266602348658347625676485)
                  ·
                    refine ⟨612487940373440179814341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3266602348658347625676485 612487940373440179814341)
                    ·
                      rfl

theorem cell23_3578448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 5, 4].length) (baseStart_3578448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578448 prefixEnd_3578448 := by exact prefixLift 3578448
  have htrace : WordTrace (prefixWord ++ tailWord_3578448) baseStart_3578448 baseEnd_3578448 := by
    simpa [prefixWord, tailWord_3578448, baseEnd_3578448] using wordTrace_append hprefix tailTrace_3578448
  have hstable : (prefixWord ++ tailWord_3578448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578448).length < 2 ^ (prefixWord ++ tailWord_3578448).sum := by decide
  have hdescent : baseEnd_3578448 < baseStart_3578448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578472 : List Nat := [2, 1, 4, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_3578472 : Nat := 118140960795 + 3578472 * 2 ^ 59
def prefixEnd_3578472 : Nat := 4983230072969 + 3 ^ 40 * 3578472 * 2
def baseEnd_3578472 : Nat := 1837476144656028445542913

theorem tailTrace_3578472 : CollatzResearch.WordTrace tailWord_3578472 prefixEnd_3578472 1837476144656028445542913 := by
  unfold tailWord_3578472
  simp only [CollatzResearch.WordTrace]
  refine ⟨65258798145907286603112835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87011730861209715470817113 65258798145907286603112835)
  ·
    refine ⟨97888197218860929904669253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65258798145907286603112835 97888197218860929904669253)
    ·
      refine ⟨18354036978536424357125485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97888197218860929904669253 18354036978536424357125485)
      ·
        refine ⟨6882763866951159133922057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18354036978536424357125485 6882763866951159133922057)
        ·
          refine ⟨5162072900213369350441543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6882763866951159133922057 5162072900213369350441543)
          ·
            refine ⟨7743109350320054025662315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5162072900213369350441543 7743109350320054025662315)
            ·
              refine ⟨11614664025480081038493473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7743109350320054025662315 11614664025480081038493473)
              ·
                refine ⟨8710998019110060778870105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11614664025480081038493473 8710998019110060778870105)
                ·
                  refine ⟨6533248514332545584152579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8710998019110060778870105 6533248514332545584152579)
                  ·
                    refine ⟨9799872771498818376228869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6533248514332545584152579 9799872771498818376228869)
                    ·
                      refine ⟨1837476144656028445542913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9799872771498818376228869 1837476144656028445542913)
                      ·
                        rfl

theorem cell23_3578472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_3578472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578472 prefixEnd_3578472 := by exact prefixLift 3578472
  have htrace : WordTrace (prefixWord ++ tailWord_3578472) baseStart_3578472 baseEnd_3578472 := by
    simpa [prefixWord, tailWord_3578472, baseEnd_3578472] using wordTrace_append hprefix tailTrace_3578472
  have hstable : (prefixWord ++ tailWord_3578472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578472).length < 2 ^ (prefixWord ++ tailWord_3578472).sum := by decide
  have hdescent : baseEnd_3578472 < baseStart_3578472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578505 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 5, 1, 3]
def baseStart_3578505 : Nat := 118140960795 + 3578505 * 2 ^ 59
def prefixEnd_3578505 : Nat := 4983230072969 + 3 ^ 40 * 3578505 * 2
def baseEnd_3578505 : Nat := 1837493089517626816430261

theorem tailTrace_3578505 : CollatzResearch.WordTrace tailWord_3578505 prefixEnd_3578505 1837493089517626816430261 := by
  unfold tailWord_3578505
  simp only [CollatzResearch.WordTrace]
  refine ⟨130518799900695019842176969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87012533267130013228117979 130518799900695019842176969)
  ·
    refine ⟨97889099925521264881632727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130518799900695019842176969 97889099925521264881632727)
    ·
      refine ⟨146833649888281897322449091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97889099925521264881632727 146833649888281897322449091)
      ·
        refine ⟨220250474832422845983673637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146833649888281897322449091 220250474832422845983673637)
        ·
          refine ⟨41296964031079283621938807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220250474832422845983673637 41296964031079283621938807)
          ·
            refine ⟨61945446046618925432908211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41296964031079283621938807 61945446046618925432908211)
            ·
              refine ⟨92918169069928388149362317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61945446046618925432908211 92918169069928388149362317)
              ·
                refine ⟨34844313401223145556010869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92918169069928388149362317 34844313401223145556010869)
                ·
                  refine ⟨3266654381364669895876019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34844313401223145556010869 3266654381364669895876019)
                  ·
                    refine ⟨4899981572047004843814029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3266654381364669895876019 4899981572047004843814029)
                    ·
                      refine ⟨1837493089517626816430261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4899981572047004843814029 1837493089517626816430261)
                      ·
                        rfl

theorem cell23_3578505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 1, 3].length) (baseStart_3578505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578505 prefixEnd_3578505 := by exact prefixLift 3578505
  have htrace : WordTrace (prefixWord ++ tailWord_3578505) baseStart_3578505 baseEnd_3578505 := by
    simpa [prefixWord, tailWord_3578505, baseEnd_3578505] using wordTrace_append hprefix tailTrace_3578505
  have hstable : (prefixWord ++ tailWord_3578505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578505).length < 2 ^ (prefixWord ++ tailWord_3578505).sum := by decide
  have hdescent : baseEnd_3578505 < baseStart_3578505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578515 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 6, 3, 2]
def baseStart_3578515 : Nat := 118140960795 + 3578515 * 2 ^ 59
def prefixEnd_3578515 : Nat := 4983230072969 + 3 ^ 40 * 3578515 * 2
def baseEnd_3578515 : Nat := 1837498224324171777305215

theorem tailTrace_3578515 : CollatzResearch.WordTrace tailWord_3578515 prefixEnd_3578515 1837498224324171777305215 := by
  unfold tailWord_3578515
  simp only [CollatzResearch.WordTrace]
  refine ⟨130519164630658791550040999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87012776420439194366693999 130519164630658791550040999)
  ·
    refine ⟨195778746945988187325061499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130519164630658791550040999 195778746945988187325061499)
    ·
      refine ⟨293668120418982280987592249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195778746945988187325061499 293668120418982280987592249)
      ·
        refine ⟨220251090314236710740694187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293668120418982280987592249 220251090314236710740694187)
        ·
          refine ⟨330376635471355066111041281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220251090314236710740694187 330376635471355066111041281)
          ·
            refine ⟨247782476603516299583280961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330376635471355066111041281 247782476603516299583280961)
            ·
              refine ⟨185836857452637224687460721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247782476603516299583280961 185836857452637224687460721)
              ·
                refine ⟨139377643089477918515595541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185836857452637224687460721 139377643089477918515595541)
                ·
                  refine ⟨6533327019819277430418541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139377643089477918515595541 6533327019819277430418541)
                  ·
                    refine ⟨2449997632432229036406953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6533327019819277430418541 2449997632432229036406953)
                    ·
                      refine ⟨1837498224324171777305215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2449997632432229036406953 1837498224324171777305215)
                      ·
                        rfl

theorem cell23_3578515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 3, 2].length) (baseStart_3578515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578515 prefixEnd_3578515 := by exact prefixLift 3578515
  have htrace : WordTrace (prefixWord ++ tailWord_3578515) baseStart_3578515 baseEnd_3578515 := by
    simpa [prefixWord, tailWord_3578515, baseEnd_3578515] using wordTrace_append hprefix tailTrace_3578515
  have hstable : (prefixWord ++ tailWord_3578515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578515).length < 2 ^ (prefixWord ++ tailWord_3578515).sum := by decide
  have hdescent : baseEnd_3578515 < baseStart_3578515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578525 : List Nat := [1, 4, 2, 1, 1, 1, 2, 5, 1, 5]
def baseStart_3578525 : Nat := 118140960795 + 3578525 * 2 ^ 59
def prefixEnd_3578525 : Nat := 4983230072969 + 3 ^ 40 * 3578525 * 2
def baseEnd_3578525 : Nat := 612501119710238912726723

theorem tailTrace_3578525 : CollatzResearch.WordTrace tailWord_3578525 prefixEnd_3578525 612501119710238912726723 := by
  unfold tailWord_3578525
  simp only [CollatzResearch.WordTrace]
  refine ⟨130519529360622563257905029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87013019573748375505270019 130519529360622563257905029)
  ·
    refine ⟨24472411755116730610857193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130519529360622563257905029 24472411755116730610857193)
    ·
      refine ⟨18354308816337547958142895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24472411755116730610857193 18354308816337547958142895)
      ·
        refine ⟨27531463224506321937214343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18354308816337547958142895 27531463224506321937214343)
        ·
          refine ⟨41297194836759482905821515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27531463224506321937214343 41297194836759482905821515)
          ·
            refine ⟨61945792255139224358732273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41297194836759482905821515 61945792255139224358732273)
            ·
              refine ⟨46459344191354418269049205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61945792255139224358732273 46459344191354418269049205)
              ·
                refine ⟨4355563517939476712723363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46459344191354418269049205 4355563517939476712723363)
                ·
                  refine ⟨6533345276909215069085045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4355563517939476712723363 6533345276909215069085045)
                  ·
                    refine ⟨612501119710238912726723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6533345276909215069085045 612501119710238912726723)
                    ·
                      rfl

theorem cell23_3578525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_3578525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578525 prefixEnd_3578525 := by exact prefixLift 3578525
  have htrace : WordTrace (prefixWord ++ tailWord_3578525) baseStart_3578525 baseEnd_3578525 := by
    simpa [prefixWord, tailWord_3578525, baseEnd_3578525] using wordTrace_append hprefix tailTrace_3578525
  have hstable : (prefixWord ++ tailWord_3578525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578525).length < 2 ^ (prefixWord ++ tailWord_3578525).sum := by decide
  have hdescent : baseEnd_3578525 < baseStart_3578525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578532 : List Nat := [2, 3, 1, 2, 2, 1, 1, 4, 2, 3, 2]
def baseStart_3578532 : Nat := 118140960795 + 3578532 * 2 ^ 59
def prefixEnd_3578532 : Nat := 4983230072969 + 3 ^ 40 * 3578532 * 2
def baseEnd_3578532 : Nat := 1837506953495298210792637

theorem tailTrace_3578532 : CollatzResearch.WordTrace tailWord_3578532 prefixEnd_3578532 1837506953495298210792637 := by
  unfold tailWord_3578532
  simp only [CollatzResearch.WordTrace]
  refine ⟨65259892335798601726704925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87013189781064802302273233 65259892335798601726704925)
  ·
    refine ⟨24472459625924475647514347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65259892335798601726704925 24472459625924475647514347)
    ·
      refine ⟨36708689438886713471271521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24472459625924475647514347 36708689438886713471271521)
      ·
        refine ⟨27531517079165035103453641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36708689438886713471271521 27531517079165035103453641)
        ·
          refine ⟨20648637809373776327590231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27531517079165035103453641 20648637809373776327590231)
          ·
            refine ⟨30972956714060664491385347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20648637809373776327590231 30972956714060664491385347)
            ·
              refine ⟨46459435071090996737078021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30972956714060664491385347 46459435071090996737078021)
              ·
                refine ⟨8711144075829561888202129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46459435071090996737078021 8711144075829561888202129)
                ·
                  refine ⟨6533358056872171416151597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8711144075829561888202129 6533358056872171416151597)
                  ·
                    refine ⟨2450009271327064281056849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6533358056872171416151597 2450009271327064281056849)
                    ·
                      refine ⟨1837506953495298210792637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2450009271327064281056849 1837506953495298210792637)
                      ·
                        rfl

theorem cell23_3578532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_3578532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578532 prefixEnd_3578532 := by exact prefixLift 3578532
  have htrace : WordTrace (prefixWord ++ tailWord_3578532) baseStart_3578532 baseEnd_3578532 := by
    simpa [prefixWord, tailWord_3578532, baseEnd_3578532] using wordTrace_append hprefix tailTrace_3578532
  have hstable : (prefixWord ++ tailWord_3578532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578532).length < 2 ^ (prefixWord ++ tailWord_3578532).sum := by decide
  have hdescent : baseEnd_3578532 < baseStart_3578532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578542 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 3, 5]
def baseStart_3578542 : Nat := 118140960795 + 3578542 * 2 ^ 59
def prefixEnd_3578542 : Nat := 4983230072969 + 3 ^ 40 * 3578542 * 2
def baseEnd_3578542 : Nat := 612504029433947723889197

theorem tailTrace_3578542 : CollatzResearch.WordTrace tailWord_3578542 prefixEnd_3578542 612504029433947723889197 := by
  unfold tailWord_3578542
  simp only [CollatzResearch.WordTrace]
  refine ⟨16315018675195121895159235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87013432934373983440849253 16315018675195121895159235)
  ·
    refine ⟨24472528012792682842738853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16315018675195121895159235 24472528012792682842738853)
    ·
      refine ⟨4588599002398628033013535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24472528012792682842738853 4588599002398628033013535)
      ·
        refine ⟨6882898503597942049520303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4588599002398628033013535 6882898503597942049520303)
        ·
          refine ⟨10324347755396913074280455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6882898503597942049520303 10324347755396913074280455)
          ·
            refine ⟨15486521633095369611420683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10324347755396913074280455 15486521633095369611420683)
            ·
              refine ⟨23229782449643054417131025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15486521633095369611420683 23229782449643054417131025)
              ·
                refine ⟨17422336837232290812848269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23229782449643054417131025 17422336837232290812848269)
                ·
                  refine ⟨6533376313962109054818101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17422336837232290812848269 6533376313962109054818101)
                  ·
                    refine ⟨612504029433947723889197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6533376313962109054818101 612504029433947723889197)
                    ·
                      rfl

theorem cell23_3578542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_3578542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578542 prefixEnd_3578542 := by exact prefixLift 3578542
  have htrace : WordTrace (prefixWord ++ tailWord_3578542) baseStart_3578542 baseEnd_3578542 := by
    simpa [prefixWord, tailWord_3578542, baseEnd_3578542] using wordTrace_append hprefix tailTrace_3578542
  have hstable : (prefixWord ++ tailWord_3578542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578542).length < 2 ^ (prefixWord ++ tailWord_3578542).sum := by decide
  have hdescent : baseEnd_3578542 < baseStart_3578542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578596 : List Nat := [2, 3, 1, 1, 1, 4, 2, 4, 1, 2, 2]
def baseStart_3578596 : Nat := 118140960795 + 3578596 * 2 ^ 59
def prefixEnd_3578596 : Nat := 4983230072969 + 3 ^ 40 * 3578596 * 2
def baseEnd_3578596 : Nat := 1837539816257185960392343

theorem tailTrace_3578596 : CollatzResearch.WordTrace tailWord_3578596 prefixEnd_3578596 1837539816257185960392343 := by
  unfold tailWord_3578596
  simp only [CollatzResearch.WordTrace]
  refine ⟨65261059471682671191869821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87014745962243561589159761 65261059471682671191869821)
  ·
    refine ⟨24472897301881001696951183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65261059471682671191869821 24472897301881001696951183)
    ·
      refine ⟨36709345952821502545426775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24472897301881001696951183 36709345952821502545426775)
      ·
        refine ⟨55064018929232253818140163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36709345952821502545426775 55064018929232253818140163)
        ·
          refine ⟨82596028393848380727210245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55064018929232253818140163 82596028393848380727210245)
          ·
            refine ⟨15486755323846571386351921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82596028393848380727210245 15486755323846571386351921)
            ·
              refine ⟨11615066492884928539763941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15486755323846571386351921 11615066492884928539763941)
              ·
                refine ⟨2177824967415924101205739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11615066492884928539763941 2177824967415924101205739)
                ·
                  refine ⟨3266737451123886151808609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2177824967415924101205739 3266737451123886151808609)
                  ·
                    refine ⟨2450053088342914613856457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3266737451123886151808609 2450053088342914613856457)
                    ·
                      refine ⟨1837539816257185960392343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2450053088342914613856457 1837539816257185960392343)
                      ·
                        rfl

theorem cell23_3578596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 1, 2, 2].length) (baseStart_3578596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578596 prefixEnd_3578596 := by exact prefixLift 3578596
  have htrace : WordTrace (prefixWord ++ tailWord_3578596) baseStart_3578596 baseEnd_3578596 := by
    simpa [prefixWord, tailWord_3578596, baseEnd_3578596] using wordTrace_append hprefix tailTrace_3578596
  have hstable : (prefixWord ++ tailWord_3578596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578596).length < 2 ^ (prefixWord ++ tailWord_3578596).sum := by decide
  have hdescent : baseEnd_3578596 < baseStart_3578596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578613 : List Nat := [1, 3, 6, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3578613 : Nat := 118140960795 + 3578613 * 2 ^ 59
def prefixEnd_3578613 : Nat := 4983230072969 + 3 ^ 40 * 3578613 * 2
def baseEnd_3578613 : Nat := 1837548545428312393879765

theorem tailTrace_3578613 : CollatzResearch.WordTrace tailWord_3578613 prefixEnd_3578613 1837548545428312393879765 := by
  unfold tailWord_3578613
  simp only [CollatzResearch.WordTrace]
  refine ⟨130522738984303754287108493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87015159322869169524738995 130522738984303754287108493)
  ·
    refine ⟨48946027119113907857665685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130522738984303754287108493 48946027119113907857665685)
    ·
      refine ⟨2294345021208464430828079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48946027119113907857665685 2294345021208464430828079)
      ·
        refine ⟨3441517531812696646242119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2294345021208464430828079 3441517531812696646242119)
        ·
          refine ⟨5162276297719044969363179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3441517531812696646242119 5162276297719044969363179)
          ·
            refine ⟨7743414446578567454044769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5162276297719044969363179 7743414446578567454044769)
            ·
              refine ⟨5807560834933925590533577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7743414446578567454044769 5807560834933925590533577)
              ·
                refine ⟨4355670626200444192900183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5807560834933925590533577 4355670626200444192900183)
                ·
                  refine ⟨6533505939300666289350275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4355670626200444192900183 6533505939300666289350275)
                  ·
                    refine ⟨9800258908950999434025413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6533505939300666289350275 9800258908950999434025413)
                    ·
                      refine ⟨1837548545428312393879765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9800258908950999434025413 1837548545428312393879765)
                      ·
                        rfl

theorem cell23_3578613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3578613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578613 prefixEnd_3578613 := by exact prefixLift 3578613
  have htrace : WordTrace (prefixWord ++ tailWord_3578613) baseStart_3578613 baseEnd_3578613 := by
    simpa [prefixWord, tailWord_3578613, baseEnd_3578613] using wordTrace_append hprefix tailTrace_3578613
  have hstable : (prefixWord ++ tailWord_3578613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578613).length < 2 ^ (prefixWord ++ tailWord_3578613).sum := by decide
  have hdescent : baseEnd_3578613 < baseStart_3578613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578686 : List Nat := [4, 2, 1, 2, 3, 1, 1, 2, 1, 4, 2]
def baseStart_3578686 : Nat := 118140960795 + 3578686 * 2 ^ 59
def prefixEnd_3578686 : Nat := 4983230072969 + 3 ^ 40 * 3578686 * 2
def baseEnd_3578686 : Nat := 1837586029516090608266929

theorem tailTrace_3578686 : CollatzResearch.WordTrace tailWord_3578686 prefixEnd_3578686 1837586029516090608266929 := by
  unfold tailWord_3578686
  simp only [CollatzResearch.WordTrace]
  refine ⟨16315675189129910969314489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87016934342026191836343941 16315675189129910969314489)
  ·
    refine ⟨12236756391847433226985867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16315675189129910969314489 12236756391847433226985867)
    ·
      refine ⟨18355134587771149840478801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12236756391847433226985867 18355134587771149840478801)
      ·
        refine ⟨13766350940828362380359101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18355134587771149840478801 13766350940828362380359101)
        ·
          refine ⟨5162381602810635892634663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13766350940828362380359101 5162381602810635892634663)
          ·
            refine ⟨7743572404215953838951995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5162381602810635892634663 7743572404215953838951995)
            ·
              refine ⟨11615358606323930758427993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7743572404215953838951995 11615358606323930758427993)
              ·
                refine ⟨8711518954742948068820995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11615358606323930758427993 8711518954742948068820995)
                ·
                  refine ⟨13067278432114422103231493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8711518954742948068820995 13067278432114422103231493)
                  ·
                    refine ⟨2450114706021454144355905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13067278432114422103231493 2450114706021454144355905)
                    ·
                      refine ⟨1837586029516090608266929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2450114706021454144355905 1837586029516090608266929)
                      ·
                        rfl

theorem cell23_3578686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_3578686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578686 prefixEnd_3578686 := by exact prefixLift 3578686
  have htrace : WordTrace (prefixWord ++ tailWord_3578686) baseStart_3578686 baseEnd_3578686 := by
    simpa [prefixWord, tailWord_3578686, baseEnd_3578686] using wordTrace_append hprefix tailTrace_3578686
  have hstable : (prefixWord ++ tailWord_3578686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578686).length < 2 ^ (prefixWord ++ tailWord_3578686).sum := by decide
  have hdescent : baseEnd_3578686 < baseStart_3578686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578754 : List Nat := [3, 4, 2, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_3578754 : Nat := 118140960795 + 3578754 * 2 ^ 59
def prefixEnd_3578754 : Nat := 4983230072969 + 3 ^ 40 * 3578754 * 2
def baseEnd_3578754 : Nat := 1837620946200596342216617

theorem tailTrace_3578754 : CollatzResearch.WordTrace tailWord_3578754 prefixEnd_3578754 1837620946200596342216617 := by
  unfold tailWord_3578754
  simp only [CollatzResearch.WordTrace]
  refine ⟨32631970419198233841997829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87018587784528623578660877 32631970419198233841997829)
  ·
    refine ⟨6118494453599668845374593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32631970419198233841997829 6118494453599668845374593)
    ·
      refine ⟨4588870840199751634030945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6118494453599668845374593 4588870840199751634030945)
      ·
        refine ⟨3441653130149813725523209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4588870840199751634030945 3441653130149813725523209)
        ·
          refine ⟨2581239847612360294142407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3441653130149813725523209 2581239847612360294142407)
          ·
            refine ⟨3871859771418540441213611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2581239847612360294142407 3871859771418540441213611)
            ·
              refine ⟨5807789657127810661820417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3871859771418540441213611 5807789657127810661820417)
              ·
                refine ⟨4355842242845857996365313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5807789657127810661820417 4355842242845857996365313)
                ·
                  refine ⟨3266881682134393497273985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4355842242845857996365313 3266881682134393497273985)
                  ·
                    refine ⟨2450161261600795122955489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3266881682134393497273985 2450161261600795122955489)
                    ·
                      refine ⟨1837620946200596342216617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2450161261600795122955489 1837620946200596342216617)
                      ·
                        rfl

theorem cell23_3578754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_3578754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578754 prefixEnd_3578754 := by exact prefixLift 3578754
  have htrace : WordTrace (prefixWord ++ tailWord_3578754) baseStart_3578754 baseEnd_3578754 := by
    simpa [prefixWord, tailWord_3578754, baseEnd_3578754] using wordTrace_append hprefix tailTrace_3578754
  have hstable : (prefixWord ++ tailWord_3578754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578754).length < 2 ^ (prefixWord ++ tailWord_3578754).sum := by decide
  have hdescent : baseEnd_3578754 < baseStart_3578754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578755 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 6]
def baseStart_3578755 : Nat := 118140960795 + 3578755 * 2 ^ 59
def prefixEnd_3578755 : Nat := 4983230072969 + 3 ^ 40 * 3578755 * 2
def baseEnd_3578755 : Nat := 1837621459681250838304111

theorem tailTrace_3578755 : CollatzResearch.WordTrace tailWord_3578755 prefixEnd_3578755 1837621459681250838304111 := by
  unfold tailWord_3578755
  simp only [CollatzResearch.WordTrace]
  refine ⟨130527918149789312538777719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87018612099859541692518479 130527918149789312538777719)
  ·
    refine ⟨195791877224683968808166579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130527918149789312538777719 195791877224683968808166579)
    ·
      refine ⟨293687815837025953212249869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195791877224683968808166579 293687815837025953212249869)
      ·
        refine ⟨110132930938884732454593701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293687815837025953212249869 110132930938884732454593701)
        ·
          refine ⟨20649924551040887335236319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110132930938884732454593701 20649924551040887335236319)
          ·
            refine ⟨30974886826561331002854479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20649924551040887335236319 30974886826561331002854479)
            ·
              refine ⟨46462330239841996504281719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30974886826561331002854479 46462330239841996504281719)
              ·
                refine ⟨69693495359762994756422579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46462330239841996504281719 69693495359762994756422579)
                ·
                  refine ⟨104540243039644492134633869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69693495359762994756422579 104540243039644492134633869)
                  ·
                    refine ⟨39202591139866684550487701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104540243039644492134633869 39202591139866684550487701)
                    ·
                      refine ⟨1837621459681250838304111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39202591139866684550487701 1837621459681250838304111)
                      ·
                        rfl

theorem cell23_3578755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_3578755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578755 prefixEnd_3578755 := by exact prefixLift 3578755
  have htrace : WordTrace (prefixWord ++ tailWord_3578755) baseStart_3578755 baseEnd_3578755 := by
    simpa [prefixWord, tailWord_3578755, baseEnd_3578755] using wordTrace_append hprefix tailTrace_3578755
  have hstable : (prefixWord ++ tailWord_3578755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578755).length < 2 ^ (prefixWord ++ tailWord_3578755).sum := by decide
  have hdescent : baseEnd_3578755 < baseStart_3578755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578759 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 2, 4, 2]
def baseStart_3578759 : Nat := 118140960795 + 3578759 * 2 ^ 59
def prefixEnd_3578759 : Nat := 4983230072969 + 3 ^ 40 * 3578759 * 2
def baseEnd_3578759 : Nat := 1837623513603868822654093

theorem tailTrace_3578759 : CollatzResearch.WordTrace tailWord_3578759 prefixEnd_3578759 1837623513603868822654093 := by
  unfold tailWord_3578759
  simp only [CollatzResearch.WordTrace]
  refine ⟨130528064041774821221923331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87018709361183214147948887 130528064041774821221923331)
  ·
    refine ⟨195792096062662231832884997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130528064041774821221923331 195792096062662231832884997)
    ·
      refine ⟨36711018011749168468665937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195792096062662231832884997 36711018011749168468665937)
      ·
        refine ⟨27533263508811876351499453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36711018011749168468665937 27533263508811876351499453)
        ·
          refine ⟨10324973815804453631812295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27533263508811876351499453 10324973815804453631812295)
          ·
            refine ⟨15487460723706680447718443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10324973815804453631812295 15487460723706680447718443)
            ·
              refine ⟨23231191085560020671577665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15487460723706680447718443 23231191085560020671577665)
              ·
                refine ⟨17423393314170015503683249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23231191085560020671577665 17423393314170015503683249)
                ·
                  refine ⟨13067544985627511627762437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17423393314170015503683249 13067544985627511627762437)
                  ·
                    refine ⟨2450164684805158430205457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13067544985627511627762437 2450164684805158430205457)
                    ·
                      refine ⟨1837623513603868822654093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2450164684805158430205457 1837623513603868822654093)
                      ·
                        rfl

theorem cell23_3578759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_3578759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578759 prefixEnd_3578759 := by exact prefixLift 3578759
  have htrace : WordTrace (prefixWord ++ tailWord_3578759) baseStart_3578759 baseEnd_3578759 := by
    simpa [prefixWord, tailWord_3578759, baseEnd_3578759] using wordTrace_append hprefix tailTrace_3578759
  have hstable : (prefixWord ++ tailWord_3578759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578759).length < 2 ^ (prefixWord ++ tailWord_3578759).sum := by decide
  have hdescent : baseEnd_3578759 < baseStart_3578759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578772 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_3578772 : Nat := 118140960795 + 3578772 * 2 ^ 59
def prefixEnd_3578772 : Nat := 4983230072969 + 3 ^ 40 * 3578772 * 2
def baseEnd_3578772 : Nat := 1837630188852377271791533

theorem tailTrace_3578772 : CollatzResearch.WordTrace tailWord_3578772 prefixEnd_3578772 1837630188852377271791533 := by
  unfold tailWord_3578772
  simp only [CollatzResearch.WordTrace]
  refine ⟨65264269095363862221073285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87019025460485149628097713 65264269095363862221073285)
  ·
    refine ⟨12237050455380724166451241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65264269095363862221073285 12237050455380724166451241)
    ·
      refine ⟨9177787841535543124838431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12237050455380724166451241 9177787841535543124838431)
      ·
        refine ⟨13766681762303314687257647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9177787841535543124838431 13766681762303314687257647)
        ·
          refine ⟨20650022643454972030886471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13766681762303314687257647 20650022643454972030886471)
          ·
            refine ⟨30975033965182458046329707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20650022643454972030886471 30975033965182458046329707)
            ·
              refine ⟨46462550947773687069494561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30975033965182458046329707 46462550947773687069494561)
              ·
                refine ⟨34846913210830265302120921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46462550947773687069494561 34846913210830265302120921)
                ·
                  refine ⟨26135184908122698976590691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34846913210830265302120921 26135184908122698976590691)
                  ·
                    refine ⟨39202777362184048464886037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26135184908122698976590691 39202777362184048464886037)
                    ·
                      refine ⟨1837630188852377271791533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39202777362184048464886037 1837630188852377271791533)
                      ·
                        rfl

theorem cell23_3578772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_3578772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578772 prefixEnd_3578772 := by exact prefixLift 3578772
  have htrace : WordTrace (prefixWord ++ tailWord_3578772) baseStart_3578772 baseEnd_3578772 := by
    simpa [prefixWord, tailWord_3578772, baseEnd_3578772] using wordTrace_append hprefix tailTrace_3578772
  have hstable : (prefixWord ++ tailWord_3578772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578772).length < 2 ^ (prefixWord ++ tailWord_3578772).sum := by decide
  have hdescent : baseEnd_3578772 < baseStart_3578772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578819 : List Nat := [1, 1, 1, 3, 1, 1, 2, 6, 2, 3, 2]
def baseStart_3578819 : Nat := 118140960795 + 3578819 * 2 ^ 59
def prefixEnd_3578819 : Nat := 4983230072969 + 3 ^ 40 * 3578819 * 2
def baseEnd_3578819 : Nat := 1837654322443138587903817

theorem tailTrace_3578819 : CollatzResearch.WordTrace tailWord_3578819 prefixEnd_3578819 1837654322443138587903817 := by
  unfold tailWord_3578819
  simp only [CollatzResearch.WordTrace]
  refine ⟨130530252421557451469107511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87020168281038300979405007 130530252421557451469107511)
  ·
    refine ⟨195795378632336177203661267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130530252421557451469107511 195795378632336177203661267)
    ·
      refine ⟨293693067948504265805491901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195795378632336177203661267 293693067948504265805491901)
      ·
        refine ⟨110134900480689099677059463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293693067948504265805491901 110134900480689099677059463)
        ·
          refine ⟨165202350721033649515589195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110134900480689099677059463 165202350721033649515589195)
          ·
            refine ⟨247803526081550474273383793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165202350721033649515589195 247803526081550474273383793)
            ·
              refine ⟨185852644561162855705037845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247803526081550474273383793 185852644561162855705037845)
              ·
                refine ⟨8711842713804508861173649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 185852644561162855705037845 8711842713804508861173649)
                ·
                  refine ⟨6533882035353381645880237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8711842713804508861173649 6533882035353381645880237)
                  ·
                    refine ⟨2450205763257518117205089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6533882035353381645880237 2450205763257518117205089)
                    ·
                      refine ⟨1837654322443138587903817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2450205763257518117205089 1837654322443138587903817)
                      ·
                        rfl

theorem cell23_3578819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 3, 2].length) (baseStart_3578819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578819 prefixEnd_3578819 := by exact prefixLift 3578819
  have htrace : WordTrace (prefixWord ++ tailWord_3578819) baseStart_3578819 baseEnd_3578819 := by
    simpa [prefixWord, tailWord_3578819, baseEnd_3578819] using wordTrace_append hprefix tailTrace_3578819
  have hstable : (prefixWord ++ tailWord_3578819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578819).length < 2 ^ (prefixWord ++ tailWord_3578819).sum := by decide
  have hdescent : baseEnd_3578819 < baseStart_3578819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578820 : List Nat := [2, 3, 3, 3, 2, 1, 1, 1, 3, 4]
def baseStart_3578820 : Nat := 118140960795 + 3578820 * 2 ^ 59
def prefixEnd_3578820 : Nat := 4983230072969 + 3 ^ 40 * 3578820 * 2
def baseEnd_3578820 : Nat := 612551611974597694663771

theorem tailTrace_3578820 : CollatzResearch.WordTrace tailWord_3578820 prefixEnd_3578820 612551611974597694663771 := by
  unfold tailWord_3578820
  simp only [CollatzResearch.WordTrace]
  refine ⟨65265144447276914319946957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87020192596369219093262609 65265144447276914319946957)
  ·
    refine ⟨24474429167728842869980109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65265144447276914319946957 24474429167728842869980109)
    ·
      refine ⟨9177910937898316076242541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24474429167728842869980109 9177910937898316076242541)
      ·
        refine ⟨3441716601711868528590953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9177910937898316076242541 3441716601711868528590953)
        ·
          refine ⟨2581287451283901396443215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3441716601711868528590953 2581287451283901396443215)
          ·
            refine ⟨3871931176925852094664823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2581287451283901396443215 3871931176925852094664823)
            ·
              refine ⟨5807896765388778141997235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3871931176925852094664823 5807896765388778141997235)
              ·
                refine ⟨8711845148083167212995853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5807896765388778141997235 8711845148083167212995853)
                ·
                  refine ⟨3266941930531187704873445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8711845148083167212995853 3266941930531187704873445)
                  ·
                    refine ⟨612551611974597694663771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3266941930531187704873445 612551611974597694663771)
                    ·
                      rfl

theorem cell23_3578820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_3578820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578820 prefixEnd_3578820 := by exact prefixLift 3578820
  have htrace : WordTrace (prefixWord ++ tailWord_3578820) baseStart_3578820 baseEnd_3578820 := by
    simpa [prefixWord, tailWord_3578820, baseEnd_3578820] using wordTrace_append hprefix tailTrace_3578820
  have hstable : (prefixWord ++ tailWord_3578820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578820).length < 2 ^ (prefixWord ++ tailWord_3578820).sum := by decide
  have hdescent : baseEnd_3578820 < baseStart_3578820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578825 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 2, 10]
def baseStart_3578825 : Nat := 118140960795 + 3578825 * 2 ^ 59
def prefixEnd_3578825 : Nat := 4983230072969 + 3 ^ 40 * 3578825 * 2
def baseEnd_3578825 : Nat := 612552467775688521476263

theorem tailTrace_3578825 : CollatzResearch.WordTrace tailWord_3578825 prefixEnd_3578825 612552467775688521476263 := by
  unfold tailWord_3578825
  simp only [CollatzResearch.WordTrace]
  refine ⟨130530471259535714493825929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87020314173023809662550619 130530471259535714493825929)
  ·
    refine ⟨97897853444651785870369447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130530471259535714493825929 97897853444651785870369447)
    ·
      refine ⟨146846780166977678805554171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97897853444651785870369447 146846780166977678805554171)
      ·
        refine ⟨220270170250466518208331257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146846780166977678805554171 220270170250466518208331257)
        ·
          refine ⟨165202627687849888656248443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220270170250466518208331257 165202627687849888656248443)
          ·
            refine ⟨247803941531774832984372665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165202627687849888656248443 247803941531774832984372665)
            ·
              refine ⟨185852956148831124738279499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247803941531774832984372665 185852956148831124738279499)
              ·
                refine ⟨278779434223246687107419249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185852956148831124738279499 278779434223246687107419249)
                ·
                  refine ⟨209084575667435015330564437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278779434223246687107419249 209084575667435015330564437)
                  ·
                    refine ⟨612552467775688521476263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 209084575667435015330564437 612552467775688521476263)
                    ·
                      rfl

theorem cell23_3578825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 10].length) (baseStart_3578825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578825 prefixEnd_3578825 := by exact prefixLift 3578825
  have htrace : WordTrace (prefixWord ++ tailWord_3578825) baseStart_3578825 baseEnd_3578825 := by
    simpa [prefixWord, tailWord_3578825, baseEnd_3578825] using wordTrace_append hprefix tailTrace_3578825
  have hstable : (prefixWord ++ tailWord_3578825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578825).length < 2 ^ (prefixWord ++ tailWord_3578825).sum := by decide
  have hdescent : baseEnd_3578825 < baseStart_3578825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578832 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 4]
def baseStart_3578832 : Nat := 118140960795 + 3578832 * 2 ^ 59
def prefixEnd_3578832 : Nat := 4983230072969 + 3 ^ 40 * 3578832 * 2
def baseEnd_3578832 : Nat := 1837660997691647037041257

theorem tailTrace_3578832 : CollatzResearch.WordTrace tailWord_3578832 prefixEnd_3578832 1837660997691647037041257 := by
  unfold tailWord_3578832
  simp only [CollatzResearch.WordTrace]
  refine ⟨65265363285255177344665375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87020484380340236459553833 65265363285255177344665375)
  ·
    refine ⟨97898044927882766016998063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65265363285255177344665375 97898044927882766016998063)
    ·
      refine ⟨146847067391824149025497095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97898044927882766016998063 146847067391824149025497095)
      ·
        refine ⟨220270601087736223538245643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146847067391824149025497095 220270601087736223538245643)
        ·
          refine ⟨330405901631604335307368465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220270601087736223538245643 330405901631604335307368465)
          ·
            refine ⟨247804426223703251480526349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330405901631604335307368465 247804426223703251480526349)
            ·
              refine ⟨92926659833888719305197381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247804426223703251480526349 92926659833888719305197381)
              ·
                refine ⟨17423748718854134869724509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92926659833888719305197381 17423748718854134869724509)
                ·
                  refine ⟨6533905769570300576146691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17423748718854134869724509 6533905769570300576146691)
                  ·
                    refine ⟨9800858654355450864220037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6533905769570300576146691 9800858654355450864220037)
                    ·
                      refine ⟨1837660997691647037041257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9800858654355450864220037 1837660997691647037041257)
                      ·
                        rfl

theorem cell23_3578832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 4].length) (baseStart_3578832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578832 prefixEnd_3578832 := by exact prefixLift 3578832
  have htrace : WordTrace (prefixWord ++ tailWord_3578832) baseStart_3578832 baseEnd_3578832 := by
    simpa [prefixWord, tailWord_3578832, baseEnd_3578832] using wordTrace_append hprefix tailTrace_3578832
  have hstable : (prefixWord ++ tailWord_3578832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578832).length < 2 ^ (prefixWord ++ tailWord_3578832).sum := by decide
  have hdescent : baseEnd_3578832 < baseStart_3578832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578876 : List Nat := [2, 2, 2, 1, 2, 4, 2, 2, 2, 4]
def baseStart_3578876 : Nat := 118140960795 + 3578876 * 2 ^ 59
def prefixEnd_3578876 : Nat := 4983230072969 + 3 ^ 40 * 3578876 * 2
def baseEnd_3578876 : Nat := 612561196946814954963685

theorem tailTrace_3578876 : CollatzResearch.WordTrace tailWord_3578876 prefixEnd_3578876 612561196946814954963685 := by
  unfold tailWord_3578876
  simp only [CollatzResearch.WordTrace]
  refine ⟨65266165691175475101966241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87021554254900633469288321 65266165691175475101966241)
  ·
    refine ⟨48949624268381606326474681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65266165691175475101966241 48949624268381606326474681)
    ·
      refine ⟨36712218201286204744856011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48949624268381606326474681 36712218201286204744856011)
      ·
        refine ⟨55068327301929307117284017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36712218201286204744856011 55068327301929307117284017)
        ·
          refine ⟨41301245476446980337963013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55068327301929307117284017 41301245476446980337963013)
          ·
            refine ⟨7743983526833808813368065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41301245476446980337963013 7743983526833808813368065)
            ·
              refine ⟨5807987645125356610026049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7743983526833808813368065 5807987645125356610026049)
              ·
                refine ⟨4355990733844017457519537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5807987645125356610026049 4355990733844017457519537)
                ·
                  refine ⟨3266993050383013093139653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4355990733844017457519537 3266993050383013093139653)
                  ·
                    refine ⟨612561196946814954963685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3266993050383013093139653 612561196946814954963685)
                    ·
                      rfl

theorem cell23_3578876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_3578876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578876 prefixEnd_3578876 := by exact prefixLift 3578876
  have htrace : WordTrace (prefixWord ++ tailWord_3578876) baseStart_3578876 baseEnd_3578876 := by
    simpa [prefixWord, tailWord_3578876, baseEnd_3578876] using wordTrace_append hprefix tailTrace_3578876
  have hstable : (prefixWord ++ tailWord_3578876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578876).length < 2 ^ (prefixWord ++ tailWord_3578876).sum := by decide
  have hdescent : baseEnd_3578876 < baseStart_3578876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578899 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 6, 1, 3]
def baseStart_3578899 : Nat := 118140960795 + 3578899 * 2 ^ 59
def prefixEnd_3578899 : Nat := 4983230072969 + 3 ^ 40 * 3578899 * 2
def baseEnd_3578899 : Nat := 1837695400895498274903449

theorem tailTrace_3578899 : CollatzResearch.WordTrace tailWord_3578899 prefixEnd_3578899 1837695400895498274903449 := by
  unfold tailWord_3578899
  simp only [CollatzResearch.WordTrace]
  refine ⟨130533170261267625132019751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87022113507511750088013167 130533170261267625132019751)
  ·
    refine ⟨195799755391901437698029627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130533170261267625132019751 195799755391901437698029627)
    ·
      refine ⟨293699633087852156547044441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195799755391901437698029627 293699633087852156547044441)
      ·
        refine ⟨220274724815889117410283331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293699633087852156547044441 220274724815889117410283331)
        ·
          refine ⟨330412087223833676115424997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220274724815889117410283331 330412087223833676115424997)
          ·
            refine ⟨61952266354468814271642187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 330412087223833676115424997 61952266354468814271642187)
            ·
              refine ⟨92928399531703221407463281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61952266354468814271642187 92928399531703221407463281)
              ·
                refine ⟨69696299648777416055597461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92928399531703221407463281 69696299648777416055597461)
                ·
                  refine ⟨3267014046036441377606131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69696299648777416055597461 3267014046036441377606131)
                  ·
                    refine ⟨4900521069054662066409197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3267014046036441377606131 4900521069054662066409197)
                    ·
                      refine ⟨1837695400895498274903449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4900521069054662066409197 1837695400895498274903449)
                      ·
                        rfl

theorem cell23_3578899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 1, 3].length) (baseStart_3578899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578899 prefixEnd_3578899 := by exact prefixLift 3578899
  have htrace : WordTrace (prefixWord ++ tailWord_3578899) baseStart_3578899 baseEnd_3578899 := by
    simpa [prefixWord, tailWord_3578899, baseEnd_3578899] using wordTrace_append hprefix tailTrace_3578899
  have hstable : (prefixWord ++ tailWord_3578899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578899).length < 2 ^ (prefixWord ++ tailWord_3578899).sum := by decide
  have hdescent : baseEnd_3578899 < baseStart_3578899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578916 : List Nat := [2, 3, 1, 4, 1, 1, 2, 2, 1, 3, 3]
def baseStart_3578916 : Nat := 118140960795 + 3578916 * 2 ^ 59
def prefixEnd_3578916 : Nat := 4983230072969 + 3 ^ 40 * 3578916 * 2
def baseEnd_3578916 : Nat := 1837704130066624708390871

theorem tailTrace_3578916 : CollatzResearch.WordTrace tailWord_3578916 prefixEnd_3578916 1837704130066624708390871 := by
  unfold tailWord_3578916
  simp only [CollatzResearch.WordTrace]
  refine ⟨65266895151103018517694301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87022526868137358023592401 65266895151103018517694301)
  ·
    refine ⟨24475085681663631944135363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65266895151103018517694301 24475085681663631944135363)
    ·
      refine ⟨36712628522495447916203045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24475085681663631944135363 36712628522495447916203045)
      ·
        refine ⟨6883617847967896484288071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36712628522495447916203045 6883617847967896484288071)
        ·
          refine ⟨10325426771951844726432107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6883617847967896484288071 10325426771951844726432107)
          ·
            refine ⟨15488140157927767089648161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10325426771951844726432107 15488140157927767089648161)
            ·
              refine ⟨11616105118445825317236121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15488140157927767089648161 11616105118445825317236121)
              ·
                refine ⟨8712078838834368987927091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11616105118445825317236121 8712078838834368987927091)
                ·
                  refine ⟨13068118258251553481890637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8712078838834368987927091 13068118258251553481890637)
                  ·
                    refine ⟨4900544346844332555708989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13068118258251553481890637 4900544346844332555708989)
                    ·
                      refine ⟨1837704130066624708390871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4900544346844332555708989 1837704130066624708390871)
                      ·
                        rfl

theorem cell23_3578916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_3578916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578916 prefixEnd_3578916 := by exact prefixLift 3578916
  have htrace : WordTrace (prefixWord ++ tailWord_3578916) baseStart_3578916 baseEnd_3578916 := by
    simpa [prefixWord, tailWord_3578916, baseEnd_3578916] using wordTrace_append hprefix tailTrace_3578916
  have hstable : (prefixWord ++ tailWord_3578916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578916).length < 2 ^ (prefixWord ++ tailWord_3578916).sum := by decide
  have hdescent : baseEnd_3578916 < baseStart_3578916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578950 : List Nat := [6, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_3578950 : Nat := 118140960795 + 3578950 * 2 ^ 59
def prefixEnd_3578950 : Nat := 4983230072969 + 3 ^ 40 * 3578950 * 2
def baseEnd_3578950 : Nat := 1837721588408877575365715

theorem tailTrace_3578950 : CollatzResearch.WordTrace tailWord_3578950 prefixEnd_3578950 1837721588408877575365715 := by
  unfold tailWord_3578950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4079219699502589401316447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87023353589388573894750869 4079219699502589401316447)
  ·
    refine ⟨6118829549253884101974671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4079219699502589401316447 6118829549253884101974671)
    ·
      refine ⟨9178244323880826152962007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6118829549253884101974671 9178244323880826152962007)
      ·
        refine ⟨13767366485821239229443011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9178244323880826152962007 13767366485821239229443011)
        ·
          refine ⟨20651049728731858844164517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13767366485821239229443011 20651049728731858844164517)
          ·
            refine ⟨3872071824137223533280847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20651049728731858844164517 3872071824137223533280847)
            ·
              refine ⟨5808107736205835299921271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3872071824137223533280847 5808107736205835299921271)
              ·
                refine ⟨8712161604308752949881907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5808107736205835299921271 8712161604308752949881907)
                ·
                  refine ⟨13068242406463129424822861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8712161604308752949881907 13068242406463129424822861)
                  ·
                    refine ⟨4900590902423673534308573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13068242406463129424822861 4900590902423673534308573)
                    ·
                      refine ⟨1837721588408877575365715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4900590902423673534308573 1837721588408877575365715)
                      ·
                        rfl

theorem cell23_3578950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_3578950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3578950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3578950 prefixEnd_3578950 := by exact prefixLift 3578950
  have htrace : WordTrace (prefixWord ++ tailWord_3578950) baseStart_3578950 baseEnd_3578950 := by
    simpa [prefixWord, tailWord_3578950, baseEnd_3578950] using wordTrace_append hprefix tailTrace_3578950
  have hstable : (prefixWord ++ tailWord_3578950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578950).length < 2 ^ (prefixWord ++ tailWord_3578950).sum := by decide
  have hdescent : baseEnd_3578950 < baseStart_3578950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579026 : List Nat := [3, 2, 3, 1, 1, 2, 1, 3, 2, 5]
def baseStart_3579026 : Nat := 118140960795 + 3579026 * 2 ^ 59
def prefixEnd_3579026 : Nat := 4983230072969 + 3 ^ 40 * 3579026 * 2
def baseEnd_3579026 : Nat := 612586870979539759338455

theorem tailTrace_3579026 : CollatzResearch.WordTrace tailWord_3579026 prefixEnd_3579026 612586870979539759338455 := by
  unfold tailWord_3579026
  simp only [CollatzResearch.WordTrace]
  refine ⟨32634450582951881455473233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87025201554538350547928621 32634450582951881455473233)
  ·
    refine ⟨24475837937213911091604925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32634450582951881455473233 24475837937213911091604925)
    ·
      refine ⟨9178439226455216659351847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24475837937213911091604925 9178439226455216659351847)
      ·
        refine ⟨13767658839682824989027771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9178439226455216659351847 13767658839682824989027771)
        ·
          refine ⟨20651488259524237483541657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13767658839682824989027771 20651488259524237483541657)
          ·
            refine ⟨15488616194643178112656243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20651488259524237483541657 15488616194643178112656243)
            ·
              refine ⟨23232924291964767168984365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15488616194643178112656243 23232924291964767168984365)
              ·
                refine ⟨8712346609486787688369137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23232924291964767168984365 8712346609486787688369137)
                ·
                  refine ⟨6534259957115090766276853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8712346609486787688369137 6534259957115090766276853)
                  ·
                    refine ⟨612586870979539759338455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6534259957115090766276853 612586870979539759338455)
                    ·
                      rfl

theorem cell23_3579026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_3579026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579026 prefixEnd_3579026 := by exact prefixLift 3579026
  have htrace : WordTrace (prefixWord ++ tailWord_3579026) baseStart_3579026 baseEnd_3579026 := by
    simpa [prefixWord, tailWord_3579026, baseEnd_3579026] using wordTrace_append hprefix tailTrace_3579026
  have hstable : (prefixWord ++ tailWord_3579026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579026).length < 2 ^ (prefixWord ++ tailWord_3579026).sum := by decide
  have hdescent : baseEnd_3579026 < baseStart_3579026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579073 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 5, 4]
def baseStart_3579073 : Nat := 118140960795 + 3579073 * 2 ^ 59
def prefixEnd_3579073 : Nat := 4983230072969 + 3 ^ 40 * 3579073 * 2
def baseEnd_3579073 : Nat := 612594915509793531375883

theorem tailTrace_3579073 : CollatzResearch.WordTrace tailWord_3579073 prefixEnd_3579073 612594915509793531375883 := by
  unfold tailWord_3579073
  simp only [CollatzResearch.WordTrace]
  refine ⟨130539516562637252848853873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87026344375091501899235915 130539516562637252848853873)
  ·
    refine ⟨97904637421977939636640405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130539516562637252848853873 97904637421977939636640405)
    ·
      refine ⟨4589279879155215920467519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97904637421977939636640405 4589279879155215920467519)
      ·
        refine ⟨6883919818732823880701279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4589279879155215920467519 6883919818732823880701279)
        ·
          refine ⟨10325879728099235821051919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6883919818732823880701279 10325879728099235821051919)
          ·
            refine ⟨15488819592148853731577879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10325879728099235821051919 15488819592148853731577879)
            ·
              refine ⟨23233229388223280597366819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15488819592148853731577879 23233229388223280597366819)
              ·
                refine ⟨34849844082334920896050229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23233229388223280597366819 34849844082334920896050229)
                ·
                  refine ⟨3267172882718898834004709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34849844082334920896050229 3267172882718898834004709)
                  ·
                    refine ⟨612594915509793531375883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3267172882718898834004709 612594915509793531375883)
                    ·
                      rfl

theorem cell23_3579073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_3579073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579073 prefixEnd_3579073 := by exact prefixLift 3579073
  have htrace : WordTrace (prefixWord ++ tailWord_3579073) baseStart_3579073 baseEnd_3579073 := by
    simpa [prefixWord, tailWord_3579073, baseEnd_3579073] using wordTrace_append hprefix tailTrace_3579073
  have hstable : (prefixWord ++ tailWord_3579073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579073).length < 2 ^ (prefixWord ++ tailWord_3579073).sum := by decide
  have hdescent : baseEnd_3579073 < baseStart_3579073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579090 : List Nat := [3, 2, 2, 2, 1, 1, 4, 3, 1, 4]
def baseStart_3579090 : Nat := 118140960795 + 3579090 * 2 ^ 59
def prefixEnd_3579090 : Nat := 4983230072969 + 3 ^ 40 * 3579090 * 2
def baseEnd_3579090 : Nat := 612597825233502342538357

theorem tailTrace_3579090 : CollatzResearch.WordTrace tailWord_3579090 prefixEnd_3579090 612597825233502342538357 := by
  unfold tailWord_3579090
  simp only [CollatzResearch.WordTrace]
  refine ⟨32635034150893916188055681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87026757735717109834815149 32635034150893916188055681)
  ·
    refine ⟨24476275613170437141041761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32635034150893916188055681 24476275613170437141041761)
    ·
      refine ⟨18357206709877827855781321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24476275613170437141041761 18357206709877827855781321)
      ·
        refine ⟨13767905032408370891835991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18357206709877827855781321 13767905032408370891835991)
        ·
          refine ⟨20651857548612556337753987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13767905032408370891835991 20651857548612556337753987)
          ·
            refine ⟨30977786322918834506630981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20651857548612556337753987 30977786322918834506630981)
            ·
              refine ⟨5808334935547281469993309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30977786322918834506630981 5808334935547281469993309)
              ·
                refine ⟨2178125600830230551247491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5808334935547281469993309 2178125600830230551247491)
                ·
                  refine ⟨3267188401245345826871237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2178125600830230551247491 3267188401245345826871237)
                  ·
                    refine ⟨612597825233502342538357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3267188401245345826871237 612597825233502342538357)
                    ·
                      rfl

theorem cell23_3579090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_3579090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579090 prefixEnd_3579090 := by exact prefixLift 3579090
  have htrace : WordTrace (prefixWord ++ tailWord_3579090) baseStart_3579090 baseEnd_3579090 := by
    simpa [prefixWord, tailWord_3579090, baseEnd_3579090] using wordTrace_append hprefix tailTrace_3579090
  have hstable : (prefixWord ++ tailWord_3579090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579090).length < 2 ^ (prefixWord ++ tailWord_3579090).sum := by decide
  have hdescent : baseEnd_3579090 < baseStart_3579090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579136 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 1, 8, 2]
def baseStart_3579136 : Nat := 118140960795 + 3579136 * 2 ^ 59
def prefixEnd_3579136 : Nat := 4983230072969 + 3 ^ 40 * 3579136 * 2
def baseEnd_3579136 : Nat := 1837817095810613847639859

theorem tailTrace_3579136 : CollatzResearch.WordTrace tailWord_3579136 prefixEnd_3579136 1837817095810613847639859 := by
  unfold tailWord_3579136
  simp only [CollatzResearch.WordTrace]
  refine ⟨65270907180704507304198631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87027876240939343072264841 65270907180704507304198631)
  ·
    refine ⟨97906360771056760956297947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65270907180704507304198631 97906360771056760956297947)
    ·
      refine ⟨146859541156585141434446921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97906360771056760956297947 146859541156585141434446921)
      ·
        refine ⟨110144655867438856075835191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146859541156585141434446921 110144655867438856075835191)
        ·
          refine ⟨165216983801158284113752787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110144655867438856075835191 165216983801158284113752787)
          ·
            refine ⟨247825475701737426170629181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165216983801158284113752787 247825475701737426170629181)
            ·
              refine ⟨92934553388151534813985943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247825475701737426170629181 92934553388151534813985943)
              ·
                refine ⟨139401830082227302220978915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92934553388151534813985943 139401830082227302220978915)
                ·
                  refine ⟨209102745123340953331468373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139401830082227302220978915 209102745123340953331468373)
                  ·
                    refine ⟨2450422794414151796853145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 209102745123340953331468373 2450422794414151796853145)
                    ·
                      refine ⟨1837817095810613847639859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2450422794414151796853145 1837817095810613847639859)
                      ·
                        rfl

theorem cell23_3579136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 8, 2].length) (baseStart_3579136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579136 prefixEnd_3579136 := by exact prefixLift 3579136
  have htrace : WordTrace (prefixWord ++ tailWord_3579136) baseStart_3579136 baseEnd_3579136 := by
    simpa [prefixWord, tailWord_3579136, baseEnd_3579136] using wordTrace_append hprefix tailTrace_3579136
  have hstable : (prefixWord ++ tailWord_3579136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579136).length < 2 ^ (prefixWord ++ tailWord_3579136).sum := by decide
  have hdescent : baseEnd_3579136 < baseStart_3579136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579147 : List Nat := [1, 1, 1, 1, 5, 5, 1, 3, 1, 1, 3]
def baseStart_3579147 : Nat := 118140960795 + 3579147 * 2 ^ 59
def prefixEnd_3579147 : Nat := 4983230072969 + 3 ^ 40 * 3579147 * 2
def baseEnd_3579147 : Nat := 1837822744097813304602309

theorem tailTrace_3579147 : CollatzResearch.WordTrace tailWord_3579147 prefixEnd_3579147 1837822744097813304602309 := by
  unfold tailWord_3579147
  simp only [CollatzResearch.WordTrace]
  refine ⟨130542215564369163487047695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87028143709579442324698463 130542215564369163487047695)
  ·
    refine ⟨195813323346553745230571543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130542215564369163487047695 195813323346553745230571543)
    ·
      refine ⟨293719985019830617845857315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195813323346553745230571543 293719985019830617845857315)
      ·
        refine ⟨440579977529745926768785973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293719985019830617845857315 440579977529745926768785973)
        ·
          refine ⟨41304372893413680634573685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 440579977529745926768785973 41304372893413680634573685)
          ·
            refine ⟨3872284958757532559491283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41304372893413680634573685 3872284958757532559491283)
            ·
              refine ⟨5808427438136298839236925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3872284958757532559491283 5808427438136298839236925)
              ·
                refine ⟨2178160289301112064713847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5808427438136298839236925 2178160289301112064713847)
                ·
                  refine ⟨3267240433951668097070771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2178160289301112064713847 3267240433951668097070771)
                  ·
                    refine ⟨4900860650927502145606157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3267240433951668097070771 4900860650927502145606157)
                    ·
                      refine ⟨1837822744097813304602309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4900860650927502145606157 1837822744097813304602309)
                      ·
                        rfl

theorem cell23_3579147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 1, 1, 3].length) (baseStart_3579147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579147 prefixEnd_3579147 := by exact prefixLift 3579147
  have htrace : WordTrace (prefixWord ++ tailWord_3579147) baseStart_3579147 baseEnd_3579147 := by
    simpa [prefixWord, tailWord_3579147, baseEnd_3579147] using wordTrace_append hprefix tailTrace_3579147
  have hstable : (prefixWord ++ tailWord_3579147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579147).length < 2 ^ (prefixWord ++ tailWord_3579147).sum := by decide
  have hdescent : baseEnd_3579147 < baseStart_3579147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579176 : List Nat := [2, 1, 5, 1, 2, 1, 1, 10]
def baseStart_3579176 : Nat := 118140960795 + 3579176 * 2 ^ 59
def prefixEnd_3579176 : Nat := 4983230072969 + 3 ^ 40 * 3579176 * 2
def baseEnd_3579176 : Nat := 68068060556918284857025

theorem tailTrace_3579176 : CollatzResearch.WordTrace tailWord_3579176 prefixEnd_3579176 68068060556918284857025 := by
  unfold tailWord_3579176
  simp only [CollatzResearch.WordTrace]
  refine ⟨65271636640632050719926691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87028848854176067626568921 65271636640632050719926691)
  ·
    refine ⟨97907454960948076079890037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65271636640632050719926691 97907454960948076079890037)
    ·
      refine ⟨9178823902588882132489691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97907454960948076079890037 9178823902588882132489691)
      ·
        refine ⟨13768235853883323198734537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9178823902588882132489691 13768235853883323198734537)
        ·
          refine ⟨10326176890412492399050903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13768235853883323198734537 10326176890412492399050903)
          ·
            refine ⟨15489265335618738598576355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10326176890412492399050903 15489265335618738598576355)
            ·
              refine ⟨23233898003428107897864533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15489265335618738598576355 23233898003428107897864533)
              ·
                refine ⟨68068060556918284857025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23233898003428107897864533 68068060556918284857025)
                ·
                  rfl

theorem cell23_3579176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 10].length) (baseStart_3579176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579176 prefixEnd_3579176 := by exact prefixLift 3579176
  have htrace : WordTrace (prefixWord ++ tailWord_3579176) baseStart_3579176 baseEnd_3579176 := by
    simpa [prefixWord, tailWord_3579176, baseEnd_3579176] using wordTrace_append hprefix tailTrace_3579176
  have hstable : (prefixWord ++ tailWord_3579176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579176).length < 2 ^ (prefixWord ++ tailWord_3579176).sum := by decide
  have hdescent : baseEnd_3579176 < baseStart_3579176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579221 : List Nat := [1, 3, 2, 2, 3, 3, 2, 2, 1, 2, 2]
def baseStart_3579221 : Nat := 118140960795 + 3579221 * 2 ^ 59
def prefixEnd_3579221 : Nat := 4983230072969 + 3 ^ 40 * 3579221 * 2
def baseEnd_3579221 : Nat := 1837860741666246015076969

theorem tailTrace_3579221 : CollatzResearch.WordTrace tailWord_3579221 prefixEnd_3579221 1837860741666246015076969 := by
  unfold tailWord_3579221
  simp only [CollatzResearch.WordTrace]
  refine ⟨130544914566101074125241517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87029943044067382750161011 130544914566101074125241517)
  ·
    refine ⟨48954342962287902796965569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130544914566101074125241517 48954342962287902796965569)
    ·
      refine ⟨36715757221715927097724177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48954342962287902796965569 36715757221715927097724177)
      ·
        refine ⟨27536817916286945323293133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36715757221715927097724177 27536817916286945323293133)
        ·
          refine ⟨10326306718607604496234925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27536817916286945323293133 10326306718607604496234925)
          ·
            refine ⟨3872365019477851686088097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10326306718607604496234925 3872365019477851686088097)
            ·
              refine ⟨2904273764608388764566073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3872365019477851686088097 2904273764608388764566073)
              ·
                refine ⟨2178205323456291573424555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2904273764608388764566073 2178205323456291573424555)
                ·
                  refine ⟨3267307985184437360136833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2178205323456291573424555 3267307985184437360136833)
                  ·
                    refine ⟨2450480988888328020102625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3267307985184437360136833 2450480988888328020102625)
                    ·
                      refine ⟨1837860741666246015076969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2450480988888328020102625 1837860741666246015076969)
                      ·
                        rfl

theorem cell23_3579221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_3579221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579221 prefixEnd_3579221 := by exact prefixLift 3579221
  have htrace : WordTrace (prefixWord ++ tailWord_3579221) baseStart_3579221 baseEnd_3579221 := by
    simpa [prefixWord, tailWord_3579221, baseEnd_3579221] using wordTrace_append hprefix tailTrace_3579221
  have hstable : (prefixWord ++ tailWord_3579221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579221).length < 2 ^ (prefixWord ++ tailWord_3579221).sum := by decide
  have hdescent : baseEnd_3579221 < baseStart_3579221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579226 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4]
def baseStart_3579226 : Nat := 118140960795 + 3579226 * 2 ^ 59
def prefixEnd_3579226 : Nat := 4983230072969 + 3 ^ 40 * 3579226 * 2
def baseEnd_3579226 : Nat := 1837863309069518495514445

theorem tailTrace_3579226 : CollatzResearch.WordTrace tailWord_3579226 prefixEnd_3579226 1837863309069518495514445 := by
  unfold tailWord_3579226
  simp only [CollatzResearch.WordTrace]
  refine ⟨32636274232770739994793383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87030064620721973319449021 32636274232770739994793383)
  ·
    refine ⟨48954411349156109992190075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32636274232770739994793383 48954411349156109992190075)
    ·
      refine ⟨73431617023734164988285113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48954411349156109992190075 73431617023734164988285113)
      ·
        refine ⟨55073712767800623741213835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73431617023734164988285113 55073712767800623741213835)
        ·
          refine ⟨82610569151700935611820753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55073712767800623741213835 82610569151700935611820753)
          ·
            refine ⟨61957926863775701708865565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82610569151700935611820753 61957926863775701708865565)
            ·
              refine ⟨23234222573915888140824587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61957926863775701708865565 23234222573915888140824587)
              ·
                refine ⟨34851333860873832211236881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23234222573915888140824587 34851333860873832211236881)
                ·
                  refine ⟨26138500395655374158427661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34851333860873832211236881 26138500395655374158427661)
                  ·
                    refine ⟨9801937648370765309410373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26138500395655374158427661 9801937648370765309410373)
                    ·
                      refine ⟨1837863309069518495514445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9801937648370765309410373 1837863309069518495514445)
                      ·
                        rfl

theorem cell23_3579226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_3579226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579226 prefixEnd_3579226 := by exact prefixLift 3579226
  have htrace : WordTrace (prefixWord ++ tailWord_3579226) baseStart_3579226 baseEnd_3579226 := by
    simpa [prefixWord, tailWord_3579226, baseEnd_3579226] using wordTrace_append hprefix tailTrace_3579226
  have hstable : (prefixWord ++ tailWord_3579226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579226).length < 2 ^ (prefixWord ++ tailWord_3579226).sum := by decide
  have hdescent : baseEnd_3579226 < baseStart_3579226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579236 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 1, 8]
def baseStart_3579236 : Nat := 118140960795 + 3579236 * 2 ^ 59
def prefixEnd_3579236 : Nat := 4983230072969 + 3 ^ 40 * 3579236 * 2
def baseEnd_3579236 : Nat := 612622814625354485463133

theorem tailTrace_3579236 : CollatzResearch.WordTrace tailWord_3579236 prefixEnd_3579236 612622814625354485463133 := by
  unfold tailWord_3579236
  simp only [CollatzResearch.WordTrace]
  refine ⟨65272730830523365843518781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87030307774031154458025041 65272730830523365843518781)
  ·
    refine ⟨24477274061446262191319543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65272730830523365843518781 24477274061446262191319543)
    ·
      refine ⟨36715911092169393286979315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24477274061446262191319543 36715911092169393286979315)
      ·
        refine ⟨55073866638254089930468973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36715911092169393286979315 55073866638254089930468973)
        ·
          refine ⟨20652699989345283723925865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55073866638254089930468973 20652699989345283723925865)
          ·
            refine ⟨15489524992008962792944399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20652699989345283723925865 15489524992008962792944399)
            ·
              refine ⟨23234287488013444189416599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15489524992008962792944399 23234287488013444189416599)
              ·
                refine ⟨34851431232020166284124899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23234287488013444189416599 34851431232020166284124899)
                ·
                  refine ⟨52277146848030249426187349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34851431232020166284124899 52277146848030249426187349)
                  ·
                    refine ⟨612622814625354485463133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52277146848030249426187349 612622814625354485463133)
                    ·
                      rfl

theorem cell23_3579236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_3579236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579236 prefixEnd_3579236 := by exact prefixLift 3579236
  have htrace : WordTrace (prefixWord ++ tailWord_3579236) baseStart_3579236 baseEnd_3579236 := by
    simpa [prefixWord, tailWord_3579236, baseEnd_3579236] using wordTrace_append hprefix tailTrace_3579236
  have hstable : (prefixWord ++ tailWord_3579236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579236).length < 2 ^ (prefixWord ++ tailWord_3579236).sum := by decide
  have hdescent : baseEnd_3579236 < baseStart_3579236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579260 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 4, 2, 2]
def baseStart_3579260 : Nat := 118140960795 + 3579260 * 2 ^ 59
def prefixEnd_3579260 : Nat := 4983230072969 + 3 ^ 40 * 3579260 * 2
def baseEnd_3579260 : Nat := 1837880767411771362489289

theorem tailTrace_3579260 : CollatzResearch.WordTrace tailWord_3579260 prefixEnd_3579260 1837880767411771362489289 := by
  unfold tailWord_3579260
  simp only [CollatzResearch.WordTrace]
  refine ⟨65273168506479891892955617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87030891341973189190607489 65273168506479891892955617)
  ·
    refine ⟨48954876379859918919716713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65273168506479891892955617 48954876379859918919716713)
    ·
      refine ⟨36716157284894939189787535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48954876379859918919716713 36716157284894939189787535)
      ·
        refine ⟨55074235927342408784681303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36716157284894939189787535 55074235927342408784681303)
        ·
          refine ⟨82611353891013613177021955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55074235927342408784681303 82611353891013613177021955)
          ·
            refine ⟨123917030836520419765532933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82611353891013613177021955 123917030836520419765532933)
            ·
              refine ⟨23234443281847578706037425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123917030836520419765532933 23234443281847578706037425)
              ·
                refine ⟨17425832461385684029528069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23234443281847578706037425 17425832461385684029528069)
                ·
                  refine ⟨3267343586509815755536513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17425832461385684029528069 3267343586509815755536513)
                  ·
                    refine ⟨2450507689882361816652385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3267343586509815755536513 2450507689882361816652385)
                    ·
                      refine ⟨1837880767411771362489289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2450507689882361816652385 1837880767411771362489289)
                      ·
                        rfl

theorem cell23_3579260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_3579260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579260 prefixEnd_3579260 := by exact prefixLift 3579260
  have htrace : WordTrace (prefixWord ++ tailWord_3579260) baseStart_3579260 baseEnd_3579260 := by
    simpa [prefixWord, tailWord_3579260, baseEnd_3579260] using wordTrace_append hprefix tailTrace_3579260
  have hstable : (prefixWord ++ tailWord_3579260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579260).length < 2 ^ (prefixWord ++ tailWord_3579260).sum := by decide
  have hdescent : baseEnd_3579260 < baseStart_3579260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579296 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 3, 7]
def baseStart_3579296 : Nat := 118140960795 + 3579296 * 2 ^ 59
def prefixEnd_3579296 : Nat := 4983230072969 + 3 ^ 40 * 3579296 * 2
def baseEnd_3579296 : Nat := 612633084238444407213041

theorem tailTrace_3579296 : CollatzResearch.WordTrace tailWord_3579296 prefixEnd_3579296 612633084238444407213041 := by
  unfold tailWord_3579296
  simp only [CollatzResearch.WordTrace]
  refine ⟨65273825020414680967110871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87031766693886241289481161 65273825020414680967110871)
  ·
    refine ⟨97910737530622021450666307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65273825020414680967110871 97910737530622021450666307)
    ·
      refine ⟨146866106295933032175999461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97910737530622021450666307 146866106295933032175999461)
      ·
        refine ⟨27537394930487443532999899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146866106295933032175999461 27537394930487443532999899)
        ·
          refine ⟨41306092395731165299499849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27537394930487443532999899 41306092395731165299499849)
          ·
            refine ⟨30979569296798373974624887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41306092395731165299499849 30979569296798373974624887)
            ·
              refine ⟨46469353945197560961937331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30979569296798373974624887 46469353945197560961937331)
              ·
                refine ⟨69704030917796341442905997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46469353945197560961937331 69704030917796341442905997)
                ·
                  refine ⟨26139011594173628041089749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69704030917796341442905997 26139011594173628041089749)
                  ·
                    refine ⟨612633084238444407213041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26139011594173628041089749 612633084238444407213041)
                    ·
                      rfl

theorem cell23_3579296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 3, 7].length) (baseStart_3579296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579296 prefixEnd_3579296 := by exact prefixLift 3579296
  have htrace : WordTrace (prefixWord ++ tailWord_3579296) baseStart_3579296 baseEnd_3579296 := by
    simpa [prefixWord, tailWord_3579296, baseEnd_3579296] using wordTrace_append hprefix tailTrace_3579296
  have hstable : (prefixWord ++ tailWord_3579296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579296).length < 2 ^ (prefixWord ++ tailWord_3579296).sum := by decide
  have hdescent : baseEnd_3579296 < baseStart_3579296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579313 : List Nat := [1, 2, 2, 4, 1, 1, 2, 3, 2, 5]
def baseStart_3579313 : Nat := 118140960795 + 3579313 * 2 ^ 59
def prefixEnd_3579313 : Nat := 4983230072969 + 3 ^ 40 * 3579313 * 2
def baseEnd_3579313 : Nat := 612635993962153218375515

theorem tailTrace_3579313 : CollatzResearch.WordTrace tailWord_3579313 prefixEnd_3579313 612635993962153218375515 := by
  unfold tailWord_3579313
  simp only [CollatzResearch.WordTrace]
  refine ⟨130548270081767773837590593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87032180054511849225060395 130548270081767773837590593)
  ·
    refine ⟨97911202561325830378192945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130548270081767773837590593 97911202561325830378192945)
    ·
      refine ⟨73433401920994372783644709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97911202561325830378192945 73433401920994372783644709)
      ·
        refine ⟨13768762860186444896933383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73433401920994372783644709 13768762860186444896933383)
        ·
          refine ⟨20653144290279667345400075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13768762860186444896933383 20653144290279667345400075)
          ·
            refine ⟨30979716435419501018100113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20653144290279667345400075 30979716435419501018100113)
            ·
              refine ⟨23234787326564625763575085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30979716435419501018100113 23234787326564625763575085)
              ·
                refine ⟨8713045247461734661340657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23234787326564625763575085 8713045247461734661340657)
                ·
                  refine ⟨6534783935596300996005493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8713045247461734661340657 6534783935596300996005493)
                  ·
                    refine ⟨612635993962153218375515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6534783935596300996005493 612635993962153218375515)
                    ·
                      rfl

theorem cell23_3579313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_3579313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579313 prefixEnd_3579313 := by exact prefixLift 3579313
  have htrace : WordTrace (prefixWord ++ tailWord_3579313) baseStart_3579313 baseEnd_3579313 := by
    simpa [prefixWord, tailWord_3579313, baseEnd_3579313] using wordTrace_append hprefix tailTrace_3579313
  have hstable : (prefixWord ++ tailWord_3579313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579313).length < 2 ^ (prefixWord ++ tailWord_3579313).sum := by decide
  have hdescent : baseEnd_3579313 < baseStart_3579313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579317 : List Nat := [1, 3, 3, 2, 2, 3, 1, 3, 5]
def baseStart_3579317 : Nat := 118140960795 + 3579317 * 2 ^ 59
def prefixEnd_3579317 : Nat := 4983230072969 + 3 ^ 40 * 3579317 * 2
def baseEnd_3579317 : Nat := 204212226201008626608503

theorem tailTrace_3579317 : CollatzResearch.WordTrace tailWord_3579317 prefixEnd_3579317 204212226201008626608503 := by
  unfold tailWord_3579317
  simp only [CollatzResearch.WordTrace]
  refine ⟨130548415973753282520736205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87032277315835521680490803 130548415973753282520736205)
  ·
    refine ⟨48955655990157480945276077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130548415973753282520736205 48955655990157480945276077)
    ·
      refine ⟨18358370996309055354478529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48955655990157480945276077 18358370996309055354478529)
      ·
        refine ⟨13768778247231791515858897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18358370996309055354478529 13768778247231791515858897)
        ·
          refine ⟨10326583685423843636894173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13768778247231791515858897 10326583685423843636894173)
          ·
            refine ⟨3872468882033941363835315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10326583685423843636894173 3872468882033941363835315)
            ·
              refine ⟨5808703323050912045752973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3872468882033941363835315 5808703323050912045752973)
              ·
                refine ⟨2178263746144092017157365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5808703323050912045752973 2178263746144092017157365)
                ·
                  refine ⟨204212226201008626608503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2178263746144092017157365 204212226201008626608503)
                  ·
                    rfl

theorem cell23_3579317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 5].length) (baseStart_3579317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579317 prefixEnd_3579317 := by exact prefixLift 3579317
  have htrace : WordTrace (prefixWord ++ tailWord_3579317) baseStart_3579317 baseEnd_3579317 := by
    simpa [prefixWord, tailWord_3579317, baseEnd_3579317] using wordTrace_append hprefix tailTrace_3579317
  have hstable : (prefixWord ++ tailWord_3579317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579317).length < 2 ^ (prefixWord ++ tailWord_3579317).sum := by decide
  have hdescent : baseEnd_3579317 < baseStart_3579317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579420 : List Nat := [2, 2, 3, 1, 2, 1, 2, 4, 1, 5]
def baseStart_3579420 : Nat := 118140960795 + 3579420 * 2 ^ 59
def prefixEnd_3579420 : Nat := 4983230072969 + 3 ^ 40 * 3579420 * 2
def baseEnd_3579420 : Nat := 612654308105496912162851

theorem tailTrace_3579420 : CollatzResearch.WordTrace tailWord_3579420 prefixEnd_3579420 612654308105496912162851 := by
  unfold tailWord_3579420
  simp only [CollatzResearch.WordTrace]
  refine ⟨65276086346190065555867857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87034781794920087407823809 65276086346190065555867857)
  ·
    refine ⟨48957064759642549166900893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65276086346190065555867857 48957064759642549166900893)
    ·
      refine ⟨18358899284865955937587835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48957064759642549166900893 18358899284865955937587835)
      ·
        refine ⟨27538348927298933906381753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18358899284865955937587835 27538348927298933906381753)
        ·
          refine ⟨20653761695474200429786315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27538348927298933906381753 20653761695474200429786315)
          ·
            refine ⟨30980642543211300644679473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20653761695474200429786315 30980642543211300644679473)
            ·
              refine ⟨23235481907408475483509605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30980642543211300644679473 23235481907408475483509605)
              ·
                refine ⟨4356652857639089153158051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23235481907408475483509605 4356652857639089153158051)
                ·
                  refine ⟨6534979286458633729737077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4356652857639089153158051 6534979286458633729737077)
                  ·
                    refine ⟨612654308105496912162851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6534979286458633729737077 612654308105496912162851)
                    ·
                      rfl

theorem cell23_3579420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_3579420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579420 prefixEnd_3579420 := by exact prefixLift 3579420
  have htrace : WordTrace (prefixWord ++ tailWord_3579420) baseStart_3579420 baseEnd_3579420 := by
    simpa [prefixWord, tailWord_3579420, baseEnd_3579420] using wordTrace_append hprefix tailTrace_3579420
  have hstable : (prefixWord ++ tailWord_3579420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579420).length < 2 ^ (prefixWord ++ tailWord_3579420).sum := by decide
  have hdescent : baseEnd_3579420 < baseStart_3579420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579427 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 1, 5, 2]
def baseStart_3579427 : Nat := 118140960795 + 3579427 * 2 ^ 59
def prefixEnd_3579427 : Nat := 4983230072969 + 3 ^ 40 * 3579427 * 2
def baseEnd_3579427 : Nat := 1837966518681072209101021

theorem tailTrace_3579427 : CollatzResearch.WordTrace tailWord_3579427 prefixEnd_3579427 1837966518681072209101021 := by
  unfold tailWord_3579427
  simp only [CollatzResearch.WordTrace]
  refine ⟨130552428003354771307240535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87034952002236514204827023 130552428003354771307240535)
  ·
    refine ⟨195828642005032156960860803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130552428003354771307240535 195828642005032156960860803)
    ·
      refine ⟨293742963007548235441291205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195828642005032156960860803 293742963007548235441291205)
      ·
        refine ⟨55076805563915294145242101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293742963007548235441291205 55076805563915294145242101)
        ·
          refine ⟨5163450521617058826116447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55076805563915294145242101 5163450521617058826116447)
          ·
            refine ⟨7745175782425588239174671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5163450521617058826116447 7745175782425588239174671)
            ·
              refine ⟨11617763673638382358762007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7745175782425588239174671 11617763673638382358762007)
              ·
                refine ⟨17426645510457573538143011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11617763673638382358762007 17426645510457573538143011)
                ·
                  refine ⟨26139968265686360307214517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17426645510457573538143011 26139968265686360307214517)
                  ·
                    refine ⟨2450622024908096278801361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26139968265686360307214517 2450622024908096278801361)
                    ·
                      refine ⟨1837966518681072209101021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2450622024908096278801361 1837966518681072209101021)
                      ·
                        rfl

theorem cell23_3579427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_3579427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579427 prefixEnd_3579427 := by exact prefixLift 3579427
  have htrace : WordTrace (prefixWord ++ tailWord_3579427) baseStart_3579427 baseEnd_3579427 := by
    simpa [prefixWord, tailWord_3579427, baseEnd_3579427] using wordTrace_append hprefix tailTrace_3579427
  have hstable : (prefixWord ++ tailWord_3579427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579427).length < 2 ^ (prefixWord ++ tailWord_3579427).sum := by decide
  have hdescent : baseEnd_3579427 < baseStart_3579427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579450 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 4, 4]
def baseStart_3579450 : Nat := 118140960795 + 3579450 * 2 ^ 59
def prefixEnd_3579450 : Nat := 4983230072969 + 3 ^ 40 * 3579450 * 2
def baseEnd_3579450 : Nat := 612659442912041873037805

theorem tailTrace_3579450 : CollatzResearch.WordTrace tailWord_3579450 prefixEnd_3579450 612659442912041873037805 := by
  unfold tailWord_3579450
  simp only [CollatzResearch.WordTrace]
  refine ⟨32638316720567861558831951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87035511254847630823551869 32638316720567861558831951)
  ·
    refine ⟨48957475080851792338247927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32638316720567861558831951 48957475080851792338247927)
    ·
      refine ⟨73436212621277688507371891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48957475080851792338247927 73436212621277688507371891)
      ·
        refine ⟨110154318931916532761057837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73436212621277688507371891 110154318931916532761057837)
        ·
          refine ⟨41307869599468699785396689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110154318931916532761057837 41307869599468699785396689)
          ·
            refine ⟨30980902199601524839047517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41307869599468699785396689 30980902199601524839047517)
            ·
              refine ⟨11617838324850571814642819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30980902199601524839047517 11617838324850571814642819)
              ·
                refine ⟨17426757487275857721964229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11617838324850571814642819 17426757487275857721964229)
                ·
                  refine ⟨3267517028864223322868293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17426757487275857721964229 3267517028864223322868293)
                  ·
                    refine ⟨612659442912041873037805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3267517028864223322868293 612659442912041873037805)
                    ·
                      rfl

theorem cell23_3579450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_3579450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579450 prefixEnd_3579450 := by exact prefixLift 3579450
  have htrace : WordTrace (prefixWord ++ tailWord_3579450) baseStart_3579450 baseEnd_3579450 := by
    simpa [prefixWord, tailWord_3579450, baseEnd_3579450] using wordTrace_append hprefix tailTrace_3579450
  have hstable : (prefixWord ++ tailWord_3579450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579450).length < 2 ^ (prefixWord ++ tailWord_3579450).sum := by decide
  have hdescent : baseEnd_3579450 < baseStart_3579450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579474 : List Nat := [3, 2, 2, 1, 2, 2, 2, 2, 3, 2, 2]
def baseStart_3579474 : Nat := 118140960795 + 3579474 * 2 ^ 59
def prefixEnd_3579474 : Nat := 4983230072969 + 3 ^ 40 * 3579474 * 2
def baseEnd_3579474 : Nat := 1837990652271833525213305

theorem tailTrace_3579474 : CollatzResearch.WordTrace tailWord_3579474 prefixEnd_3579474 1837990652271833525213305 := by
  unfold tailWord_3579474
  simp only [CollatzResearch.WordTrace]
  refine ⟨32638535558546124583550369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87036094822789665556134317 32638535558546124583550369)
  ·
    refine ⟨24478901668909593437662777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32638535558546124583550369 24478901668909593437662777)
    ·
      refine ⟨18359176251682195078247083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24478901668909593437662777 18359176251682195078247083)
      ·
        refine ⟨27538764377523292617370625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18359176251682195078247083 27538764377523292617370625)
        ·
          refine ⟨20654073283142469463027969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27538764377523292617370625 20654073283142469463027969)
          ·
            refine ⟨15490554962356852097270977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20654073283142469463027969 15490554962356852097270977)
            ·
              refine ⟨11617916221767639072953233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15490554962356852097270977 11617916221767639072953233)
              ·
                refine ⟨8713437166325729304714925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11617916221767639072953233 8713437166325729304714925)
                ·
                  refine ⟨3267538937372148489268097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8713437166325729304714925 3267538937372148489268097)
                  ·
                    refine ⟨2450654203029111366951073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3267538937372148489268097 2450654203029111366951073)
                    ·
                      refine ⟨1837990652271833525213305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2450654203029111366951073 1837990652271833525213305)
                      ·
                        rfl

theorem cell23_3579474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_3579474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579474 prefixEnd_3579474 := by exact prefixLift 3579474
  have htrace : WordTrace (prefixWord ++ tailWord_3579474) baseStart_3579474 baseEnd_3579474 := by
    simpa [prefixWord, tailWord_3579474, baseEnd_3579474] using wordTrace_append hprefix tailTrace_3579474
  have hstable : (prefixWord ++ tailWord_3579474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579474).length < 2 ^ (prefixWord ++ tailWord_3579474).sum := by decide
  have hdescent : baseEnd_3579474 < baseStart_3579474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579485 : List Nat := [1, 4, 4, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_3579485 : Nat := 118140960795 + 3579485 * 2 ^ 59
def prefixEnd_3579485 : Nat := 4983230072969 + 3 ^ 40 * 3579485 * 2
def baseEnd_3579485 : Nat := 1837996300559032982175755

theorem tailTrace_3579485 : CollatzResearch.WordTrace tailWord_3579485 prefixEnd_3579485 1837996300559032982175755 := by
  unfold tailWord_3579485
  simp only [CollatzResearch.WordTrace]
  refine ⟨130554543437144647212851909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87036362291429764808567939 130554543437144647212851909)
  ·
    refine ⟨24478976894464621352409733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130554543437144647212851909 24478976894464621352409733)
    ·
      refine ⟨4589808167712116503576825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24478976894464621352409733 4589808167712116503576825)
      ·
        refine ⟨3442356125784087377682619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4589808167712116503576825 3442356125784087377682619)
        ·
          refine ⟨5163534188676131066523929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3442356125784087377682619 5163534188676131066523929)
          ·
            refine ⟨3872650641507098299892947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5163534188676131066523929 3872650641507098299892947)
            ·
              refine ⟨5808975962260647449839421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3872650641507098299892947 5808975962260647449839421)
              ·
                refine ⟨2178365985847742793689783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5808975962260647449839421 2178365985847742793689783)
                ·
                  refine ⟨3267548978771614190534675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2178365985847742793689783 3267548978771614190534675)
                  ·
                    refine ⟨4901323468157421285802013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3267548978771614190534675 4901323468157421285802013)
                    ·
                      refine ⟨1837996300559032982175755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4901323468157421285802013 1837996300559032982175755)
                      ·
                        rfl

theorem cell23_3579485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_3579485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579485 prefixEnd_3579485 := by exact prefixLift 3579485
  have htrace : WordTrace (prefixWord ++ tailWord_3579485) baseStart_3579485 baseEnd_3579485 := by
    simpa [prefixWord, tailWord_3579485, baseEnd_3579485] using wordTrace_append hprefix tailTrace_3579485
  have hstable : (prefixWord ++ tailWord_3579485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579485).length < 2 ^ (prefixWord ++ tailWord_3579485).sum := by decide
  have hdescent : baseEnd_3579485 < baseStart_3579485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579491 : List Nat := [1, 1, 1, 5, 1, 3, 3, 3, 1, 2, 2]
def baseStart_3579491 : Nat := 118140960795 + 3579491 * 2 ^ 59
def prefixEnd_3579491 : Nat := 4983230072969 + 3 ^ 40 * 3579491 * 2
def baseEnd_3579491 : Nat := 1837999381442959958700727

theorem tailTrace_3579491 : CollatzResearch.WordTrace tailWord_3579491 prefixEnd_3579491 1837999381442959958700727 := by
  unfold tailWord_3579491
  simp only [CollatzResearch.WordTrace]
  refine ⟨130554762275122910237570327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87036508183415273491713551 130554762275122910237570327)
  ·
    refine ⟨195832143412684365356355491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130554762275122910237570327 195832143412684365356355491)
    ·
      refine ⟨293748215119026548034533237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195832143412684365356355491 293748215119026548034533237)
      ·
        refine ⟨27538895167408738878237491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 293748215119026548034533237 27538895167408738878237491)
        ·
          refine ⟨41308342751113108317356237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27538895167408738878237491 41308342751113108317356237)
          ·
            refine ⟨15490628531667415619008589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41308342751113108317356237 15490628531667415619008589)
            ·
              refine ⟨5808985699375280857128221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15490628531667415619008589 5808985699375280857128221)
              ·
                refine ⟨2178369637265730321423083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5808985699375280857128221 2178369637265730321423083)
                ·
                  refine ⟨3267554455898595482134625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2178369637265730321423083 3267554455898595482134625)
                  ·
                    refine ⟨2450665841923946611600969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3267554455898595482134625 2450665841923946611600969)
                    ·
                      refine ⟨1837999381442959958700727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2450665841923946611600969 1837999381442959958700727)
                      ·
                        rfl

theorem cell23_3579491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_3579491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579491 prefixEnd_3579491 := by exact prefixLift 3579491
  have htrace : WordTrace (prefixWord ++ tailWord_3579491) baseStart_3579491 baseEnd_3579491 := by
    simpa [prefixWord, tailWord_3579491, baseEnd_3579491] using wordTrace_append hprefix tailTrace_3579491
  have hstable : (prefixWord ++ tailWord_3579491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579491).length < 2 ^ (prefixWord ++ tailWord_3579491).sum := by decide
  have hdescent : baseEnd_3579491 < baseStart_3579491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579503 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 5]
def baseStart_3579503 : Nat := 118140960795 + 3579503 * 2 ^ 59
def prefixEnd_3579503 : Nat := 4983230072969 + 3 ^ 40 * 3579503 * 2
def baseEnd_3579503 : Nat := 1838005543210813911750671

theorem tailTrace_3579503 : CollatzResearch.WordTrace tailWord_3579503 prefixEnd_3579503 1838005543210813911750671 := by
  unfold tailWord_3579503
  simp only [CollatzResearch.WordTrace]
  refine ⟨130555199951079436287007163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87036799967386290858004775 130555199951079436287007163)
  ·
    refine ⟨195832799926619154430510745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130555199951079436287007163 195832799926619154430510745)
    ·
      refine ⟨146874599944964365822883059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195832799926619154430510745 146874599944964365822883059)
      ·
        refine ⟨220311899917446548734324589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146874599944964365822883059 220311899917446548734324589)
        ·
          refine ⟨82616962469042455775371721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220311899917446548734324589 82616962469042455775371721)
          ·
            refine ⟨61962721851781841831528791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82616962469042455775371721 61962721851781841831528791)
            ·
              refine ⟨92944082777672762747293187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61962721851781841831528791 92944082777672762747293187)
              ·
                refine ⟨139416124166509144120939781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92944082777672762747293187 139416124166509144120939781)
                ·
                  refine ⟨26140523281220464522676209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139416124166509144120939781 26140523281220464522676209)
                  ·
                    refine ⟨19605392460915348392007157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26140523281220464522676209 19605392460915348392007157)
                    ·
                      refine ⟨1838005543210813911750671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19605392460915348392007157 1838005543210813911750671)
                      ·
                        rfl

theorem cell23_3579503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_3579503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579503 prefixEnd_3579503 := by exact prefixLift 3579503
  have htrace : WordTrace (prefixWord ++ tailWord_3579503) baseStart_3579503 baseEnd_3579503 := by
    simpa [prefixWord, tailWord_3579503, baseEnd_3579503] using wordTrace_append hprefix tailTrace_3579503
  have hstable : (prefixWord ++ tailWord_3579503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579503).length < 2 ^ (prefixWord ++ tailWord_3579503).sum := by decide
  have hdescent : baseEnd_3579503 < baseStart_3579503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579523 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 1, 8]
def baseStart_3579523 : Nat := 118140960795 + 3579523 * 2 ^ 59
def prefixEnd_3579523 : Nat := 4983230072969 + 3 ^ 40 * 3579523 * 2
def baseEnd_3579523 : Nat := 612671937607967944500193

theorem tailTrace_3579523 : CollatzResearch.WordTrace tailWord_3579523 prefixEnd_3579523 612671937607967944500193 := by
  unfold tailWord_3579523
  simp only [CollatzResearch.WordTrace]
  refine ⟨130555929411006979702735223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87037286274004653135156815 130555929411006979702735223)
  ·
    refine ⟨195833894116510469554102835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130555929411006979702735223 195833894116510469554102835)
    ·
      refine ⟨293750841174765704331154253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195833894116510469554102835 293750841174765704331154253)
      ·
        refine ⟨110156565440537139124182845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293750841174765704331154253 110156565440537139124182845)
        ·
          refine ⟨41308712040201427171568567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110156565440537139124182845 41308712040201427171568567)
          ·
            refine ⟨61963068060302140757352851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41308712040201427171568567 61963068060302140757352851)
            ·
              refine ⟨92944602090453211136029277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61963068060302140757352851 92944602090453211136029277)
              ·
                refine ⟨34854225783919954176010979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92944602090453211136029277 34854225783919954176010979)
                ·
                  refine ⟨52281338675879931264016469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34854225783919954176010979 52281338675879931264016469)
                  ·
                    refine ⟨612671937607967944500193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52281338675879931264016469 612671937607967944500193)
                    ·
                      rfl

theorem cell23_3579523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 8].length) (baseStart_3579523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579523 prefixEnd_3579523 := by exact prefixLift 3579523
  have htrace : WordTrace (prefixWord ++ tailWord_3579523) baseStart_3579523 baseEnd_3579523 := by
    simpa [prefixWord, tailWord_3579523, baseEnd_3579523] using wordTrace_append hprefix tailTrace_3579523
  have hstable : (prefixWord ++ tailWord_3579523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579523).length < 2 ^ (prefixWord ++ tailWord_3579523).sum := by decide
  have hdescent : baseEnd_3579523 < baseStart_3579523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579528 : List Nat := [2, 1, 3, 5, 2, 1, 1, 2, 1, 2, 3]
def baseStart_3579528 : Nat := 118140960795 + 3579528 * 2 ^ 59
def prefixEnd_3579528 : Nat := 4983230072969 + 3 ^ 40 * 3579528 * 2
def baseEnd_3579528 : Nat := 1838018380227176313938057

theorem tailTrace_3579528 : CollatzResearch.WordTrace tailWord_3579528 prefixEnd_3579528 1838018380227176313938057 := by
  unfold tailWord_3579528
  simp only [CollatzResearch.WordTrace]
  refine ⟨65278055887994432778333619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87037407850659243704444825 65278055887994432778333619)
  ·
    refine ⟨97917083831991649167500429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65278055887994432778333619 97917083831991649167500429)
    ·
      refine ⟨36718906436996868437812661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97917083831991649167500429 36718906436996868437812661)
      ·
        refine ⟨3442397478468456416044937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36718906436996868437812661 3442397478468456416044937)
        ·
          refine ⟨2581798108851342312033703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3442397478468456416044937 2581798108851342312033703)
          ·
            refine ⟨3872697163277013468050555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2581798108851342312033703 3872697163277013468050555)
            ·
              refine ⟨5809045744915520202075833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3872697163277013468050555 5809045744915520202075833)
              ·
                refine ⟨4356784308686640151556875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5809045744915520202075833 4356784308686640151556875)
                ·
                  refine ⟨6535176463029960227335313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4356784308686640151556875 6535176463029960227335313)
                  ·
                    refine ⟨4901382347272470170501485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6535176463029960227335313 4901382347272470170501485)
                    ·
                      refine ⟨1838018380227176313938057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4901382347272470170501485 1838018380227176313938057)
                      ·
                        rfl

theorem cell23_3579528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_3579528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579528 prefixEnd_3579528 := by exact prefixLift 3579528
  have htrace : WordTrace (prefixWord ++ tailWord_3579528) baseStart_3579528 baseEnd_3579528 := by
    simpa [prefixWord, tailWord_3579528, baseEnd_3579528] using wordTrace_append hprefix tailTrace_3579528
  have hstable : (prefixWord ++ tailWord_3579528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579528).length < 2 ^ (prefixWord ++ tailWord_3579528).sum := by decide
  have hdescent : baseEnd_3579528 < baseStart_3579528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579534 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2]
def baseStart_3579534 : Nat := 118140960795 + 3579534 * 2 ^ 59
def prefixEnd_3579534 : Nat := 4983230072969 + 3 ^ 40 * 3579534 * 2
def baseEnd_3579534 : Nat := 1838021461111103290463029

theorem tailTrace_3579534 : CollatzResearch.WordTrace tailWord_3579534 prefixEnd_3579534 1838021461111103290463029 := by
  unfold tailWord_3579534
  simp only [CollatzResearch.WordTrace]
  refine ⟨16319541326745891072673207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87037553742644752387590437 16319541326745891072673207)
  ·
    refine ⟨24479311990118836609009811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16319541326745891072673207 24479311990118836609009811)
    ·
      refine ⟨36718967985178254913514717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24479311990118836609009811 36718967985178254913514717)
      ·
        refine ⟨13769612994441845592568019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36718967985178254913514717 13769612994441845592568019)
        ·
          refine ⟨20654419491662768388852029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13769612994441845592568019 20654419491662768388852029)
          ·
            refine ⟨7745407309373538145819511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20654419491662768388852029 7745407309373538145819511)
            ·
              refine ⟨11618110964060307218729267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7745407309373538145819511 11618110964060307218729267)
              ·
                refine ⟨17427166446090460828093901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11618110964060307218729267 17427166446090460828093901)
                ·
                  refine ⟨6535187417283922810535213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17427166446090460828093901 6535187417283922810535213)
                  ·
                    refine ⟨2450695281481471053950705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6535187417283922810535213 2450695281481471053950705)
                    ·
                      refine ⟨1838021461111103290463029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2450695281481471053950705 1838021461111103290463029)
                      ·
                        rfl

theorem cell23_3579534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_3579534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579534 prefixEnd_3579534 := by exact prefixLift 3579534
  have htrace : WordTrace (prefixWord ++ tailWord_3579534) baseStart_3579534 baseEnd_3579534 := by
    simpa [prefixWord, tailWord_3579534, baseEnd_3579534] using wordTrace_append hprefix tailTrace_3579534
  have hstable : (prefixWord ++ tailWord_3579534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579534).length < 2 ^ (prefixWord ++ tailWord_3579534).sum := by decide
  have hdescent : baseEnd_3579534 < baseStart_3579534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579574 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_3579574 : Nat := 118140960795 + 3579574 * 2 ^ 59
def prefixEnd_3579574 : Nat := 4983230072969 + 3 ^ 40 * 3579574 * 2
def baseEnd_3579574 : Nat := 612680666779094377987615

theorem tailTrace_3579574 : CollatzResearch.WordTrace tailWord_3579574 prefixEnd_3579574 612680666779094377987615 := by
  unfold tailWord_3579574
  simp only [CollatzResearch.WordTrace]
  refine ⟨8159861845863888463302611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87038526355881476941894517 8159861845863888463302611)
  ·
    refine ⟨12239792768795832694953917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8159861845863888463302611 12239792768795832694953917)
    ·
      refine ⟨4589922288298437260607719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12239792768795832694953917 4589922288298437260607719)
      ·
        refine ⟨6884883432447655890911579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4589922288298437260607719 6884883432447655890911579)
        ·
          refine ⟨10327325148671483836367369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6884883432447655890911579 10327325148671483836367369)
          ·
            refine ⟨7745493861503612877275527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10327325148671483836367369 7745493861503612877275527)
            ·
              refine ⟨11618240792255419315913291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7745493861503612877275527 11618240792255419315913291)
              ·
                refine ⟨17427361188383128973869937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11618240792255419315913291 17427361188383128973869937)
                ·
                  refine ⟨13070520891287346730402453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17427361188383128973869937 13070520891287346730402453)
                  ·
                    refine ⟨612680666779094377987615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13070520891287346730402453 612680666779094377987615)
                    ·
                      rfl

theorem cell23_3579574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_3579574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579574 prefixEnd_3579574 := by exact prefixLift 3579574
  have htrace : WordTrace (prefixWord ++ tailWord_3579574) baseStart_3579574 baseEnd_3579574 := by
    simpa [prefixWord, tailWord_3579574, baseEnd_3579574] using wordTrace_append hprefix tailTrace_3579574
  have hstable : (prefixWord ++ tailWord_3579574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579574).length < 2 ^ (prefixWord ++ tailWord_3579574).sum := by decide
  have hdescent : baseEnd_3579574 < baseStart_3579574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579600 : List Nat := [2, 1, 1, 1, 1, 2, 1, 7, 2, 5]
def baseStart_3579600 : Nat := 118140960795 + 3579600 * 2 ^ 59
def prefixEnd_3579600 : Nat := 4983230072969 + 3 ^ 40 * 3579600 * 2
def baseEnd_3579600 : Nat := 612685116944766677412575

theorem tailTrace_3579600 : CollatzResearch.WordTrace tailWord_3579600 prefixEnd_3579600 612685116944766677412575 := by
  unfold tailWord_3579600
  simp only [CollatzResearch.WordTrace]
  refine ⟨65279368915864010926644127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87039158554485347902192169 65279368915864010926644127)
  ·
    refine ⟨97919053373796016389966191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65279368915864010926644127 97919053373796016389966191)
    ·
      refine ⟨146878580060694024584949287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97919053373796016389966191 146878580060694024584949287)
      ·
        refine ⟨220317870091041036877423931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146878580060694024584949287 220317870091041036877423931)
        ·
          refine ⟨330476805136561555316135897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220317870091041036877423931 330476805136561555316135897)
          ·
            refine ⟨247857603852421166487101923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330476805136561555316135897 247857603852421166487101923)
            ·
              refine ⟨371786405778631749730652885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247857603852421166487101923 371786405778631749730652885)
              ·
                refine ⟨8713743885436681634312177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 371786405778631749730652885 8713743885436681634312177)
                ·
                  refine ⟨6535307914077511225734133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8713743885436681634312177 6535307914077511225734133)
                  ·
                    refine ⟨612685116944766677412575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6535307914077511225734133 612685116944766677412575)
                    ·
                      rfl

theorem cell23_3579600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 2, 5].length) (baseStart_3579600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579600 prefixEnd_3579600 := by exact prefixLift 3579600
  have htrace : WordTrace (prefixWord ++ tailWord_3579600) baseStart_3579600 baseEnd_3579600 := by
    simpa [prefixWord, tailWord_3579600, baseEnd_3579600] using wordTrace_append hprefix tailTrace_3579600
  have hstable : (prefixWord ++ tailWord_3579600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579600).length < 2 ^ (prefixWord ++ tailWord_3579600).sum := by decide
  have hdescent : baseEnd_3579600 < baseStart_3579600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579604 : List Nat := [2, 4, 1, 3, 1, 1, 1, 5, 5]
def baseStart_3579604 : Nat := 118140960795 + 3579604 * 2 ^ 59
def prefixEnd_3579604 : Nat := 4983230072969 + 3 ^ 40 * 3579604 * 2
def baseEnd_3579604 : Nat := 204228600528546446287523

theorem tailTrace_3579604 : CollatzResearch.WordTrace tailWord_3579604 prefixEnd_3579604 204228600528546446287523 := by
  unfold tailWord_3579604
  simp only [CollatzResearch.WordTrace]
  refine ⟨65279441861856765268216933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87039255815809020357622577 65279441861856765268216933)
  ·
    refine ⟨12239895349098143487790675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65279441861856765268216933 12239895349098143487790675)
    ·
      refine ⟨18359843023647215231686013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12239895349098143487790675 18359843023647215231686013)
      ·
        refine ⟨6884941133867705711882255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18359843023647215231686013 6884941133867705711882255)
        ·
          refine ⟨10327411700801558567823383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6884941133867705711882255 10327411700801558567823383)
          ·
            refine ⟨15491117551202337851735075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10327411700801558567823383 15491117551202337851735075)
            ·
              refine ⟨23236676326803506777602613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15491117551202337851735075 23236676326803506777602613)
              ·
                refine ⟨2178438405637828760400245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23236676326803506777602613 2178438405637828760400245)
                ·
                  refine ⟨204228600528546446287523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2178438405637828760400245 204228600528546446287523)
                  ·
                    rfl

theorem cell23_3579604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_3579604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579604 prefixEnd_3579604 := by exact prefixLift 3579604
  have htrace : WordTrace (prefixWord ++ tailWord_3579604) baseStart_3579604 baseEnd_3579604 := by
    simpa [prefixWord, tailWord_3579604, baseEnd_3579604] using wordTrace_append hprefix tailTrace_3579604
  have hstable : (prefixWord ++ tailWord_3579604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579604).length < 2 ^ (prefixWord ++ tailWord_3579604).sum := by decide
  have hdescent : baseEnd_3579604 < baseStart_3579604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579647 : List Nat := [1, 1, 2, 2, 1, 3, 4, 2, 3, 4]
def baseStart_3579647 : Nat := 118140960795 + 3579647 * 2 ^ 59
def prefixEnd_3579647 : Nat := 4983230072969 + 3 ^ 40 * 3579647 * 2
def baseEnd_3579647 : Nat := 612693161475020449450003

theorem tailTrace_3579647 : CollatzResearch.WordTrace tailWord_3579647 prefixEnd_3579647 612693161475020449450003 := by
  unfold tailWord_3579647
  simp only [CollatzResearch.WordTrace]
  refine ⟨130560452062557748880249195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87040301375038499253499463 130560452062557748880249195)
  ·
    refine ⟨195840678093836623320373793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130560452062557748880249195 195840678093836623320373793)
    ·
      refine ⟨146880508570377467490280345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195840678093836623320373793 146880508570377467490280345)
      ·
        refine ⟨110160381427783100617710259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146880508570377467490280345 110160381427783100617710259)
        ·
          refine ⟨165240572141674650926565389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110160381427783100617710259 165240572141674650926565389)
          ·
            refine ⟨61965214553127994097462021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165240572141674650926565389 61965214553127994097462021)
            ·
              refine ⟨11618477728711498893274129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61965214553127994097462021 11618477728711498893274129)
              ·
                refine ⟨8713858296533624169955597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11618477728711498893274129 8713858296533624169955597)
                ·
                  refine ⟨3267696861200109063733349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8713858296533624169955597 3267696861200109063733349)
                  ·
                    refine ⟨612693161475020449450003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3267696861200109063733349 612693161475020449450003)
                    ·
                      rfl

theorem cell23_3579647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 4].length) (baseStart_3579647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579647 prefixEnd_3579647 := by exact prefixLift 3579647
  have htrace : WordTrace (prefixWord ++ tailWord_3579647) baseStart_3579647 baseEnd_3579647 := by
    simpa [prefixWord, tailWord_3579647, baseEnd_3579647] using wordTrace_append hprefix tailTrace_3579647
  have hstable : (prefixWord ++ tailWord_3579647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579647).length < 2 ^ (prefixWord ++ tailWord_3579647).sum := by decide
  have hdescent : baseEnd_3579647 < baseStart_3579647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579657 : List Nat := [1, 2, 1, 1, 3, 2, 1, 5, 2, 2, 3]
def baseStart_3579657 : Nat := 118140960795 + 3579657 * 2 ^ 59
def prefixEnd_3579657 : Nat := 4983230072969 + 3 ^ 40 * 3579657 * 2
def baseEnd_3579657 : Nat := 1838084619231606309224963

theorem tailTrace_3579657 : CollatzResearch.WordTrace tailWord_3579657 prefixEnd_3579657 1838084619231606309224963 := by
  unfold tailWord_3579657
  simp only [CollatzResearch.WordTrace]
  refine ⟨130560816792521520588113225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87040544528347680392075483 130560816792521520588113225)
  ·
    refine ⟨97920612594391140441084919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130560816792521520588113225 97920612594391140441084919)
    ·
      refine ⟨146880918891586710661627379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97920612594391140441084919 146880918891586710661627379)
      ·
        refine ⟨220321378337380065992441069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146880918891586710661627379 220321378337380065992441069)
        ·
          refine ⟨82620516876517524747165401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220321378337380065992441069 82620516876517524747165401)
          ·
            refine ⟨61965387657388143560374051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82620516876517524747165401 61965387657388143560374051)
            ·
              refine ⟨92948081486082215340561077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61965387657388143560374051 92948081486082215340561077)
              ·
                refine ⟨8713882639320207688177601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92948081486082215340561077 8713882639320207688177601)
                ·
                  refine ⟨6535411979490155766133201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8713882639320207688177601 6535411979490155766133201)
                  ·
                    refine ⟨4901558984617616824599901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6535411979490155766133201 4901558984617616824599901)
                    ·
                      refine ⟨1838084619231606309224963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4901558984617616824599901 1838084619231606309224963)
                      ·
                        rfl

theorem cell23_3579657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 2, 3].length) (baseStart_3579657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579657 prefixEnd_3579657 := by exact prefixLift 3579657
  have htrace : WordTrace (prefixWord ++ tailWord_3579657) baseStart_3579657 baseEnd_3579657 := by
    simpa [prefixWord, tailWord_3579657, baseEnd_3579657] using wordTrace_append hprefix tailTrace_3579657
  have hstable : (prefixWord ++ tailWord_3579657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579657).length < 2 ^ (prefixWord ++ tailWord_3579657).sum := by decide
  have hdescent : baseEnd_3579657 < baseStart_3579657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579660 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 8]
def baseStart_3579660 : Nat := 118140960795 + 3579660 * 2 ^ 59
def prefixEnd_3579660 : Nat := 4983230072969 + 3 ^ 40 * 3579660 * 2
def baseEnd_3579660 : Nat := 204231795519285533054161

theorem tailTrace_3579660 : CollatzResearch.WordTrace tailWord_3579660 prefixEnd_3579660 204231795519285533054161 := by
  unfold tailWord_3579660
  simp only [CollatzResearch.WordTrace]
  refine ⟨65280463105755326050236217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87040617474340434733648289 65280463105755326050236217)
  ·
    refine ⟨48960347329316494537677163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65280463105755326050236217 48960347329316494537677163)
    ·
      refine ⟨73440520993974741806515745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48960347329316494537677163 73440520993974741806515745)
      ·
        refine ⟨55080390745481056354886809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73440520993974741806515745 55080390745481056354886809)
        ·
          refine ⟨41310293059110792266165107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55080390745481056354886809 41310293059110792266165107)
          ·
            refine ⟨61965439588666188399247661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41310293059110792266165107 61965439588666188399247661)
            ·
              refine ⟨23237039845749820649717873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61965439588666188399247661 23237039845749820649717873)
              ·
                refine ⟨17427779884312365487288405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23237039845749820649717873 17427779884312365487288405)
                ·
                  refine ⟨204231795519285533054161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17427779884312365487288405 204231795519285533054161)
                  ·
                    rfl

theorem cell23_3579660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 8].length) (baseStart_3579660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579660 prefixEnd_3579660 := by exact prefixLift 3579660
  have htrace : WordTrace (prefixWord ++ tailWord_3579660) baseStart_3579660 baseEnd_3579660 := by
    simpa [prefixWord, tailWord_3579660, baseEnd_3579660] using wordTrace_append hprefix tailTrace_3579660
  have hstable : (prefixWord ++ tailWord_3579660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579660).length < 2 ^ (prefixWord ++ tailWord_3579660).sum := by decide
  have hdescent : baseEnd_3579660 < baseStart_3579660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579668 : List Nat := [2, 4, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3579668 : Nat := 118140960795 + 3579668 * 2 ^ 59
def prefixEnd_3579668 : Nat := 4983230072969 + 3 ^ 40 * 3579668 * 2
def baseEnd_3579668 : Nat := 612696755839601922062471

theorem tailTrace_3579668 : CollatzResearch.WordTrace tailWord_3579668 prefixEnd_3579668 612696755839601922062471 := by
  unfold tailWord_3579668
  simp only [CollatzResearch.WordTrace]
  refine ⟨65280608997740834733381829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87040811996987779644509105 65280608997740834733381829)
  ·
    refine ⟨12240114187076406512509093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65280608997740834733381829 12240114187076406512509093)
    ·
      refine ⟨2295021410076826221095455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12240114187076406512509093 2295021410076826221095455)
      ·
        refine ⟨3442532115115239331643183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2295021410076826221095455 3442532115115239331643183)
        ·
          refine ⟨5163798172672858997464775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3442532115115239331643183 5163798172672858997464775)
          ·
            refine ⟨7745697259009288496197163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5163798172672858997464775 7745697259009288496197163)
            ·
              refine ⟨11618545888513932744295745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7745697259009288496197163 11618545888513932744295745)
              ·
                refine ⟨8713909416385449558221809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11618545888513932744295745 8713909416385449558221809)
                ·
                  refine ⟨6535432062289087168666357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8713909416385449558221809 6535432062289087168666357)
                  ·
                    refine ⟨612696755839601922062471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6535432062289087168666357 612696755839601922062471)
                    ·
                      rfl

theorem cell23_3579668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3579668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579668 prefixEnd_3579668 := by exact prefixLift 3579668
  have htrace : WordTrace (prefixWord ++ tailWord_3579668) baseStart_3579668 baseEnd_3579668 := by
    simpa [prefixWord, tailWord_3579668, baseEnd_3579668] using wordTrace_append hprefix tailTrace_3579668
  have hstable : (prefixWord ++ tailWord_3579668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579668).length < 2 ^ (prefixWord ++ tailWord_3579668).sum := by decide
  have hdescent : baseEnd_3579668 < baseStart_3579668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579674 : List Nat := [3, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3]
def baseStart_3579674 : Nat := 118140960795 + 3579674 * 2 ^ 59
def prefixEnd_3579674 : Nat := 4983230072969 + 3 ^ 40 * 3579674 * 2
def baseEnd_3579674 : Nat := 1838093348402732742712385

theorem tailTrace_3579674 : CollatzResearch.WordTrace tailWord_3579674 prefixEnd_3579674 1838093348402732742712385 := by
  unfold tailWord_3579674
  simp only [CollatzResearch.WordTrace]
  refine ⟨32640359208364983122870519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87040957888973288327654717 32640359208364983122870519)
  ·
    refine ⟨48960538812547474684305779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32640359208364983122870519 48960538812547474684305779)
    ·
      refine ⟨73440808218821212026458669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48960538812547474684305779 73440808218821212026458669)
      ·
        refine ⟨27540303082057954509922001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73440808218821212026458669 27540303082057954509922001)
        ·
          refine ⟨20655227311543465882441501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27540303082057954509922001 20655227311543465882441501)
          ·
            refine ⟨7745710241828799705915563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20655227311543465882441501 7745710241828799705915563)
            ·
              refine ⟨11618565362743199558873345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7745710241828799705915563 11618565362743199558873345)
              ·
                refine ⟨8713924022057399669155009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11618565362743199558873345 8713924022057399669155009)
                ·
                  refine ⟨6535443016543049751866257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8713924022057399669155009 6535443016543049751866257)
                  ·
                    refine ⟨4901582262407287313899693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6535443016543049751866257 4901582262407287313899693)
                    ·
                      refine ⟨1838093348402732742712385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4901582262407287313899693 1838093348402732742712385)
                      ·
                        rfl

theorem cell23_3579674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_3579674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579674 prefixEnd_3579674 := by exact prefixLift 3579674
  have htrace : WordTrace (prefixWord ++ tailWord_3579674) baseStart_3579674 baseEnd_3579674 := by
    simpa [prefixWord, tailWord_3579674, baseEnd_3579674] using wordTrace_append hprefix tailTrace_3579674
  have hstable : (prefixWord ++ tailWord_3579674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579674).length < 2 ^ (prefixWord ++ tailWord_3579674).sum := by decide
  have hdescent : baseEnd_3579674 < baseStart_3579674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579721 : List Nat := [1, 2, 1, 1, 2, 4, 2, 5, 1, 1, 3]
def baseStart_3579721 : Nat := 118140960795 + 3579721 * 2 ^ 59
def prefixEnd_3579721 : Nat := 4983230072969 + 3 ^ 40 * 3579721 * 2
def baseEnd_3579721 : Nat := 1838117481993494058824669

theorem tailTrace_3579721 : CollatzResearch.WordTrace tailWord_3579721 prefixEnd_3579721 1838117481993494058824669 := by
  unfold tailWord_3579721
  simp only [CollatzResearch.WordTrace]
  refine ⟨130563151064289659518443017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87042100709526439678962011 130563151064289659518443017)
  ·
    refine ⟨97922363298217244638832263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130563151064289659518443017 97922363298217244638832263)
    ·
      refine ⟨146883544947325866958248395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97922363298217244638832263 146883544947325866958248395)
      ·
        refine ⟨220325317420988800437372593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146883544947325866958248395 220325317420988800437372593)
        ·
          refine ⟨165243988065741600328029445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220325317420988800437372593 165243988065741600328029445)
          ·
            refine ⟨30983247762326550061505521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165243988065741600328029445 30983247762326550061505521)
            ·
              refine ⟨23237435821744912546129141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30983247762326550061505521 23237435821744912546129141)
              ·
                refine ⟨2178509608288585551199607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23237435821744912546129141 2178509608288585551199607)
                ·
                  refine ⟨3267764412432878326799411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2178509608288585551199607 3267764412432878326799411)
                  ·
                    refine ⟨4901646618649317490199117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3267764412432878326799411 4901646618649317490199117)
                    ·
                      refine ⟨1838117481993494058824669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4901646618649317490199117 1838117481993494058824669)
                      ·
                        rfl

theorem cell23_3579721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 1, 1, 3].length) (baseStart_3579721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579721 prefixEnd_3579721 := by exact prefixLift 3579721
  have htrace : WordTrace (prefixWord ++ tailWord_3579721) baseStart_3579721 baseEnd_3579721 := by
    simpa [prefixWord, tailWord_3579721, baseEnd_3579721] using wordTrace_append hprefix tailTrace_3579721
  have hstable : (prefixWord ++ tailWord_3579721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579721).length < 2 ^ (prefixWord ++ tailWord_3579721).sum := by decide
  have hdescent : baseEnd_3579721 < baseStart_3579721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579757 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_3579757 : Nat := 118140960795 + 3579757 * 2 ^ 59
def prefixEnd_3579757 : Nat := 4983230072969 + 3 ^ 40 * 3579757 * 2
def baseEnd_3579757 : Nat := 1838135967297055917974503

theorem tailTrace_3579757 : CollatzResearch.WordTrace tailWord_3579757 prefixEnd_3579757 1838135967297055917974503 := by
  unfold tailWord_3579757
  simp only [CollatzResearch.WordTrace]
  refine ⟨130564464092159237666753525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87042976061439491777835683 130564464092159237666753525)
  ·
    refine ⟨12240418508639928531258143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130564464092159237666753525 12240418508639928531258143)
    ·
      refine ⟨18360627762959892796887215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12240418508639928531258143 18360627762959892796887215)
      ·
        refine ⟨27540941644439839195330823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18360627762959892796887215 27540941644439839195330823)
        ·
          refine ⟨41311412466659758792996235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27540941644439839195330823 41311412466659758792996235)
          ·
            refine ⟨61967118699989638189494353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41311412466659758792996235 61967118699989638189494353)
            ·
              refine ⟨46475339024992228642120765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61967118699989638189494353 46475339024992228642120765)
              ·
                refine ⟨17428252134372085740795287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46475339024992228642120765 17428252134372085740795287)
                ·
                  refine ⟨26142378201558128611192931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17428252134372085740795287 26142378201558128611192931)
                  ·
                    refine ⟨39213567302337192916789397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26142378201558128611192931 39213567302337192916789397)
                    ·
                      refine ⟨1838135967297055917974503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39213567302337192916789397 1838135967297055917974503)
                      ·
                        rfl

theorem cell23_3579757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_3579757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579757 prefixEnd_3579757 := by exact prefixLift 3579757
  have htrace : WordTrace (prefixWord ++ tailWord_3579757) baseStart_3579757 baseEnd_3579757 := by
    simpa [prefixWord, tailWord_3579757, baseEnd_3579757] using wordTrace_append hprefix tailTrace_3579757
  have hstable : (prefixWord ++ tailWord_3579757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579757).length < 2 ^ (prefixWord ++ tailWord_3579757).sum := by decide
  have hdescent : baseEnd_3579757 < baseStart_3579757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579761 : List Nat := [1, 2, 2, 2, 1, 3, 3, 2, 3, 2, 2]
def baseStart_3579761 : Nat := 118140960795 + 3579761 * 2 ^ 59
def prefixEnd_3579761 : Nat := 4983230072969 + 3 ^ 40 * 3579761 * 2
def baseEnd_3579761 : Nat := 1838138021219673902324485

theorem tailTrace_3579761 : CollatzResearch.WordTrace tailWord_3579761 prefixEnd_3579761 1838138021219673902324485 := by
  unfold tailWord_3579761
  simp only [CollatzResearch.WordTrace]
  refine ⟨130564609984144746349899137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87043073322763164233266091 130564609984144746349899137)
  ·
    refine ⟨97923457488108559762424353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130564609984144746349899137 97923457488108559762424353)
    ·
      refine ⟨73442593116081419821818265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97923457488108559762424353 73442593116081419821818265)
      ·
        refine ⟨55081944837061064866363699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73442593116081419821818265 55081944837061064866363699)
        ·
          refine ⟨82622917255591597299545549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55081944837061064866363699 82622917255591597299545549)
          ·
            refine ⟨30983593970846848987329581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82622917255591597299545549 30983593970846848987329581)
            ·
              refine ⟨11618847739067568370248593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30983593970846848987329581 11618847739067568370248593)
              ·
                refine ⟨8714135804300676277686445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11618847739067568370248593 8714135804300676277686445)
                ·
                  refine ⟨3267800926612753604132417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8714135804300676277686445 3267800926612753604132417)
                  ·
                    refine ⟨2450850694959565203099313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3267800926612753604132417 2450850694959565203099313)
                    ·
                      refine ⟨1838138021219673902324485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2450850694959565203099313 1838138021219673902324485)
                      ·
                        rfl

theorem cell23_3579761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_3579761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579761 prefixEnd_3579761 := by exact prefixLift 3579761
  have htrace : WordTrace (prefixWord ++ tailWord_3579761) baseStart_3579761 baseEnd_3579761 := by
    simpa [prefixWord, tailWord_3579761, baseEnd_3579761] using wordTrace_append hprefix tailTrace_3579761
  have hstable : (prefixWord ++ tailWord_3579761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579761).length < 2 ^ (prefixWord ++ tailWord_3579761).sum := by decide
  have hdescent : baseEnd_3579761 < baseStart_3579761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579838 : List Nat := [4, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2]
def baseStart_3579838 : Nat := 118140960795 + 3579838 * 2 ^ 59
def prefixEnd_3579838 : Nat := 4983230072969 + 3 ^ 40 * 3579838 * 2
def baseEnd_3579838 : Nat := 1838177559230070101061631

theorem tailTrace_3579838 : CollatzResearch.WordTrace tailWord_3579838 prefixEnd_3579838 1838177559230070101061631 := by
  unfold tailWord_3579838
  simp only [CollatzResearch.WordTrace]
  refine ⟨16320927300608223562556521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87044945603243859000301445 16320927300608223562556521)
  ·
    refine ⟨12240695475456167671917391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16320927300608223562556521 12240695475456167671917391)
    ·
      refine ⟨18361043213184251507876087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12240695475456167671917391 18361043213184251507876087)
      ·
        refine ⟨27541564819776377261814131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18361043213184251507876087 27541564819776377261814131)
        ·
          refine ⟨41312347229664565892721197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27541564819776377261814131 41312347229664565892721197)
          ·
            refine ⟨15492130211124212209770449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41312347229664565892721197 15492130211124212209770449)
            ·
              refine ⟨11619097658343159157327837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15492130211124212209770449 11619097658343159157327837)
              ·
                refine ⟨4357161621878684683997939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11619097658343159157327837 4357161621878684683997939)
                ·
                  refine ⟨6535742432818027025996909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4357161621878684683997939 6535742432818027025996909)
                  ·
                    refine ⟨2450903412306760134748841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6535742432818027025996909 2450903412306760134748841)
                    ·
                      refine ⟨1838177559230070101061631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2450903412306760134748841 1838177559230070101061631)
                      ·
                        rfl

theorem cell23_3579838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_3579838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579838 prefixEnd_3579838 := by exact prefixLift 3579838
  have htrace : WordTrace (prefixWord ++ tailWord_3579838) baseStart_3579838 baseEnd_3579838 := by
    simpa [prefixWord, tailWord_3579838, baseEnd_3579838] using wordTrace_append hprefix tailTrace_3579838
  have hstable : (prefixWord ++ tailWord_3579838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579838).length < 2 ^ (prefixWord ++ tailWord_3579838).sum := by decide
  have hdescent : baseEnd_3579838 < baseStart_3579838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579851 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 4, 2, 2]
def baseStart_3579851 : Nat := 118140960795 + 3579851 * 2 ^ 59
def prefixEnd_3579851 : Nat := 4983230072969 + 3 ^ 40 * 3579851 * 2
def baseEnd_3579851 : Nat := 1838184234478578550199071

theorem tailTrace_3579851 : CollatzResearch.WordTrace tailWord_3579851 prefixEnd_3579851 1838184234478578550199071 := by
  unfold tailWord_3579851
  simp only [CollatzResearch.WordTrace]
  refine ⟨130567892553818691720675407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87045261702545794480450271 130567892553818691720675407)
  ·
    refine ⟨195851838830728037581013111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130567892553818691720675407 195851838830728037581013111)
    ·
      refine ⟨293777758246092056371519667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195851838830728037581013111 293777758246092056371519667)
      ·
        refine ⟨440666637369138084557279501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293777758246092056371519667 440666637369138084557279501)
        ·
          refine ⟨165249989013426781708979813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 440666637369138084557279501 165249989013426781708979813)
          ·
            refine ⟨30984372940017521570433715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165249989013426781708979813 30984372940017521570433715)
            ·
              refine ⟨46476559410026282355650573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30984372940017521570433715 46476559410026282355650573)
              ·
                refine ⟨17428709778759855883368965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46476559410026282355650573 17428709778759855883368965)
                ·
                  refine ⟨3267883083517472978131681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17428709778759855883368965 3267883083517472978131681)
                  ·
                    refine ⟨2450912312638104733598761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3267883083517472978131681 2450912312638104733598761)
                    ·
                      refine ⟨1838184234478578550199071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2450912312638104733598761 1838184234478578550199071)
                      ·
                        rfl

theorem cell23_3579851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 2, 2].length) (baseStart_3579851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579851 prefixEnd_3579851 := by exact prefixLift 3579851
  have htrace : WordTrace (prefixWord ++ tailWord_3579851) baseStart_3579851 baseEnd_3579851 := by
    simpa [prefixWord, tailWord_3579851, baseEnd_3579851] using wordTrace_append hprefix tailTrace_3579851
  have hstable : (prefixWord ++ tailWord_3579851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579851).length < 2 ^ (prefixWord ++ tailWord_3579851).sum := by decide
  have hdescent : baseEnd_3579851 < baseStart_3579851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579854 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3]
def baseStart_3579854 : Nat := 118140960795 + 3579854 * 2 ^ 59
def prefixEnd_3579854 : Nat := 4983230072969 + 3 ^ 40 * 3579854 * 2
def baseEnd_3579854 : Nat := 1838185774920542038461557

theorem tailTrace_3579854 : CollatzResearch.WordTrace tailWord_3579854 prefixEnd_3579854 1838185774920542038461557 := by
  unfold tailWord_3579854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16321000246600977904129327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87045334648538548822023077 16321000246600977904129327)
  ·
    refine ⟨24481500369901466856193991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16321000246600977904129327 24481500369901466856193991)
    ·
      refine ⟨36722250554852200284290987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24481500369901466856193991 36722250554852200284290987)
      ·
        refine ⟨55083375832278300426436481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36722250554852200284290987 55083375832278300426436481)
        ·
          refine ⟨41312531874208725319827361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55083375832278300426436481 41312531874208725319827361)
          ·
            refine ⟨30984398905656543989870521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41312531874208725319827361 30984398905656543989870521)
            ·
              refine ⟨23238299179242407992402891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30984398905656543989870521 23238299179242407992402891)
              ·
                refine ⟨34857448768863611988604337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23238299179242407992402891 34857448768863611988604337)
                ·
                  refine ⟨26143086576647708991453253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34857448768863611988604337 26143086576647708991453253)
                  ·
                    refine ⟨4901828733121445435897485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26143086576647708991453253 4901828733121445435897485)
                    ·
                      refine ⟨1838185774920542038461557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4901828733121445435897485 1838185774920542038461557)
                      ·
                        rfl

theorem cell23_3579854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_3579854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579854 prefixEnd_3579854 := by exact prefixLift 3579854
  have htrace : WordTrace (prefixWord ++ tailWord_3579854) baseStart_3579854 baseEnd_3579854 := by
    simpa [prefixWord, tailWord_3579854, baseEnd_3579854] using wordTrace_append hprefix tailTrace_3579854
  have hstable : (prefixWord ++ tailWord_3579854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579854).length < 2 ^ (prefixWord ++ tailWord_3579854).sum := by decide
  have hdescent : baseEnd_3579854 < baseStart_3579854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579857 : List Nat := [1, 2, 2, 1, 2, 1, 2, 5, 7]
def baseStart_3579857 : Nat := 118140960795 + 3579857 * 2 ^ 59
def prefixEnd_3579857 : Nat := 4983230072969 + 3 ^ 40 * 3579857 * 2
def baseEnd_3579857 : Nat := 204243035040278391858227

theorem tailTrace_3579857 : CollatzResearch.WordTrace tailWord_3579857 prefixEnd_3579857 204243035040278391858227 := by
  unfold tailWord_3579857
  simp only [CollatzResearch.WordTrace]
  refine ⟨130568111391796954745393825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87045407594531303163595883 130568111391796954745393825)
  ·
    refine ⟨97926083543847716059045369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130568111391796954745393825 97926083543847716059045369)
    ·
      refine ⟨73444562657885787044284027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97926083543847716059045369 73444562657885787044284027)
      ·
        refine ⟨110166843986828680566426041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73444562657885787044284027 110166843986828680566426041)
        ·
          refine ⟨82625132990121510424819531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110166843986828680566426041 82625132990121510424819531)
          ·
            refine ⟨123937699485182265637229297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82625132990121510424819531 123937699485182265637229297)
            ·
              refine ⟨92953274613886699227921973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123937699485182265637229297 92953274613886699227921973)
              ·
                refine ⟨8714369495051878052617685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92953274613886699227921973 8714369495051878052617685)
                ·
                  refine ⟨204243035040278391858227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8714369495051878052617685 204243035040278391858227)
                  ·
                    rfl

theorem cell23_3579857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 7].length) (baseStart_3579857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579857 prefixEnd_3579857 := by exact prefixLift 3579857
  have htrace : WordTrace (prefixWord ++ tailWord_3579857) baseStart_3579857 baseEnd_3579857 := by
    simpa [prefixWord, tailWord_3579857, baseEnd_3579857] using wordTrace_append hprefix tailTrace_3579857
  have hstable : (prefixWord ++ tailWord_3579857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579857).length < 2 ^ (prefixWord ++ tailWord_3579857).sum := by decide
  have hdescent : baseEnd_3579857 < baseStart_3579857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579885 : List Nat := [1, 5, 1, 4, 1, 1, 1, 2, 1, 4, 2]
def baseStart_3579885 : Nat := 118140960795 + 3579885 * 2 ^ 59
def prefixEnd_3579885 : Nat := 4983230072969 + 3 ^ 40 * 3579885 * 2
def baseEnd_3579885 : Nat := 1838201692820831417173915

theorem tailTrace_3579885 : CollatzResearch.WordTrace tailWord_3579885 prefixEnd_3579885 1838201692820831417173915 := by
  unfold tailWord_3579885
  simp only [CollatzResearch.WordTrace]
  refine ⟨130569132635695515527413109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87046088423797010351608739 130569132635695515527413109)
  ·
    refine ⟨12240856184596454580694979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130569132635695515527413109 12240856184596454580694979)
    ·
      refine ⟨18361284276894681871042469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12240856184596454580694979 18361284276894681871042469)
      ·
        refine ⟨3442740801917752850820463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18361284276894681871042469 3442740801917752850820463)
        ·
          refine ⟨5164111202876629276230695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3442740801917752850820463 5164111202876629276230695)
          ·
            refine ⟨7746166804314943914346043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5164111202876629276230695 7746166804314943914346043)
            ·
              refine ⟨11619250206472415871519065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7746166804314943914346043 11619250206472415871519065)
              ·
                refine ⟨8714437654854311903639299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11619250206472415871519065 8714437654854311903639299)
                ·
                  refine ⟨13071656482281467855458949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8714437654854311903639299 13071656482281467855458949)
                  ·
                    refine ⟨2450935590427775222898553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13071656482281467855458949 2450935590427775222898553)
                    ·
                      refine ⟨1838201692820831417173915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2450935590427775222898553 1838201692820831417173915)
                      ·
                        rfl

theorem cell23_3579885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_3579885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579885 prefixEnd_3579885 := by exact prefixLift 3579885
  have htrace : WordTrace (prefixWord ++ tailWord_3579885) baseStart_3579885 baseEnd_3579885 := by
    simpa [prefixWord, tailWord_3579885, baseEnd_3579885] using wordTrace_append hprefix tailTrace_3579885
  have hstable : (prefixWord ++ tailWord_3579885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579885).length < 2 ^ (prefixWord ++ tailWord_3579885).sum := by decide
  have hdescent : baseEnd_3579885 < baseStart_3579885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579902 : List Nat := [4, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_3579902 : Nat := 118140960795 + 3579902 * 2 ^ 59
def prefixEnd_3579902 : Nat := 4983230072969 + 3 ^ 40 * 3579902 * 2
def baseEnd_3579902 : Nat := 1838210421991957850661337

theorem tailTrace_3579902 : CollatzResearch.WordTrace tailWord_3579902 prefixEnd_3579902 1838210421991957850661337 := by
  unfold tailWord_3579902
  simp only [CollatzResearch.WordTrace]
  refine ⟨16321219084579240928847745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87046501784422618287187973 16321219084579240928847745)
  ·
    refine ⟨12240914313434430696635809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16321219084579240928847745 12240914313434430696635809)
    ·
      refine ⟨9180685735075823022476857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12240914313434430696635809 9180685735075823022476857)
      ·
        refine ⟨6885514301306867266857643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9180685735075823022476857 6885514301306867266857643)
        ·
          refine ⟨10328271451960300900286465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6885514301306867266857643 10328271451960300900286465)
          ·
            refine ⟨7746203588970225675214849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10328271451960300900286465 7746203588970225675214849)
            ·
              refine ⟨5809652691727669256411137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7746203588970225675214849 5809652691727669256411137)
              ·
                refine ⟨4357239518795751942308353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5809652691727669256411137 4357239518795751942308353)
                ·
                  refine ⟨3267929639096813956731265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4357239518795751942308353 3267929639096813956731265)
                  ·
                    refine ⟨2450947229322610467548449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3267929639096813956731265 2450947229322610467548449)
                    ·
                      refine ⟨1838210421991957850661337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2450947229322610467548449 1838210421991957850661337)
                      ·
                        rfl

theorem cell23_3579902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_3579902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579902 prefixEnd_3579902 := by exact prefixLift 3579902
  have htrace : WordTrace (prefixWord ++ tailWord_3579902) baseStart_3579902 baseEnd_3579902 := by
    simpa [prefixWord, tailWord_3579902, baseEnd_3579902] using wordTrace_append hprefix tailTrace_3579902
  have hstable : (prefixWord ++ tailWord_3579902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579902).length < 2 ^ (prefixWord ++ tailWord_3579902).sum := by decide
  have hdescent : baseEnd_3579902 < baseStart_3579902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579911 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 2, 5, 2]
def baseStart_3579911 : Nat := 118140960795 + 3579911 * 2 ^ 59
def prefixEnd_3579911 : Nat := 4983230072969 + 3 ^ 40 * 3579911 * 2
def baseEnd_3579911 : Nat := 1838215043317848315448795

theorem tailTrace_3579911 : CollatzResearch.WordTrace tailWord_3579911 prefixEnd_3579911 1838215043317848315448795 := by
  unfold tailWord_3579911
  simp only [CollatzResearch.WordTrace]
  refine ⟨130570080933601321967859587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87046720622400881311906391 130570080933601321967859587)
  ·
    refine ⟨195855121400401982951789381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130570080933601321967859587 195855121400401982951789381)
    ·
      refine ⟨36722835262575371803460509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195855121400401982951789381 36722835262575371803460509)
      ·
        refine ⟨13771063223465764426297691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36722835262575371803460509 13771063223465764426297691)
        ·
          refine ⟨20656594835198646639446537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13771063223465764426297691 20656594835198646639446537)
          ·
            refine ⟨15492446126398984979584903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20656594835198646639446537 15492446126398984979584903)
            ·
              refine ⟨23238669189598477469377355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15492446126398984979584903 23238669189598477469377355)
              ·
                refine ⟨34858003784397716204066033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23238669189598477469377355 34858003784397716204066033)
                ·
                  refine ⟨26143502838298287153049525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34858003784397716204066033 26143502838298287153049525)
                  ·
                    refine ⟨2450953391090464420598393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26143502838298287153049525 2450953391090464420598393)
                    ·
                      refine ⟨1838215043317848315448795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2450953391090464420598393 1838215043317848315448795)
                      ·
                        rfl

theorem cell23_3579911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_3579911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579911 prefixEnd_3579911 := by exact prefixLift 3579911
  have htrace : WordTrace (prefixWord ++ tailWord_3579911) baseStart_3579911 baseEnd_3579911 := by
    simpa [prefixWord, tailWord_3579911, baseEnd_3579911] using wordTrace_append hprefix tailTrace_3579911
  have hstable : (prefixWord ++ tailWord_3579911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579911).length < 2 ^ (prefixWord ++ tailWord_3579911).sum := by decide
  have hdescent : baseEnd_3579911 < baseStart_3579911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579941 : List Nat := [1, 3, 1, 2, 2, 3, 3, 1, 2, 1, 4]
def baseStart_3579941 : Nat := 118140960795 + 3579941 * 2 ^ 59
def prefixEnd_3579941 : Nat := 4983230072969 + 3 ^ 40 * 3579941 * 2
def baseEnd_3579941 : Nat := 1838230447737483198073657

theorem tailTrace_3579941 : CollatzResearch.WordTrace tailWord_3579941 prefixEnd_3579941 1838230447737483198073657 := by
  unfold tailWord_3579941
  simp only [CollatzResearch.WordTrace]
  refine ⟨130571175123492637091451677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87047450082328424727634451 130571175123492637091451677)
  ·
    refine ⟨48964190671309738909294379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130571175123492637091451677 48964190671309738909294379)
    ·
      refine ⟨73446286006964608363941569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48964190671309738909294379 73446286006964608363941569)
      ·
        refine ⟨55084714505223456272956177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73446286006964608363941569 55084714505223456272956177)
        ·
          refine ⟨41313535878917592204717133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55084714505223456272956177 41313535878917592204717133)
          ·
            refine ⟨15492575954594097076768925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41313535878917592204717133 15492575954594097076768925)
            ·
              refine ⟨5809715982972786403788347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15492575954594097076768925 5809715982972786403788347)
              ·
                refine ⟨8714573974459179605682521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5809715982972786403788347 8714573974459179605682521)
                ·
                  refine ⟨6535930480844384704261891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8714573974459179605682521 6535930480844384704261891)
                  ·
                    refine ⟨9803895721266577056392837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6535930480844384704261891 9803895721266577056392837)
                    ·
                      refine ⟨1838230447737483198073657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9803895721266577056392837 1838230447737483198073657)
                      ·
                        rfl

theorem cell23_3579941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_3579941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579941 prefixEnd_3579941 := by exact prefixLift 3579941
  have htrace : WordTrace (prefixWord ++ tailWord_3579941) baseStart_3579941 baseEnd_3579941 := by
    simpa [prefixWord, tailWord_3579941, baseEnd_3579941] using wordTrace_append hprefix tailTrace_3579941
  have hstable : (prefixWord ++ tailWord_3579941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579941).length < 2 ^ (prefixWord ++ tailWord_3579941).sum := by decide
  have hdescent : baseEnd_3579941 < baseStart_3579941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579954 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_3579954 : Nat := 118140960795 + 3579954 * 2 ^ 59
def prefixEnd_3579954 : Nat := 4983230072969 + 3 ^ 40 * 3579954 * 2
def baseEnd_3579954 : Nat := 1838237122985991647211097

theorem tailTrace_3579954 : CollatzResearch.WordTrace tailWord_3579954 prefixEnd_3579954 1838237122985991647211097 := by
  unfold tailWord_3579954
  simp only [CollatzResearch.WordTrace]
  refine ⟨32642912318111385077918729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87047766181630360207783277 32642912318111385077918729)
  ·
    refine ⟨24482184238583538808439047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32642912318111385077918729 24482184238583538808439047)
    ·
      refine ⟨36723276357875308212658571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24482184238583538808439047 36723276357875308212658571)
      ·
        refine ⟨55084914536812962318987857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36723276357875308212658571 55084914536812962318987857)
        ·
          refine ⟨41313685902609721739240893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55084914536812962318987857 41313685902609721739240893)
          ·
            refine ⟨15492632213478645652215335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41313685902609721739240893 15492632213478645652215335)
            ·
              refine ⟨23238948320217968478323003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15492632213478645652215335 23238948320217968478323003)
              ·
                refine ⟨34858422480326952717484505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23238948320217968478323003 34858422480326952717484505)
                ·
                  refine ⟨26143816860245214538113379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34858422480326952717484505 26143816860245214538113379)
                  ·
                    refine ⟨39215725290367821807170069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26143816860245214538113379 39215725290367821807170069)
                    ·
                      refine ⟨1838237122985991647211097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39215725290367821807170069 1838237122985991647211097)
                      ·
                        rfl

theorem cell23_3579954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_3579954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579954 prefixEnd_3579954 := by exact prefixLift 3579954
  have htrace : WordTrace (prefixWord ++ tailWord_3579954) baseStart_3579954 baseEnd_3579954 := by
    simpa [prefixWord, tailWord_3579954, baseEnd_3579954] using wordTrace_append hprefix tailTrace_3579954
  have hstable : (prefixWord ++ tailWord_3579954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579954).length < 2 ^ (prefixWord ++ tailWord_3579954).sum := by decide
  have hdescent : baseEnd_3579954 < baseStart_3579954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579958 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_3579958 : Nat := 118140960795 + 3579958 * 2 ^ 59
def prefixEnd_3579958 : Nat := 4983230072969 + 3 ^ 40 * 3579958 * 2
def baseEnd_3579958 : Nat := 1838239176908609631561079

theorem tailTrace_3579958 : CollatzResearch.WordTrace tailWord_3579958 prefixEnd_3579958 1838239176908609631561079 := by
  unfold tailWord_3579958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8160737197776940562176283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87047863442954032663213685 8160737197776940562176283)
  ·
    refine ⟨12241105796665410843264425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8160737197776940562176283 12241105796665410843264425)
    ·
      refine ⟨9180829347499058132448319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12241105796665410843264425 9180829347499058132448319)
      ·
        refine ⟨13771244021248587198672479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9180829347499058132448319 13771244021248587198672479)
        ·
          refine ⟨20656866031872880798008719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13771244021248587198672479 20656866031872880798008719)
          ·
            refine ⟨30985299047809321197013079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20656866031872880798008719 30985299047809321197013079)
            ·
              refine ⟨46477948571713981795519619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30985299047809321197013079 46477948571713981795519619)
              ·
                refine ⟨69716922857570972693279429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46477948571713981795519619 69716922857570972693279429)
                ·
                  refine ⟨13071923035794557379989893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69716922857570972693279429 13071923035794557379989893)
                  ·
                    refine ⟨2450985569211479508748105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13071923035794557379989893 2450985569211479508748105)
                    ·
                      refine ⟨1838239176908609631561079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2450985569211479508748105 1838239176908609631561079)
                      ·
                        rfl

theorem cell23_3579958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_3579958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579958 prefixEnd_3579958 := by exact prefixLift 3579958
  have htrace : WordTrace (prefixWord ++ tailWord_3579958) baseStart_3579958 baseEnd_3579958 := by
    simpa [prefixWord, tailWord_3579958, baseEnd_3579958] using wordTrace_append hprefix tailTrace_3579958
  have hstable : (prefixWord ++ tailWord_3579958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579958).length < 2 ^ (prefixWord ++ tailWord_3579958).sum := by decide
  have hdescent : baseEnd_3579958 < baseStart_3579958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579964 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 8]
def baseStart_3579964 : Nat := 118140960795 + 3579964 * 2 ^ 59
def prefixEnd_3579964 : Nat := 4983230072969 + 3 ^ 40 * 3579964 * 2
def baseEnd_3579964 : Nat := 204249139754726289787339

theorem tailTrace_3579964 : CollatzResearch.WordTrace tailWord_3579964 prefixEnd_3579964 204249139754726289787339 := by
  unfold tailWord_3579964
  simp only [CollatzResearch.WordTrace]
  refine ⟨65286007001204656009769473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87048009334939541346359297 65286007001204656009769473)
  ·
    refine ⟨48964505250903492007327105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65286007001204656009769473 48964505250903492007327105)
    ·
      refine ⟨36723378938177619005495329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48964505250903492007327105 36723378938177619005495329)
      ·
        refine ⟨27542534203633214254121497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36723378938177619005495329 27542534203633214254121497)
        ·
          refine ⟨20656900652724910690591123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27542534203633214254121497 20656900652724910690591123)
          ·
            refine ⟨30985350979087366035886685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20656900652724910690591123 30985350979087366035886685)
            ·
              refine ⟨11619506617157762263457507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30985350979087366035886685 11619506617157762263457507)
              ·
                refine ⟨17429259925736643395186261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11619506617157762263457507 17429259925736643395186261)
                ·
                  refine ⟨204249139754726289787339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17429259925736643395186261 204249139754726289787339)
                  ·
                    rfl

theorem cell23_3579964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 8].length) (baseStart_3579964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579964 prefixEnd_3579964 := by exact prefixLift 3579964
  have htrace : WordTrace (prefixWord ++ tailWord_3579964) baseStart_3579964 baseEnd_3579964 := by
    simpa [prefixWord, tailWord_3579964, baseEnd_3579964] using wordTrace_append hprefix tailTrace_3579964
  have hstable : (prefixWord ++ tailWord_3579964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579964).length < 2 ^ (prefixWord ++ tailWord_3579964).sum := by decide
  have hdescent : baseEnd_3579964 < baseStart_3579964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579968 : List Nat := [2, 1, 1, 2, 2, 4, 2, 4, 1, 4]
def baseStart_3579968 : Nat := 118140960795 + 3579968 * 2 ^ 59
def prefixEnd_3579968 : Nat := 4983230072969 + 3 ^ 40 * 3579968 * 2
def baseEnd_3579968 : Nat := 612748103905051530812011

theorem tailTrace_3579968 : CollatzResearch.WordTrace tailWord_3579968 prefixEnd_3579968 612748103905051530812011 := by
  unfold tailWord_3579968
  simp only [CollatzResearch.WordTrace]
  refine ⟨65286079947197410351342279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87048106596263213801789705 65286079947197410351342279)
  ·
    refine ⟨97929119920796115527013419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65286079947197410351342279 97929119920796115527013419)
    ·
      refine ⟨146893679881194173290520129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97929119920796115527013419 146893679881194173290520129)
      ·
        refine ⟨110170259910895629967890097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146893679881194173290520129 110170259910895629967890097)
        ·
          refine ⟨82627694933171722475917573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110170259910895629967890097 82627694933171722475917573)
          ·
            refine ⟨15492692799969697964234545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82627694933171722475917573 15492692799969697964234545)
            ·
              refine ⟨11619519599977273473175909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15492692799969697964234545 11619519599977273473175909)
              ·
                refine ⟨2178659924995738776220483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11619519599977273473175909 2178659924995738776220483)
                ·
                  refine ⟨3267989887493608164330725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2178659924995738776220483 3267989887493608164330725)
                  ·
                    refine ⟨612748103905051530812011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3267989887493608164330725 612748103905051530812011)
                    ·
                      rfl

theorem cell23_3579968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 1, 4].length) (baseStart_3579968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3579968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3579968 prefixEnd_3579968 := by exact prefixLift 3579968
  have htrace : WordTrace (prefixWord ++ tailWord_3579968) baseStart_3579968 baseEnd_3579968 := by
    simpa [prefixWord, tailWord_3579968, baseEnd_3579968] using wordTrace_append hprefix tailTrace_3579968
  have hstable : (prefixWord ++ tailWord_3579968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579968).length < 2 ^ (prefixWord ++ tailWord_3579968).sum := by decide
  have hdescent : baseEnd_3579968 < baseStart_3579968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580018 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 4, 3, 2]
def baseStart_3580018 : Nat := 118140960795 + 3580018 * 2 ^ 59
def prefixEnd_3580018 : Nat := 4983230072969 + 3 ^ 40 * 3580018 * 2
def baseEnd_3580018 : Nat := 1838269985747879396810803

theorem tailTrace_3580018 : CollatzResearch.WordTrace tailWord_3580018 prefixEnd_3580018 1838269985747879396810803 := by
  unfold tailWord_3580018
  simp only [CollatzResearch.WordTrace]
  refine ⟨32643495886053419810501177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87049322362809119494669805 32643495886053419810501177)
  ·
    refine ⟨24482621914540064857875883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32643495886053419810501177 24482621914540064857875883)
    ·
      refine ⟨36723932871810097286813825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24482621914540064857875883 36723932871810097286813825)
      ·
        refine ⟨27542949653857572965110369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36723932871810097286813825 27542949653857572965110369)
        ·
          refine ⟨20657212240393179723832777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27542949653857572965110369 20657212240393179723832777)
          ·
            refine ⟨15492909180294884792874583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20657212240393179723832777 15492909180294884792874583)
            ·
              refine ⟨23239363770442327189311875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15492909180294884792874583 23239363770442327189311875)
              ·
                refine ⟨34859045655663490783967813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23239363770442327189311875 34859045655663490783967813)
                ·
                  refine ⟨6536071060436904521993965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34859045655663490783967813 6536071060436904521993965)
                  ·
                    refine ⟨2451026647663839195747737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6536071060436904521993965 2451026647663839195747737)
                    ·
                      refine ⟨1838269985747879396810803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2451026647663839195747737 1838269985747879396810803)
                      ·
                        rfl

theorem cell23_3580018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_3580018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580018 prefixEnd_3580018 := by exact prefixLift 3580018
  have htrace : WordTrace (prefixWord ++ tailWord_3580018) baseStart_3580018 baseEnd_3580018 := by
    simpa [prefixWord, tailWord_3580018, baseEnd_3580018] using wordTrace_append hprefix tailTrace_3580018
  have hstable : (prefixWord ++ tailWord_3580018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580018).length < 2 ^ (prefixWord ++ tailWord_3580018).sum := by decide
  have hdescent : baseEnd_3580018 < baseStart_3580018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580025 : List Nat := [1, 2, 1, 3, 4, 3, 1, 1, 3, 1, 3]
def baseStart_3580025 : Nat := 118140960795 + 3580025 * 2 ^ 59
def prefixEnd_3580025 : Nat := 4983230072969 + 3 ^ 40 * 3580025 * 2
def baseEnd_3580025 : Nat := 1838273580112460869423271

theorem tailTrace_3580025 : CollatzResearch.WordTrace tailWord_3580025 prefixEnd_3580025 1838273580112460869423271 := by
  unfold tailWord_3580025
  simp only [CollatzResearch.WordTrace]
  refine ⟨130574238855188319437509529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87049492570125546291673019 130574238855188319437509529)
  ·
    refine ⟨97930679141391239578132147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130574238855188319437509529 97930679141391239578132147)
    ·
      refine ⟨146896018712086859367198221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97930679141391239578132147 146896018712086859367198221)
      ·
        refine ⟨55086007017032572262699333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146896018712086859367198221 55086007017032572262699333)
        ·
          refine ⟨10328626315693607299256125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55086007017032572262699333 10328626315693607299256125)
          ·
            refine ⟨3873234868385102737221047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10328626315693607299256125 3873234868385102737221047)
            ·
              refine ⟨5809852302577654105831571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3873234868385102737221047 5809852302577654105831571)
              ·
                refine ⟨8714778453866481158747357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5809852302577654105831571 8714778453866481158747357)
                ·
                  refine ⟨3268041920199930434530259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8714778453866481158747357 3268041920199930434530259)
                  ·
                    refine ⟨4902062880299895651795389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3268041920199930434530259 4902062880299895651795389)
                    ·
                      refine ⟨1838273580112460869423271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4902062880299895651795389 1838273580112460869423271)
                      ·
                        rfl

theorem cell23_3580025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_3580025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580025 prefixEnd_3580025 := by exact prefixLift 3580025
  have htrace : WordTrace (prefixWord ++ tailWord_3580025) baseStart_3580025 baseEnd_3580025 := by
    simpa [prefixWord, tailWord_3580025, baseEnd_3580025] using wordTrace_append hprefix tailTrace_3580025
  have hstable : (prefixWord ++ tailWord_3580025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580025).length < 2 ^ (prefixWord ++ tailWord_3580025).sum := by decide
  have hdescent : baseEnd_3580025 < baseStart_3580025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580048 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 5, 2, 2]
def baseStart_3580048 : Nat := 118140960795 + 3580048 * 2 ^ 59
def prefixEnd_3580048 : Nat := 4983230072969 + 3 ^ 40 * 3580048 * 2
def baseEnd_3580048 : Nat := 1838285390167514279435665

theorem tailTrace_3580048 : CollatzResearch.WordTrace tailWord_3580048 prefixEnd_3580048 1838285390167514279435665 := by
  unfold tailWord_3580048
  simp only [CollatzResearch.WordTrace]
  refine ⟨65287538867052497182798399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87050051822736662910397865 65287538867052497182798399)
  ·
    refine ⟨97931308300578745774197599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65287538867052497182798399 97931308300578745774197599)
    ·
      refine ⟨146896962450868118661296399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97931308300578745774197599 146896962450868118661296399)
      ·
        refine ⟨220345443676302177991944599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146896962450868118661296399 220345443676302177991944599)
        ·
          refine ⟨330518165514453266987916899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220345443676302177991944599 330518165514453266987916899)
          ·
            refine ⟨495777248271679900481875349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330518165514453266987916899 495777248271679900481875349)
            ·
              refine ⟨23239558512734995335087907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 495777248271679900481875349 23239558512734995335087907)
              ·
                refine ⟨34859337769102493002631861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23239558512734995335087907 34859337769102493002631861)
                ·
                  refine ⟨3268062915853358718996737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34859337769102493002631861 3268062915853358718996737)
                  ·
                    refine ⟨2451047186890019039247553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3268062915853358718996737 2451047186890019039247553)
                    ·
                      refine ⟨1838285390167514279435665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2451047186890019039247553 1838285390167514279435665)
                      ·
                        rfl

theorem cell23_3580048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 5, 2, 2].length) (baseStart_3580048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580048 prefixEnd_3580048 := by exact prefixLift 3580048
  have htrace : WordTrace (prefixWord ++ tailWord_3580048) baseStart_3580048 baseEnd_3580048 := by
    simpa [prefixWord, tailWord_3580048, baseEnd_3580048] using wordTrace_append hprefix tailTrace_3580048
  have hstable : (prefixWord ++ tailWord_3580048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580048).length < 2 ^ (prefixWord ++ tailWord_3580048).sum := by decide
  have hdescent : baseEnd_3580048 < baseStart_3580048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580058 : List Nat := [3, 1, 1, 5, 2, 1, 1, 2, 1, 6]
def baseStart_3580058 : Nat := 118140960795 + 3580058 * 2 ^ 59
def prefixEnd_3580058 : Nat := 4983230072969 + 3 ^ 40 * 3580058 * 2
def baseEnd_3580058 : Nat := 612763508324686413436873

theorem tailTrace_3580058 : CollatzResearch.WordTrace tailWord_3580058 prefixEnd_3580058 612763508324686413436873 := by
  unfold tailWord_3580058
  simp only [CollatzResearch.WordTrace]
  refine ⟨32643860616017191518365207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87050294976045844048973885 32643860616017191518365207)
  ·
    refine ⟨48965790924025787277547811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32643860616017191518365207 48965790924025787277547811)
    ·
      refine ⟨73448686386038680916321717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48965790924025787277547811 73448686386038680916321717)
      ·
        refine ⟨6885814348691126335905161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73448686386038680916321717 6885814348691126335905161)
        ·
          refine ⟨5164360761518344751928871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6885814348691126335905161 5164360761518344751928871)
          ·
            refine ⟨7746541142277517127893307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5164360761518344751928871 7746541142277517127893307)
            ·
              refine ⟨11619811713416275691839961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7746541142277517127893307 11619811713416275691839961)
              ·
                refine ⟨8714858785062206768879971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11619811713416275691839961 8714858785062206768879971)
                ·
                  refine ⟨13072288177593310153319957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8714858785062206768879971 13072288177593310153319957)
                  ·
                    refine ⟨612763508324686413436873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13072288177593310153319957 612763508324686413436873)
                    ·
                      rfl

theorem cell23_3580058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_3580058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580058 prefixEnd_3580058 := by exact prefixLift 3580058
  have htrace : WordTrace (prefixWord ++ tailWord_3580058) baseStart_3580058 baseEnd_3580058 := by
    simpa [prefixWord, tailWord_3580058, baseEnd_3580058] using wordTrace_append hprefix tailTrace_3580058
  have hstable : (prefixWord ++ tailWord_3580058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580058).length < 2 ^ (prefixWord ++ tailWord_3580058).sum := by decide
  have hdescent : baseEnd_3580058 < baseStart_3580058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580061 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_3580061 : Nat := 118140960795 + 3580061 * 2 ^ 59
def prefixEnd_3580061 : Nat := 4983230072969 + 3 ^ 40 * 3580061 * 2
def baseEnd_3580061 : Nat := 1838292065416022728573105

theorem tailTrace_3580061 : CollatzResearch.WordTrace tailWord_3580061 prefixEnd_3580061 1838292065416022728573105 := by
  unfold tailWord_3580061
  simp only [CollatzResearch.WordTrace]
  refine ⟨130575551883057897585820037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87050367922038598390546691 130575551883057897585820037)
  ·
    refine ⟨24482915978073355797341257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130575551883057897585820037 24482915978073355797341257)
    ·
      refine ⟨18362186983555016848005943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24482915978073355797341257 18362186983555016848005943)
      ·
        refine ⟨27543280475332525272008915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18362186983555016848005943 27543280475332525272008915)
        ·
          refine ⟨41314920712998787908013373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27543280475332525272008915 41314920712998787908013373)
          ·
            refine ⟨15493095267374545465505015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41314920712998787908013373 15493095267374545465505015)
            ·
              refine ⟨23239642901061818198257523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15493095267374545465505015 23239642901061818198257523)
              ·
                refine ⟨34859464351592727297386285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23239642901061818198257523 34859464351592727297386285)
                ·
                  refine ⟨13072299131847272736519857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34859464351592727297386285 13072299131847272736519857)
                  ·
                    refine ⟨9804224348885454552389893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13072299131847272736519857 9804224348885454552389893)
                    ·
                      refine ⟨1838292065416022728573105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9804224348885454552389893 1838292065416022728573105)
                      ·
                        rfl

theorem cell23_3580061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_3580061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580061 prefixEnd_3580061 := by exact prefixLift 3580061
  have htrace : WordTrace (prefixWord ++ tailWord_3580061) baseStart_3580061 baseEnd_3580061 := by
    simpa [prefixWord, tailWord_3580061, baseEnd_3580061] using wordTrace_append hprefix tailTrace_3580061
  have hstable : (prefixWord ++ tailWord_3580061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580061).length < 2 ^ (prefixWord ++ tailWord_3580061).sum := by decide
  have hdescent : baseEnd_3580061 < baseStart_3580061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580062 : List Nat := [4, 3, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_3580062 : Nat := 118140960795 + 3580062 * 2 ^ 59
def prefixEnd_3580062 : Nat := 4983230072969 + 3 ^ 40 * 3580062 * 2
def baseEnd_3580062 : Nat := 612764192965559074886867

theorem tailTrace_3580062 : CollatzResearch.WordTrace tailWord_3580062 prefixEnd_3580062 612764192965559074886867 := by
  unfold tailWord_3580062
  simp only [CollatzResearch.WordTrace]
  refine ⟨16321948544506784344575805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87050392237369516504404293 16321948544506784344575805)
  ·
    refine ⟨6120730704190044129215927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16321948544506784344575805 6120730704190044129215927)
    ·
      refine ⟨9181096056285066193823891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6120730704190044129215927 9181096056285066193823891)
      ·
        refine ⟨13771644084427599290735837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9181096056285066193823891 13771644084427599290735837)
        ·
          refine ⟨5164366531660349734025939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13771644084427599290735837 5164366531660349734025939)
          ·
            refine ⟨7746549797490524601038909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5164366531660349734025939 7746549797490524601038909)
            ·
              refine ⟨2904956174058946725389591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7746549797490524601038909 2904956174058946725389591)
              ·
                refine ⟨4357434261088420088084387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2904956174058946725389591 4357434261088420088084387)
                ·
                  refine ⟨6536151391632630132126581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4357434261088420088084387 6536151391632630132126581)
                  ·
                    refine ⟨612764192965559074886867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6536151391632630132126581 612764192965559074886867)
                    ·
                      rfl

theorem cell23_3580062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_3580062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580062 prefixEnd_3580062 := by exact prefixLift 3580062
  have htrace : WordTrace (prefixWord ++ tailWord_3580062) baseStart_3580062 baseEnd_3580062 := by
    simpa [prefixWord, tailWord_3580062, baseEnd_3580062] using wordTrace_append hprefix tailTrace_3580062
  have hstable : (prefixWord ++ tailWord_3580062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580062).length < 2 ^ (prefixWord ++ tailWord_3580062).sum := by decide
  have hdescent : baseEnd_3580062 < baseStart_3580062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580065 : List Nat := [1, 2, 3, 3, 1, 3, 3, 1, 1, 1, 4]
def baseStart_3580065 : Nat := 118140960795 + 3580065 * 2 ^ 59
def prefixEnd_3580065 : Nat := 4983230072969 + 3 ^ 40 * 3580065 * 2
def baseEnd_3580065 : Nat := 1838294119338640712923087

theorem tailTrace_3580065 : CollatzResearch.WordTrace tailWord_3580065 prefixEnd_3580065 1838294119338640712923087 := by
  unfold tailWord_3580065
  simp only [CollatzResearch.WordTrace]
  refine ⟨130575697775043406268965649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87050465183362270845977099 130575697775043406268965649)
  ·
    refine ⟨97931773331282554701724237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130575697775043406268965649 97931773331282554701724237)
    ·
      refine ⟨36724414999230958013146589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97931773331282554701724237 36724414999230958013146589)
      ·
        refine ⟨13771655624711609254929971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36724414999230958013146589 13771655624711609254929971)
        ·
          refine ⟨20657483437067413882394957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13771655624711609254929971 20657483437067413882394957)
          ·
            refine ⟨7746556288900280205898109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20657483437067413882394957 7746556288900280205898109)
            ·
              refine ⟨2904958608337605077211791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7746556288900280205898109 2904958608337605077211791)
              ·
                refine ⟨4357437912506407615817687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2904958608337605077211791 4357437912506407615817687)
                ·
                  refine ⟨6536156868759611423726531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4357437912506407615817687 6536156868759611423726531)
                  ·
                    refine ⟨9804235303139417135589797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6536156868759611423726531 9804235303139417135589797)
                    ·
                      refine ⟨1838294119338640712923087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9804235303139417135589797 1838294119338640712923087)
                      ·
                        rfl

theorem cell23_3580065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_3580065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580065 prefixEnd_3580065 := by exact prefixLift 3580065
  have htrace : WordTrace (prefixWord ++ tailWord_3580065) baseStart_3580065 baseEnd_3580065 := by
    simpa [prefixWord, tailWord_3580065, baseEnd_3580065] using wordTrace_append hprefix tailTrace_3580065
  have hstable : (prefixWord ++ tailWord_3580065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580065).length < 2 ^ (prefixWord ++ tailWord_3580065).sum := by decide
  have hdescent : baseEnd_3580065 < baseStart_3580065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580071 : List Nat := [1, 1, 6, 2, 2, 11]
def baseStart_3580071 : Nat := 118140960795 + 3580071 * 2 ^ 59
def prefixEnd_3580071 : Nat := 4983230072969 + 3 ^ 40 * 3580071 * 2
def baseEnd_3580071 : Nat := 7565009054413858804313

theorem tailTrace_3580071 : CollatzResearch.WordTrace tailWord_3580071 prefixEnd_3580071 7565009054413858804313 := by
  unfold tailWord_3580071
  simp only [CollatzResearch.WordTrace]
  refine ⟨130575916613021669293684067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87050611075347779529122711 130575916613021669293684067)
  ·
    refine ⟨195863874919532503940526101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130575916613021669293684067 195863874919532503940526101)
    ·
      refine ⟨9181119136853086122212161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 195863874919532503940526101 9181119136853086122212161)
      ·
        refine ⟨6885839352639814591659121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9181119136853086122212161 6885839352639814591659121)
        ·
          refine ⟨5164379514479860943744341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6885839352639814591659121 5164379514479860943744341)
          ·
            refine ⟨7565009054413858804313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5164379514479860943744341 7565009054413858804313)
            ·
              rfl

theorem cell23_3580071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 11].length) (baseStart_3580071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580071 prefixEnd_3580071 := by exact prefixLift 3580071
  have htrace : WordTrace (prefixWord ++ tailWord_3580071) baseStart_3580071 baseEnd_3580071 := by
    simpa [prefixWord, tailWord_3580071, baseEnd_3580071] using wordTrace_append hprefix tailTrace_3580071
  have hstable : (prefixWord ++ tailWord_3580071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580071).length < 2 ^ (prefixWord ++ tailWord_3580071).sum := by decide
  have hdescent : baseEnd_3580071 < baseStart_3580071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580082 : List Nat := [3, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2]
def baseStart_3580082 : Nat := 118140960795 + 3580082 * 2 ^ 59
def prefixEnd_3580082 : Nat := 4983230072969 + 3 ^ 40 * 3580082 * 2
def baseEnd_3580082 : Nat := 1838302848509767146410509

theorem tailTrace_3580082 : CollatzResearch.WordTrace tailWord_3580082 prefixEnd_3580082 1838302848509767146410509 := by
  unfold tailWord_3580082
  simp only [CollatzResearch.WordTrace]
  refine ⟨32644079453995454543083625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87050878543987878781556333 32644079453995454543083625)
  ·
    refine ⟨24483059590496590907312719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32644079453995454543083625 24483059590496590907312719)
    ·
      refine ⟨36724589385744886360969079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24483059590496590907312719 36724589385744886360969079)
      ·
        refine ⟨55086884078617329541453619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36724589385744886360969079 55086884078617329541453619)
        ·
          refine ⟨82630326117925994312180429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55086884078617329541453619 82630326117925994312180429)
          ·
            refine ⟨30986372294222247867067661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82630326117925994312180429 30986372294222247867067661)
            ·
              refine ⟨11619889610333342950150373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30986372294222247867067661 11619889610333342950150373)
              ·
                refine ⟨2178729301937501803153195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11619889610333342950150373 2178729301937501803153195)
                ·
                  refine ⟨3268093952906252704729793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2178729301937501803153195 3268093952906252704729793)
                  ·
                    refine ⟨2451070464679689528547345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3268093952906252704729793 2451070464679689528547345)
                    ·
                      refine ⟨1838302848509767146410509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2451070464679689528547345 1838302848509767146410509)
                      ·
                        rfl

theorem cell23_3580082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2].length) (baseStart_3580082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580082 prefixEnd_3580082 := by exact prefixLift 3580082
  have htrace : WordTrace (prefixWord ++ tailWord_3580082) baseStart_3580082 baseEnd_3580082 := by
    simpa [prefixWord, tailWord_3580082, baseEnd_3580082] using wordTrace_append hprefix tailTrace_3580082
  have hstable : (prefixWord ++ tailWord_3580082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580082).length < 2 ^ (prefixWord ++ tailWord_3580082).sum := by decide
  have hdescent : baseEnd_3580082 < baseStart_3580082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580158 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_3580158 : Nat := 118140960795 + 3580158 * 2 ^ 59
def prefixEnd_3580158 : Nat := 4983230072969 + 3 ^ 40 * 3580158 * 2
def baseEnd_3580158 : Nat := 1838341873039508849060159

theorem tailTrace_3580158 : CollatzResearch.WordTrace tailWord_3580158 prefixEnd_3580158 1838341873039508849060159 := by
  unfold tailWord_3580158
  simp only [CollatzResearch.WordTrace]
  refine ⟨16322386220463310394012641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87052726509137655434734085 16322386220463310394012641)
  ·
    refine ⟨12241789665347482795509481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16322386220463310394012641 12241789665347482795509481)
    ·
      refine ⟨9181342249010612096632111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12241789665347482795509481 9181342249010612096632111)
      ·
        refine ⟨13772013373515918144948167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9181342249010612096632111 13772013373515918144948167)
        ·
          refine ⟨20658020060273877217422251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13772013373515918144948167 20658020060273877217422251)
          ·
            refine ⟨30987030090410815826133377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20658020060273877217422251 30987030090410815826133377)
            ·
              refine ⟨23240272567808111869600033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30987030090410815826133377 23240272567808111869600033)
              ·
                refine ⟨17430204425856083902200025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23240272567808111869600033 17430204425856083902200025)
                ·
                  refine ⟨13072653319392062926650019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17430204425856083902200025 13072653319392062926650019)
                  ·
                    refine ⟨19608979979088094389975029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13072653319392062926650019 19608979979088094389975029)
                    ·
                      refine ⟨1838341873039508849060159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19608979979088094389975029 1838341873039508849060159)
                      ·
                        rfl

theorem cell23_3580158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_3580158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580158 prefixEnd_3580158 := by exact prefixLift 3580158
  have htrace : WordTrace (prefixWord ++ tailWord_3580158) baseStart_3580158 baseEnd_3580158 := by
    simpa [prefixWord, tailWord_3580158, baseEnd_3580158] using wordTrace_append hprefix tailTrace_3580158
  have hstable : (prefixWord ++ tailWord_3580158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580158).length < 2 ^ (prefixWord ++ tailWord_3580158).sum := by decide
  have hdescent : baseEnd_3580158 < baseStart_3580158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580161 : List Nat := [1, 2, 4, 1, 1, 2, 1, 4, 7]
def baseStart_3580161 : Nat := 118140960795 + 3580161 * 2 ^ 59
def prefixEnd_3580161 : Nat := 4983230072969 + 3 ^ 40 * 3580161 * 2
def baseEnd_3580161 : Nat := 204260379275719148591405

theorem tailTrace_3580161 : CollatzResearch.WordTrace tailWord_3580161 prefixEnd_3580161 204260379275719148591405 := by
  unfold tailWord_3580161
  simp only [CollatzResearch.WordTrace]
  refine ⟨130579199182695614664460337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87052799455130409776306891 130579199182695614664460337)
  ·
    refine ⟨97934399387021710998345253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130579199182695614664460337 97934399387021710998345253)
    ·
      refine ⟨18362699885066570812189735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97934399387021710998345253 18362699885066570812189735)
      ·
        refine ⟨27544049827599856218284603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18362699885066570812189735 27544049827599856218284603)
        ·
          refine ⟨41316074741399784327426905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27544049827599856218284603 41316074741399784327426905)
          ·
            refine ⟨30987056056049838245570179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41316074741399784327426905 30987056056049838245570179)
            ·
              refine ⟨46480584084074757368355269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30987056056049838245570179 46480584084074757368355269)
              ·
                refine ⟨8715109515764017006566613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46480584084074757368355269 8715109515764017006566613)
                ·
                  refine ⟨204260379275719148591405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8715109515764017006566613 204260379275719148591405)
                  ·
                    rfl

theorem cell23_3580161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 7].length) (baseStart_3580161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580161 prefixEnd_3580161 := by exact prefixLift 3580161
  have htrace : WordTrace (prefixWord ++ tailWord_3580161) baseStart_3580161 baseEnd_3580161 := by
    simpa [prefixWord, tailWord_3580161, baseEnd_3580161] using wordTrace_append hprefix tailTrace_3580161
  have hstable : (prefixWord ++ tailWord_3580161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580161).length < 2 ^ (prefixWord ++ tailWord_3580161).sum := by decide
  have hdescent : baseEnd_3580161 < baseStart_3580161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580195 : List Nat := [1, 1, 1, 4, 2, 2, 5, 2, 5]
def baseStart_3580195 : Nat := 118140960795 + 3580195 * 2 ^ 59
def prefixEnd_3580195 : Nat := 4983230072969 + 3 ^ 40 * 3580195 * 2
def baseEnd_3580195 : Nat := 204262319091525022699721

theorem tailTrace_3580195 : CollatzResearch.WordTrace tailWord_3580195 prefixEnd_3580195 204262319091525022699721 := by
  unfold tailWord_3580195
  simp only [CollatzResearch.WordTrace]
  refine ⟨130580439264572438471198039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87053626176381625647465359 130580439264572438471198039)
  ·
    refine ⟨195870658896858657706797059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130580439264572438471198039 195870658896858657706797059)
    ·
      refine ⟨293805988345287986560195589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195870658896858657706797059 293805988345287986560195589)
      ·
        refine ⟨55088622814741497480036673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293805988345287986560195589 55088622814741497480036673)
        ·
          refine ⟨41316467111056123110027505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55088622814741497480036673 41316467111056123110027505)
          ·
            refine ⟨30987350333292092332520629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41316467111056123110027505 30987350333292092332520629)
            ·
              refine ⟨2905064093746133656173809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30987350333292092332520629 2905064093746133656173809)
              ·
                refine ⟨2178798070309600242130357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2905064093746133656173809 2178798070309600242130357)
                ·
                  refine ⟨204262319091525022699721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2178798070309600242130357 204262319091525022699721)
                  ·
                    rfl

theorem cell23_3580195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 5].length) (baseStart_3580195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580195 prefixEnd_3580195 := by exact prefixLift 3580195
  have htrace : WordTrace (prefixWord ++ tailWord_3580195) baseStart_3580195 baseEnd_3580195 := by
    simpa [prefixWord, tailWord_3580195, baseEnd_3580195] using wordTrace_append hprefix tailTrace_3580195
  have hstable : (prefixWord ++ tailWord_3580195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580195).length < 2 ^ (prefixWord ++ tailWord_3580195).sum := by decide
  have hdescent : baseEnd_3580195 < baseStart_3580195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580206 : List Nat := [4, 1, 3, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_3580206 : Nat := 118140960795 + 3580206 * 2 ^ 59
def prefixEnd_3580206 : Nat := 4983230072969 + 3 ^ 40 * 3580206 * 2
def baseEnd_3580206 : Nat := 1838366520110924661259939

theorem tailTrace_3580206 : CollatzResearch.WordTrace tailWord_3580206 prefixEnd_3580206 1838366520110924661259939 := by
  unfold tailWord_3580206
  simp only [CollatzResearch.WordTrace]
  refine ⟨16322605058441573418731059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87053893645021724899898981 16322605058441573418731059)
  ·
    refine ⟨24483907587662360128096589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16322605058441573418731059 24483907587662360128096589)
    ·
      refine ⟨9181465345373385048036221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24483907587662360128096589 9181465345373385048036221)
      ·
        refine ⟨3443049504515019393013583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9181465345373385048036221 3443049504515019393013583)
        ·
          refine ⟨5164574256772529089520375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3443049504515019393013583 5164574256772529089520375)
          ·
            refine ⟨7746861385158793634280563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5164574256772529089520375 7746861385158793634280563)
            ·
              refine ⟨11620292077738190451420845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7746861385158793634280563 11620292077738190451420845)
              ·
                refine ⟨4357609529151821419282817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11620292077738190451420845 4357609529151821419282817)
                ·
                  refine ⟨3268207146863866064462113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4357609529151821419282817 3268207146863866064462113)
                  ·
                    refine ⟨2451155360147899548346585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3268207146863866064462113 2451155360147899548346585)
                    ·
                      refine ⟨1838366520110924661259939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2451155360147899548346585 1838366520110924661259939)
                      ·
                        rfl

theorem cell23_3580206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_3580206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580206 prefixEnd_3580206 := by exact prefixLift 3580206
  have htrace : WordTrace (prefixWord ++ tailWord_3580206) baseStart_3580206 baseEnd_3580206 := by
    simpa [prefixWord, tailWord_3580206, baseEnd_3580206] using wordTrace_append hprefix tailTrace_3580206
  have hstable : (prefixWord ++ tailWord_3580206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580206).length < 2 ^ (prefixWord ++ tailWord_3580206).sum := by decide
  have hdescent : baseEnd_3580206 < baseStart_3580206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580238 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 7, 4]
def baseStart_3580238 : Nat := 118140960795 + 3580238 * 2 ^ 59
def prefixEnd_3580238 : Nat := 4983230072969 + 3 ^ 40 * 3580238 * 2
def baseEnd_3580238 : Nat := 612794317163956178686597

theorem tailTrace_3580238 : CollatzResearch.WordTrace tailWord_3580238 prefixEnd_3580238 612794317163956178686597 := by
  unfold tailWord_3580238
  simp only [CollatzResearch.WordTrace]
  refine ⟨16322750950427082101876671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87054671735611104543342245 16322750950427082101876671)
  ·
    refine ⟨24484126425640623152815007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16322750950427082101876671 24484126425640623152815007)
    ·
      refine ⟨36726189638460934729222511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24484126425640623152815007 36726189638460934729222511)
      ·
        refine ⟨55089284457691402093833767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36726189638460934729222511 55089284457691402093833767)
        ·
          refine ⟨82633926686537103140750651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55089284457691402093833767 82633926686537103140750651)
          ·
            refine ⟨123950890029805654711125977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82633926686537103140750651 123950890029805654711125977)
            ·
              refine ⟨92963167522354241033344483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123950890029805654711125977 92963167522354241033344483)
              ·
                refine ⟨139444751283531361550016725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92963167522354241033344483 139444751283531361550016725)
                ·
                  refine ⟨3268236358207766286328517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 139444751283531361550016725 3268236358207766286328517)
                  ·
                    refine ⟨612794317163956178686597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3268236358207766286328517 612794317163956178686597)
                    ·
                      rfl

theorem cell23_3580238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_3580238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580238 prefixEnd_3580238 := by exact prefixLift 3580238
  have htrace : WordTrace (prefixWord ++ tailWord_3580238) baseStart_3580238 baseEnd_3580238 := by
    simpa [prefixWord, tailWord_3580238, baseEnd_3580238] using wordTrace_append hprefix tailTrace_3580238
  have hstable : (prefixWord ++ tailWord_3580238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580238).length < 2 ^ (prefixWord ++ tailWord_3580238).sum := by decide
  have hdescent : baseEnd_3580238 < baseStart_3580238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580248 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 4, 2, 3]
def baseStart_3580248 : Nat := 118140960795 + 3580248 * 2 ^ 59
def prefixEnd_3580248 : Nat := 4983230072969 + 3 ^ 40 * 3580248 * 2
def baseEnd_3580248 : Nat := 1838388086298413496934745

theorem tailTrace_3580248 : CollatzResearch.WordTrace tailWord_3580248 prefixEnd_3580248 1838388086298413496934745 := by
  unfold tailWord_3580248
  simp only [CollatzResearch.WordTrace]
  refine ⟨65291186166690214261438699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87054914888920285681918265 65291186166690214261438699)
  ·
    refine ⟨97936779250035321392158049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65291186166690214261438699 97936779250035321392158049)
    ·
      refine ⟨73452584437526491044118537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97936779250035321392158049 73452584437526491044118537)
      ·
        refine ⟨55089438328144868283088903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73452584437526491044118537 55089438328144868283088903)
        ·
          refine ⟨82634157492217302424633355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55089438328144868283088903 82634157492217302424633355)
          ·
            refine ⟨123951236238325953636950033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82634157492217302424633355 123951236238325953636950033)
            ·
              refine ⟨92963427178744465227712525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123951236238325953636950033 92963427178744465227712525)
              ·
                refine ⟨34861285192029174460392197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92963427178744465227712525 34861285192029174460392197)
                ·
                  refine ⟨6536490973505470211323537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34861285192029174460392197 6536490973505470211323537)
                  ·
                    refine ⟨4902368230129102658492653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6536490973505470211323537 4902368230129102658492653)
                    ·
                      refine ⟨1838388086298413496934745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4902368230129102658492653 1838388086298413496934745)
                      ·
                        rfl

theorem cell23_3580248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_3580248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580248 prefixEnd_3580248 := by exact prefixLift 3580248
  have htrace : WordTrace (prefixWord ++ tailWord_3580248) baseStart_3580248 baseEnd_3580248 := by
    simpa [prefixWord, tailWord_3580248, baseEnd_3580248] using wordTrace_append hprefix tailTrace_3580248
  have hstable : (prefixWord ++ tailWord_3580248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580248).length < 2 ^ (prefixWord ++ tailWord_3580248).sum := by decide
  have hdescent : baseEnd_3580248 < baseStart_3580248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580271 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 6]
def baseStart_3580271 : Nat := 118140960795 + 3580271 * 2 ^ 59
def prefixEnd_3580271 : Nat := 4983230072969 + 3 ^ 40 * 3580271 * 2
def baseEnd_3580271 : Nat := 1838399896353466906947139

theorem tailTrace_3580271 : CollatzResearch.WordTrace tailWord_3580271 prefixEnd_3580271 1838399896353466906947139 := by
  unfold tailWord_3580271
  simp only [CollatzResearch.WordTrace]
  refine ⟨130583211212297103450964667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87055474141531402300643111 130583211212297103450964667)
  ·
    refine ⟨195874816818445655176447001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130583211212297103450964667 195874816818445655176447001)
    ·
      refine ⟨146906112613834241382335251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195874816818445655176447001 146906112613834241382335251)
      ·
        refine ⟨220359168920751362073502877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146906112613834241382335251 220359168920751362073502877)
        ·
          refine ⟨82634688345281760777563579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220359168920751362073502877 82634688345281760777563579)
          ·
            refine ⟨123952032517922641166345369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82634688345281760777563579 123952032517922641166345369)
            ·
              refine ⟨92964024388441980874759027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123952032517922641166345369 92964024388441980874759027)
              ·
                refine ⟨139446036582662971312138541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92964024388441980874759027 139446036582662971312138541)
                ·
                  refine ⟨52292263718498614242051953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139446036582662971312138541 52292263718498614242051953)
                  ·
                    refine ⟨39219197788873960681538965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52292263718498614242051953 39219197788873960681538965)
                    ·
                      refine ⟨1838399896353466906947139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39219197788873960681538965 1838399896353466906947139)
                      ·
                        rfl

theorem cell23_3580271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_3580271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580271 prefixEnd_3580271 := by exact prefixLift 3580271
  have htrace : WordTrace (prefixWord ++ tailWord_3580271) baseStart_3580271 baseEnd_3580271 := by
    simpa [prefixWord, tailWord_3580271, baseEnd_3580271] using wordTrace_append hprefix tailTrace_3580271
  have hstable : (prefixWord ++ tailWord_3580271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580271).length < 2 ^ (prefixWord ++ tailWord_3580271).sum := by decide
  have hdescent : baseEnd_3580271 < baseStart_3580271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580289 : List Nat := [1, 2, 4, 3, 1, 2, 2, 3, 1, 4]
def baseStart_3580289 : Nat := 118140960795 + 3580289 * 2 ^ 59
def prefixEnd_3580289 : Nat := 4983230072969 + 3 ^ 40 * 3580289 * 2
def baseEnd_3580289 : Nat := 612803046335082612174019

theorem tailTrace_3580289 : CollatzResearch.WordTrace tailWord_3580289 prefixEnd_3580289 612803046335082612174019 := by
  unfold tailWord_3580289
  simp only [CollatzResearch.WordTrace]
  refine ⟨130583867726231892525119921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87055911817487928350079947 130583867726231892525119921)
  ·
    refine ⟨97937900794673919393839941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130583867726231892525119921 97937900794673919393839941)
    ·
      refine ⟨18363356399001359886344989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97937900794673919393839941 18363356399001359886344989)
      ·
        refine ⟨6886258649625509957379371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18363356399001359886344989 6886258649625509957379371)
        ·
          refine ⟨10329387974438264936069057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6886258649625509957379371 10329387974438264936069057)
          ·
            refine ⟨7747040980828698702051793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10329387974438264936069057 7747040980828698702051793)
            ·
              refine ⟨5810280735621524026538845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7747040980828698702051793 5810280735621524026538845)
              ·
                refine ⟨2178855275858071509952067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5810280735621524026538845 2178855275858071509952067)
                ·
                  refine ⟨3268282913787107264928101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2178855275858071509952067 3268282913787107264928101)
                  ·
                    refine ⟨612803046335082612174019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3268282913787107264928101 612803046335082612174019)
                    ·
                      rfl

theorem cell23_3580289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_3580289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580289 prefixEnd_3580289 := by exact prefixLift 3580289
  have htrace : WordTrace (prefixWord ++ tailWord_3580289) baseStart_3580289 baseEnd_3580289 := by
    simpa [prefixWord, tailWord_3580289, baseEnd_3580289] using wordTrace_append hprefix tailTrace_3580289
  have hstable : (prefixWord ++ tailWord_3580289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580289).length < 2 ^ (prefixWord ++ tailWord_3580289).sum := by decide
  have hdescent : baseEnd_3580289 < baseStart_3580289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580295 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 5, 1, 3]
def baseStart_3580295 : Nat := 118140960795 + 3580295 * 2 ^ 59
def prefixEnd_3580295 : Nat := 4983230072969 + 3 ^ 40 * 3580295 * 2
def baseEnd_3580295 : Nat := 1838412219889174813047029

theorem tailTrace_3580295 : CollatzResearch.WordTrace tailWord_3580295 prefixEnd_3580295 1838412219889174813047029 := by
  unfold tailWord_3580295
  simp only [CollatzResearch.WordTrace]
  refine ⟨130584086564210155549838339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87056057709473437033225559 130584086564210155549838339)
  ·
    refine ⟨195876129846315233324757509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130584086564210155549838339 195876129846315233324757509)
    ·
      refine ⟨36726774346184106248392033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195876129846315233324757509 36726774346184106248392033)
      ·
        refine ⟨27545080759638079686294025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36726774346184106248392033 27545080759638079686294025)
        ·
          refine ⟨20658810569728559764720519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27545080759638079686294025 20658810569728559764720519)
          ·
            refine ⟨30988215854592839647080779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20658810569728559764720519 30988215854592839647080779)
            ·
              refine ⟨46482323781889259470621169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30988215854592839647080779 46482323781889259470621169)
              ·
                refine ⟨34861742836416944602965877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46482323781889259470621169 34861742836416944602965877)
                ·
                  refine ⟨3268288390914088556528051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34861742836416944602965877 3268288390914088556528051)
                  ·
                    refine ⟨4902432586371132834792077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3268288390914088556528051 4902432586371132834792077)
                    ·
                      refine ⟨1838412219889174813047029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4902432586371132834792077 1838412219889174813047029)
                      ·
                        rfl

theorem cell23_3580295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_3580295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580295 prefixEnd_3580295 := by exact prefixLift 3580295
  have htrace : WordTrace (prefixWord ++ tailWord_3580295) baseStart_3580295 baseEnd_3580295 := by
    simpa [prefixWord, tailWord_3580295, baseEnd_3580295] using wordTrace_append hprefix tailTrace_3580295
  have hstable : (prefixWord ++ tailWord_3580295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580295).length < 2 ^ (prefixWord ++ tailWord_3580295).sum := by decide
  have hdescent : baseEnd_3580295 < baseStart_3580295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580302 : List Nat := [4, 1, 1, 4, 1, 3, 1, 2, 6]
def baseStart_3580302 : Nat := 118140960795 + 3580302 * 2 ^ 59
def prefixEnd_3580302 : Nat := 4983230072969 + 3 ^ 40 * 3580302 * 2
def baseEnd_3580302 : Nat := 204268423805972920628833

theorem tailTrace_3580302 : CollatzResearch.WordTrace tailWord_3580302 prefixEnd_3580302 204268423805972920628833 := by
  unfold tailWord_3580302
  simp only [CollatzResearch.WordTrace]
  refine ⟨16323042734398099468167895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87056227916789863830228773 16323042734398099468167895)
  ·
    refine ⟨24484564101597149202251843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16323042734398099468167895 24484564101597149202251843)
    ·
      refine ⟨36726846152395723803377765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24484564101597149202251843 36726846152395723803377765)
      ·
        refine ⟨6886283653574198213133331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36726846152395723803377765 6886283653574198213133331)
        ·
          refine ⟨10329425480361297319699997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6886283653574198213133331 10329425480361297319699997)
          ·
            refine ⟨3873534555135486494887499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10329425480361297319699997 3873534555135486494887499)
            ·
              refine ⟨5810301832703229742331249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3873534555135486494887499 5810301832703229742331249)
              ·
                refine ⟨4357726374527422306748437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5810301832703229742331249 4357726374527422306748437)
                ·
                  refine ⟨204268423805972920628833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4357726374527422306748437 204268423805972920628833)
                  ·
                    rfl

theorem cell23_3580302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_3580302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580302 prefixEnd_3580302 := by exact prefixLift 3580302
  have htrace : WordTrace (prefixWord ++ tailWord_3580302) baseStart_3580302 baseEnd_3580302 := by
    simpa [prefixWord, tailWord_3580302, baseEnd_3580302] using wordTrace_append hprefix tailTrace_3580302
  have hstable : (prefixWord ++ tailWord_3580302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580302).length < 2 ^ (prefixWord ++ tailWord_3580302).sum := by decide
  have hdescent : baseEnd_3580302 < baseStart_3580302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580312 : List Nat := [2, 1, 2, 5, 1, 1, 1, 3, 3, 1, 3]
def baseStart_3580312 : Nat := 118140960795 + 3580312 * 2 ^ 59
def prefixEnd_3580312 : Nat := 4983230072969 + 3 ^ 40 * 3580312 * 2
def baseEnd_3580312 : Nat := 1838420949060301246534451

theorem tailTrace_3580312 : CollatzResearch.WordTrace tailWord_3580312 prefixEnd_3580312 1838420949060301246534451 := by
  unfold tailWord_3580312
  simp only [CollatzResearch.WordTrace]
  refine ⟨65292353302574283726603595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87056471070099044968804793 65292353302574283726603595)
  ·
    refine ⟨97938529953861425589905393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65292353302574283726603595 97938529953861425589905393)
    ·
      refine ⟨73453897465396069192429045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97938529953861425589905393 73453897465396069192429045)
      ·
        refine ⟨6886302887380881486790223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73453897465396069192429045 6886302887380881486790223)
        ·
          refine ⟨10329454331071322230185335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6886302887380881486790223 10329454331071322230185335)
          ·
            refine ⟨15494181496606983345278003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10329454331071322230185335 15494181496606983345278003)
            ·
              refine ⟨23241272244910475017917005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15494181496606983345278003 23241272244910475017917005)
              ·
                refine ⟨8715477091841428131718877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23241272244910475017917005 8715477091841428131718877)
                ·
                  refine ⟨3268303909440535549394579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8715477091841428131718877 3268303909440535549394579)
                  ·
                    refine ⟨4902455864160803324091869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3268303909440535549394579 4902455864160803324091869)
                    ·
                      refine ⟨1838420949060301246534451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4902455864160803324091869 1838420949060301246534451)
                      ·
                        rfl

theorem cell23_3580312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_3580312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580312 prefixEnd_3580312 := by exact prefixLift 3580312
  have htrace : WordTrace (prefixWord ++ tailWord_3580312) baseStart_3580312 baseEnd_3580312 := by
    simpa [prefixWord, tailWord_3580312, baseEnd_3580312] using wordTrace_append hprefix tailTrace_3580312
  have hstable : (prefixWord ++ tailWord_3580312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580312).length < 2 ^ (prefixWord ++ tailWord_3580312).sum := by decide
  have hdescent : baseEnd_3580312 < baseStart_3580312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580338 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_3580338 : Nat := 118140960795 + 3580338 * 2 ^ 59
def prefixEnd_3580338 : Nat := 4983230072969 + 3 ^ 40 * 3580338 * 2
def baseEnd_3580338 : Nat := 1838434299557318144809331

theorem tailTrace_3580338 : CollatzResearch.WordTrace tailWord_3580338 prefixEnd_3580338 1838434299557318144809331 := by
  unfold tailWord_3580338
  simp only [CollatzResearch.WordTrace]
  refine ⟨32646413725763593473413417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87057103268702915929102445 32646413725763593473413417)
  ·
    refine ⟨24484810294322695105060063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32646413725763593473413417 24484810294322695105060063)
    ·
      refine ⟨36727215441484042657590095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24484810294322695105060063 36727215441484042657590095)
      ·
        refine ⟨55090823162226063986385143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36727215441484042657590095 55090823162226063986385143)
        ·
          refine ⟨82636234743339095979577715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55090823162226063986385143 82636234743339095979577715)
          ·
            refine ⟨123954352115008643969366573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82636234743339095979577715 123954352115008643969366573)
            ·
              refine ⟨46482882043128241488512465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123954352115008643969366573 46482882043128241488512465)
              ·
                refine ⟨34862161532346181116384349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46482882043128241488512465 34862161532346181116384349)
                ·
                  refine ⟨13073310574629817918644131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34862161532346181116384349 13073310574629817918644131)
                  ·
                    refine ⟨19609965861944726877966197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13073310574629817918644131 19609965861944726877966197)
                    ·
                      refine ⟨1838434299557318144809331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19609965861944726877966197 1838434299557318144809331)
                      ·
                        rfl

theorem cell23_3580338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_3580338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580338 prefixEnd_3580338 := by exact prefixLift 3580338
  have htrace : WordTrace (prefixWord ++ tailWord_3580338) baseStart_3580338 baseEnd_3580338 := by
    simpa [prefixWord, tailWord_3580338, baseEnd_3580338] using wordTrace_append hprefix tailTrace_3580338
  have hstable : (prefixWord ++ tailWord_3580338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580338).length < 2 ^ (prefixWord ++ tailWord_3580338).sum := by decide
  have hdescent : baseEnd_3580338 < baseStart_3580338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580340 : List Nat := [2, 5, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_3580340 : Nat := 118140960795 + 3580340 * 2 ^ 59
def prefixEnd_3580340 : Nat := 4983230072969 + 3 ^ 40 * 3580340 * 2
def baseEnd_3580340 : Nat := 612811775506209045661441

theorem tailTrace_3580340 : CollatzResearch.WordTrace tailWord_3580340 prefixEnd_3580340 612811775506209045661441 := by
  unfold tailWord_3580340
  simp only [CollatzResearch.WordTrace]
  refine ⟨65292863924523564117613237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87057151899364752156817649 65292863924523564117613237)
  ·
    refine ⟨6121205992924084136026241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65292863924523564117613237 6121205992924084136026241)
    ·
      refine ⟨4590904494693063102019681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6121205992924084136026241 4590904494693063102019681)
      ·
        refine ⟨3443178371019797326514761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4590904494693063102019681 3443178371019797326514761)
        ·
          refine ⟨2582383778264847994886071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3443178371019797326514761 2582383778264847994886071)
          ·
            refine ⟨3873575667397271992329107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582383778264847994886071 3873575667397271992329107)
            ·
              refine ⟨5810363501095907988493661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3873575667397271992329107 5810363501095907988493661)
              ·
                refine ⟨2178886312910965495685123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5810363501095907988493661 2178886312910965495685123)
                ·
                  refine ⟨3268329469366448243527685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2178886312910965495685123 3268329469366448243527685)
                  ·
                    refine ⟨612811775506209045661441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3268329469366448243527685 612811775506209045661441)
                    ·
                      rfl

theorem cell23_3580340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_3580340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580340 prefixEnd_3580340 := by exact prefixLift 3580340
  have htrace : WordTrace (prefixWord ++ tailWord_3580340) baseStart_3580340 baseEnd_3580340 := by
    simpa [prefixWord, tailWord_3580340, baseEnd_3580340] using wordTrace_append hprefix tailTrace_3580340
  have hstable : (prefixWord ++ tailWord_3580340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580340).length < 2 ^ (prefixWord ++ tailWord_3580340).sum := by decide
  have hdescent : baseEnd_3580340 < baseStart_3580340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580345 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 4, 4]
def baseStart_3580345 : Nat := 118140960795 + 3580345 * 2 ^ 59
def prefixEnd_3580345 : Nat := 4983230072969 + 3 ^ 40 * 3580345 * 2
def baseEnd_3580345 : Nat := 612812631307299872473933

theorem tailTrace_3580345 : CollatzResearch.WordTrace tailWord_3580345 prefixEnd_3580345 612812631307299872473933 := by
  unfold tailWord_3580345
  simp only [CollatzResearch.WordTrace]
  refine ⟨130585910214029014089158489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87057273476019342726105659 130585910214029014089158489)
  ·
    refine ⟨97939432660521760566868867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130585910214029014089158489 97939432660521760566868867)
    ·
      refine ⟨146909148990782640850303301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97939432660521760566868867 146909148990782640850303301)
      ·
        refine ⟨27545465435771745159431869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146909148990782640850303301 27545465435771745159431869)
        ·
          refine ⟨10329549538414404434786951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27545465435771745159431869 10329549538414404434786951)
          ·
            refine ⟨15494324307621606652180427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10329549538414404434786951 15494324307621606652180427)
            ·
              refine ⟨23241486461432409978270641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15494324307621606652180427 23241486461432409978270641)
              ·
                refine ⟨17431114846074307483702981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23241486461432409978270641 17431114846074307483702981)
                ·
                  refine ⟨3268334033638932653194309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17431114846074307483702981 3268334033638932653194309)
                  ·
                    refine ⟨612812631307299872473933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3268334033638932653194309 612812631307299872473933)
                    ·
                      rfl

theorem cell23_3580345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 4].length) (baseStart_3580345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580345 prefixEnd_3580345 := by exact prefixLift 3580345
  have htrace : WordTrace (prefixWord ++ tailWord_3580345) baseStart_3580345 baseEnd_3580345 := by
    simpa [prefixWord, tailWord_3580345, baseEnd_3580345] using wordTrace_append hprefix tailTrace_3580345
  have hstable : (prefixWord ++ tailWord_3580345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580345).length < 2 ^ (prefixWord ++ tailWord_3580345).sum := by decide
  have hdescent : baseEnd_3580345 < baseStart_3580345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580368 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 3]
def baseStart_3580368 : Nat := 118140960795 + 3580368 * 2 ^ 59
def prefixEnd_3580368 : Nat := 4983230072969 + 3 ^ 40 * 3580368 * 2
def baseEnd_3580368 : Nat := 1838449703976953027434193

theorem tailTrace_3580368 : CollatzResearch.WordTrace tailWord_3580368 prefixEnd_3580368 1838449703976953027434193 := by
  unfold tailWord_3580368
  simp only [CollatzResearch.WordTrace]
  refine ⟨65293374546472844508622879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87057832728630459344830505 65293374546472844508622879)
  ·
    refine ⟨97940061819709266762934319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65293374546472844508622879 97940061819709266762934319)
    ·
      refine ⟨146910092729563900144401479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97940061819709266762934319 146910092729563900144401479)
      ·
        refine ⟨220365139094345850216602219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146910092729563900144401479 220365139094345850216602219)
        ·
          refine ⟨330547708641518775324903329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220365139094345850216602219 330547708641518775324903329)
          ·
            refine ⟨247910781481139081493677497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330547708641518775324903329 247910781481139081493677497)
            ·
              refine ⟨185933086110854311120258123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247910781481139081493677497 185933086110854311120258123)
              ·
                refine ⟨278899629166281466680387185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185933086110854311120258123 278899629166281466680387185)
                ·
                  refine ⟨209174721874711100010290389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278899629166281466680387185 209174721874711100010290389)
                  ·
                    refine ⟨4902532543938541406491181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 209174721874711100010290389 4902532543938541406491181)
                    ·
                      refine ⟨1838449703976953027434193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4902532543938541406491181 1838449703976953027434193)
                      ·
                        rfl

theorem cell23_3580368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 3].length) (baseStart_3580368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580368 prefixEnd_3580368 := by exact prefixLift 3580368
  have htrace : WordTrace (prefixWord ++ tailWord_3580368) baseStart_3580368 baseEnd_3580368 := by
    simpa [prefixWord, tailWord_3580368, baseEnd_3580368] using wordTrace_append hprefix tailTrace_3580368
  have hstable : (prefixWord ++ tailWord_3580368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580368).length < 2 ^ (prefixWord ++ tailWord_3580368).sum := by decide
  have hdescent : baseEnd_3580368 < baseStart_3580368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580369 : List Nat := [1, 2, 2, 1, 2, 1, 1, 8, 1, 2, 2]
def baseStart_3580369 : Nat := 118140960795 + 3580369 * 2 ^ 59
def prefixEnd_3580369 : Nat := 4983230072969 + 3 ^ 40 * 3580369 * 2
def baseEnd_3580369 : Nat := 1838450217457607523521689

theorem tailTrace_3580369 : CollatzResearch.WordTrace tailWord_3580369 prefixEnd_3580369 1838450217457607523521689 := by
  unfold tailWord_3580369
  simp only [CollatzResearch.WordTrace]
  refine ⟨130586785565942066188032161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87057857043961377458688107 130586785565942066188032161)
  ·
    refine ⟨97940089174456549641024121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130586785565942066188032161 97940089174456549641024121)
    ·
      refine ⟨73455066880842412230768091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97940089174456549641024121 73455066880842412230768091)
      ·
        refine ⟨110182600321263618346152137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73455066880842412230768091 110182600321263618346152137)
        ·
          refine ⟨82636950240947713759614103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110182600321263618346152137 82636950240947713759614103)
          ·
            refine ⟨123955425361421570639421155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82636950240947713759614103 123955425361421570639421155)
            ·
              refine ⟨185933138042132355959131733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123955425361421570639421155 185933138042132355959131733)
              ·
                refine ⟨2178903961431238546396075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 185933138042132355959131733 2178903961431238546396075)
                ·
                  refine ⟨3268355942146857819594113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2178903961431238546396075 3268355942146857819594113)
                  ·
                    refine ⟨2451266956610143364695585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3268355942146857819594113 2451266956610143364695585)
                    ·
                      refine ⟨1838450217457607523521689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2451266956610143364695585 1838450217457607523521689)
                      ·
                        rfl

theorem cell23_3580369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 1, 2, 2].length) (baseStart_3580369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580369 prefixEnd_3580369 := by exact prefixLift 3580369
  have htrace : WordTrace (prefixWord ++ tailWord_3580369) baseStart_3580369 baseEnd_3580369 := by
    simpa [prefixWord, tailWord_3580369, baseEnd_3580369] using wordTrace_append hprefix tailTrace_3580369
  have hstable : (prefixWord ++ tailWord_3580369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580369).length < 2 ^ (prefixWord ++ tailWord_3580369).sum := by decide
  have hdescent : baseEnd_3580369 < baseStart_3580369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580378 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6]
def baseStart_3580378 : Nat := 118140960795 + 3580378 * 2 ^ 59
def prefixEnd_3580378 : Nat := 4983230072969 + 3 ^ 40 * 3580378 * 2
def baseEnd_3580378 : Nat := 1838454838783497988309147

theorem tailTrace_3580378 : CollatzResearch.WordTrace tailWord_3580378 prefixEnd_3580378 1838454838783497988309147 := by
  unfold tailWord_3580378
  simp only [CollatzResearch.WordTrace]
  refine ⟨32646778455727365181277447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87058075881939640483406525 32646778455727365181277447)
  ·
    refine ⟨48970167683591047771916171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32646778455727365181277447 48970167683591047771916171)
    ·
      refine ⟨73455251525386571657874257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48970167683591047771916171 73455251525386571657874257)
      ·
        refine ⟨55091438644039928743405693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73455251525386571657874257 55091438644039928743405693)
        ·
          refine ⟨20659289491514973278777135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55091438644039928743405693 20659289491514973278777135)
          ·
            refine ⟨30988934237272459918165703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20659289491514973278777135 30988934237272459918165703)
            ·
              refine ⟨46483401355908689877248555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30988934237272459918165703 46483401355908689877248555)
              ·
                refine ⟨69725102033863034815872833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46483401355908689877248555 69725102033863034815872833)
                ·
                  refine ⟨52293826525397276111904625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69725102033863034815872833 52293826525397276111904625)
                  ·
                    refine ⟨39220369894047957083928469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52293826525397276111904625 39220369894047957083928469)
                    ·
                      refine ⟨1838454838783497988309147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39220369894047957083928469 1838454838783497988309147)
                      ·
                        rfl

theorem cell23_3580378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_3580378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580378 prefixEnd_3580378 := by exact prefixLift 3580378
  have htrace : WordTrace (prefixWord ++ tailWord_3580378) baseStart_3580378 baseEnd_3580378 := by
    simpa [prefixWord, tailWord_3580378, baseEnd_3580378] using wordTrace_append hprefix tailTrace_3580378
  have hstable : (prefixWord ++ tailWord_3580378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580378).length < 2 ^ (prefixWord ++ tailWord_3580378).sum := by decide
  have hdescent : baseEnd_3580378 < baseStart_3580378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580385 : List Nat := [1, 2, 3, 1, 2, 2, 2, 3, 1, 3, 3]
def baseStart_3580385 : Nat := 118140960795 + 3580385 * 2 ^ 59
def prefixEnd_3580385 : Nat := 4983230072969 + 3 ^ 40 * 3580385 * 2
def baseEnd_3580385 : Nat := 1838458433148079460921615

theorem tailTrace_3580385 : CollatzResearch.WordTrace tailWord_3580385 prefixEnd_3580385 1838458433148079460921615 := by
  unfold tailWord_3580385
  simp only [CollatzResearch.WordTrace]
  refine ⟨130587369133884100920614609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87058246089256067280409739 130587369133884100920614609)
  ·
    refine ⟨97940526850413075690460957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130587369133884100920614609 97940526850413075690460957)
    ·
      refine ⟨36727697568904903383922859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97940526850413075690460957 36727697568904903383922859)
      ·
        refine ⟨55091546353357355075884289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36727697568904903383922859 55091546353357355075884289)
        ·
          refine ⟨41318659765018016306913217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55091546353357355075884289 41318659765018016306913217)
          ·
            refine ⟨30988994823763512230184913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41318659765018016306913217 30988994823763512230184913)
            ·
              refine ⟨23241746117822634172638685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30988994823763512230184913 23241746117822634172638685)
              ·
                refine ⟨8715654794183487814739507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23241746117822634172638685 8715654794183487814739507)
                ·
                  refine ⟨13073482191275231722109261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8715654794183487814739507 13073482191275231722109261)
                  ·
                    refine ⟨4902555821728211895790973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13073482191275231722109261 4902555821728211895790973)
                    ·
                      refine ⟨1838458433148079460921615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4902555821728211895790973 1838458433148079460921615)
                      ·
                        rfl

theorem cell23_3580385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_3580385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580385 prefixEnd_3580385 := by exact prefixLift 3580385
  have htrace : WordTrace (prefixWord ++ tailWord_3580385) baseStart_3580385 baseEnd_3580385 := by
    simpa [prefixWord, tailWord_3580385, baseEnd_3580385] using wordTrace_append hprefix tailTrace_3580385
  have hstable : (prefixWord ++ tailWord_3580385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580385).length < 2 ^ (prefixWord ++ tailWord_3580385).sum := by decide
  have hdescent : baseEnd_3580385 < baseStart_3580385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580420 : List Nat := [2, 3, 2, 3, 1, 3, 2, 2, 1, 2, 2]
def baseStart_3580420 : Nat := 118140960795 + 3580420 * 2 ^ 59
def prefixEnd_3580420 : Nat := 4983230072969 + 3 ^ 40 * 3580420 * 2
def baseEnd_3580420 : Nat := 1838476404970986823983955

theorem tailTrace_3580420 : CollatzResearch.WordTrace tailWord_3580420 prefixEnd_3580420 1838476404970986823983955 := by
  unfold tailWord_3580420
  simp only [CollatzResearch.WordTrace]
  refine ⟨65294322844378650949069357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87059097125838201265425809 65294322844378650949069357)
  ·
    refine ⟨24485371066641994105901009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65294322844378650949069357 24485371066641994105901009)
    ·
      refine ⟨18364028299981495579425757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24485371066641994105901009 18364028299981495579425757)
      ·
        refine ⟨6886510612493060842284659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18364028299981495579425757 6886510612493060842284659)
        ·
          refine ⟨10329765918739591263426989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6886510612493060842284659 10329765918739591263426989)
          ·
            refine ⟨3873662219527346723785121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10329765918739591263426989 3873662219527346723785121)
            ·
              refine ⟨2905246664645510042838841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3873662219527346723785121 2905246664645510042838841)
              ·
                refine ⟨2178934998484132532129131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2905246664645510042838841 2178934998484132532129131)
                ·
                  refine ⟨3268402497726198798193697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2178934998484132532129131 3268402497726198798193697)
                  ·
                    refine ⟨2451301873294649098645273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3268402497726198798193697 2451301873294649098645273)
                    ·
                      refine ⟨1838476404970986823983955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2451301873294649098645273 1838476404970986823983955)
                      ·
                        rfl

theorem cell23_3580420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_3580420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580420 prefixEnd_3580420 := by exact prefixLift 3580420
  have htrace : WordTrace (prefixWord ++ tailWord_3580420) baseStart_3580420 baseEnd_3580420 := by
    simpa [prefixWord, tailWord_3580420, baseEnd_3580420] using wordTrace_append hprefix tailTrace_3580420
  have hstable : (prefixWord ++ tailWord_3580420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580420).length < 2 ^ (prefixWord ++ tailWord_3580420).sum := by decide
  have hdescent : baseEnd_3580420 < baseStart_3580420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580436 : List Nat := [2, 4, 3, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_3580436 : Nat := 118140960795 + 3580436 * 2 ^ 59
def prefixEnd_3580436 : Nat := 4983230072969 + 3 ^ 40 * 3580436 * 2
def baseEnd_3580436 : Nat := 1838484620661458761383881

theorem tailTrace_3580436 : CollatzResearch.WordTrace tailWord_3580436 prefixEnd_3580436 1838484620661458761383881 := by
  unfold tailWord_3580436
  simp only [CollatzResearch.WordTrace]
  refine ⟨65294614628349668315360581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87059486171132891087147441 65294614628349668315360581)
  ·
    refine ⟨12242740242815562809130109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65294614628349668315360581 12242740242815562809130109)
    ·
      refine ⟨4591027591055836053423791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12242740242815562809130109 4591027591055836053423791)
      ·
        refine ⟨6886541386583754080135687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4591027591055836053423791 6886541386583754080135687)
        ·
          refine ⟨10329812079875631120203531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6886541386583754080135687 10329812079875631120203531)
          ·
            refine ⟨15494718119813446680305297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10329812079875631120203531 15494718119813446680305297)
            ·
              refine ⟨11621038589860085010228973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15494718119813446680305297 11621038589860085010228973)
              ·
                refine ⟨4357889471197531878835865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11621038589860085010228973 4357889471197531878835865)
                ·
                  refine ⟨3268417103398148909126899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4357889471197531878835865 3268417103398148909126899)
                  ·
                    refine ⟨4902625655097223363690349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3268417103398148909126899 4902625655097223363690349)
                    ·
                      refine ⟨1838484620661458761383881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4902625655097223363690349 1838484620661458761383881)
                      ·
                        rfl

theorem cell23_3580436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_3580436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580436 prefixEnd_3580436 := by exact prefixLift 3580436
  have htrace : WordTrace (prefixWord ++ tailWord_3580436) baseStart_3580436 baseEnd_3580436 := by
    simpa [prefixWord, tailWord_3580436, baseEnd_3580436] using wordTrace_append hprefix tailTrace_3580436
  have hstable : (prefixWord ++ tailWord_3580436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580436).length < 2 ^ (prefixWord ++ tailWord_3580436).sum := by decide
  have hdescent : baseEnd_3580436 < baseStart_3580436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580442 : List Nat := [3, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2]
def baseStart_3580442 : Nat := 118140960795 + 3580442 * 2 ^ 59
def prefixEnd_3580442 : Nat := 4983230072969 + 3 ^ 40 * 3580442 * 2
def baseEnd_3580442 : Nat := 1838487701545385737908853

theorem tailTrace_3580442 : CollatzResearch.WordTrace tailWord_3580442 prefixEnd_3580442 1838487701545385737908853 := by
  unfold tailWord_3580442
  simp only [CollatzResearch.WordTrace]
  refine ⟨32647362023669399913859895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87059632063118399770293053 32647362023669399913859895)
  ·
    refine ⟨48971043035504099870789843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32647362023669399913859895 48971043035504099870789843)
    ·
      refine ⟨73456564553256149806184765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48971043035504099870789843 73456564553256149806184765)
      ·
        refine ⟨27546211707471056177319287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73456564553256149806184765 27546211707471056177319287)
        ·
          refine ⟨41319317561206584265978931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27546211707471056177319287 41319317561206584265978931)
          ·
            refine ⟨61978976341809876398968397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41319317561206584265978931 61978976341809876398968397)
            ·
              refine ⟨23242116128178703649613149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61978976341809876398968397 23242116128178703649613149)
              ·
                refine ⟨8715793548067013868604931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23242116128178703649613149 8715793548067013868604931)
                ·
                  refine ⟨13073690322100520802907397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8715793548067013868604931 13073690322100520802907397)
                  ·
                    refine ⟨2451316935393847650545137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13073690322100520802907397 2451316935393847650545137)
                    ·
                      refine ⟨1838487701545385737908853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2451316935393847650545137 1838487701545385737908853)
                      ·
                        rfl

theorem cell23_3580442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_3580442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580442 prefixEnd_3580442 := by exact prefixLift 3580442
  have htrace : WordTrace (prefixWord ++ tailWord_3580442) baseStart_3580442 baseEnd_3580442 := by
    simpa [prefixWord, tailWord_3580442, baseEnd_3580442] using wordTrace_append hprefix tailTrace_3580442
  have hstable : (prefixWord ++ tailWord_3580442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580442).length < 2 ^ (prefixWord ++ tailWord_3580442).sum := by decide
  have hdescent : baseEnd_3580442 < baseStart_3580442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580476 : List Nat := [2, 2, 2, 2, 3, 1, 3, 2, 2, 2, 2]
def baseStart_3580476 : Nat := 118140960795 + 3580476 * 2 ^ 59
def prefixEnd_3580476 : Nat := 4983230072969 + 3 ^ 40 * 3580476 * 2
def baseEnd_3580476 : Nat := 1838505159887638604883697

theorem tailTrace_3580476 : CollatzResearch.WordTrace tailWord_3580476 prefixEnd_3580476 1838505159887638604883697 := by
  unfold tailWord_3580476
  simp only [CollatzResearch.WordTrace]
  refine ⟨65295344088277211731088641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87060458784369615641451521 65295344088277211731088641)
  ·
    refine ⟨48971508066207908798316481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65295344088277211731088641 48971508066207908798316481)
    ·
      refine ⟨36728631049655931598737361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48971508066207908798316481 36728631049655931598737361)
      ·
        refine ⟨27546473287241948699053021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36728631049655931598737361 27546473287241948699053021)
        ·
          refine ⟨10329927482715730762144883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27546473287241948699053021 10329927482715730762144883)
          ·
            refine ⟨15494891224073596143217325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10329927482715730762144883 15494891224073596143217325)
            ·
              refine ⟨5810584209027598553706497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15494891224073596143217325 5810584209027598553706497)
              ·
                refine ⟨4357938156770698915279873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5810584209027598553706497 4357938156770698915279873)
                ·
                  refine ⟨3268453617578024186459905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4357938156770698915279873 3268453617578024186459905)
                  ·
                    refine ⟨2451340213183518139844929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3268453617578024186459905 2451340213183518139844929)
                    ·
                      refine ⟨1838505159887638604883697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2451340213183518139844929 1838505159887638604883697)
                      ·
                        rfl

theorem cell23_3580476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_3580476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580476 prefixEnd_3580476 := by exact prefixLift 3580476
  have htrace : WordTrace (prefixWord ++ tailWord_3580476) baseStart_3580476 baseEnd_3580476 := by
    simpa [prefixWord, tailWord_3580476, baseEnd_3580476] using wordTrace_append hprefix tailTrace_3580476
  have hstable : (prefixWord ++ tailWord_3580476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580476).length < 2 ^ (prefixWord ++ tailWord_3580476).sum := by decide
  have hdescent : baseEnd_3580476 < baseStart_3580476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580515 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 4]
def baseStart_3580515 : Nat := 118140960795 + 3580515 * 2 ^ 59
def prefixEnd_3580515 : Nat := 4983230072969 + 3 ^ 40 * 3580515 * 2
def baseEnd_3580515 : Nat := 1838525185633163952296017

theorem tailTrace_3580515 : CollatzResearch.WordTrace tailWord_3580515 prefixEnd_3580515 1838525185633163952296017 := by
  unfold tailWord_3580515
  simp only [CollatzResearch.WordTrace]
  refine ⟨130592110623413133122846999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87061407082275422081897999 130592110623413133122846999)
  ·
    refine ⟨195888165935119699684270499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130592110623413133122846999 195888165935119699684270499)
    ·
      refine ⟨293832248902679549526405749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195888165935119699684270499 293832248902679549526405749)
      ·
        refine ⟨27546773334626207768100539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 293832248902679549526405749 27546773334626207768100539)
        ·
          refine ⟨41320160001939311652150809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27546773334626207768100539 41320160001939311652150809)
          ·
            refine ⟨30990120001454483739113107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41320160001939311652150809 30990120001454483739113107)
            ·
              refine ⟨46485180002181725608669661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30990120001454483739113107 46485180002181725608669661)
              ·
                refine ⟨17431942500818147103251123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46485180002181725608669661 17431942500818147103251123)
                ·
                  refine ⟨26147913751227220654876685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17431942500818147103251123 26147913751227220654876685)
                  ·
                    refine ⟨9805467656710207745578757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26147913751227220654876685 9805467656710207745578757)
                    ·
                      refine ⟨1838525185633163952296017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9805467656710207745578757 1838525185633163952296017)
                      ·
                        rfl

theorem cell23_3580515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_3580515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580515 prefixEnd_3580515 := by exact prefixLift 3580515
  have htrace : WordTrace (prefixWord ++ tailWord_3580515) baseStart_3580515 baseEnd_3580515 := by
    simpa [prefixWord, tailWord_3580515, baseEnd_3580515] using wordTrace_append hprefix tailTrace_3580515
  have hstable : (prefixWord ++ tailWord_3580515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580515).length < 2 ^ (prefixWord ++ tailWord_3580515).sum := by decide
  have hdescent : baseEnd_3580515 < baseStart_3580515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580585 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 5, 5]
def baseStart_3580585 : Nat := 118140960795 + 3580585 * 2 ^ 59
def prefixEnd_3580585 : Nat := 4983230072969 + 3 ^ 40 * 3580585 * 2
def baseEnd_3580585 : Nat := 612853709759659559473565

theorem tailTrace_3580585 : CollatzResearch.WordTrace tailWord_3580585 prefixEnd_3580585 612853709759659559473565 := by
  unfold tailWord_3580585
  simp only [CollatzResearch.WordTrace]
  refine ⟨130594663733159535077895209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87063109155439690051930139 130594663733159535077895209)
  ·
    refine ⟨97945997799869651308421407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130594663733159535077895209 97945997799869651308421407)
    ·
      refine ⟨146918996699804476962632111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97945997799869651308421407 146918996699804476962632111)
      ·
        refine ⟨220378495049706715443948167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146918996699804476962632111 220378495049706715443948167)
        ·
          refine ⟨330567742574560073165922251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220378495049706715443948167 330567742574560073165922251)
          ·
            refine ⟨495851613861840109748883377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330567742574560073165922251 495851613861840109748883377)
            ·
              refine ⟨371888710396380082311662533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495851613861840109748883377 371888710396380082311662533)
              ·
                refine ⟨69729133199321265433436725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 371888710396380082311662533 69729133199321265433436725)
                ·
                  refine ⟨6537106237436368634384693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69729133199321265433436725 6537106237436368634384693)
                  ·
                    refine ⟨612853709759659559473565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6537106237436368634384693 612853709759659559473565)
                    ·
                      rfl

theorem cell23_3580585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 5].length) (baseStart_3580585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580585 prefixEnd_3580585 := by exact prefixLift 3580585
  have htrace : WordTrace (prefixWord ++ tailWord_3580585) baseStart_3580585 baseEnd_3580585 := by
    simpa [prefixWord, tailWord_3580585, baseEnd_3580585] using wordTrace_append hprefix tailTrace_3580585
  have hstable : (prefixWord ++ tailWord_3580585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580585).length < 2 ^ (prefixWord ++ tailWord_3580585).sum := by decide
  have hdescent : baseEnd_3580585 < baseStart_3580585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580589 : List Nat := [1, 5, 2, 1, 1, 3, 2, 2, 6]
def baseStart_3580589 : Nat := 118140960795 + 3580589 * 2 ^ 59
def prefixEnd_3580589 : Nat := 4983230072969 + 3 ^ 40 * 3580589 * 2
def baseEnd_3580589 : Nat := 204284798133510740307853

theorem tailTrace_3580589 : CollatzResearch.WordTrace tailWord_3580589 prefixEnd_3580589 204284798133510740307853 := by
  unfold tailWord_3580589
  simp only [CollatzResearch.WordTrace]
  refine ⟨130594809625145043761040821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87063206416763362507360547 130594809625145043761040821)
  ·
    refine ⟨12243263402357347852597577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130594809625145043761040821 12243263402357347852597577)
    ·
      refine ⟨9182447551768010889448183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12243263402357347852597577 9182447551768010889448183)
      ·
        refine ⟨13773671327652016334172275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9182447551768010889448183 13773671327652016334172275)
        ·
          refine ⟨20660506991478024501258413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13773671327652016334172275 20660506991478024501258413)
          ·
            refine ⟨7747690121804259187971905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20660506991478024501258413 7747690121804259187971905)
            ·
              refine ⟨5810767591353194390978929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7747690121804259187971905 5810767591353194390978929)
              ·
                refine ⟨4358075693514895793234197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5810767591353194390978929 4358075693514895793234197)
                ·
                  refine ⟨204284798133510740307853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4358075693514895793234197 204284798133510740307853)
                  ·
                    rfl

theorem cell23_3580589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_3580589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580589 prefixEnd_3580589 := by exact prefixLift 3580589
  have htrace : WordTrace (prefixWord ++ tailWord_3580589) baseStart_3580589 baseEnd_3580589 := by
    simpa [prefixWord, tailWord_3580589, baseEnd_3580589] using wordTrace_append hprefix tailTrace_3580589
  have hstable : (prefixWord ++ tailWord_3580589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580589).length < 2 ^ (prefixWord ++ tailWord_3580589).sum := by decide
  have hdescent : baseEnd_3580589 < baseStart_3580589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580592 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 3, 5, 2]
def baseStart_3580592 : Nat := 118140960795 + 3580592 * 2 ^ 59
def prefixEnd_3580592 : Nat := 4983230072969 + 3 ^ 40 * 3580592 * 2
def baseEnd_3580592 : Nat := 1838564723643560151033163

theorem tailTrace_3580592 : CollatzResearch.WordTrace tailWord_3580592 prefixEnd_3580592 1838564723643560151033163 := by
  unfold tailWord_3580592
  simp only [CollatzResearch.WordTrace]
  refine ⟨65297459522067087636700015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87063279362756116848933353 65297459522067087636700015)
  ·
    refine ⟨97946189283100631455050023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65297459522067087636700015 97946189283100631455050023)
    ·
      refine ⟨146919283924650947182575035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97946189283100631455050023 146919283924650947182575035)
      ·
        refine ⟨220378925886976420773862553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146919283924650947182575035 220378925886976420773862553)
        ·
          refine ⟨165284194415232315580396915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220378925886976420773862553 165284194415232315580396915)
          ·
            refine ⟨247926291622848473370595373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165284194415232315580396915 247926291622848473370595373)
            ·
              refine ⟨92972359358568177513973265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247926291622848473370595373 92972359358568177513973265)
              ·
                refine ⟨69729269518926133135479949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92972359358568177513973265 69729269518926133135479949)
                ·
                  refine ⟨26148476069597299925804981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69729269518926133135479949 26148476069597299925804981)
                  ·
                    refine ⟨2451419631524746868044217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26148476069597299925804981 2451419631524746868044217)
                    ·
                      refine ⟨1838564723643560151033163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2451419631524746868044217 1838564723643560151033163)
                      ·
                        rfl

theorem cell23_3580592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 3, 5, 2].length) (baseStart_3580592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580592 prefixEnd_3580592 := by exact prefixLift 3580592
  have htrace : WordTrace (prefixWord ++ tailWord_3580592) baseStart_3580592 baseEnd_3580592 := by
    simpa [prefixWord, tailWord_3580592, baseEnd_3580592] using wordTrace_append hprefix tailTrace_3580592
  have hstable : (prefixWord ++ tailWord_3580592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580592).length < 2 ^ (prefixWord ++ tailWord_3580592).sum := by decide
  have hdescent : baseEnd_3580592 < baseStart_3580592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580593 : List Nat := [1, 2, 2, 6, 1, 1, 1, 4, 1, 4]
def baseStart_3580593 : Nat := 118140960795 + 3580593 * 2 ^ 59
def prefixEnd_3580593 : Nat := 4983230072969 + 3 ^ 40 * 3580593 * 2
def baseEnd_3580593 : Nat := 612855079041404882373553

theorem tailTrace_3580593 : CollatzResearch.WordTrace tailWord_3580593 prefixEnd_3580593 612855079041404882373553 := by
  unfold tailWord_3580593
  simp only [CollatzResearch.WordTrace]
  refine ⟨130594955517130552444186433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87063303678087034962790955 130594955517130552444186433)
  ·
    refine ⟨97946216637847914333139825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130594955517130552444186433 97946216637847914333139825)
    ·
      refine ⟨73459662478385935749854869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97946216637847914333139825 73459662478385935749854869)
      ·
        refine ⟨3443421678674340738274447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 73459662478385935749854869 3443421678674340738274447)
        ·
          refine ⟨5165132518011511107411671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3443421678674340738274447 5165132518011511107411671)
          ·
            refine ⟨7747698777017266661117507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5165132518011511107411671 7747698777017266661117507)
            ·
              refine ⟨11621548165525899991676261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7747698777017266661117507 11621548165525899991676261)
              ·
                refine ⟨2179040281036106248439299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11621548165525899991676261 2179040281036106248439299)
                ·
                  refine ⟨3268560421554159372658949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2179040281036106248439299 3268560421554159372658949)
                  ·
                    refine ⟨612855079041404882373553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3268560421554159372658949 612855079041404882373553)
                    ·
                      rfl

theorem cell23_3580593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 1, 4].length) (baseStart_3580593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580593 prefixEnd_3580593 := by exact prefixLift 3580593
  have htrace : WordTrace (prefixWord ++ tailWord_3580593) baseStart_3580593 baseEnd_3580593 := by
    simpa [prefixWord, tailWord_3580593, baseEnd_3580593] using wordTrace_append hprefix tailTrace_3580593
  have hstable : (prefixWord ++ tailWord_3580593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580593).length < 2 ^ (prefixWord ++ tailWord_3580593).sum := by decide
  have hdescent : baseEnd_3580593 < baseStart_3580593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580626 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 1, 5, 2]
def baseStart_3580626 : Nat := 118140960795 + 3580626 * 2 ^ 59
def prefixEnd_3580626 : Nat := 4983230072969 + 3 ^ 40 * 3580626 * 2
def baseEnd_3580626 : Nat := 1838582181985813018008007

theorem tailTrace_3580626 : CollatzResearch.WordTrace tailWord_3580626 prefixEnd_3580626 1838582181985813018008007 := by
  unfold tailWord_3580626
  simp only [CollatzResearch.WordTrace]
  refine ⟨32649039781502749770034433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87064106084007332720091821 32649039781502749770034433)
  ·
    refine ⟨24486779836127062327525825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32649039781502749770034433 24486779836127062327525825)
    ·
      refine ⟨18365084877095296745644369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24486779836127062327525825 18365084877095296745644369)
      ·
        refine ⟨13773813657821472559233277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18365084877095296745644369 13773813657821472559233277)
        ·
          refine ⟨5165180121683052209712479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13773813657821472559233277 5165180121683052209712479)
          ·
            refine ⟨7747770182524578314568719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5165180121683052209712479 7747770182524578314568719)
            ·
              refine ⟨11621655273786867471853079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7747770182524578314568719 11621655273786867471853079)
              ·
                refine ⟨17432482910680301207779619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11621655273786867471853079 17432482910680301207779619)
                ·
                  refine ⟨26148724366020451811669429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17432482910680301207779619 26148724366020451811669429)
                  ·
                    refine ⟨2451442909314417357344009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26148724366020451811669429 2451442909314417357344009)
                    ·
                      refine ⟨1838582181985813018008007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2451442909314417357344009 1838582181985813018008007)
                      ·
                        rfl

theorem cell23_3580626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_3580626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580626 prefixEnd_3580626 := by exact prefixLift 3580626
  have htrace : WordTrace (prefixWord ++ tailWord_3580626) baseStart_3580626 baseEnd_3580626 := by
    simpa [prefixWord, tailWord_3580626, baseEnd_3580626] using wordTrace_append hprefix tailTrace_3580626
  have hstable : (prefixWord ++ tailWord_3580626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580626).length < 2 ^ (prefixWord ++ tailWord_3580626).sum := by decide
  have hdescent : baseEnd_3580626 < baseStart_3580626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580632 : List Nat := [2, 1, 2, 2, 3, 2, 2, 2, 1, 6]
def baseStart_3580632 : Nat := 118140960795 + 3580632 * 2 ^ 59
def prefixEnd_3580632 : Nat := 4983230072969 + 3 ^ 40 * 3580632 * 2
def baseEnd_3580632 : Nat := 612861754289913331510993

theorem tailTrace_3580632 : CollatzResearch.WordTrace tailWord_3580632 prefixEnd_3580632 612861754289913331510993 := by
  unfold tailWord_3580632
  simp only [CollatzResearch.WordTrace]
  refine ⟨65298188981994631052428075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87064251975992841403237433 65298188981994631052428075)
  ·
    refine ⟨97947283472991946578642113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65298188981994631052428075 97947283472991946578642113)
    ·
      refine ⟨73460462604743959933981585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97947283472991946578642113 73460462604743959933981585)
      ·
        refine ⟨55095346953557969950486189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73460462604743959933981585 55095346953557969950486189)
        ·
          refine ⟨20660755107584238731432321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55095346953557969950486189 20660755107584238731432321)
          ·
            refine ⟨15495566330688179048574241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20660755107584238731432321 15495566330688179048574241)
            ·
              refine ⟨11621674748016134286430681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15495566330688179048574241 11621674748016134286430681)
              ·
                refine ⟨8716256061012100714823011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11621674748016134286430681 8716256061012100714823011)
                ·
                  refine ⟨13074384091518151072234517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8716256061012100714823011 13074384091518151072234517)
                  ·
                    refine ⟨612861754289913331510993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13074384091518151072234517 612861754289913331510993)
                    ·
                      rfl

theorem cell23_3580632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_3580632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580632 prefixEnd_3580632 := by exact prefixLift 3580632
  have htrace : WordTrace (prefixWord ++ tailWord_3580632) baseStart_3580632 baseEnd_3580632 := by
    simpa [prefixWord, tailWord_3580632, baseEnd_3580632] using wordTrace_append hprefix tailTrace_3580632
  have hstable : (prefixWord ++ tailWord_3580632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580632).length < 2 ^ (prefixWord ++ tailWord_3580632).sum := by decide
  have hdescent : baseEnd_3580632 < baseStart_3580632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580636 : List Nat := [2, 2, 5, 1, 1, 2, 1, 3, 1, 5]
def baseStart_3580636 : Nat := 118140960795 + 3580636 * 2 ^ 59
def prefixEnd_3580636 : Nat := 4983230072969 + 3 ^ 40 * 3580636 * 2
def baseEnd_3580636 : Nat := 612862438930785992960987

theorem tailTrace_3580636 : CollatzResearch.WordTrace tailWord_3580636 prefixEnd_3580636 612862438930785992960987 := by
  unfold tailWord_3580636
  simp only [CollatzResearch.WordTrace]
  refine ⟨65298261927987385394000881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87064349237316513858667841 65298261927987385394000881)
  ·
    refine ⟨48973696445990539045500661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65298261927987385394000881 48973696445990539045500661)
    ·
      refine ⟨4591284041811613035515687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48973696445990539045500661 4591284041811613035515687)
      ·
        refine ⟨6886926062717419553273531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4591284041811613035515687 6886926062717419553273531)
        ·
          refine ⟨10330389094076129329910297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6886926062717419553273531 10330389094076129329910297)
          ·
            refine ⟨7747791820557096997432723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10330389094076129329910297 7747791820557096997432723)
            ·
              refine ⟨11621687730835645496149085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7747791820557096997432723 11621687730835645496149085)
              ·
                refine ⟨4358132899063367061055907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11621687730835645496149085 4358132899063367061055907)
                ·
                  refine ⟨6537199348595050591583861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4358132899063367061055907 6537199348595050591583861)
                  ·
                    refine ⟨612862438930785992960987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6537199348595050591583861 612862438930785992960987)
                    ·
                      rfl

theorem cell23_3580636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_3580636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580636 prefixEnd_3580636 := by exact prefixLift 3580636
  have htrace : WordTrace (prefixWord ++ tailWord_3580636) baseStart_3580636 baseEnd_3580636 := by
    simpa [prefixWord, tailWord_3580636, baseEnd_3580636] using wordTrace_append hprefix tailTrace_3580636
  have hstable : (prefixWord ++ tailWord_3580636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580636).length < 2 ^ (prefixWord ++ tailWord_3580636).sum := by decide
  have hdescent : baseEnd_3580636 < baseStart_3580636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580639 : List Nat := [1, 1, 2, 3, 2, 4, 1, 3, 1, 1, 4]
def baseStart_3580639 : Nat := 118140960795 + 3580639 * 2 ^ 59
def prefixEnd_3580639 : Nat := 4983230072969 + 3 ^ 40 * 3580639 * 2
def baseEnd_3580639 : Nat := 1838588857234321467145447

theorem tailTrace_3580639 : CollatzResearch.WordTrace tailWord_3580639 prefixEnd_3580639 1838588857234321467145447 := by
  unfold tailWord_3580639
  simp only [CollatzResearch.WordTrace]
  refine ⟨130596633274963902300360971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87064422183309268200240647 130596633274963902300360971)
  ·
    refine ⟨195894949912445853450541457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130596633274963902300360971 195894949912445853450541457)
    ·
      refine ⟨146921212434334390087906093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195894949912445853450541457 146921212434334390087906093)
      ·
        refine ⟨55095454662875396282964785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146921212434334390087906093 55095454662875396282964785)
        ·
          refine ⟨41321590997156547212223589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55095454662875396282964785 41321590997156547212223589)
          ·
            refine ⟨7747798311966852602291923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41321590997156547212223589 7747798311966852602291923)
            ·
              refine ⟨11621697467950278903437885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7747798311966852602291923 11621697467950278903437885)
              ·
                refine ⟨4358136550481354588789207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11621697467950278903437885 4358136550481354588789207)
                ·
                  refine ⟨6537204825722031883183811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4358136550481354588789207 6537204825722031883183811)
                  ·
                    refine ⟨9805807238583047824775717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6537204825722031883183811 9805807238583047824775717)
                    ·
                      refine ⟨1838588857234321467145447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9805807238583047824775717 1838588857234321467145447)
                      ·
                        rfl

theorem cell23_3580639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_3580639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580639 prefixEnd_3580639 := by exact prefixLift 3580639
  have htrace : WordTrace (prefixWord ++ tailWord_3580639) baseStart_3580639 baseEnd_3580639 := by
    simpa [prefixWord, tailWord_3580639, baseEnd_3580639] using wordTrace_append hprefix tailTrace_3580639
  have hstable : (prefixWord ++ tailWord_3580639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580639).length < 2 ^ (prefixWord ++ tailWord_3580639).sum := by decide
  have hdescent : baseEnd_3580639 < baseStart_3580639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580649 : List Nat := [1, 2, 1, 1, 1, 2, 7, 2, 2, 4]
def baseStart_3580649 : Nat := 118140960795 + 3580649 * 2 ^ 59
def prefixEnd_3580649 : Nat := 4983230072969 + 3 ^ 40 * 3580649 * 2
def baseEnd_3580649 : Nat := 612864664013622142673467

theorem tailTrace_3580649 : CollatzResearch.WordTrace tailWord_3580649 prefixEnd_3580649 612864664013622142673467 := by
  unfold tailWord_3580649
  simp only [CollatzResearch.WordTrace]
  refine ⟨130596998004927674008225001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87064665336618449338816667 130596998004927674008225001)
  ·
    refine ⟨97947748503695755506168751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130596998004927674008225001 97947748503695755506168751)
    ·
      refine ⟨146921622755543633259253127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97947748503695755506168751 146921622755543633259253127)
      ·
        refine ⟨220382434133315449888879691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146921622755543633259253127 220382434133315449888879691)
        ·
          refine ⟨330573651199973174833319537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220382434133315449888879691 330573651199973174833319537)
          ·
            refine ⟨247930238399979881124989653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330573651199973174833319537 247930238399979881124989653)
            ·
              refine ⟨5810864962499528463866945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 247930238399979881124989653 5810864962499528463866945)
              ·
                refine ⟨4358148721874646347900209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5810864962499528463866945 4358148721874646347900209)
                ·
                  refine ⟨3268611541405984760925157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4358148721874646347900209 3268611541405984760925157)
                  ·
                    refine ⟨612864664013622142673467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3268611541405984760925157 612864664013622142673467)
                    ·
                      rfl

theorem cell23_3580649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 4].length) (baseStart_3580649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580649 prefixEnd_3580649 := by exact prefixLift 3580649
  have htrace : WordTrace (prefixWord ++ tailWord_3580649) baseStart_3580649 baseEnd_3580649 := by
    simpa [prefixWord, tailWord_3580649, baseEnd_3580649] using wordTrace_append hprefix tailTrace_3580649
  have hstable : (prefixWord ++ tailWord_3580649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580649).length < 2 ^ (prefixWord ++ tailWord_3580649).sum := by decide
  have hdescent : baseEnd_3580649 < baseStart_3580649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580656 : List Nat := [2, 1, 1, 1, 3, 1, 6, 1, 3, 2, 2]
def baseStart_3580656 : Nat := 118140960795 + 3580656 * 2 ^ 59
def prefixEnd_3580656 : Nat := 4983230072969 + 3 ^ 40 * 3580656 * 2
def baseEnd_3580656 : Nat := 1838597586405447900632869

theorem tailTrace_3580656 : CollatzResearch.WordTrace tailWord_3580656 prefixEnd_3580656 1838597586405447900632869 := by
  unfold tailWord_3580656
  simp only [CollatzResearch.WordTrace]
  refine ⟨65298626657951157101864911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87064835543934876135819881 65298626657951157101864911)
  ·
    refine ⟨97947939986926735652797367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65298626657951157101864911 97947939986926735652797367)
    ·
      refine ⟨146921909980390103479196051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97947939986926735652797367 146921909980390103479196051)
      ·
        refine ⟨220382864970585155218794077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146921909980390103479196051 220382864970585155218794077)
        ·
          refine ⟨82643574363969433207047779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220382864970585155218794077 82643574363969433207047779)
          ·
            refine ⟨123965361545954149810571669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82643574363969433207047779 123965361545954149810571669)
            ·
              refine ⟨5810876322466600772370547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123965361545954149810571669 5810876322466600772370547)
              ·
                refine ⟨8716314483699901158555821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5810876322466600772370547 8716314483699901158555821)
                ·
                  refine ⟨3268617931387462934458433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8716314483699901158555821 3268617931387462934458433)
                  ·
                    refine ⟨2451463448540597200843825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3268617931387462934458433 2451463448540597200843825)
                    ·
                      refine ⟨1838597586405447900632869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2451463448540597200843825 1838597586405447900632869)
                      ·
                        rfl

theorem cell23_3580656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 3, 2, 2].length) (baseStart_3580656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580656 prefixEnd_3580656 := by exact prefixLift 3580656
  have htrace : WordTrace (prefixWord ++ tailWord_3580656) baseStart_3580656 baseEnd_3580656 := by
    simpa [prefixWord, tailWord_3580656, baseEnd_3580656] using wordTrace_append hprefix tailTrace_3580656
  have hstable : (prefixWord ++ tailWord_3580656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580656).length < 2 ^ (prefixWord ++ tailWord_3580656).sum := by decide
  have hdescent : baseEnd_3580656 < baseStart_3580656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580662 : List Nat := [5, 1, 1, 1, 1, 2, 2, 10]
def baseStart_3580662 : Nat := 118140960795 + 3580662 * 2 ^ 59
def prefixEnd_3580662 : Nat := 4983230072969 + 3 ^ 40 * 3580662 * 2
def baseEnd_3580662 : Nat := 68096321010717588042883

theorem tailTrace_3580662 : CollatzResearch.WordTrace tailWord_3580662 prefixEnd_3580662 68096321010717588042883 := by
  unfold tailWord_3580662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8162342009617536076778015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87064981435920384818965493 8162342009617536076778015)
  ·
    refine ⟨12243513014426304115167023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8162342009617536076778015 12243513014426304115167023)
    ·
      refine ⟨18365269521639456172750535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12243513014426304115167023 18365269521639456172750535)
      ·
        refine ⟨27547904282459184259125803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18365269521639456172750535 27547904282459184259125803)
        ·
          refine ⟨41321856423688776388688705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27547904282459184259125803 41321856423688776388688705)
          ·
            refine ⟨30991392317766582291516529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41321856423688776388688705 30991392317766582291516529)
            ·
              refine ⟨23243544238324936718637397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30991392317766582291516529 23243544238324936718637397)
              ·
                refine ⟨68096321010717588042883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23243544238324936718637397 68096321010717588042883)
                ·
                  rfl

theorem cell23_3580662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_3580662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580662 prefixEnd_3580662 := by exact prefixLift 3580662
  have htrace : WordTrace (prefixWord ++ tailWord_3580662) baseStart_3580662 baseEnd_3580662 := by
    simpa [prefixWord, tailWord_3580662, baseEnd_3580662] using wordTrace_append hprefix tailTrace_3580662
  have hstable : (prefixWord ++ tailWord_3580662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580662).length < 2 ^ (prefixWord ++ tailWord_3580662).sum := by decide
  have hdescent : baseEnd_3580662 < baseStart_3580662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580676 : List Nat := [2, 3, 2, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_3580676 : Nat := 118140960795 + 3580676 * 2 ^ 59
def prefixEnd_3580676 : Nat := 4983230072969 + 3 ^ 40 * 3580676 * 2
def baseEnd_3580676 : Nat := 1838607856018537822382777

theorem tailTrace_3580676 : CollatzResearch.WordTrace tailWord_3580676 prefixEnd_3580676 1838607856018537822382777 := by
  unfold tailWord_3580676
  simp only [CollatzResearch.WordTrace]
  refine ⟨65298991387914928809728941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87065321850553238412971921 65298991387914928809728941)
  ·
    refine ⟨24487121770468098303648353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65298991387914928809728941 24487121770468098303648353)
    ·
      refine ⟨18365341327851073727736265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24487121770468098303648353 18365341327851073727736265)
      ·
        refine ⟨13774005995888305295802199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18365341327851073727736265 13774005995888305295802199)
        ·
          refine ⟨20661008993832457943703299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13774005995888305295802199 20661008993832457943703299)
          ·
            refine ⟨30991513490748686915554949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20661008993832457943703299 30991513490748686915554949)
            ·
              refine ⟨5810908779515378796666553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30991513490748686915554949 5810908779515378796666553)
              ·
                refine ⟨4358181584636534097499915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5810908779515378796666553 4358181584636534097499915)
                ·
                  refine ⟨6537272376954801146249873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4358181584636534097499915 6537272376954801146249873)
                  ·
                    refine ⟨4902954282716100859687405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6537272376954801146249873 4902954282716100859687405)
                    ·
                      refine ⟨1838607856018537822382777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4902954282716100859687405 1838607856018537822382777)
                      ·
                        rfl

theorem cell23_3580676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_3580676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580676 prefixEnd_3580676 := by exact prefixLift 3580676
  have htrace : WordTrace (prefixWord ++ tailWord_3580676) baseStart_3580676 baseEnd_3580676 := by
    simpa [prefixWord, tailWord_3580676, baseEnd_3580676] using wordTrace_append hprefix tailTrace_3580676
  have hstable : (prefixWord ++ tailWord_3580676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580676).length < 2 ^ (prefixWord ++ tailWord_3580676).sum := by decide
  have hdescent : baseEnd_3580676 < baseStart_3580676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580679 : List Nat := [1, 1, 4, 4, 1, 1, 4, 7]
def baseStart_3580679 : Nat := 118140960795 + 3580679 * 2 ^ 59
def prefixEnd_3580679 : Nat := 4983230072969 + 3 ^ 40 * 3580679 * 2
def baseEnd_3580679 : Nat := 68096644313351900394269

theorem tailTrace_3580679 : CollatzResearch.WordTrace tailWord_3580679 prefixEnd_3580679 68096644313351900394269 := by
  unfold tailWord_3580679
  simp only [CollatzResearch.WordTrace]
  refine ⟨130598092194818989131817091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87065394796545992754544727 130598092194818989131817091)
  ·
    refine ⟨195897138292228483697725637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130598092194818989131817091 195897138292228483697725637)
    ·
      refine ⟨36730713429792840693323557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195897138292228483697725637 36730713429792840693323557)
      ·
        refine ⟨6887008768086157629998167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36730713429792840693323557 6887008768086157629998167)
        ·
          refine ⟨10330513152129236444997251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6887008768086157629998167 10330513152129236444997251)
          ·
            refine ⟨15495769728193854667495877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10330513152129236444997251 15495769728193854667495877)
            ·
              refine ⟨2905456824036347750155477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15495769728193854667495877 2905456824036347750155477)
              ·
                refine ⟨68096644313351900394269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2905456824036347750155477 68096644313351900394269)
                ·
                  rfl

theorem cell23_3580679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 7].length) (baseStart_3580679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580679 prefixEnd_3580679 := by exact prefixLift 3580679
  have htrace : WordTrace (prefixWord ++ tailWord_3580679) baseStart_3580679 baseEnd_3580679 := by
    simpa [prefixWord, tailWord_3580679, baseEnd_3580679] using wordTrace_append hprefix tailTrace_3580679
  have hstable : (prefixWord ++ tailWord_3580679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580679).length < 2 ^ (prefixWord ++ tailWord_3580679).sum := by decide
  have hdescent : baseEnd_3580679 < baseStart_3580679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580689 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 4, 1, 3]
def baseStart_3580689 : Nat := 118140960795 + 3580689 * 2 ^ 59
def prefixEnd_3580689 : Nat := 4983230072969 + 3 ^ 40 * 3580689 * 2
def baseEnd_3580689 : Nat := 1838614531267046271520217

theorem tailTrace_3580689 : CollatzResearch.WordTrace tailWord_3580689 prefixEnd_3580689 1838614531267046271520217 := by
  unfold tailWord_3580689
  simp only [CollatzResearch.WordTrace]
  refine ⟨130598456924782760839681121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87065637949855173893120747 130598456924782760839681121)
  ·
    refine ⟨97948842693587070629760841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130598456924782760839681121 97948842693587070629760841)
    ·
      refine ⟨73461632020190302972320631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97948842693587070629760841 73461632020190302972320631)
      ·
        refine ⟨110192448030285454458480947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73461632020190302972320631 110192448030285454458480947)
        ·
          refine ⟨165288672045428181687721421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110192448030285454458480947 165288672045428181687721421)
          ·
            refine ⟨61983252017035568132895533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165288672045428181687721421 61983252017035568132895533)
            ·
              refine ⟨23243719506388338049835825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61983252017035568132895533 23243719506388338049835825)
              ·
                refine ⟨17432789629791253537376869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23243719506388338049835825 17432789629791253537376869)
                ·
                  refine ⟨3268648055585860038258163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17432789629791253537376869 3268648055585860038258163)
                  ·
                    refine ⟨4902972083378790057387245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3268648055585860038258163 4902972083378790057387245)
                    ·
                      refine ⟨1838614531267046271520217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4902972083378790057387245 1838614531267046271520217)
                      ·
                        rfl

theorem cell23_3580689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 1, 3].length) (baseStart_3580689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580689 prefixEnd_3580689 := by exact prefixLift 3580689
  have htrace : WordTrace (prefixWord ++ tailWord_3580689) baseStart_3580689 baseEnd_3580689 := by
    simpa [prefixWord, tailWord_3580689, baseEnd_3580689] using wordTrace_append hprefix tailTrace_3580689
  have hstable : (prefixWord ++ tailWord_3580689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580689).length < 2 ^ (prefixWord ++ tailWord_3580689).sum := by decide
  have hdescent : baseEnd_3580689 < baseStart_3580689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580706 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_3580706 : Nat := 118140960795 + 3580706 * 2 ^ 59
def prefixEnd_3580706 : Nat := 4983230072969 + 3 ^ 40 * 3580706 * 2
def baseEnd_3580706 : Nat := 1838623260438172705007639

theorem tailTrace_3580706 : CollatzResearch.WordTrace tailWord_3580706 prefixEnd_3580706 1838623260438172705007639 := by
  unfold tailWord_3580706
  simp only [CollatzResearch.WordTrace]
  refine ⟨32649769241430293185762493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87066051310480781828699981 32649769241430293185762493)
  ·
    refine ⟨12243663465536359944660935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32649769241430293185762493 12243663465536359944660935)
    ·
      refine ⟨18365495198304539916991403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12243663465536359944660935 18365495198304539916991403)
      ·
        refine ⟨27548242797456809875487105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18365495198304539916991403 27548242797456809875487105)
        ·
          refine ⟨20661182098092607406615329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27548242797456809875487105 20661182098092607406615329)
          ·
            refine ⟨15495886573569455554961497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20661182098092607406615329 15495886573569455554961497)
            ·
              refine ⟨11621914930177091666221123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15495886573569455554961497 11621914930177091666221123)
              ·
                refine ⟨17432872395265637499331685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11621914930177091666221123 17432872395265637499331685)
                ·
                  refine ⟨3268663574112307031124691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17432872395265637499331685 3268663574112307031124691)
                  ·
                    refine ⟨4902995361168460546687037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3268663574112307031124691 4902995361168460546687037)
                    ·
                      refine ⟨1838623260438172705007639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4902995361168460546687037 1838623260438172705007639)
                      ·
                        rfl

theorem cell23_3580706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_3580706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580706 prefixEnd_3580706 := by exact prefixLift 3580706
  have htrace : WordTrace (prefixWord ++ tailWord_3580706) baseStart_3580706 baseEnd_3580706 := by
    simpa [prefixWord, tailWord_3580706, baseEnd_3580706] using wordTrace_append hprefix tailTrace_3580706
  have hstable : (prefixWord ++ tailWord_3580706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580706).length < 2 ^ (prefixWord ++ tailWord_3580706).sum := by decide
  have hdescent : baseEnd_3580706 < baseStart_3580706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580717 : List Nat := [1, 5, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_3580717 : Nat := 118140960795 + 3580717 * 2 ^ 59
def prefixEnd_3580717 : Nat := 4983230072969 + 3 ^ 40 * 3580717 * 2
def baseEnd_3580717 : Nat := 612876302908457387323363

theorem tailTrace_3580717 : CollatzResearch.WordTrace tailWord_3580717 prefixEnd_3580717 612876302908457387323363 := by
  unfold tailWord_3580717
  simp only [CollatzResearch.WordTrace]
  refine ⟨130599478168681321621700405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87066318779120881081133603 130599478168681321621700405)
  ·
    refine ⟨12243701078313873902034413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130599478168681321621700405 12243701078313873902034413)
    ·
      refine ⟨4591387904367702713262905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12243701078313873902034413 4591387904367702713262905)
      ·
        refine ⟨3443540928275777034947179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4591387904367702713262905 3443540928275777034947179)
        ·
          refine ⟨5165311392413665552420769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3443540928275777034947179 5165311392413665552420769)
          ·
            refine ⟨3873983544310249164315577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5165311392413665552420769 3873983544310249164315577)
            ·
              refine ⟨2905487658232686873236683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3873983544310249164315577 2905487658232686873236683)
              ·
                refine ⟨4358231487349030309855025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2905487658232686873236683 4358231487349030309855025)
                ·
                  refine ⟨3268673615511772732391269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4358231487349030309855025 3268673615511772732391269)
                  ·
                    refine ⟨612876302908457387323363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3268673615511772732391269 612876302908457387323363)
                    ·
                      rfl

theorem cell23_3580717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_3580717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580717 prefixEnd_3580717 := by exact prefixLift 3580717
  have htrace : WordTrace (prefixWord ++ tailWord_3580717) baseStart_3580717 baseEnd_3580717 := by
    simpa [prefixWord, tailWord_3580717, baseEnd_3580717] using wordTrace_append hprefix tailTrace_3580717
  have hstable : (prefixWord ++ tailWord_3580717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580717).length < 2 ^ (prefixWord ++ tailWord_3580717).sum := by decide
  have hdescent : baseEnd_3580717 < baseStart_3580717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580722 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 1, 8]
def baseStart_3580722 : Nat := 118140960795 + 3580722 * 2 ^ 59
def prefixEnd_3580722 : Nat := 4983230072969 + 3 ^ 40 * 3580722 * 2
def baseEnd_3580722 : Nat := 612877158709548214135855

theorem tailTrace_3580722 : CollatzResearch.WordTrace tailWord_3580722 prefixEnd_3580722 612877158709548214135855 := by
  unfold tailWord_3580722
  simp only [CollatzResearch.WordTrace]
  refine ⟨32649915133415801868908105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87066440355775471650421613 32649915133415801868908105)
  ·
    refine ⟨24487436350061851401681079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32649915133415801868908105 24487436350061851401681079)
    ·
      refine ⟨36731154525092777102521619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24487436350061851401681079 36731154525092777102521619)
      ·
        refine ⟨55096731787639165653782429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36731154525092777102521619 55096731787639165653782429)
        ·
          refine ⟨20661274420364687120168411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55096731787639165653782429 20661274420364687120168411)
          ·
            refine ⟨30991911630547030680252617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20661274420364687120168411 30991911630547030680252617)
            ·
              refine ⟨23243933722910273010189463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30991911630547030680252617 23243933722910273010189463)
              ·
                refine ⟨34865900584365409515284195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23243933722910273010189463 34865900584365409515284195)
                ·
                  refine ⟨52298850876548114272926293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34865900584365409515284195 52298850876548114272926293)
                  ·
                    refine ⟨612877158709548214135855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52298850876548114272926293 612877158709548214135855)
                    ·
                      rfl

theorem cell23_3580722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_3580722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580722 prefixEnd_3580722 := by exact prefixLift 3580722
  have htrace : WordTrace (prefixWord ++ tailWord_3580722) baseStart_3580722 baseEnd_3580722 := by
    simpa [prefixWord, tailWord_3580722, baseEnd_3580722] using wordTrace_append hprefix tailTrace_3580722
  have hstable : (prefixWord ++ tailWord_3580722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580722).length < 2 ^ (prefixWord ++ tailWord_3580722).sum := by decide
  have hdescent : baseEnd_3580722 < baseStart_3580722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580723 : List Nat := [1, 1, 1, 2, 6, 1, 4, 1, 2, 1, 3]
def baseStart_3580723 : Nat := 118140960795 + 3580723 * 2 ^ 59
def prefixEnd_3580723 : Nat := 4983230072969 + 3 ^ 40 * 3580723 * 2
def baseEnd_3580723 : Nat := 1838631989609299138495061

theorem tailTrace_3580723 : CollatzResearch.WordTrace tailWord_3580723 prefixEnd_3580723 1838631989609299138495061 := by
  unfold tailWord_3580723
  simp only [CollatzResearch.WordTrace]
  refine ⟨130599697006659584646418823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87066464671106389764279215 130599697006659584646418823)
  ·
    refine ⟨195899545509989376969628235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130599697006659584646418823 195899545509989376969628235)
    ·
      refine ⟨293849318264984065454442353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195899545509989376969628235 293849318264984065454442353)
      ·
        refine ⟨220386988698738049090831765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293849318264984065454442353 220386988698738049090831765)
        ·
          refine ⟨10330640095253346051132739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 220386988698738049090831765 10330640095253346051132739)
          ·
            refine ⟨15495960142880019076699109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10330640095253346051132739 15495960142880019076699109)
            ·
              refine ⟨2905492526790003576881083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15495960142880019076699109 2905492526790003576881083)
              ·
                refine ⟨4358238790185005365321625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2905492526790003576881083 4358238790185005365321625)
                ·
                  refine ⟨3268679092638754023991219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4358238790185005365321625 3268679092638754023991219)
                  ·
                    refine ⟨4903018638958131035986829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3268679092638754023991219 4903018638958131035986829)
                    ·
                      refine ⟨1838631989609299138495061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4903018638958131035986829 1838631989609299138495061)
                      ·
                        rfl

theorem cell23_3580723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 2, 1, 3].length) (baseStart_3580723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580723 prefixEnd_3580723 := by exact prefixLift 3580723
  have htrace : WordTrace (prefixWord ++ tailWord_3580723) baseStart_3580723 baseEnd_3580723 := by
    simpa [prefixWord, tailWord_3580723, baseEnd_3580723] using wordTrace_append hprefix tailTrace_3580723
  have hstable : (prefixWord ++ tailWord_3580723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580723).length < 2 ^ (prefixWord ++ tailWord_3580723).sum := by decide
  have hdescent : baseEnd_3580723 < baseStart_3580723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580733 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 3, 3, 2]
def baseStart_3580733 : Nat := 118140960795 + 3580733 * 2 ^ 59
def prefixEnd_3580733 : Nat := 4983230072969 + 3 ^ 40 * 3580733 * 2
def baseEnd_3580733 : Nat := 1838637124415844099370015

theorem tailTrace_3580733 : CollatzResearch.WordTrace tailWord_3580733 prefixEnd_3580733 1838637124415844099370015 := by
  unfold tailWord_3580733
  simp only [CollatzResearch.WordTrace]
  refine ⟨130600061736623356354282853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87066707824415570902855235 130600061736623356354282853)
  ·
    refine ⟨24487511575616879316428035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130600061736623356354282853 24487511575616879316428035)
    ·
      refine ⟨36731267363425318974642053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24487511575616879316428035 36731267363425318974642053)
      ·
        refine ⟨6887112630642247307745385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36731267363425318974642053 6887112630642247307745385)
        ·
          refine ⟨5165334472981685480809039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6887112630642247307745385 5165334472981685480809039)
          ·
            refine ⟨7748001709472528221213559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5165334472981685480809039 7748001709472528221213559)
            ·
              refine ⟨11622002564208792331820339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7748001709472528221213559 11622002564208792331820339)
              ·
                refine ⟨17433003846313188497730509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11622002564208792331820339 17433003846313188497730509)
                ·
                  refine ⟨6537376442367445686648941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17433003846313188497730509 6537376442367445686648941)
                  ·
                    refine ⟨2451516165887792132493353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6537376442367445686648941 2451516165887792132493353)
                    ·
                      refine ⟨1838637124415844099370015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2451516165887792132493353 1838637124415844099370015)
                      ·
                        rfl

theorem cell23_3580733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_3580733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580733 prefixEnd_3580733 := by exact prefixLift 3580733
  have htrace : WordTrace (prefixWord ++ tailWord_3580733) baseStart_3580733 baseEnd_3580733 := by
    simpa [prefixWord, tailWord_3580733, baseEnd_3580733] using wordTrace_append hprefix tailTrace_3580733
  have hstable : (prefixWord ++ tailWord_3580733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580733).length < 2 ^ (prefixWord ++ tailWord_3580733).sum := by decide
  have hdescent : baseEnd_3580733 < baseStart_3580733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580746 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 4, 2, 2]
def baseStart_3580746 : Nat := 118140960795 + 3580746 * 2 ^ 59
def prefixEnd_3580746 : Nat := 4983230072969 + 3 ^ 40 * 3580746 * 2
def baseEnd_3580746 : Nat := 1838643799664352548507455

theorem tailTrace_3580746 : CollatzResearch.WordTrace tailWord_3580746 prefixEnd_3580746 1838643799664352548507455 := by
  unfold tailWord_3580746
  simp only [CollatzResearch.WordTrace]
  refine ⟨32650133971394064893626523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87067023923717506383004061 32650133971394064893626523)
  ·
    refine ⟨48975200957091097340439785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32650133971394064893626523 48975200957091097340439785)
    ·
      refine ⟨36731400717818323005329839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48975200957091097340439785 36731400717818323005329839)
      ·
        refine ⟨55097101076727484507994759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36731400717818323005329839 55097101076727484507994759)
        ·
          refine ⟨82645651615091226761992139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55097101076727484507994759 82645651615091226761992139)
          ·
            refine ⟨123968477422636840142988209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82645651615091226761992139 123968477422636840142988209)
            ·
              refine ⟨92976358066977630107241157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123968477422636840142988209 92976358066977630107241157)
              ·
                refine ⟨17433067137558305645107717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92976358066977630107241157 17433067137558305645107717)
                ·
                  refine ⟨3268700088292182308457697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17433067137558305645107717 3268700088292182308457697)
                  ·
                    refine ⟨2451525066219136731343273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3268700088292182308457697 2451525066219136731343273)
                    ·
                      refine ⟨1838643799664352548507455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2451525066219136731343273 1838643799664352548507455)
                      ·
                        rfl

theorem cell23_3580746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_3580746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580746 prefixEnd_3580746 := by exact prefixLift 3580746
  have htrace : WordTrace (prefixWord ++ tailWord_3580746) baseStart_3580746 baseEnd_3580746 := by
    simpa [prefixWord, tailWord_3580746, baseEnd_3580746] using wordTrace_append hprefix tailTrace_3580746
  have hstable : (prefixWord ++ tailWord_3580746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580746).length < 2 ^ (prefixWord ++ tailWord_3580746).sum := by decide
  have hdescent : baseEnd_3580746 < baseStart_3580746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580792 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 3, 2, 5]
def baseStart_3580792 : Nat := 118140960795 + 3580792 * 2 ^ 59
def prefixEnd_3580792 : Nat := 4983230072969 + 3 ^ 40 * 3580792 * 2
def baseEnd_3580792 : Nat := 1838667419774459368532243

theorem tailTrace_3580792 : CollatzResearch.WordTrace tailWord_3580792 prefixEnd_3580792 1838667419774459368532243 := by
  unfold tailWord_3580792
  simp only [CollatzResearch.WordTrace]
  refine ⟨65301106821704804715340315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87068142428939739620453753 65301106821704804715340315)
  ·
    refine ⟨97951660232557207073010473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65301106821704804715340315 97951660232557207073010473)
    ·
      refine ⟨73463745174417905304757855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97951660232557207073010473 73463745174417905304757855)
      ·
        refine ⟨110195617761626857957136783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73463745174417905304757855 110195617761626857957136783)
        ·
          refine ⟨165293426642440286935705175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110195617761626857957136783 165293426642440286935705175)
          ·
            refine ⟨247940139963660430403557763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165293426642440286935705175 247940139963660430403557763)
            ·
              refine ⟨371910209945490645605336645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247940139963660430403557763 371910209945490645605336645)
              ·
                refine ⟨69733164364779496051000621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 371910209945490645605336645 69733164364779496051000621)
                ·
                  refine ⟨26149936636792311019125233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69733164364779496051000621 26149936636792311019125233)
                  ·
                    refine ⟨19612452477594233264343925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26149936636792311019125233 19612452477594233264343925)
                    ·
                      refine ⟨1838667419774459368532243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19612452477594233264343925 1838667419774459368532243)
                      ·
                        rfl

theorem cell23_3580792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_3580792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580792 prefixEnd_3580792 := by exact prefixLift 3580792
  have htrace : WordTrace (prefixWord ++ tailWord_3580792) baseStart_3580792 baseEnd_3580792 := by
    simpa [prefixWord, tailWord_3580792, baseEnd_3580792] using wordTrace_append hprefix tailTrace_3580792
  have hstable : (prefixWord ++ tailWord_3580792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580792).length < 2 ^ (prefixWord ++ tailWord_3580792).sum := by decide
  have hdescent : baseEnd_3580792 < baseStart_3580792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580799 : List Nat := [1, 1, 2, 2, 1, 1, 7, 1, 2, 5]
def baseStart_3580799 : Nat := 118140960795 + 3580799 * 2 ^ 59
def prefixEnd_3580799 : Nat := 4983230072969 + 3 ^ 40 * 3580799 * 2
def baseEnd_3580799 : Nat := 612890338046346947048237

theorem tailTrace_3580799 : CollatzResearch.WordTrace tailWord_3580799 prefixEnd_3580799 612890338046346947048237 := by
  unfold tailWord_3580799
  simp only [CollatzResearch.WordTrace]
  refine ⟨130602468954384249626185451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87068312636256166417456967 130602468954384249626185451)
  ·
    refine ⟨195903703431576374439278177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130602468954384249626185451 195903703431576374439278177)
    ·
      refine ⟨146927777573682280829458633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195903703431576374439278177 146927777573682280829458633)
      ·
        refine ⟨110195833180261710622093975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146927777573682280829458633 110195833180261710622093975)
        ·
          refine ⟨165293749770392565933140963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110195833180261710622093975 165293749770392565933140963)
          ·
            refine ⟨247940624655588848899711445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165293749770392565933140963 247940624655588848899711445)
            ·
              refine ⟨5811108390365363646086987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 247940624655588848899711445 5811108390365363646086987)
              ·
                refine ⟨8716662585548045469130481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5811108390365363646086987 8716662585548045469130481)
                ·
                  refine ⟨6537496939161034101847861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8716662585548045469130481 6537496939161034101847861)
                  ·
                    refine ⟨612890338046346947048237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6537496939161034101847861 612890338046346947048237)
                    ·
                      rfl

theorem cell23_3580799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 5].length) (baseStart_3580799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580799 prefixEnd_3580799 := by exact prefixLift 3580799
  have htrace : WordTrace (prefixWord ++ tailWord_3580799) baseStart_3580799 baseEnd_3580799 := by
    simpa [prefixWord, tailWord_3580799, baseEnd_3580799] using wordTrace_append hprefix tailTrace_3580799
  have hstable : (prefixWord ++ tailWord_3580799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580799).length < 2 ^ (prefixWord ++ tailWord_3580799).sum := by decide
  have hdescent : baseEnd_3580799 < baseStart_3580799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580836 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 2, 4, 2]
def baseStart_3580836 : Nat := 118140960795 + 3580836 * 2 ^ 59
def prefixEnd_3580836 : Nat := 4983230072969 + 3 ^ 40 * 3580836 * 2
def baseEnd_3580836 : Nat := 1838690012923257196382041

theorem tailTrace_3580836 : CollatzResearch.WordTrace tailWord_3580836 prefixEnd_3580836 1838690012923257196382041 := by
  unfold tailWord_3580836
  simp only [CollatzResearch.WordTrace]
  refine ⟨65301909227625102472641181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87069212303500136630188241 65301909227625102472641181)
  ·
    refine ⟨24488215960359413427240443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65301909227625102472641181 24488215960359413427240443)
    ·
      refine ⟨36732323940539120140860665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24488215960359413427240443 36732323940539120140860665)
      ·
        refine ⟨27549242955404340105645499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36732323940539120140860665 27549242955404340105645499)
        ·
          refine ⟨41323864433106510158468249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27549242955404340105645499 41323864433106510158468249)
          ·
            refine ⟨30992898324829882618851187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41323864433106510158468249 30992898324829882618851187)
            ·
              refine ⟨46489347487244823928276781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30992898324829882618851187 46489347487244823928276781)
              ·
                refine ⟨17433505307716808973103793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46489347487244823928276781 17433505307716808973103793)
                ·
                  refine ⟨13075128980787606729827845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17433505307716808973103793 13075128980787606729827845)
                  ·
                    refine ⟨2451586683897676261842721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13075128980787606729827845 2451586683897676261842721)
                    ·
                      refine ⟨1838690012923257196382041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2451586683897676261842721 1838690012923257196382041)
                      ·
                        rfl

theorem cell23_3580836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_3580836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580836 prefixEnd_3580836 := by exact prefixLift 3580836
  have htrace : WordTrace (prefixWord ++ tailWord_3580836) baseStart_3580836 baseEnd_3580836 := by
    simpa [prefixWord, tailWord_3580836, baseEnd_3580836] using wordTrace_append hprefix tailTrace_3580836
  have hstable : (prefixWord ++ tailWord_3580836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580836).length < 2 ^ (prefixWord ++ tailWord_3580836).sum := by decide
  have hdescent : baseEnd_3580836 < baseStart_3580836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580854 : List Nat := [5, 1, 4, 1, 1, 2, 1, 3, 5]
def baseStart_3580854 : Nat := 118140960795 + 3580854 * 2 ^ 59
def prefixEnd_3580854 : Nat := 4983230072969 + 3 ^ 40 * 3580854 * 2
def baseEnd_3580854 : Nat := 204299917286115347328551

theorem tailTrace_3580854 : CollatzResearch.WordTrace tailWord_3580854 prefixEnd_3580854 204299917286115347328551 := by
  unfold tailWord_3580854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8162779685574062126214851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87069649979456662679625077 8162779685574062126214851)
  ·
    refine ⟨12244169528361093189322277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8162779685574062126214851 12244169528361093189322277)
    ·
      refine ⟨2295781786567704972997927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12244169528361093189322277 2295781786567704972997927)
      ·
        refine ⟨3443672679851557459496891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2295781786567704972997927 3443672679851557459496891)
        ·
          refine ⟨5165509019777336189245337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3443672679851557459496891 5165509019777336189245337)
          ·
            refine ⟨3874131764833002141934003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5165509019777336189245337 3874131764833002141934003)
            ·
              refine ⟨5811197647249503212901005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3874131764833002141934003 5811197647249503212901005)
              ·
                refine ⟨2179199117718563704837877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5811197647249503212901005 2179199117718563704837877)
                ·
                  refine ⟨204299917286115347328551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2179199117718563704837877 204299917286115347328551)
                  ·
                    rfl

theorem cell23_3580854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_3580854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580854 prefixEnd_3580854 := by exact prefixLift 3580854
  have htrace : WordTrace (prefixWord ++ tailWord_3580854) baseStart_3580854 baseEnd_3580854 := by
    simpa [prefixWord, tailWord_3580854, baseEnd_3580854] using wordTrace_append hprefix tailTrace_3580854
  have hstable : (prefixWord ++ tailWord_3580854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580854).length < 2 ^ (prefixWord ++ tailWord_3580854).sum := by decide
  have hdescent : baseEnd_3580854 < baseStart_3580854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580893 : List Nat := [1, 4, 3, 1, 2, 1, 4, 1, 6]
def baseStart_3580893 : Nat := 118140960795 + 3580893 * 2 ^ 59
def prefixEnd_3580893 : Nat := 4983230072969 + 3 ^ 40 * 3580893 * 2
def baseEnd_3580893 : Nat := 204302142368951497041031

theorem tailTrace_3580893 : CollatzResearch.WordTrace tailWord_3580893 prefixEnd_3580893 204302142368951497041031 := by
  unfold tailWord_3580893
  simp only [CollatzResearch.WordTrace]
  refine ⟨130605897416043703680107333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87070598277362469120071555 130605897416043703680107333)
  ·
    refine ⟨24488605765508194440020125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130605897416043703680107333 24488605765508194440020125)
    ·
      refine ⟨9183227162065572915007547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24488605765508194440020125 9183227162065572915007547)
      ·
        refine ⟨13774840743098359372511321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9183227162065572915007547 13774840743098359372511321)
        ·
          refine ⟨10331130557323769529383491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13774840743098359372511321 10331130557323769529383491)
          ·
            refine ⟨15496695835985654294075237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10331130557323769529383491 15496695835985654294075237)
            ·
              refine ⟨2905630469247310180139107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15496695835985654294075237 2905630469247310180139107)
              ·
                refine ⟨4358445703870965270208661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2905630469247310180139107 4358445703870965270208661)
                ·
                  refine ⟨204302142368951497041031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4358445703870965270208661 204302142368951497041031)
                  ·
                    rfl

theorem cell23_3580893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_3580893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580893 prefixEnd_3580893 := by exact prefixLift 3580893
  have htrace : WordTrace (prefixWord ++ tailWord_3580893) baseStart_3580893 baseEnd_3580893 := by
    simpa [prefixWord, tailWord_3580893, baseEnd_3580893] using wordTrace_append hprefix tailTrace_3580893
  have hstable : (prefixWord ++ tailWord_3580893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580893).length < 2 ^ (prefixWord ++ tailWord_3580893).sum := by decide
  have hdescent : baseEnd_3580893 < baseStart_3580893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580906 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 3, 5]
def baseStart_3580906 : Nat := 118140960795 + 3580906 * 2 ^ 59
def prefixEnd_3580906 : Nat := 4983230072969 + 3 ^ 40 * 3580906 * 2
def baseEnd_3580906 : Nat := 612908652189690640835573

theorem tailTrace_3580906 : CollatzResearch.WordTrace tailWord_3580906 prefixEnd_3580906 612908652189690640835573 := by
  unfold tailWord_3580906
  simp only [CollatzResearch.WordTrace]
  refine ⟨32651592891249151725082643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87070914376664404600220381 32651592891249151725082643)
  ·
    refine ⟨48977389336873727587623965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32651592891249151725082643 48977389336873727587623965)
    ·
      refine ⟨18366521001327647845358987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48977389336873727587623965 18366521001327647845358987)
      ·
        refine ⟨27549781501991471768038481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18366521001327647845358987 27549781501991471768038481)
        ·
          refine ⟨20662336126493603826028861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27549781501991471768038481 20662336126493603826028861)
          ·
            refine ⟨7748376047435101434760823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20662336126493603826028861 7748376047435101434760823)
            ·
              refine ⟨11622564071152652152141235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7748376047435101434760823 11622564071152652152141235)
              ·
                refine ⟨17433846106728978228211853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11622564071152652152141235 17433846106728978228211853)
                ·
                  refine ⟨6537692290023366835579445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17433846106728978228211853 6537692290023366835579445)
                  ·
                    refine ⟨612908652189690640835573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6537692290023366835579445 612908652189690640835573)
                    ·
                      rfl

theorem cell23_3580906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_3580906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580906 prefixEnd_3580906 := by exact prefixLift 3580906
  have htrace : WordTrace (prefixWord ++ tailWord_3580906) baseStart_3580906 baseEnd_3580906 := by
    simpa [prefixWord, tailWord_3580906, baseEnd_3580906] using wordTrace_append hprefix tailTrace_3580906
  have hstable : (prefixWord ++ tailWord_3580906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580906).length < 2 ^ (prefixWord ++ tailWord_3580906).sum := by decide
  have hdescent : baseEnd_3580906 < baseStart_3580906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580913 : List Nat := [1, 2, 2, 2, 4, 1, 1, 3, 2, 3, 2]
def baseStart_3580913 : Nat := 118140960795 + 3580913 * 2 ^ 59
def prefixEnd_3580913 : Nat := 4983230072969 + 3 ^ 40 * 3580913 * 2
def baseEnd_3580913 : Nat := 1838729550933653395119187

theorem tailTrace_3580913 : CollatzResearch.WordTrace tailWord_3580913 prefixEnd_3580913 1838729550933653395119187 := by
  unfold tailWord_3580913
  simp only [CollatzResearch.WordTrace]
  refine ⟨130606626875971247095835393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87071084583980831397223595 130606626875971247095835393)
  ·
    refine ⟨97954970156978435321876545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130606626875971247095835393 97954970156978435321876545)
    ·
      refine ⟨73466227617733826491407409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97954970156978435321876545 73466227617733826491407409)
      ·
        refine ⟨55099670713300369868555557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73466227617733826491407409 55099670713300369868555557)
        ·
          refine ⟨10331188258743819350354167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55099670713300369868555557 10331188258743819350354167)
          ·
            refine ⟨15496782388115729025531251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10331188258743819350354167 15496782388115729025531251)
            ·
              refine ⟨23245173582173593538296877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15496782388115729025531251 23245173582173593538296877)
              ·
                refine ⟨8716940093315097576861329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23245173582173593538296877 8716940093315097576861329)
                ·
                  refine ⟨6537705069986323182645997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8716940093315097576861329 6537705069986323182645997)
                  ·
                    refine ⟨2451639401244871193492249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6537705069986323182645997 2451639401244871193492249)
                    ·
                      refine ⟨1838729550933653395119187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2451639401244871193492249 1838729550933653395119187)
                      ·
                        rfl

theorem cell23_3580913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_3580913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580913 prefixEnd_3580913 := by exact prefixLift 3580913
  have htrace : WordTrace (prefixWord ++ tailWord_3580913) baseStart_3580913 baseEnd_3580913 := by
    simpa [prefixWord, tailWord_3580913, baseEnd_3580913] using wordTrace_append hprefix tailTrace_3580913
  have hstable : (prefixWord ++ tailWord_3580913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580913).length < 2 ^ (prefixWord ++ tailWord_3580913).sum := by decide
  have hdescent : baseEnd_3580913 < baseStart_3580913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580976 : List Nat := [2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 3]
def baseStart_3580976 : Nat := 118140960795 + 3580976 * 2 ^ 59
def prefixEnd_3580976 : Nat := 4983230072969 + 3 ^ 40 * 3580976 * 2
def baseEnd_3580976 : Nat := 1838761900214886648631397

theorem tailTrace_3580976 : CollatzResearch.WordTrace tailWord_3580976 prefixEnd_3580976 1838761900214886648631397 := by
  unfold tailWord_3580976
  simp only [CollatzResearch.WordTrace]
  refine ⟨65304462337371504427689391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87072616449828672570252521 65304462337371504427689391)
  ·
    refine ⟨97956693506057256641534087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65304462337371504427689391 97956693506057256641534087)
    ·
      refine ⟨146935040259085884962301131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97956693506057256641534087 146935040259085884962301131)
      ·
        refine ⟨220402560388628827443451697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146935040259085884962301131 220402560388628827443451697)
        ·
          refine ⟨165301920291471620582588773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220402560388628827443451697 165301920291471620582588773)
          ·
            refine ⟨30994110054650928859235395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165301920291471620582588773 30994110054650928859235395)
            ·
              refine ⟨46491165081976393288853093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30994110054650928859235395 46491165081976393288853093)
              ·
                refine ⟨8717093452870573741659955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46491165081976393288853093 8717093452870573741659955)
                ·
                  refine ⟨13075640179305860612489933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8717093452870573741659955 13075640179305860612489933)
                  ·
                    refine ⟨4903365067239697729683725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13075640179305860612489933 4903365067239697729683725)
                    ·
                      refine ⟨1838761900214886648631397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4903365067239697729683725 1838761900214886648631397)
                      ·
                        rfl

theorem cell23_3580976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 3].length) (baseStart_3580976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580976 prefixEnd_3580976 := by exact prefixLift 3580976
  have htrace : WordTrace (prefixWord ++ tailWord_3580976) baseStart_3580976 baseEnd_3580976 := by
    simpa [prefixWord, tailWord_3580976, baseEnd_3580976] using wordTrace_append hprefix tailTrace_3580976
  have hstable : (prefixWord ++ tailWord_3580976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580976).length < 2 ^ (prefixWord ++ tailWord_3580976).sum := by decide
  have hdescent : baseEnd_3580976 < baseStart_3580976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580977 : List Nat := [1, 2, 2, 3, 1, 2, 4, 3, 1, 2, 2]
def baseStart_3580977 : Nat := 118140960795 + 3580977 * 2 ^ 59
def prefixEnd_3580977 : Nat := 4983230072969 + 3 ^ 40 * 3580977 * 2
def baseEnd_3580977 : Nat := 1838762413695541144718893

theorem tailTrace_3580977 : CollatzResearch.WordTrace tailWord_3580977 prefixEnd_3580977 1838762413695541144718893 := by
  unfold tailWord_3580977
  simp only [CollatzResearch.WordTrace]
  refine ⟨130608961147739386026165185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87072640765159590684110123 130608961147739386026165185)
  ·
    refine ⟨97956720860804539519623889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130608961147739386026165185 97956720860804539519623889)
    ·
      refine ⟨73467540645603404639717917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97956720860804539519623889 73467540645603404639717917)
      ·
        refine ⟨27550327742101276739894219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73467540645603404639717917 27550327742101276739894219)
        ·
          refine ⟨41325491613151915109841329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27550327742101276739894219 41325491613151915109841329)
          ·
            refine ⟨30994118709863936332380997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41325491613151915109841329 30994118709863936332380997)
            ·
              refine ⟨5811397258099488062321437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30994118709863936332380997 5811397258099488062321437)
              ·
                refine ⟨2179273971787308023370539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5811397258099488062321437 2179273971787308023370539)
                ·
                  refine ⟨3268910957680962035055809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2179273971787308023370539 3268910957680962035055809)
                  ·
                    refine ⟨2451683218260721526291857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3268910957680962035055809 2451683218260721526291857)
                    ·
                      refine ⟨1838762413695541144718893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2451683218260721526291857 1838762413695541144718893)
                      ·
                        rfl

theorem cell23_3580977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_3580977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3580977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3580977 prefixEnd_3580977 := by exact prefixLift 3580977
  have htrace : WordTrace (prefixWord ++ tailWord_3580977) baseStart_3580977 baseEnd_3580977 := by
    simpa [prefixWord, tailWord_3580977, baseEnd_3580977] using wordTrace_append hprefix tailTrace_3580977
  have hstable : (prefixWord ++ tailWord_3580977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580977).length < 2 ^ (prefixWord ++ tailWord_3580977).sum := by decide
  have hdescent : baseEnd_3580977 < baseStart_3580977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581010 : List Nat := [3, 2, 2, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_3581010 : Nat := 118140960795 + 3581010 * 2 ^ 59
def prefixEnd_3581010 : Nat := 4983230072969 + 3 ^ 40 * 3581010 * 2
def baseEnd_3581010 : Nat := 1838779358557139515606241

theorem tailTrace_3581010 : CollatzResearch.WordTrace tailWord_3581010 prefixEnd_3581010 1838779358557139515606241 := by
  unfold tailWord_3581010
  simp only [CollatzResearch.WordTrace]
  refine ⟨32652541189154958165529121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87073443171079888441410989 32652541189154958165529121)
  ·
    refine ⟨24489405891866218624146841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32652541189154958165529121 24489405891866218624146841)
    ·
      refine ⟨18367054418899663968110131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24489405891866218624146841 18367054418899663968110131)
      ·
        refine ⟨27550581628349495952165197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18367054418899663968110131 27550581628349495952165197)
        ·
          refine ⟨10331468110631060982061949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27550581628349495952165197 10331468110631060982061949)
          ·
            refine ⟨3874300541486647868273231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10331468110631060982061949 3874300541486647868273231)
            ·
              refine ⟨5811450812229971802409847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3874300541486647868273231 5811450812229971802409847)
              ·
                refine ⟨8717176218344957703614771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5811450812229971802409847 8717176218344957703614771)
                ·
                  refine ⟨13075764327517436555422157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8717176218344957703614771 13075764327517436555422157)
                  ·
                    refine ⟨4903411622819038708283309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13075764327517436555422157 4903411622819038708283309)
                    ·
                      refine ⟨1838779358557139515606241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4903411622819038708283309 1838779358557139515606241)
                      ·
                        rfl

theorem cell23_3581010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_3581010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581010 prefixEnd_3581010 := by exact prefixLift 3581010
  have htrace : WordTrace (prefixWord ++ tailWord_3581010) baseStart_3581010 baseEnd_3581010 := by
    simpa [prefixWord, tailWord_3581010, baseEnd_3581010] using wordTrace_append hprefix tailTrace_3581010
  have hstable : (prefixWord ++ tailWord_3581010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581010).length < 2 ^ (prefixWord ++ tailWord_3581010).sum := by decide
  have hdescent : baseEnd_3581010 < baseStart_3581010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581014 : List Nat := [5, 2, 2, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_3581014 : Nat := 118140960795 + 3581014 * 2 ^ 59
def prefixEnd_3581014 : Nat := 4983230072969 + 3 ^ 40 * 3581014 * 2
def baseEnd_3581014 : Nat := 1838781412479757499956223

theorem tailTrace_3581014 : CollatzResearch.WordTrace tailWord_3581014 prefixEnd_3581014 1838781412479757499956223 := by
  unfold tailWord_3581014
  simp only [CollatzResearch.WordTrace]
  refine ⟨8163144415537833834078881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87073540432403560896841397 8163144415537833834078881)
  ·
    refine ⟨6122358311653375375559161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8163144415537833834078881 6122358311653375375559161)
    ·
      refine ⟨4591768733740031531669371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6122358311653375375559161 4591768733740031531669371)
      ·
        refine ⟨6887653100610047297504057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4591768733740031531669371 6887653100610047297504057)
        ·
          refine ⟨5165739825457535473128043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6887653100610047297504057 5165739825457535473128043)
          ·
            refine ⟨7748609738186303209692065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5165739825457535473128043 7748609738186303209692065)
            ·
              refine ⟨5811457303639727407269049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7748609738186303209692065 5811457303639727407269049)
              ·
                refine ⟨4358592977729795555451787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5811457303639727407269049 4358592977729795555451787)
                ·
                  refine ⟨6537889466594693333177681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4358592977729795555451787 6537889466594693333177681)
                  ·
                    refine ⟨4903417099946019999883261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6537889466594693333177681 4903417099946019999883261)
                    ·
                      refine ⟨1838781412479757499956223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4903417099946019999883261 1838781412479757499956223)
                      ·
                        rfl

theorem cell23_3581014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_3581014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581014 prefixEnd_3581014 := by exact prefixLift 3581014
  have htrace : WordTrace (prefixWord ++ tailWord_3581014) baseStart_3581014 baseEnd_3581014 := by
    simpa [prefixWord, tailWord_3581014, baseEnd_3581014] using wordTrace_append hprefix tailTrace_3581014
  have hstable : (prefixWord ++ tailWord_3581014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581014).length < 2 ^ (prefixWord ++ tailWord_3581014).sum := by decide
  have hdescent : baseEnd_3581014 < baseStart_3581014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581036 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 5]
def baseStart_3581036 : Nat := 118140960795 + 3581036 * 2 ^ 59
def prefixEnd_3581036 : Nat := 4983230072969 + 3 ^ 40 * 3581036 * 2
def baseEnd_3581036 : Nat := 1838792709054156413881121

theorem tailTrace_3581036 : CollatzResearch.WordTrace tailWord_3581036 prefixEnd_3581036 1838792709054156413881121 := by
  unfold tailWord_3581036
  simp only [CollatzResearch.WordTrace]
  refine ⟨65305556527262819551281481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87074075369683759401708641 65305556527262819551281481)
  ·
    refine ⟨48979167395447114663461111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65305556527262819551281481 48979167395447114663461111)
    ·
      refine ⟨73468751093170671995191667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48979167395447114663461111 73468751093170671995191667)
      ·
        refine ⟨110203126639756007992787501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73468751093170671995191667 110203126639756007992787501)
        ·
          refine ⟨41326172489908502997295313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110203126639756007992787501 41326172489908502997295313)
          ·
            refine ⟨30994629367431377247971485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41326172489908502997295313 30994629367431377247971485)
            ·
              refine ⟨11622986012786766467989307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30994629367431377247971485 11622986012786766467989307)
              ·
                refine ⟨17434479019180149701983961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11622986012786766467989307 17434479019180149701983961)
                ·
                  refine ⟨13075859264385112276487971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17434479019180149701983961 13075859264385112276487971)
                  ·
                    refine ⟨19613788896577668414731957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13075859264385112276487971 19613788896577668414731957)
                    ·
                      refine ⟨1838792709054156413881121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19613788896577668414731957 1838792709054156413881121)
                      ·
                        rfl

theorem cell23_3581036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_3581036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581036 prefixEnd_3581036 := by exact prefixLift 3581036
  have htrace : WordTrace (prefixWord ++ tailWord_3581036) baseStart_3581036 baseEnd_3581036 := by
    simpa [prefixWord, tailWord_3581036, baseEnd_3581036] using wordTrace_append hprefix tailTrace_3581036
  have hstable : (prefixWord ++ tailWord_3581036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581036).length < 2 ^ (prefixWord ++ tailWord_3581036).sum := by decide
  have hdescent : baseEnd_3581036 < baseStart_3581036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581056 : List Nat := [2, 1, 1, 2, 1, 3, 5, 1, 7]
def baseStart_3581056 : Nat := 118140960795 + 3581056 * 2 ^ 59
def prefixEnd_3581056 : Nat := 4983230072969 + 3 ^ 40 * 3581056 * 2
def baseEnd_3581056 : Nat := 204311442074138481736781

theorem tailTrace_3581056 : CollatzResearch.WordTrace tailWord_3581056 prefixEnd_3581056 204311442074138481736781 := by
  unfold tailWord_3581056
  simp only [CollatzResearch.WordTrace]
  refine ⟨65305921257226591259145511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87074561676302121678860681 65305921257226591259145511)
  ·
    refine ⟨97958881885839886888718267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65305921257226591259145511 97958881885839886888718267)
    ·
      refine ⟨146938322828759830333077401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97958881885839886888718267 146938322828759830333077401)
      ·
        refine ⟨110203742121569872749808051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146938322828759830333077401 110203742121569872749808051)
        ·
          refine ⟨165305613182354809124712077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110203742121569872749808051 165305613182354809124712077)
          ·
            refine ⟨61989604943383053421767029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165305613182354809124712077 61989604943383053421767029)
            ·
              refine ⟨5811525463442161258290659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61989604943383053421767029 5811525463442161258290659)
              ·
                refine ⟨8717288195163241887435989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5811525463442161258290659 8717288195163241887435989)
                ·
                  refine ⟨204311442074138481736781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8717288195163241887435989 204311442074138481736781)
                  ·
                    rfl

theorem cell23_3581056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 7].length) (baseStart_3581056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581056 prefixEnd_3581056 := by exact prefixLift 3581056
  have htrace : WordTrace (prefixWord ++ tailWord_3581056) baseStart_3581056 baseEnd_3581056 := by
    simpa [prefixWord, tailWord_3581056, baseEnd_3581056] using wordTrace_append hprefix tailTrace_3581056
  have hstable : (prefixWord ++ tailWord_3581056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581056).length < 2 ^ (prefixWord ++ tailWord_3581056).sum := by decide
  have hdescent : baseEnd_3581056 < baseStart_3581056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581146 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 8]
def baseStart_3581146 : Nat := 118140960795 + 3581146 * 2 ^ 59
def prefixEnd_3581146 : Nat := 4983230072969 + 3 ^ 40 * 3581146 * 2
def baseEnd_3581146 : Nat := 204316576880683442611735

theorem tailTrace_3581146 : CollatzResearch.WordTrace tailWord_3581146 prefixEnd_3581146 204316576880683442611735 := by
  unfold tailWord_3581146
  simp only [CollatzResearch.WordTrace]
  refine ⟨32653781271031781972266823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87076750056084751926044861 32653781271031781972266823)
  ·
    refine ⟨48980671906547672958400235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32653781271031781972266823 48980671906547672958400235)
    ·
      refine ⟨73471007859821509437600353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48980671906547672958400235 73471007859821509437600353)
      ·
        refine ⟨55103255894866132078200265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73471007859821509437600353 55103255894866132078200265)
        ·
          refine ⟨41327441921149599058650199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55103255894866132078200265 41327441921149599058650199)
          ·
            refine ⟨61991162881724398587975299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41327441921149599058650199 61991162881724398587975299)
            ·
              refine ⟨92986744322586597881962949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61991162881724398587975299 92986744322586597881962949)
              ·
                refine ⟨17435014560484987102868053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92986744322586597881962949 17435014560484987102868053)
                ·
                  refine ⟨204316576880683442611735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17435014560484987102868053 204316576880683442611735)
                  ·
                    rfl

theorem cell23_3581146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 8].length) (baseStart_3581146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581146 prefixEnd_3581146 := by exact prefixLift 3581146
  have htrace : WordTrace (prefixWord ++ tailWord_3581146) baseStart_3581146 baseEnd_3581146 := by
    simpa [prefixWord, tailWord_3581146, baseEnd_3581146] using wordTrace_append hprefix tailTrace_3581146
  have hstable : (prefixWord ++ tailWord_3581146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581146).length < 2 ^ (prefixWord ++ tailWord_3581146).sum := by decide
  have hdescent : baseEnd_3581146 < baseStart_3581146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581163 : List Nat := [1, 1, 1, 1, 2, 6, 3, 2, 6]
def baseStart_3581163 : Nat := 118140960795 + 3581163 * 2 ^ 59
def prefixEnd_3581163 : Nat := 4983230072969 + 3 ^ 40 * 3581163 * 2
def baseEnd_3581163 : Nat := 204317546788586379665893

theorem tailTrace_3581163 : CollatzResearch.WordTrace tailWord_3581163 prefixEnd_3581163 204317546788586379665893 := by
  unfold tailWord_3581163
  simp only [CollatzResearch.WordTrace]
  refine ⟨130615745125065539792436143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87077163416710359861624095 130615745125065539792436143)
  ·
    refine ⟨195923617687598309688654215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130615745125065539792436143 195923617687598309688654215)
    ·
      refine ⟨293885426531397464532981323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195923617687598309688654215 293885426531397464532981323)
      ·
        refine ⟨440828139797096196799471985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293885426531397464532981323 440828139797096196799471985)
        ·
          refine ⟨330621104847822147599603989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440828139797096196799471985 330621104847822147599603989)
          ·
            refine ⟨15497864289741663168731437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 330621104847822147599603989 15497864289741663168731437)
            ·
              refine ⟨5811699108653123688274289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15497864289741663168731437 5811699108653123688274289)
              ·
                refine ⟨4358774331489842766205717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5811699108653123688274289 4358774331489842766205717)
                ·
                  refine ⟨204317546788586379665893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4358774331489842766205717 204317546788586379665893)
                  ·
                    rfl

theorem cell23_3581163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 6].length) (baseStart_3581163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581163 prefixEnd_3581163 := by exact prefixLift 3581163
  have htrace : WordTrace (prefixWord ++ tailWord_3581163) baseStart_3581163 baseEnd_3581163 := by
    simpa [prefixWord, tailWord_3581163, baseEnd_3581163] using wordTrace_append hprefix tailTrace_3581163
  have hstable : (prefixWord ++ tailWord_3581163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581163).length < 2 ^ (prefixWord ++ tailWord_3581163).sum := by decide
  have hdescent : baseEnd_3581163 < baseStart_3581163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581210 : List Nat := [3, 1, 1, 3, 3, 1, 2, 3, 1, 5]
def baseStart_3581210 : Nat := 118140960795 + 3581210 * 2 ^ 59
def prefixEnd_3581210 : Nat := 4983230072969 + 3 ^ 40 * 3581210 * 2
def baseEnd_3581210 : Nat := 612960684896012911035107

theorem tailTrace_3581210 : CollatzResearch.WordTrace tailWord_3581210 prefixEnd_3581210 612960684896012911035107 := by
  unfold tailWord_3581210
  simp only [CollatzResearch.WordTrace]
  refine ⟨32654364838973816704849271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87078306237263511212931389 32654364838973816704849271)
  ·
    refine ⟨48981547258460725057273907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32654364838973816704849271 48981547258460725057273907)
    ·
      refine ⟨73472320887691087585910861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48981547258460725057273907 73472320887691087585910861)
      ·
        refine ⟨27552120332884157844716573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73472320887691087585910861 27552120332884157844716573)
        ·
          refine ⟨10332045124831559191768715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27552120332884157844716573 10332045124831559191768715)
          ·
            refine ⟨15498067687247338787653073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10332045124831559191768715 15498067687247338787653073)
            ·
              refine ⟨11623550765435504090739805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15498067687247338787653073 11623550765435504090739805)
              ·
                refine ⟨4358831537038314034027427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11623550765435504090739805 4358831537038314034027427)
                ·
                  refine ⟨6538247305557471051041141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4358831537038314034027427 6538247305557471051041141)
                  ·
                    refine ⟨612960684896012911035107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6538247305557471051041141 612960684896012911035107)
                    ·
                      rfl

theorem cell23_3581210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_3581210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581210 prefixEnd_3581210 := by exact prefixLift 3581210
  have htrace : WordTrace (prefixWord ++ tailWord_3581210) baseStart_3581210 baseEnd_3581210 := by
    simpa [prefixWord, tailWord_3581210, baseEnd_3581210] using wordTrace_append hprefix tailTrace_3581210
  have hstable : (prefixWord ++ tailWord_3581210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581210).length < 2 ^ (prefixWord ++ tailWord_3581210).sum := by decide
  have hdescent : baseEnd_3581210 < baseStart_3581210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581224 : List Nat := [2, 1, 5, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_3581224 : Nat := 118140960795 + 3581224 * 2 ^ 59
def prefixEnd_3581224 : Nat := 4983230072969 + 3 ^ 40 * 3581224 * 2
def baseEnd_3581224 : Nat := 1838889243417201678330257

theorem tailTrace_3581224 : CollatzResearch.WordTrace tailWord_3581224 prefixEnd_3581224 1838889243417201678330257 := by
  unfold tailWord_3581224
  simp only [CollatzResearch.WordTrace]
  refine ⟨65308984988922273605203363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87078646651896364806937817 65308984988922273605203363)
  ·
    refine ⟨97963477483383410407805045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65308984988922273605203363 97963477483383410407805045)
    ·
      refine ⟨9184076014067194725731723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97963477483383410407805045 9184076014067194725731723)
      ·
        refine ⟨13776114021100792088597585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9184076014067194725731723 13776114021100792088597585)
        ·
          refine ⟨10332085515825594066448189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13776114021100792088597585 10332085515825594066448189)
          ·
            refine ⟨3874532068434597774918071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10332085515825594066448189 3874532068434597774918071)
            ·
              refine ⟨5811798102651896662377107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3874532068434597774918071 5811798102651896662377107)
              ·
                refine ⟨8717697153977844993565661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5811798102651896662377107 8717697153977844993565661)
                ·
                  refine ⟨3269136432741691872587123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8717697153977844993565661 3269136432741691872587123)
                  ·
                    refine ⟨4903704649112537808880685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3269136432741691872587123 4903704649112537808880685)
                    ·
                      refine ⟨1838889243417201678330257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4903704649112537808880685 1838889243417201678330257)
                      ·
                        rfl

theorem cell23_3581224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_3581224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581224 prefixEnd_3581224 := by exact prefixLift 3581224
  have htrace : WordTrace (prefixWord ++ tailWord_3581224) baseStart_3581224 baseEnd_3581224 := by
    simpa [prefixWord, tailWord_3581224, baseEnd_3581224] using wordTrace_append hprefix tailTrace_3581224
  have hstable : (prefixWord ++ tailWord_3581224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581224).length < 2 ^ (prefixWord ++ tailWord_3581224).sum := by decide
  have hdescent : baseEnd_3581224 < baseStart_3581224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581247 : List Nat := [1, 1, 2, 2, 4, 4, 1, 2, 1, 1, 4]
def baseStart_3581247 : Nat := 118140960795 + 3581247 * 2 ^ 59
def prefixEnd_3581247 : Nat := 4983230072969 + 3 ^ 40 * 3581247 * 2
def baseEnd_3581247 : Nat := 1838901053472255088342651

theorem tailTrace_3581247 : CollatzResearch.WordTrace tailWord_3581247 prefixEnd_3581247 1838901053472255088342651 := by
  unfold tailWord_3581247
  simp only [CollatzResearch.WordTrace]
  refine ⟨130618808856761222138493995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87079205904507481425662663 130618808856761222138493995)
  ·
    refine ⟨195928213285141833207740993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130618808856761222138493995 195928213285141833207740993)
    ·
      refine ⟨146946159963856374905805745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195928213285141833207740993 146946159963856374905805745)
      ·
        refine ⟨110209619972892281179354309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146946159963856374905805745 110209619972892281179354309)
        ·
          refine ⟨20664303744917302721128933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110209619972892281179354309 20664303744917302721128933)
          ·
            refine ⟨3874556952171994260211675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20664303744917302721128933 3874556952171994260211675)
            ·
              refine ⟨5811835428257991390317513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3874556952171994260211675 5811835428257991390317513)
              ·
                refine ⟨4358876571193493542738135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5811835428257991390317513 4358876571193493542738135)
                ·
                  refine ⟨6538314856790240314107203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4358876571193493542738135 6538314856790240314107203)
                  ·
                    refine ⟨9807472285185360471160805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6538314856790240314107203 9807472285185360471160805)
                    ·
                      refine ⟨1838901053472255088342651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9807472285185360471160805 1838901053472255088342651)
                      ·
                        rfl

theorem cell23_3581247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 1, 4].length) (baseStart_3581247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581247 prefixEnd_3581247 := by exact prefixLift 3581247
  have htrace : WordTrace (prefixWord ++ tailWord_3581247) baseStart_3581247 baseEnd_3581247 := by
    simpa [prefixWord, tailWord_3581247, baseEnd_3581247] using wordTrace_append hprefix tailTrace_3581247
  have hstable : (prefixWord ++ tailWord_3581247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581247).length < 2 ^ (prefixWord ++ tailWord_3581247).sum := by decide
  have hdescent : baseEnd_3581247 < baseStart_3581247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581260 : List Nat := [2, 2, 1, 3, 2, 3, 1, 2, 1, 2, 4]
def baseStart_3581260 : Nat := 118140960795 + 3581260 * 2 ^ 59
def prefixEnd_3581260 : Nat := 4983230072969 + 3 ^ 40 * 3581260 * 2
def baseEnd_3581260 : Nat := 1838907728720763537480091

theorem tailTrace_3581260 : CollatzResearch.WordTrace tailWord_3581260 prefixEnd_3581260 1838907728720763537480091 := by
  unfold tailWord_3581260
  simp only [CollatzResearch.WordTrace]
  refine ⟨65309641502857062679358617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87079522003809416905811489 65309641502857062679358617)
  ·
    refine ⟨48982231127142797009518963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65309641502857062679358617 48982231127142797009518963)
    ·
      refine ⟨73473346690714195514278445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48982231127142797009518963 73473346690714195514278445)
      ·
        refine ⟨27552505009017823317854417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73473346690714195514278445 27552505009017823317854417)
        ·
          refine ⟨20664378756763367488390813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27552505009017823317854417 20664378756763367488390813)
          ·
            refine ⟨7749142033786262808146555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20664378756763367488390813 7749142033786262808146555)
            ·
              refine ⟨11623713050679394212219833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7749142033786262808146555 11623713050679394212219833)
              ·
                refine ⟨8717784788009545659164875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11623713050679394212219833 8717784788009545659164875)
                ·
                  refine ⟨13076677182014318488747313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8717784788009545659164875 13076677182014318488747313)
                  ·
                    refine ⟨9807507886510738866560485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13076677182014318488747313 9807507886510738866560485)
                    ·
                      refine ⟨1838907728720763537480091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9807507886510738866560485 1838907728720763537480091)
                      ·
                        rfl

theorem cell23_3581260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_3581260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581260 prefixEnd_3581260 := by exact prefixLift 3581260
  have htrace : WordTrace (prefixWord ++ tailWord_3581260) baseStart_3581260 baseEnd_3581260 := by
    simpa [prefixWord, tailWord_3581260, baseEnd_3581260] using wordTrace_append hprefix tailTrace_3581260
  have hstable : (prefixWord ++ tailWord_3581260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581260).length < 2 ^ (prefixWord ++ tailWord_3581260).sum := by decide
  have hdescent : baseEnd_3581260 < baseStart_3581260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581261 : List Nat := [1, 6, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_3581261 : Nat := 118140960795 + 3581261 * 2 ^ 59
def prefixEnd_3581261 : Nat := 4983230072969 + 3 ^ 40 * 3581261 * 2
def baseEnd_3581261 : Nat := 612969414067139344522529

theorem tailTrace_3581261 : CollatzResearch.WordTrace tailWord_3581261 prefixEnd_3581261 612969414067139344522529 := by
  unfold tailWord_3581261
  simp only [CollatzResearch.WordTrace]
  refine ⟨130619319478710502529503637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87079546319140335019669091 130619319478710502529503637)
  ·
    refine ⟨6122780600564554806070483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 130619319478710502529503637 6122780600564554806070483)
    ·
      refine ⟨9184170900846832209105725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6122780600564554806070483 9184170900846832209105725)
      ·
        refine ⟨3444064087817562078414647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9184170900846832209105725 3444064087817562078414647)
        ·
          refine ⟨5166096131726343117621971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3444064087817562078414647 5166096131726343117621971)
          ·
            refine ⟨7749144197589514676432957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5166096131726343117621971 7749144197589514676432957)
            ·
              refine ⟨2905929074096068003662359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7749144197589514676432957 2905929074096068003662359)
              ·
                refine ⟨4358893611144102005493539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2905929074096068003662359 4358893611144102005493539)
                ·
                  refine ⟨6538340416716153008240309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4358893611144102005493539 6538340416716153008240309)
                  ·
                    refine ⟨612969414067139344522529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6538340416716153008240309 612969414067139344522529)
                    ·
                      rfl

theorem cell23_3581261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_3581261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581261 prefixEnd_3581261 := by exact prefixLift 3581261
  have htrace : WordTrace (prefixWord ++ tailWord_3581261) baseStart_3581261 baseEnd_3581261 := by
    simpa [prefixWord, tailWord_3581261, baseEnd_3581261] using wordTrace_append hprefix tailTrace_3581261
  have hstable : (prefixWord ++ tailWord_3581261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581261).length < 2 ^ (prefixWord ++ tailWord_3581261).sum := by decide
  have hdescent : baseEnd_3581261 < baseStart_3581261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581264 : List Nat := [2, 1, 1, 1, 1, 5, 2, 5, 1, 2, 2]
def baseStart_3581264 : Nat := 118140960795 + 3581264 * 2 ^ 59
def prefixEnd_3581264 : Nat := 4983230072969 + 3 ^ 40 * 3581264 * 2
def baseEnd_3581264 : Nat := 1838909782643381521830073

theorem tailTrace_3581264 : CollatzResearch.WordTrace tailWord_3581264 prefixEnd_3581264 1838909782643381521830073 := by
  unfold tailWord_3581264
  simp only [CollatzResearch.WordTrace]
  refine ⟨65309714448849817020931423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87079619265133089361241897 65309714448849817020931423)
  ·
    refine ⟨97964571673274725531397135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65309714448849817020931423 97964571673274725531397135)
    ·
      refine ⟨146946857509912088297095703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97964571673274725531397135 146946857509912088297095703)
      ·
        refine ⟨220420286264868132445643555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146946857509912088297095703 220420286264868132445643555)
        ·
          refine ⟨330630429397302198668465333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220420286264868132445643555 330630429397302198668465333)
          ·
            refine ⟨30996602755997081125168625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 330630429397302198668465333 30996602755997081125168625)
            ·
              refine ⟨23247452066997810843876469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30996602755997081125168625 23247452066997810843876469)
              ·
                refine ⟨2179448631281044766613419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23247452066997810843876469 2179448631281044766613419)
                ·
                  refine ⟨3269172946921567149920129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2179448631281044766613419 3269172946921567149920129)
                  ·
                    refine ⟨2451879710191175362440097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3269172946921567149920129 2451879710191175362440097)
                    ·
                      refine ⟨1838909782643381521830073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2451879710191175362440097 1838909782643381521830073)
                      ·
                        rfl

theorem cell23_3581264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 1, 2, 2].length) (baseStart_3581264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581264 prefixEnd_3581264 := by exact prefixLift 3581264
  have htrace : WordTrace (prefixWord ++ tailWord_3581264) baseStart_3581264 baseEnd_3581264 := by
    simpa [prefixWord, tailWord_3581264, baseEnd_3581264] using wordTrace_append hprefix tailTrace_3581264
  have hstable : (prefixWord ++ tailWord_3581264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581264).length < 2 ^ (prefixWord ++ tailWord_3581264).sum := by decide
  have hdescent : baseEnd_3581264 < baseStart_3581264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581267 : List Nat := [1, 1, 1, 2, 1, 1, 9, 1, 1, 2, 3]
def baseStart_3581267 : Nat := 118140960795 + 3581267 * 2 ^ 59
def prefixEnd_3581267 : Nat := 4983230072969 + 3 ^ 40 * 3581267 * 2
def baseEnd_3581267 : Nat := 1838911323085345010092559

theorem tailTrace_3581267 : CollatzResearch.WordTrace tailWord_3581267 prefixEnd_3581267 1838911323085345010092559 := by
  unfold tailWord_3581267
  simp only [CollatzResearch.WordTrace]
  refine ⟨130619538316688765554222055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87079692211125843702814703 130619538316688765554222055)
  ·
    refine ⟨195929307475033148331333083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130619538316688765554222055 195929307475033148331333083)
    ·
      refine ⟨293893961212549722496999625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195929307475033148331333083 293893961212549722496999625)
      ·
        refine ⟨220420470909412291872749719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293893961212549722496999625 220420470909412291872749719)
        ·
          refine ⟨330630706364118437809124579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220420470909412291872749719 330630706364118437809124579)
          ·
            refine ⟨495946059546177656713686869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330630706364118437809124579 495946059546177656713686869)
            ·
              refine ⟨2905933942653384707306759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 495946059546177656713686869 2905933942653384707306759)
              ·
                refine ⟨4358900913980077060960139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2905933942653384707306759 4358900913980077060960139)
                ·
                  refine ⟨6538351370970115591440209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4358900913980077060960139 6538351370970115591440209)
                  ·
                    refine ⟨4903763528227586693580157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6538351370970115591440209 4903763528227586693580157)
                    ·
                      refine ⟨1838911323085345010092559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4903763528227586693580157 1838911323085345010092559)
                      ·
                        rfl

theorem cell23_3581267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 1, 2, 3].length) (baseStart_3581267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581267 prefixEnd_3581267 := by exact prefixLift 3581267
  have htrace : WordTrace (prefixWord ++ tailWord_3581267) baseStart_3581267 baseEnd_3581267 := by
    simpa [prefixWord, tailWord_3581267, baseEnd_3581267] using wordTrace_append hprefix tailTrace_3581267
  have hstable : (prefixWord ++ tailWord_3581267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581267).length < 2 ^ (prefixWord ++ tailWord_3581267).sum := by decide
  have hdescent : baseEnd_3581267 < baseStart_3581267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581283 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 2, 7]
def baseStart_3581283 : Nat := 118140960795 + 3581283 * 2 ^ 59
def prefixEnd_3581283 : Nat := 4983230072969 + 3 ^ 40 * 3581283 * 2
def baseEnd_3581283 : Nat := 612973179591938982497495

theorem tailTrace_3581283 : CollatzResearch.WordTrace tailWord_3581283 prefixEnd_3581283 612973179591938982497495 := by
  unfold tailWord_3581283
  simp only [CollatzResearch.WordTrace]
  refine ⟨130620121884630800286804503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87080081256420533524536335 130620121884630800286804503)
  ·
    refine ⟨195930182826946200430206755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130620121884630800286804503 195930182826946200430206755)
    ·
      refine ⟨293895274240419300645310133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195930182826946200430206755 293895274240419300645310133)
      ·
        refine ⟨27552681960039309435497825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 293895274240419300645310133 27552681960039309435497825)
        ·
          refine ⟨20664511470029482076623369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27552681960039309435497825 20664511470029482076623369)
          ·
            refine ⟨15498383602522111557467527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20664511470029482076623369 15498383602522111557467527)
            ·
              refine ⟨23247575403783167336201291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15498383602522111557467527 23247575403783167336201291)
              ·
                refine ⟨34871363105674751004301937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23247575403783167336201291 34871363105674751004301937)
                ·
                  refine ⟨26153522329256063253226453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34871363105674751004301937 26153522329256063253226453)
                  ·
                    refine ⟨612973179591938982497495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26153522329256063253226453 612973179591938982497495)
                    ·
                      rfl

theorem cell23_3581283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 7].length) (baseStart_3581283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581283 prefixEnd_3581283 := by exact prefixLift 3581283
  have htrace : WordTrace (prefixWord ++ tailWord_3581283) baseStart_3581283 baseEnd_3581283 := by
    simpa [prefixWord, tailWord_3581283, baseEnd_3581283] using wordTrace_append hprefix tailTrace_3581283
  have hstable : (prefixWord ++ tailWord_3581283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581283).length < 2 ^ (prefixWord ++ tailWord_3581283).sum := by decide
  have hdescent : baseEnd_3581283 < baseStart_3581283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581287 : List Nat := [1, 1, 5, 1, 5, 1, 1, 8]
def baseStart_3581287 : Nat := 118140960795 + 3581287 * 2 ^ 59
def prefixEnd_3581287 : Nat := 4983230072969 + 3 ^ 40 * 3581287 * 2
def baseEnd_3581287 : Nat := 68108207136979071549721

theorem tailTrace_3581287 : CollatzResearch.WordTrace tailWord_3581287 prefixEnd_3581287 68108207136979071549721 := by
  unfold tailWord_3581287
  simp only [CollatzResearch.WordTrace]
  refine ⟨130620267776616308969950115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87080178517744205979966743 130620267776616308969950115)
  ·
    refine ⟨195930401664924463454925173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130620267776616308969950115 195930401664924463454925173)
    ·
      refine ⟨18368475156086668448899235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195930401664924463454925173 18368475156086668448899235)
      ·
        refine ⟨27552712734130002673348853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18368475156086668448899235 27552712734130002673348853)
        ·
          refine ⟨2583066818824687750626455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27552712734130002673348853 2583066818824687750626455)
          ·
            refine ⟨3874600228237031625939683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2583066818824687750626455 3874600228237031625939683)
            ·
              refine ⟨5811900342355547438909525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3874600228237031625939683 5811900342355547438909525)
              ·
                refine ⟨68108207136979071549721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5811900342355547438909525 68108207136979071549721)
                ·
                  rfl

theorem cell23_3581287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 8].length) (baseStart_3581287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581287 prefixEnd_3581287 := by exact prefixLift 3581287
  have htrace : WordTrace (prefixWord ++ tailWord_3581287) baseStart_3581287 baseEnd_3581287 := by
    simpa [prefixWord, tailWord_3581287, baseEnd_3581287] using wordTrace_append hprefix tailTrace_3581287
  have hstable : (prefixWord ++ tailWord_3581287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581287).length < 2 ^ (prefixWord ++ tailWord_3581287).sum := by decide
  have hdescent : baseEnd_3581287 < baseStart_3581287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581294 : List Nat := [4, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_3581294 : Nat := 118140960795 + 3581294 * 2 ^ 59
def prefixEnd_3581294 : Nat := 4983230072969 + 3 ^ 40 * 3581294 * 2
def baseEnd_3581294 : Nat := 1838925187063016404454935

theorem tailTrace_3581294 : CollatzResearch.WordTrace tailWord_3581294 prefixEnd_3581294 1838925187063016404454935 := by
  unfold tailWord_3581294
  simp only [CollatzResearch.WordTrace]
  refine ⟨16327565385948868645681867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87080348725060632776969957 16327565385948868645681867)
  ·
    refine ⟨24491348078923302968522801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16327565385948868645681867 24491348078923302968522801)
    ·
      refine ⟨18368511059192477226392101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24491348078923302968522801 18368511059192477226392101)
      ·
        refine ⟨3444095823598589479948519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18368511059192477226392101 3444095823598589479948519)
        ·
          refine ⟨5166143735397884219922779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3444095823598589479948519 5166143735397884219922779)
          ·
            refine ⟨7749215603096826329884169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5166143735397884219922779 7749215603096826329884169)
            ·
              refine ⟨5811911702322619747413127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7749215603096826329884169 5811911702322619747413127)
              ·
                refine ⟨8717867553483929621119691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5811911702322619747413127 8717867553483929621119691)
                ·
                  refine ⟨13076801330225894431679537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8717867553483929621119691 13076801330225894431679537)
                  ·
                    refine ⟨9807600997669420823759653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13076801330225894431679537 9807600997669420823759653)
                    ·
                      refine ⟨1838925187063016404454935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9807600997669420823759653 1838925187063016404454935)
                      ·
                        rfl

theorem cell23_3581294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_3581294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581294 prefixEnd_3581294 := by exact prefixLift 3581294
  have htrace : WordTrace (prefixWord ++ tailWord_3581294) baseStart_3581294 baseEnd_3581294 := by
    simpa [prefixWord, tailWord_3581294, baseEnd_3581294] using wordTrace_append hprefix tailTrace_3581294
  have hstable : (prefixWord ++ tailWord_3581294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581294).length < 2 ^ (prefixWord ++ tailWord_3581294).sum := by decide
  have hdescent : baseEnd_3581294 < baseStart_3581294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581297 : List Nat := [1, 2, 2, 2, 1, 2, 4, 3, 2, 1, 3]
def baseStart_3581297 : Nat := 118140960795 + 3581297 * 2 ^ 59
def prefixEnd_3581297 : Nat := 4983230072969 + 3 ^ 40 * 3581297 * 2
def baseEnd_3581297 : Nat := 1838926727504979892717421

theorem tailTrace_3581297 : CollatzResearch.WordTrace tailWord_3581297 prefixEnd_3581297 1838926727504979892717421 := by
  unfold tailWord_3581297
  simp only [CollatzResearch.WordTrace]
  refine ⟨130620632506580080677814145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87080421671053387118542763 130620632506580080677814145)
  ·
    refine ⟨97965474379935060508360609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130620632506580080677814145 97965474379935060508360609)
    ·
      refine ⟨73474105784951295381270457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97965474379935060508360609 73474105784951295381270457)
      ·
        refine ⟨55105579338713471535952843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73474105784951295381270457 55105579338713471535952843)
        ·
          refine ⟨82658369008070207303929265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55105579338713471535952843 82658369008070207303929265)
          ·
            refine ⟨61993776756052655477946949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82658369008070207303929265 61993776756052655477946949)
            ·
              refine ⟨11623833141759872902115053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61993776756052655477946949 11623833141759872902115053)
              ·
                refine ⟨4358937428159952338293145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11623833141759872902115053 4358937428159952338293145)
                ·
                  refine ⟨3269203071119964253719859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4358937428159952338293145 3269203071119964253719859)
                  ·
                    refine ⟨4903804606679946380579789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3269203071119964253719859 4903804606679946380579789)
                    ·
                      refine ⟨1838926727504979892717421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4903804606679946380579789 1838926727504979892717421)
                      ·
                        rfl

theorem cell23_3581297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_3581297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581297 prefixEnd_3581297 := by exact prefixLift 3581297
  have htrace : WordTrace (prefixWord ++ tailWord_3581297) baseStart_3581297 baseEnd_3581297 := by
    simpa [prefixWord, tailWord_3581297, baseEnd_3581297] using wordTrace_append hprefix tailTrace_3581297
  have hstable : (prefixWord ++ tailWord_3581297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581297).length < 2 ^ (prefixWord ++ tailWord_3581297).sum := by decide
  have hdescent : baseEnd_3581297 < baseStart_3581297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581303 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 4]
def baseStart_3581303 : Nat := 118140960795 + 3581303 * 2 ^ 59
def prefixEnd_3581303 : Nat := 4983230072969 + 3 ^ 40 * 3581303 * 2
def baseEnd_3581303 : Nat := 1838929808388906869242393

theorem tailTrace_3581303 : CollatzResearch.WordTrace tailWord_3581303 prefixEnd_3581303 1838929808388906869242393 := by
  unfold tailWord_3581303
  simp only [CollatzResearch.WordTrace]
  refine ⟨130620851344558343702532563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87080567563038895801688375 130620851344558343702532563)
  ·
    refine ⟨195931277016837515553798845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130620851344558343702532563 195931277016837515553798845)
    ·
      refine ⟨73474228881314068332674567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195931277016837515553798845 73474228881314068332674567)
      ·
        refine ⟨110211343321971102499011851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73474228881314068332674567 110211343321971102499011851)
        ·
          refine ⟨165317014982956653748517777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110211343321971102499011851 165317014982956653748517777)
          ·
            refine ⟨123987761237217490311388333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165317014982956653748517777 123987761237217490311388333)
            ·
              refine ⟨46495410463956558866770625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123987761237217490311388333 46495410463956558866770625)
              ·
                refine ⟨34871557847967419150077969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46495410463956558866770625 34871557847967419150077969)
                ·
                  refine ⟨26153668385975564362558477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34871557847967419150077969 26153668385975564362558477)
                  ·
                    refine ⟨9807625644740836635959429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26153668385975564362558477 9807625644740836635959429)
                    ·
                      refine ⟨1838929808388906869242393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9807625644740836635959429 1838929808388906869242393)
                      ·
                        rfl

theorem cell23_3581303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_3581303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581303 prefixEnd_3581303 := by exact prefixLift 3581303
  have htrace : WordTrace (prefixWord ++ tailWord_3581303) baseStart_3581303 baseEnd_3581303 := by
    simpa [prefixWord, tailWord_3581303, baseEnd_3581303] using wordTrace_append hprefix tailTrace_3581303
  have hstable : (prefixWord ++ tailWord_3581303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581303).length < 2 ^ (prefixWord ++ tailWord_3581303).sum := by decide
  have hdescent : baseEnd_3581303 < baseStart_3581303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581307 : List Nat := [1, 1, 1, 1, 1, 6, 2, 4, 1, 3, 2]
def baseStart_3581307 : Nat := 118140960795 + 3581307 * 2 ^ 59
def prefixEnd_3581307 : Nat := 4983230072969 + 3 ^ 40 * 3581307 * 2
def baseEnd_3581307 : Nat := 1838931862311524853592375

theorem tailTrace_3581307 : CollatzResearch.WordTrace tailWord_3581307 prefixEnd_3581307 1838931862311524853592375 := by
  unfold tailWord_3581307
  simp only [CollatzResearch.WordTrace]
  refine ⟨130620997236543852385678175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87080664824362568257118783 130620997236543852385678175)
  ·
    refine ⟨195931495854815778578517263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130620997236543852385678175 195931495854815778578517263)
    ·
      refine ⟨293897243782223667867775895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195931495854815778578517263 293897243782223667867775895)
      ·
        refine ⟨440845865673335501801663843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293897243782223667867775895 440845865673335501801663843)
        ·
          refine ⟨661268798510003252702495765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440845865673335501801663843 661268798510003252702495765)
          ·
            refine ⟨30996974930156402470429489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 661268798510003252702495765 30996974930156402470429489)
            ·
              refine ⟨23247731197617301852822117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30996974930156402470429489 23247731197617301852822117)
              ·
                refine ⟨4358949599553244097404147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23247731197617301852822117 4358949599553244097404147)
                ·
                  refine ⟨6538424399329866146106221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4358949599553244097404147 6538424399329866146106221)
                  ·
                    refine ⟨2451909149748699804789833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6538424399329866146106221 2451909149748699804789833)
                    ·
                      refine ⟨1838931862311524853592375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2451909149748699804789833 1838931862311524853592375)
                      ·
                        rfl

theorem cell23_3581307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 3, 2].length) (baseStart_3581307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581307 prefixEnd_3581307 := by exact prefixLift 3581307
  have htrace : WordTrace (prefixWord ++ tailWord_3581307) baseStart_3581307 baseEnd_3581307 := by
    simpa [prefixWord, tailWord_3581307, baseEnd_3581307] using wordTrace_append hprefix tailTrace_3581307
  have hstable : (prefixWord ++ tailWord_3581307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581307).length < 2 ^ (prefixWord ++ tailWord_3581307).sum := by decide
  have hdescent : baseEnd_3581307 < baseStart_3581307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581314 : List Nat := [3, 4, 2, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_3581314 : Nat := 118140960795 + 3581314 * 2 ^ 59
def prefixEnd_3581314 : Nat := 4983230072969 + 3 ^ 40 * 3581314 * 2
def baseEnd_3581314 : Nat := 1838935456676106326204843

theorem tailTrace_3581314 : CollatzResearch.WordTrace tailWord_3581314 prefixEnd_3581314 1838935456676106326204843 := by
  unfold tailWord_3581314
  simp only [CollatzResearch.WordTrace]
  refine ⟨32655313136879623145295749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87080835031678995054121997 32655313136879623145295749)
  ·
    refine ⟨6122871213164929339742953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32655313136879623145295749 6122871213164929339742953)
    ·
      refine ⟨4592153409873697004807215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6122871213164929339742953 4592153409873697004807215)
      ·
        refine ⟨6888230114810545507210823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4592153409873697004807215 6888230114810545507210823)
        ·
          refine ⟨10332345172215818260816235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6888230114810545507210823 10332345172215818260816235)
          ·
            refine ⟨15498517758323727391224353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10332345172215818260816235 15498517758323727391224353)
            ·
              refine ⟨11623888318742795543418265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15498517758323727391224353 11623888318742795543418265)
              ·
                refine ⟨8717916239057096657563699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11623888318742795543418265 8717916239057096657563699)
                ·
                  refine ⟨13076874358585644986345549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8717916239057096657563699 13076874358585644986345549)
                  ·
                    refine ⟨4903827884469616869879581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13076874358585644986345549 4903827884469616869879581)
                    ·
                      refine ⟨1838935456676106326204843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4903827884469616869879581 1838935456676106326204843)
                      ·
                        rfl

theorem cell23_3581314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_3581314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581314 prefixEnd_3581314 := by exact prefixLift 3581314
  have htrace : WordTrace (prefixWord ++ tailWord_3581314) baseStart_3581314 baseEnd_3581314 := by
    simpa [prefixWord, tailWord_3581314, baseEnd_3581314] using wordTrace_append hprefix tailTrace_3581314
  have hstable : (prefixWord ++ tailWord_3581314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581314).length < 2 ^ (prefixWord ++ tailWord_3581314).sum := by decide
  have hdescent : baseEnd_3581314 < baseStart_3581314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581323 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 5]
def baseStart_3581323 : Nat := 118140960795 + 3581323 * 2 ^ 59
def prefixEnd_3581323 : Nat := 4983230072969 + 3 ^ 40 * 3581323 * 2
def baseEnd_3581323 : Nat := 1838940078001996790992301

theorem tailTrace_3581323 : CollatzResearch.WordTrace tailWord_3581323 prefixEnd_3581323 1838940078001996790992301 := by
  unfold tailWord_3581323
  simp only [CollatzResearch.WordTrace]
  refine ⟨130621580804485887118260623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87081053869657258078840415 130621580804485887118260623)
  ·
    refine ⟨195932371206728830677390935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130621580804485887118260623 195932371206728830677390935)
    ·
      refine ⟨293898556810093246016086403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195932371206728830677390935 293898556810093246016086403)
      ·
        refine ⟨440847835215139869024129605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293898556810093246016086403 440847835215139869024129605)
        ·
          refine ⟨82658969102838725442024301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 440847835215139869024129605 82658969102838725442024301)
          ·
            refine ⟨30997113413564522040759113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82658969102838725442024301 30997113413564522040759113)
            ·
              refine ⟨23247835060173391530569335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30997113413564522040759113 23247835060173391530569335)
              ·
                refine ⟨34871752590260087295854003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23247835060173391530569335 34871752590260087295854003)
                ·
                  refine ⟨52307628885390130943781005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34871752590260087295854003 52307628885390130943781005)
                  ·
                    refine ⟨19615360832021299103917877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52307628885390130943781005 19615360832021299103917877)
                    ·
                      refine ⟨1838940078001996790992301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19615360832021299103917877 1838940078001996790992301)
                      ·
                        rfl

theorem cell23_3581323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 5].length) (baseStart_3581323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581323 prefixEnd_3581323 := by exact prefixLift 3581323
  have htrace : WordTrace (prefixWord ++ tailWord_3581323) baseStart_3581323 baseEnd_3581323 := by
    simpa [prefixWord, tailWord_3581323, baseEnd_3581323] using wordTrace_append hprefix tailTrace_3581323
  have hstable : (prefixWord ++ tailWord_3581323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581323).length < 2 ^ (prefixWord ++ tailWord_3581323).sum := by decide
  have hdescent : baseEnd_3581323 < baseStart_3581323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581390 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 4, 5]
def baseStart_3581390 : Nat := 118140960795 + 3581390 * 2 ^ 59
def prefixEnd_3581390 : Nat := 4983230072969 + 3 ^ 40 * 3581390 * 2
def baseEnd_3581390 : Nat := 612991493735282676284831

theorem tailTrace_3581390 : CollatzResearch.WordTrace tailWord_3581390 prefixEnd_3581390 612991493735282676284831 := by
  unfold tailWord_3581390
  simp only [CollatzResearch.WordTrace]
  refine ⟨16328003061905394695118703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87082682996828771707299749 16328003061905394695118703)
  ·
    refine ⟨24492004592858092042678055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16328003061905394695118703 24492004592858092042678055)
    ·
      refine ⟨36738006889287138064017083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24492004592858092042678055 36738006889287138064017083)
      ·
        refine ⟨55107010333930707096025625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36738006889287138064017083 55107010333930707096025625)
        ·
          refine ⟨41330257750448030322019219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55107010333930707096025625 41330257750448030322019219)
          ·
            refine ⟨61995386625672045483028829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41330257750448030322019219 61995386625672045483028829)
            ·
              refine ⟨23248269984627017056135811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61995386625672045483028829 23248269984627017056135811)
              ·
                refine ⟨34872404976940525584203717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23248269984627017056135811 34872404976940525584203717)
                ·
                  refine ⟨6538575933176348547038197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34872404976940525584203717 6538575933176348547038197)
                  ·
                    refine ⟨612991493735282676284831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6538575933176348547038197 612991493735282676284831)
                    ·
                      rfl

theorem cell23_3581390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_3581390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581390 prefixEnd_3581390 := by exact prefixLift 3581390
  have htrace : WordTrace (prefixWord ++ tailWord_3581390) baseStart_3581390 baseEnd_3581390 := by
    simpa [prefixWord, tailWord_3581390, baseEnd_3581390] using wordTrace_append hprefix tailTrace_3581390
  have hstable : (prefixWord ++ tailWord_3581390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581390).length < 2 ^ (prefixWord ++ tailWord_3581390).sum := by decide
  have hdescent : baseEnd_3581390 < baseStart_3581390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581393 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 8]
def baseStart_3581393 : Nat := 118140960795 + 3581393 * 2 ^ 59
def prefixEnd_3581393 : Nat := 4983230072969 + 3 ^ 40 * 3581393 * 2
def baseEnd_3581393 : Nat := 1838976021647811517116979

theorem tailTrace_3581393 : CollatzResearch.WordTrace tailWord_3581393 prefixEnd_3581393 1838976021647811517116979 := by
  unfold tailWord_3581393
  simp only [CollatzResearch.WordTrace]
  refine ⟨130624133914232289073308833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87082755942821526048872555 130624133914232289073308833)
  ·
    refine ⟨97968100435674216804981625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130624133914232289073308833 97968100435674216804981625)
    ·
      refine ⟨73476075326755662603736219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97968100435674216804981625 73476075326755662603736219)
      ·
        refine ⟨110214112990133493905604329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73476075326755662603736219 110214112990133493905604329)
        ·
          refine ⟨82660584742600120429203247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110214112990133493905604329 82660584742600120429203247)
          ·
            refine ⟨123990877113900180643804871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82660584742600120429203247 123990877113900180643804871)
            ·
              refine ⟨185986315670850270965707307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123990877113900180643804871 185986315670850270965707307)
              ·
                refine ⟨278979473506275406448560961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185986315670850270965707307 278979473506275406448560961)
                ·
                  refine ⟨209234605129706554836420721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278979473506275406448560961 209234605129706554836420721)
                  ·
                    refine ⟨156925953847279916127315541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 209234605129706554836420721 156925953847279916127315541)
                    ·
                      refine ⟨1838976021647811517116979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 156925953847279916127315541 1838976021647811517116979)
                      ·
                        rfl

theorem cell23_3581393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_3581393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581393 prefixEnd_3581393 := by exact prefixLift 3581393
  have htrace : WordTrace (prefixWord ++ tailWord_3581393) baseStart_3581393 baseEnd_3581393 := by
    simpa [prefixWord, tailWord_3581393, baseEnd_3581393] using wordTrace_append hprefix tailTrace_3581393
  have hstable : (prefixWord ++ tailWord_3581393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581393).length < 2 ^ (prefixWord ++ tailWord_3581393).sum := by decide
  have hdescent : baseEnd_3581393 < baseStart_3581393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581397 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 2, 5, 2]
def baseStart_3581397 : Nat := 118140960795 + 3581397 * 2 ^ 59
def prefixEnd_3581397 : Nat := 4983230072969 + 3 ^ 40 * 3581397 * 2
def baseEnd_3581397 : Nat := 1838978075570429501466961

theorem tailTrace_3581397 : CollatzResearch.WordTrace tailWord_3581397 prefixEnd_3581397 1838978075570429501466961 := by
  unfold tailWord_3581397
  simp only [CollatzResearch.WordTrace]
  refine ⟨130624279806217797756454445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87082853204145198504302963 130624279806217797756454445)
  ·
    refine ⟨48984104927331674158670417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130624279806217797756454445 48984104927331674158670417)
    ·
      refine ⟨36738078695498755619002813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48984104927331674158670417 36738078695498755619002813)
      ·
        refine ⟨13776779510812033357126055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36738078695498755619002813 13776779510812033357126055)
        ·
          refine ⟨20665169266218050035689083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13776779510812033357126055 20665169266218050035689083)
          ·
            refine ⟨30997753899327075053533625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20665169266218050035689083 30997753899327075053533625)
            ·
              refine ⟨23248315424495306290150219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30997753899327075053533625 23248315424495306290150219)
              ·
                refine ⟨34872473136742959435225329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23248315424495306290150219 34872473136742959435225329)
                ·
                  refine ⟨26154354852557219576418997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34872473136742959435225329 26154354852557219576418997)
                  ·
                    refine ⟨2451970767427239335289281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26154354852557219576418997 2451970767427239335289281)
                    ·
                      refine ⟨1838978075570429501466961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2451970767427239335289281 1838978075570429501466961)
                      ·
                        rfl

theorem cell23_3581397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_3581397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581397 prefixEnd_3581397 := by exact prefixLift 3581397
  have htrace : WordTrace (prefixWord ++ tailWord_3581397) baseStart_3581397 baseEnd_3581397 := by
    simpa [prefixWord, tailWord_3581397, baseEnd_3581397] using wordTrace_append hprefix tailTrace_3581397
  have hstable : (prefixWord ++ tailWord_3581397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581397).length < 2 ^ (prefixWord ++ tailWord_3581397).sum := by decide
  have hdescent : baseEnd_3581397 < baseStart_3581397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581490 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_3581490 : Nat := 118140960795 + 3581490 * 2 ^ 59
def prefixEnd_3581490 : Nat := 4983230072969 + 3 ^ 40 * 3581490 * 2
def baseEnd_3581490 : Nat := 1839025829271297637604033

theorem tailTrace_3581490 : CollatzResearch.WordTrace tailWord_3581490 prefixEnd_3581490 1839025829271297637604033 := by
  unfold tailWord_3581490
  simp only [CollatzResearch.WordTrace]
  refine ⟨32656917948720218659897481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87085114529920583093059949 32656917948720218659897481)
  ·
    refine ⟨24492688461540163994923111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32656917948720218659897481 24492688461540163994923111)
    ·
      refine ⟨36739032692310245992384667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24492688461540163994923111 36739032692310245992384667)
      ·
        refine ⟨55108549038465368988577001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36739032692310245992384667 55108549038465368988577001)
        ·
          refine ⟨41331411778849026741432751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55108549038465368988577001 41331411778849026741432751)
          ·
            refine ⟨61997117668273540112149127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41331411778849026741432751 61997117668273540112149127)
            ·
              refine ⟨92995676502410310168223691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61997117668273540112149127 92995676502410310168223691)
              ·
                refine ⟨139493514753615465252335537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92995676502410310168223691 139493514753615465252335537)
                ·
                  refine ⟨104620136065211598939251653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139493514753615465252335537 104620136065211598939251653)
                  ·
                    refine ⟨19616275512227174801109685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104620136065211598939251653 19616275512227174801109685)
                    ·
                      refine ⟨1839025829271297637604033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19616275512227174801109685 1839025829271297637604033)
                      ·
                        rfl

theorem cell23_3581490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_3581490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581490 prefixEnd_3581490 := by exact prefixLift 3581490
  have htrace : WordTrace (prefixWord ++ tailWord_3581490) baseStart_3581490 baseEnd_3581490 := by
    simpa [prefixWord, tailWord_3581490, baseEnd_3581490] using wordTrace_append hprefix tailTrace_3581490
  have hstable : (prefixWord ++ tailWord_3581490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581490).length < 2 ^ (prefixWord ++ tailWord_3581490).sum := by decide
  have hdescent : baseEnd_3581490 < baseStart_3581490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581501 : List Nat := [1, 4, 1, 3, 4, 1, 1, 2, 6]
def baseStart_3581501 : Nat := 118140960795 + 3581501 * 2 ^ 59
def prefixEnd_3581501 : Nat := 4983230072969 + 3 ^ 40 * 3581501 * 2
def baseEnd_3581501 : Nat := 204336830839833010507387

theorem tailTrace_3581501 : CollatzResearch.WordTrace tailWord_3581501 prefixEnd_3581501 204336830839833010507387 := by
  unfold tailWord_3581501
  simp only [CollatzResearch.WordTrace]
  refine ⟨130628072997841023518240357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87085381998560682345493571 130628072997841023518240357)
  ·
    refine ⟨24492763687095191909670067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130628072997841023518240357 24492763687095191909670067)
    ·
      refine ⟨36739145530642787864505101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24492763687095191909670067 36739145530642787864505101)
      ·
        refine ⟨13777179573991045449189413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36739145530642787864505101 13777179573991045449189413)
        ·
          refine ⟨2583221170123321021723015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13777179573991045449189413 2583221170123321021723015)
          ·
            refine ⟨3874831755184981532584523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2583221170123321021723015 3874831755184981532584523)
            ·
              refine ⟨5812247632777472298876785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3874831755184981532584523 5812247632777472298876785)
              ·
                refine ⟨4359185724583104224157589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5812247632777472298876785 4359185724583104224157589)
                ·
                  refine ⟨204336830839833010507387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4359185724583104224157589 204336830839833010507387)
                  ·
                    rfl

theorem cell23_3581501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_3581501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581501 prefixEnd_3581501 := by exact prefixLift 3581501
  have htrace : WordTrace (prefixWord ++ tailWord_3581501) baseStart_3581501 baseEnd_3581501 := by
    simpa [prefixWord, tailWord_3581501, baseEnd_3581501] using wordTrace_append hprefix tailTrace_3581501
  have hstable : (prefixWord ++ tailWord_3581501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581501).length < 2 ^ (prefixWord ++ tailWord_3581501).sum := by decide
  have hdescent : baseEnd_3581501 < baseStart_3581501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581511 : List Nat := [1, 1, 4, 1, 5, 1, 2, 1, 3, 1, 3]
def baseStart_3581511 : Nat := 118140960795 + 3581511 * 2 ^ 59
def prefixEnd_3581511 : Nat := 4983230072969 + 3 ^ 40 * 3581511 * 2
def baseEnd_3581511 : Nat := 1839036612365042055441437

theorem tailTrace_3581511 : CollatzResearch.WordTrace tailWord_3581511 prefixEnd_3581511 1839036612365042055441437 := by
  unfold tailWord_3581511
  simp only [CollatzResearch.WordTrace]
  refine ⟨130628437727804795226104387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87085625151869863484069591 130628437727804795226104387)
  ·
    refine ⟨195942656591707192839156581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130628437727804795226104387 195942656591707192839156581)
    ·
      refine ⟨36739248110945098657341859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195942656591707192839156581 36739248110945098657341859)
      ·
        refine ⟨55108872166417647986012789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36739248110945098657341859 55108872166417647986012789)
        ·
          refine ⟨5166456765601654498688699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55108872166417647986012789 5166456765601654498688699)
          ·
            refine ⟨7749685148402481748033049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5166456765601654498688699 7749685148402481748033049)
            ·
              refine ⟨5812263861301861311024787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7749685148402481748033049 5812263861301861311024787)
              ·
                refine ⟨8718395791952791966537181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5812263861301861311024787 8718395791952791966537181)
                ·
                  refine ⟨3269398421982296987451443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8718395791952791966537181 3269398421982296987451443)
                  ·
                    refine ⟨4904097632973445481177165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3269398421982296987451443 4904097632973445481177165)
                    ·
                      refine ⟨1839036612365042055441437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4904097632973445481177165 1839036612365042055441437)
                      ·
                        rfl

theorem cell23_3581511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_3581511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581511 prefixEnd_3581511 := by exact prefixLift 3581511
  have htrace : WordTrace (prefixWord ++ tailWord_3581511) baseStart_3581511 baseEnd_3581511 := by
    simpa [prefixWord, tailWord_3581511, baseEnd_3581511] using wordTrace_append hprefix tailTrace_3581511
  have hstable : (prefixWord ++ tailWord_3581511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581511).length < 2 ^ (prefixWord ++ tailWord_3581511).sum := by decide
  have hdescent : baseEnd_3581511 < baseStart_3581511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581527 : List Nat := [1, 1, 3, 2, 2, 3, 3, 1, 1, 6]
def baseStart_3581527 : Nat := 118140960795 + 3581527 * 2 ^ 59
def prefixEnd_3581527 : Nat := 4983230072969 + 3 ^ 40 * 3581527 * 2
def baseEnd_3581527 : Nat := 613014942685171330947121

theorem tailTrace_3581527 : CollatzResearch.WordTrace tailWord_3581527 prefixEnd_3581527 613014942685171330947121 := by
  unfold tailWord_3581527
  simp only [CollatzResearch.WordTrace]
  refine ⟨130629021295746829958686835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87086014197164553305791223 130629021295746829958686835)
  ·
    refine ⟨195943531943620244938030253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130629021295746829958686835 195943531943620244938030253)
    ·
      refine ⟨73478824478857591851761345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195943531943620244938030253 73478824478857591851761345)
      ·
        refine ⟨55109118359143193888821009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73478824478857591851761345 55109118359143193888821009)
        ·
          refine ⟨41331838769357395416615757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55109118359143193888821009 41331838769357395416615757)
          ·
            refine ⟨15499439538509023281230909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41331838769357395416615757 15499439538509023281230909)
            ·
              refine ⟨5812289826940883730461591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15499439538509023281230909 5812289826940883730461591)
              ·
                refine ⟨8718434740411325595692387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5812289826940883730461591 8718434740411325595692387)
                ·
                  refine ⟨13077652110616988393538581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8718434740411325595692387 13077652110616988393538581)
                  ·
                    refine ⟨613014942685171330947121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13077652110616988393538581 613014942685171330947121)
                    ·
                      rfl

theorem cell23_3581527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_3581527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581527 prefixEnd_3581527 := by exact prefixLift 3581527
  have htrace : WordTrace (prefixWord ++ tailWord_3581527) baseStart_3581527 baseEnd_3581527 := by
    simpa [prefixWord, tailWord_3581527, baseEnd_3581527] using wordTrace_append hprefix tailTrace_3581527
  have hstable : (prefixWord ++ tailWord_3581527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581527).length < 2 ^ (prefixWord ++ tailWord_3581527).sum := by decide
  have hdescent : baseEnd_3581527 < baseStart_3581527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581544 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 4, 4]
def baseStart_3581544 : Nat := 118140960795 + 3581544 * 2 ^ 59
def prefixEnd_3581544 : Nat := 4983230072969 + 3 ^ 40 * 3581544 * 2
def baseEnd_3581544 : Nat := 613017852408880142109595

theorem tailTrace_3581544 : CollatzResearch.WordTrace tailWord_3581544 prefixEnd_3581544 613017852408880142109595 := by
  unfold tailWord_3581544
  simp only [CollatzResearch.WordTrace]
  refine ⟨65314820668342620931027843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87086427557790161241370457 65314820668342620931027843)
  ·
    refine ⟨97972231002513931396541765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65314820668342620931027843 97972231002513931396541765)
    ·
      refine ⟨18369793312971362136851581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97972231002513931396541765 18369793312971362136851581)
      ·
        refine ⟨6888672492364260801319343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18369793312971362136851581 6888672492364260801319343)
        ·
          refine ⟨10333008738546391201979015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6888672492364260801319343 10333008738546391201979015)
          ·
            refine ⟨15499513107819586802968523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10333008738546391201979015 15499513107819586802968523)
            ·
              refine ⟨23249269661729380204452785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15499513107819586802968523 23249269661729380204452785)
              ·
                refine ⟨17436952246297035153339589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23249269661729380204452785 17436952246297035153339589)
                ·
                  refine ⟨3269428546180694091251173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17436952246297035153339589 3269428546180694091251173)
                  ·
                    refine ⟨613017852408880142109595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3269428546180694091251173 613017852408880142109595)
                    ·
                      rfl

theorem cell23_3581544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_3581544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581544 prefixEnd_3581544 := by exact prefixLift 3581544
  have htrace : WordTrace (prefixWord ++ tailWord_3581544) baseStart_3581544 baseEnd_3581544 := by
    simpa [prefixWord, tailWord_3581544, baseEnd_3581544] using wordTrace_append hprefix tailTrace_3581544
  have hstable : (prefixWord ++ tailWord_3581544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581544).length < 2 ^ (prefixWord ++ tailWord_3581544).sum := by decide
  have hdescent : baseEnd_3581544 < baseStart_3581544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581554 : List Nat := [3, 2, 1, 2, 3, 2, 2, 1, 1, 1, 5]
def baseStart_3581554 : Nat := 118140960795 + 3581554 * 2 ^ 59
def prefixEnd_3581554 : Nat := 4983230072969 + 3 ^ 40 * 3581554 * 2
def baseEnd_3581554 : Nat := 1839058692033185387203739

theorem tailTrace_3581554 : CollatzResearch.WordTrace tailWord_3581554 prefixEnd_3581554 1839058692033185387203739 := by
  unfold tailWord_3581554
  simp only [CollatzResearch.WordTrace]
  refine ⟨32657501516662253392479929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87086670711099342379946477 32657501516662253392479929)
  ·
    refine ⟨24493126137496690044359947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32657501516662253392479929 24493126137496690044359947)
    ·
      refine ⟨36739689206245035066539921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24493126137496690044359947 36739689206245035066539921)
      ·
        refine ⟨27554766904683776299904941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36739689206245035066539921 27554766904683776299904941)
        ·
          refine ⟨10333037589256416112464353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27554766904683776299904941 10333037589256416112464353)
          ·
            refine ⟨7749778191942312084348265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10333037589256416112464353 7749778191942312084348265)
            ·
              refine ⟨5812333643956734063261199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7749778191942312084348265 5812333643956734063261199)
              ·
                refine ⟨8718500465935101094891799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5812333643956734063261199 8718500465935101094891799)
                ·
                  refine ⟨13077750698902651642337699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8718500465935101094891799 13077750698902651642337699)
                  ·
                    refine ⟨19616626048353977463506549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13077750698902651642337699 19616626048353977463506549)
                    ·
                      refine ⟨1839058692033185387203739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19616626048353977463506549 1839058692033185387203739)
                      ·
                        rfl

theorem cell23_3581554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_3581554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581554 prefixEnd_3581554 := by exact prefixLift 3581554
  have htrace : WordTrace (prefixWord ++ tailWord_3581554) baseStart_3581554 baseEnd_3581554 := by
    simpa [prefixWord, tailWord_3581554, baseEnd_3581554] using wordTrace_append hprefix tailTrace_3581554
  have hstable : (prefixWord ++ tailWord_3581554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581554).length < 2 ^ (prefixWord ++ tailWord_3581554).sum := by decide
  have hdescent : baseEnd_3581554 < baseStart_3581554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581557 : List Nat := [1, 3, 4, 2, 1, 1, 11]
def baseStart_3581557 : Nat := 118140960795 + 3581557 * 2 ^ 59
def prefixEnd_3581557 : Nat := 4983230072969 + 3 ^ 40 * 3581557 * 2
def baseEnd_3581557 : Nat := 22704447314508010808225

theorem tailTrace_3581557 : CollatzResearch.WordTrace tailWord_3581557 prefixEnd_3581557 22704447314508010808225 := by
  unfold tailWord_3581557
  simp only [CollatzResearch.WordTrace]
  refine ⟨130630115485638145082278925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87086743657092096721519283 130630115485638145082278925)
  ·
    refine ⟨48986293307114304405854597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130630115485638145082278925 48986293307114304405854597)
    ·
      refine ⟨9184929995083932076097737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48986293307114304405854597 9184929995083932076097737)
      ·
        refine ⟨6888697496312949057073303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9184929995083932076097737 6888697496312949057073303)
        ·
          refine ⟨10333046244469423585609955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6888697496312949057073303 10333046244469423585609955)
          ·
            refine ⟨15499569366704135378414933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10333046244469423585609955 15499569366704135378414933)
            ·
              refine ⟨22704447314508010808225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15499569366704135378414933 22704447314508010808225)
              ·
                rfl

theorem cell23_3581557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 11].length) (baseStart_3581557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581557 prefixEnd_3581557 := by exact prefixLift 3581557
  have htrace : WordTrace (prefixWord ++ tailWord_3581557) baseStart_3581557 baseEnd_3581557 := by
    simpa [prefixWord, tailWord_3581557, baseEnd_3581557] using wordTrace_append hprefix tailTrace_3581557
  have hstable : (prefixWord ++ tailWord_3581557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581557).length < 2 ^ (prefixWord ++ tailWord_3581557).sum := by decide
  have hdescent : baseEnd_3581557 < baseStart_3581557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581560 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 4, 2, 6]
def baseStart_3581560 : Nat := 118140960795 + 3581560 * 2 ^ 59
def prefixEnd_3581560 : Nat := 4983230072969 + 3 ^ 40 * 3581560 * 2
def baseEnd_3581560 : Nat := 1839061772917112363728711

theorem tailTrace_3581560 : CollatzResearch.WordTrace tailWord_3581560 prefixEnd_3581560 1839061772917112363728711 := by
  unfold tailWord_3581560
  simp only [CollatzResearch.WordTrace]
  refine ⟨65315112452313638297319067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87086816603084851063092089 65315112452313638297319067)
  ·
    refine ⟨97972668678470457445978601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65315112452313638297319067 97972668678470457445978601)
    ·
      refine ⟨73479501508852843084483951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97972668678470457445978601 73479501508852843084483951)
      ·
        refine ⟨110219252263279264626725927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73479501508852843084483951 110219252263279264626725927)
        ·
          refine ⟨165328878394918896940088891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110219252263279264626725927 165328878394918896940088891)
          ·
            refine ⟨247993317592378345410133337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165328878394918896940088891 247993317592378345410133337)
            ·
              refine ⟨185994988194283759057600003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247993317592378345410133337 185994988194283759057600003)
              ·
                refine ⟨278992482291425638586400005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185994988194283759057600003 278992482291425638586400005)
                ·
                  refine ⟨52311090429642307234950001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 278992482291425638586400005 52311090429642307234950001)
                  ·
                    refine ⟨39233317822231730426212501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52311090429642307234950001 39233317822231730426212501)
                    ·
                      refine ⟨1839061772917112363728711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39233317822231730426212501 1839061772917112363728711)
                      ·
                        rfl

theorem cell23_3581560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_3581560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581560 prefixEnd_3581560 := by exact prefixLift 3581560
  have htrace : WordTrace (prefixWord ++ tailWord_3581560) baseStart_3581560 baseEnd_3581560 := by
    simpa [prefixWord, tailWord_3581560, baseEnd_3581560] using wordTrace_append hprefix tailTrace_3581560
  have hstable : (prefixWord ++ tailWord_3581560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581560).length < 2 ^ (prefixWord ++ tailWord_3581560).sum := by decide
  have hdescent : baseEnd_3581560 < baseStart_3581560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581578 : List Nat := [3, 1, 2, 3, 2, 3, 2, 1, 2, 4]
def baseStart_3581578 : Nat := 118140960795 + 3581578 * 2 ^ 59
def prefixEnd_3581578 : Nat := 4983230072969 + 3 ^ 40 * 3581578 * 2
def baseEnd_3581578 : Nat := 613023671856297764434543

theorem tailTrace_3581578 : CollatzResearch.WordTrace tailWord_3581578 prefixEnd_3581578 613023671856297764434543 := by
  unfold tailWord_3581578
  simp only [CollatzResearch.WordTrace]
  refine ⟨32657720354640516417198347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87087254279041377112528925 32657720354640516417198347)
  ·
    refine ⟨48986580531960774625797521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32657720354640516417198347 48986580531960774625797521)
    ·
      refine ⟨36739935398970580969348141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48986580531960774625797521 36739935398970580969348141)
      ·
        refine ⟨13777475774613967863505553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36739935398970580969348141 13777475774613967863505553)
        ·
          refine ⟨10333106830960475897629165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13777475774613967863505553 10333106830960475897629165)
          ·
            refine ⟨3874915061610178461610937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10333106830960475897629165 3874915061610178461610937)
            ·
              refine ⟨2906186296207633846208203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3874915061610178461610937 2906186296207633846208203)
              ·
                refine ⟨4359279444311450769312305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2906186296207633846208203 4359279444311450769312305)
                ·
                  refine ⟨3269459583233588076984229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4359279444311450769312305 3269459583233588076984229)
                  ·
                    refine ⟨613023671856297764434543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3269459583233588076984229 613023671856297764434543)
                    ·
                      rfl

theorem cell23_3581578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_3581578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581578 prefixEnd_3581578 := by exact prefixLift 3581578
  have htrace : WordTrace (prefixWord ++ tailWord_3581578) baseStart_3581578 baseEnd_3581578 := by
    simpa [prefixWord, tailWord_3581578, baseEnd_3581578] using wordTrace_append hprefix tailTrace_3581578
  have hstable : (prefixWord ++ tailWord_3581578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581578).length < 2 ^ (prefixWord ++ tailWord_3581578).sum := by decide
  have hdescent : baseEnd_3581578 < baseStart_3581578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581637 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 2, 2, 4]
def baseStart_3581637 : Nat := 118140960795 + 3581637 * 2 ^ 59
def prefixEnd_3581637 : Nat := 4983230072969 + 3 ^ 40 * 3581637 * 2
def baseEnd_3581637 : Nat := 1839101310927508562465857

theorem tailTrace_3581637 : CollatzResearch.WordTrace tailWord_3581637 prefixEnd_3581637 1839101310927508562465857 := by
  unfold tailWord_3581637
  simp only [CollatzResearch.WordTrace]
  refine ⟨130633033325348318745191165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87088688883565545830127443 130633033325348318745191165)
  ·
    refine ⟨48987387497005619529446687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130633033325348318745191165 48987387497005619529446687)
    ·
      refine ⟨73481081245508429294170031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48987387497005619529446687 73481081245508429294170031)
      ·
        refine ⟨110221621868262643941255047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73481081245508429294170031 110221621868262643941255047)
        ·
          refine ⟨165332432802393965911882571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110221621868262643941255047 165332432802393965911882571)
          ·
            refine ⟨247998649203590948867823857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165332432802393965911882571 247998649203590948867823857)
            ·
              refine ⟨185998986902693211650867893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247998649203590948867823857 185998986902693211650867893)
              ·
                refine ⟨17437405022127488592268865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185998986902693211650867893 17437405022127488592268865)
                ·
                  refine ⟨13078053766595616444201649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17437405022127488592268865 13078053766595616444201649)
                  ·
                    refine ⟨9808540324946712333151237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13078053766595616444201649 9808540324946712333151237)
                    ·
                      refine ⟨1839101310927508562465857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9808540324946712333151237 1839101310927508562465857)
                      ·
                        rfl

theorem cell23_3581637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_3581637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581637 prefixEnd_3581637 := by exact prefixLift 3581637
  have htrace : WordTrace (prefixWord ++ tailWord_3581637) baseStart_3581637 baseEnd_3581637 := by
    simpa [prefixWord, tailWord_3581637, baseEnd_3581637] using wordTrace_append hprefix tailTrace_3581637
  have hstable : (prefixWord ++ tailWord_3581637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581637).length < 2 ^ (prefixWord ++ tailWord_3581637).sum := by decide
  have hdescent : baseEnd_3581637 < baseStart_3581637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581664 : List Nat := [2, 1, 1, 3, 1, 2, 3, 5, 5]
def baseStart_3581664 : Nat := 118140960795 + 3581664 * 2 ^ 59
def prefixEnd_3581664 : Nat := 4983230072969 + 3 ^ 40 * 3581664 * 2
def baseEnd_3581664 : Nat := 204346130545019995203137

theorem tailTrace_3581664 : CollatzResearch.WordTrace tailWord_3581664 prefixEnd_3581664 204346130545019995203137 := by
  unfold tailWord_3581664
  simp only [CollatzResearch.WordTrace]
  refine ⟨65317009048125251178212023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87089345397500334904282697 65317009048125251178212023)
  ·
    refine ⟨97975513572187876767318035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65317009048125251178212023 97975513572187876767318035)
    ·
      refine ⟨146963270358281815150977053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97975513572187876767318035 146963270358281815150977053)
      ·
        refine ⟨55111226384355680681616395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146963270358281815150977053 55111226384355680681616395)
        ·
          refine ⟨82666839576533521022424593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55111226384355680681616395 82666839576533521022424593)
          ·
            refine ⟨62000129682400140766818445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82666839576533521022424593 62000129682400140766818445)
            ·
              refine ⟨23250048630900052787556917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62000129682400140766818445 23250048630900052787556917)
              ·
                refine ⟨2179692059146879948833461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23250048630900052787556917 2179692059146879948833461)
                ·
                  refine ⟨204346130545019995203137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2179692059146879948833461 204346130545019995203137)
                  ·
                    rfl

theorem cell23_3581664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 5].length) (baseStart_3581664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581664 prefixEnd_3581664 := by exact prefixLift 3581664
  have htrace : WordTrace (prefixWord ++ tailWord_3581664) baseStart_3581664 baseEnd_3581664 := by
    simpa [prefixWord, tailWord_3581664, baseEnd_3581664] using wordTrace_append hprefix tailTrace_3581664
  have hstable : (prefixWord ++ tailWord_3581664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581664).length < 2 ^ (prefixWord ++ tailWord_3581664).sum := by decide
  have hdescent : baseEnd_3581664 < baseStart_3581664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581674 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_3581674 : Nat := 118140960795 + 3581674 * 2 ^ 59
def prefixEnd_3581674 : Nat := 4983230072969 + 3 ^ 40 * 3581674 * 2
def baseEnd_3581674 : Nat := 1839120309711724917703187

theorem tailTrace_3581674 : CollatzResearch.WordTrace tailWord_3581674 prefixEnd_3581674 1839120309711724917703187 := by
  unfold tailWord_3581674
  simp only [CollatzResearch.WordTrace]
  refine ⟨32658595706553568516072019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87089588550809516042858717 32658595706553568516072019)
  ·
    refine ⟨48987893559830352774108029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32658595706553568516072019 48987893559830352774108029)
    ·
      refine ⟨18370460084936382290290511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48987893559830352774108029 18370460084936382290290511)
      ·
        refine ⟨27555690127404573435435767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18370460084936382290290511 27555690127404573435435767)
        ·
          refine ⟨41333535191106860153153651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27555690127404573435435767 41333535191106860153153651)
          ·
            refine ⟨62000302786660290229730477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41333535191106860153153651 62000302786660290229730477)
            ·
              refine ⟨23250113544997608836148929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62000302786660290229730477 23250113544997608836148929)
              ·
                refine ⟨17437585158748206627111697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23250113544997608836148929 17437585158748206627111697)
                ·
                  refine ⟨13078188869061154970333773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17437585158748206627111697 13078188869061154970333773)
                  ·
                    refine ⟨4904320825897933113875165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13078188869061154970333773 4904320825897933113875165)
                    ·
                      refine ⟨1839120309711724917703187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4904320825897933113875165 1839120309711724917703187)
                      ·
                        rfl

theorem cell23_3581674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_3581674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581674 prefixEnd_3581674 := by exact prefixLift 3581674
  have htrace : WordTrace (prefixWord ++ tailWord_3581674) baseStart_3581674 baseEnd_3581674 := by
    simpa [prefixWord, tailWord_3581674, baseEnd_3581674] using wordTrace_append hprefix tailTrace_3581674
  have hstable : (prefixWord ++ tailWord_3581674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581674).length < 2 ^ (prefixWord ++ tailWord_3581674).sum := by decide
  have hdescent : baseEnd_3581674 < baseStart_3581674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581687 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 5]
def baseStart_3581687 : Nat := 118140960795 + 3581687 * 2 ^ 59
def prefixEnd_3581687 : Nat := 4983230072969 + 3 ^ 40 * 3581687 * 2
def baseEnd_3581687 : Nat := 1839126984960233366840627

theorem tailTrace_3581687 : CollatzResearch.WordTrace tailWord_3581687 prefixEnd_3581687 1839126984960233366840627 := by
  unfold tailWord_3581687
  simp only [CollatzResearch.WordTrace]
  refine ⟨130634856975167177284511315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87089904650111451523007543 130634856975167177284511315)
  ·
    refine ⟨195952285462750765926766973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130634856975167177284511315 195952285462750765926766973)
    ·
      refine ⟨73482107048531537222537615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195952285462750765926766973 73482107048531537222537615)
      ·
        refine ⟨110223160572797305833806423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73482107048531537222537615 110223160572797305833806423)
        ·
          refine ⟨165334740859195958750709635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110223160572797305833806423 165334740859195958750709635)
          ·
            refine ⟨248002111288793938126064453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165334740859195958750709635 248002111288793938126064453)
            ·
              refine ⟨46500395866648863398637085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248002111288793938126064453 46500395866648863398637085)
              ·
                refine ⟨17437648449993323774488907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46500395866648863398637085 17437648449993323774488907)
                ·
                  refine ⟨26156472674989985661733361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17437648449993323774488907 26156472674989985661733361)
                  ·
                    refine ⟨19617354506242489246300021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26156472674989985661733361 19617354506242489246300021)
                    ·
                      refine ⟨1839126984960233366840627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19617354506242489246300021 1839126984960233366840627)
                      ·
                        rfl

theorem cell23_3581687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_3581687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581687 prefixEnd_3581687 := by exact prefixLift 3581687
  have htrace : WordTrace (prefixWord ++ tailWord_3581687) baseStart_3581687 baseEnd_3581687 := by
    simpa [prefixWord, tailWord_3581687, baseEnd_3581687] using wordTrace_append hprefix tailTrace_3581687
  have hstable : (prefixWord ++ tailWord_3581687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581687).length < 2 ^ (prefixWord ++ tailWord_3581687).sum := by decide
  have hdescent : baseEnd_3581687 < baseStart_3581687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581788 : List Nat := [2, 2, 4, 2, 2, 1, 2, 2, 6]
def baseStart_3581788 : Nat := 118140960795 + 3581788 * 2 ^ 59
def prefixEnd_3581788 : Nat := 4983230072969 + 3 ^ 40 * 3581788 * 2
def baseEnd_3581788 : Nat := 204353205167370830186407

theorem tailTrace_3581788 : CollatzResearch.WordTrace tailWord_3581788 prefixEnd_3581788 204353205167370830186407 := by
  unfold tailWord_3581788
  simp only [CollatzResearch.WordTrace]
  refine ⟨65319270373900635766969009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87092360498534181022625345 65319270373900635766969009)
  ·
    refine ⟨48989452780425476825226757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65319270373900635766969009 48989452780425476825226757)
    ·
      refine ⟨9185522396329776904730017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48989452780425476825226757 9185522396329776904730017)
      ·
        refine ⟨6889141797247332678547513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9185522396329776904730017 6889141797247332678547513)
        ·
          refine ⟨5166856347935499508910635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6889141797247332678547513 5166856347935499508910635)
          ·
            refine ⟨7750284521903249263365953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5166856347935499508910635 7750284521903249263365953)
            ·
              refine ⟨5812713391427436947524465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7750284521903249263365953 5812713391427436947524465)
              ·
                refine ⟨4359535043570577710643349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5812713391427436947524465 4359535043570577710643349)
                ·
                  refine ⟨204353205167370830186407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4359535043570577710643349 204353205167370830186407)
                  ·
                    rfl

theorem cell23_3581788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 6].length) (baseStart_3581788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581788 prefixEnd_3581788 := by exact prefixLift 3581788
  have htrace : WordTrace (prefixWord ++ tailWord_3581788) baseStart_3581788 baseEnd_3581788 := by
    simpa [prefixWord, tailWord_3581788, baseEnd_3581788] using wordTrace_append hprefix tailTrace_3581788
  have hstable : (prefixWord ++ tailWord_3581788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581788).length < 2 ^ (prefixWord ++ tailWord_3581788).sum := by decide
  have hdescent : baseEnd_3581788 < baseStart_3581788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581821 : List Nat := [1, 4, 1, 1, 2, 1, 1, 6, 1, 1, 4]
def baseStart_3581821 : Nat := 118140960795 + 3581821 * 2 ^ 59
def prefixEnd_3581821 : Nat := 4983230072969 + 3 ^ 40 * 3581821 * 2
def baseEnd_3581821 : Nat := 1839195791367935842565011

theorem tailTrace_3581821 : CollatzResearch.WordTrace tailWord_3581821 prefixEnd_3581821 1839195791367935842565011 := by
  unfold tailWord_3581821
  simp only [CollatzResearch.WordTrace]
  refine ⟨130639744356681718169889317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87093162904454478779926211 130639744356681718169889317)
  ·
    refine ⟨24494952066877822156854247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130639744356681718169889317 24494952066877822156854247)
    ·
      refine ⟨36742428100316733235281371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24494952066877822156854247 36742428100316733235281371)
      ·
        refine ⟨55113642150475099852922057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36742428100316733235281371 55113642150475099852922057)
        ·
          refine ⟨41335231612856324889691543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55113642150475099852922057 41335231612856324889691543)
          ·
            refine ⟨62002847419284487334537315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41335231612856324889691543 62002847419284487334537315)
            ·
              refine ⟨93004271128926731001805973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62002847419284487334537315 93004271128926731001805973)
              ·
                refine ⟨4359575209168440515709655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93004271128926731001805973 4359575209168440515709655)
                ·
                  refine ⟨6539362813752660773564483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4359575209168440515709655 6539362813752660773564483)
                  ·
                    refine ⟨9809044220628991160346725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6539362813752660773564483 9809044220628991160346725)
                    ·
                      refine ⟨1839195791367935842565011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9809044220628991160346725 1839195791367935842565011)
                      ·
                        rfl

theorem cell23_3581821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_3581821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581821 prefixEnd_3581821 := by exact prefixLift 3581821
  have htrace : WordTrace (prefixWord ++ tailWord_3581821) baseStart_3581821 baseEnd_3581821 := by
    simpa [prefixWord, tailWord_3581821, baseEnd_3581821] using wordTrace_append hprefix tailTrace_3581821
  have hstable : (prefixWord ++ tailWord_3581821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581821).length < 2 ^ (prefixWord ++ tailWord_3581821).sum := by decide
  have hdescent : baseEnd_3581821 < baseStart_3581821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581825 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 1, 5, 2]
def baseStart_3581825 : Nat := 118140960795 + 3581825 * 2 ^ 59
def prefixEnd_3581825 : Nat := 4983230072969 + 3 ^ 40 * 3581825 * 2
def baseEnd_3581825 : Nat := 1839197845290553826914993

theorem tailTrace_3581825 : CollatzResearch.WordTrace tailWord_3581825 prefixEnd_3581825 1839197845290553826914993 := by
  unfold tailWord_3581825
  simp only [CollatzResearch.WordTrace]
  refine ⟨130639890248667226853034929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87093260165778151235356619 130639890248667226853034929)
  ·
    refine ⟨97979917686500420139776197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130639890248667226853034929 97979917686500420139776197)
    ·
      refine ⟨18371234566218828776208037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97979917686500420139776197 18371234566218828776208037)
      ·
        refine ⟨3444606481166030395539007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18371234566218828776208037 3444606481166030395539007)
        ·
          refine ⟨5166909721749045593308511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3444606481166030395539007 5166909721749045593308511)
          ·
            refine ⟨7750364582623568389962767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5166909721749045593308511 7750364582623568389962767)
            ·
              refine ⟨11625546873935352584944151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7750364582623568389962767 11625546873935352584944151)
              ·
                refine ⟨17438320310903028877416227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11625546873935352584944151 17438320310903028877416227)
                ·
                  refine ⟨26157480466354543316124341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17438320310903028877416227 26157480466354543316124341)
                  ·
                    refine ⟨2452263793720738435886657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26157480466354543316124341 2452263793720738435886657)
                    ·
                      refine ⟨1839197845290553826914993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2452263793720738435886657 1839197845290553826914993)
                      ·
                        rfl

theorem cell23_3581825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_3581825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581825 prefixEnd_3581825 := by exact prefixLift 3581825
  have htrace : WordTrace (prefixWord ++ tailWord_3581825) baseStart_3581825 baseEnd_3581825 := by
    simpa [prefixWord, tailWord_3581825, baseEnd_3581825] using wordTrace_append hprefix tailTrace_3581825
  have hstable : (prefixWord ++ tailWord_3581825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581825).length < 2 ^ (prefixWord ++ tailWord_3581825).sum := by decide
  have hdescent : baseEnd_3581825 < baseStart_3581825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581832 : List Nat := [2, 1, 3, 3, 3, 1, 2, 3, 1, 1, 3]
def baseStart_3581832 : Nat := 118140960795 + 3581832 * 2 ^ 59
def prefixEnd_3581832 : Nat := 4983230072969 + 3 ^ 40 * 3581832 * 2
def baseEnd_3581832 : Nat := 1839201439655135299527461

theorem tailTrace_3581832 : CollatzResearch.WordTrace tailWord_3581832 prefixEnd_3581832 1839201439655135299527461 := by
  unfold tailWord_3581832
  simp only [CollatzResearch.WordTrace]
  refine ⟨65320072779820933524269875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87093430373094578032359833 65320072779820933524269875)
  ·
    refine ⟨97980109169731400286404813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65320072779820933524269875 97980109169731400286404813)
    ·
      refine ⟨36742540938649275107401805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97980109169731400286404813 36742540938649275107401805)
      ·
        refine ⟨13778452851993478165275677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36742540938649275107401805 13778452851993478165275677)
        ·
          refine ⟨5166919819497554311978379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13778452851993478165275677 5166919819497554311978379)
          ·
            refine ⟨7750379729246331467967569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5166919819497554311978379 7750379729246331467967569)
            ·
              refine ⟨5812784796934748600975677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7750379729246331467967569 5812784796934748600975677)
              ·
                refine ⟨2179794298850530725365879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5812784796934748600975677 2179794298850530725365879)
                ·
                  refine ⟨3269691448275796088048819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2179794298850530725365879 3269691448275796088048819)
                  ·
                    refine ⟨4904537172413694132073229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3269691448275796088048819 4904537172413694132073229)
                    ·
                      refine ⟨1839201439655135299527461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4904537172413694132073229 1839201439655135299527461)
                      ·
                        rfl

theorem cell23_3581832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_3581832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581832 prefixEnd_3581832 := by exact prefixLift 3581832
  have htrace : WordTrace (prefixWord ++ tailWord_3581832) baseStart_3581832 baseEnd_3581832 := by
    simpa [prefixWord, tailWord_3581832, baseEnd_3581832] using wordTrace_append hprefix tailTrace_3581832
  have hstable : (prefixWord ++ tailWord_3581832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581832).length < 2 ^ (prefixWord ++ tailWord_3581832).sum := by decide
  have hdescent : baseEnd_3581832 < baseStart_3581832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581858 : List Nat := [3, 3, 1, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_3581858 : Nat := 118140960795 + 3581858 * 2 ^ 59
def prefixEnd_3581858 : Nat := 4983230072969 + 3 ^ 40 * 3581858 * 2
def baseEnd_3581858 : Nat := 1839214790152152197802341

theorem tailTrace_3581858 : CollatzResearch.WordTrace tailWord_3581858 prefixEnd_3581858 1839214790152152197802341 := by
  unfold tailWord_3581858
  simp only [CollatzResearch.WordTrace]
  refine ⟨32660273464386918372246557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87094062571698448992657485 32660273464386918372246557)
  ·
    refine ⟨12247602549145094389592459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32660273464386918372246557 12247602549145094389592459)
    ·
      refine ⟨18371403823717641584388689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12247602549145094389592459 18371403823717641584388689)
      ·
        refine ⟨13778552867788231188291517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18371403823717641584388689 13778552867788231188291517)
        ·
          refine ⟨5166957325420586695609319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13778552867788231188291517 5166957325420586695609319)
          ·
            refine ⟨7750435988130880043413979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5166957325420586695609319 7750435988130880043413979)
            ·
              refine ⟨11625653982196320065120969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7750435988130880043413979 11625653982196320065120969)
              ·
                refine ⟨8719240486647240048840727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11625653982196320065120969 8719240486647240048840727)
                ·
                  refine ⟨13078860729970860073261091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8719240486647240048840727 13078860729970860073261091)
                  ·
                    refine ⟨19618291094956290109891637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13078860729970860073261091 19618291094956290109891637)
                    ·
                      refine ⟨1839214790152152197802341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19618291094956290109891637 1839214790152152197802341)
                      ·
                        rfl

theorem cell23_3581858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_3581858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581858 prefixEnd_3581858 := by exact prefixLift 3581858
  have htrace : WordTrace (prefixWord ++ tailWord_3581858) baseStart_3581858 baseEnd_3581858 := by
    simpa [prefixWord, tailWord_3581858, baseEnd_3581858] using wordTrace_append hprefix tailTrace_3581858
  have hstable : (prefixWord ++ tailWord_3581858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581858).length < 2 ^ (prefixWord ++ tailWord_3581858).sum := by decide
  have hdescent : baseEnd_3581858 < baseStart_3581858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581874 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 2, 7]
def baseStart_3581874 : Nat := 118140960795 + 3581874 * 2 ^ 59
def prefixEnd_3581874 : Nat := 4983230072969 + 3 ^ 40 * 3581874 * 2
def baseEnd_3581874 : Nat := 613074335280874711734089

theorem tailTrace_3581874 : CollatzResearch.WordTrace tailWord_3581874 prefixEnd_3581874 613074335280874711734089 := by
  unfold tailWord_3581874
  simp only [CollatzResearch.WordTrace]
  refine ⟨32660419356372427055392169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87094451616993138814379117 32660419356372427055392169)
  ·
    refine ⟨24495314517279320291544127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32660419356372427055392169 24495314517279320291544127)
    ·
      refine ⟨36742971775918980437316191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24495314517279320291544127 36742971775918980437316191)
      ·
        refine ⟨55114457663878470655974287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36742971775918980437316191 55114457663878470655974287)
        ·
          refine ⟨82671686495817705983961431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55114457663878470655974287 82671686495817705983961431)
          ·
            refine ⟨124007529743726558975942147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82671686495817705983961431 124007529743726558975942147)
            ·
              refine ⟨186011294615589838463913221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124007529743726558975942147 186011294615589838463913221)
              ·
                refine ⟨34877117740423094711983729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186011294615589838463913221 34877117740423094711983729)
                ·
                  refine ⟨26157838305317321033987797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34877117740423094711983729 26157838305317321033987797)
                  ·
                    refine ⟨613074335280874711734089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26157838305317321033987797 613074335280874711734089)
                    ·
                      rfl

theorem cell23_3581874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_3581874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581874 prefixEnd_3581874 := by exact prefixLift 3581874
  have htrace : WordTrace (prefixWord ++ tailWord_3581874) baseStart_3581874 baseEnd_3581874 := by
    simpa [prefixWord, tailWord_3581874, baseEnd_3581874] using wordTrace_append hprefix tailTrace_3581874
  have hstable : (prefixWord ++ tailWord_3581874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581874).length < 2 ^ (prefixWord ++ tailWord_3581874).sum := by decide
  have hdescent : baseEnd_3581874 < baseStart_3581874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581904 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 4, 6]
def baseStart_3581904 : Nat := 118140960795 + 3581904 * 2 ^ 59
def prefixEnd_3581904 : Nat := 4983230072969 + 3 ^ 40 * 3581904 * 2
def baseEnd_3581904 : Nat := 613079470087419672609043

theorem tailTrace_3581904 : CollatzResearch.WordTrace tailWord_3581904 prefixEnd_3581904 613079470087419672609043 := by
  unfold tailWord_3581904
  simp only [CollatzResearch.WordTrace]
  refine ⟨65321385807690511672580383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87095181076920682230107177 65321385807690511672580383)
  ·
    refine ⟨97982078711535767508870575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65321385807690511672580383 97982078711535767508870575)
    ·
      refine ⟨146973118067303651263305863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97982078711535767508870575 146973118067303651263305863)
      ·
        refine ⟨220459677100955476894958795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146973118067303651263305863 220459677100955476894958795)
        ·
          refine ⟨330689515651433215342438193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220459677100955476894958795 330689515651433215342438193)
          ·
            refine ⟨248017136738574911506828645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330689515651433215342438193 248017136738574911506828645)
            ·
              refine ⟨46503213138482795907530371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248017136738574911506828645 46503213138482795907530371)
              ·
                refine ⟨69754819707724193861295557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46503213138482795907530371 69754819707724193861295557)
                ·
                  refine ⟨13079028695198286348992917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69754819707724193861295557 13079028695198286348992917)
                  ·
                    refine ⟨613079470087419672609043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13079028695198286348992917 613079470087419672609043)
                    ·
                      rfl

theorem cell23_3581904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 4, 6].length) (baseStart_3581904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581904 prefixEnd_3581904 := by exact prefixLift 3581904
  have htrace : WordTrace (prefixWord ++ tailWord_3581904) baseStart_3581904 baseEnd_3581904 := by
    simpa [prefixWord, tailWord_3581904, baseEnd_3581904] using wordTrace_append hprefix tailTrace_3581904
  have hstable : (prefixWord ++ tailWord_3581904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581904).length < 2 ^ (prefixWord ++ tailWord_3581904).sum := by decide
  have hdescent : baseEnd_3581904 < baseStart_3581904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581906 : List Nat := [3, 2, 2, 3, 2, 1, 3, 2, 1, 2, 2]
def baseStart_3581906 : Nat := 118140960795 + 3581906 * 2 ^ 59
def prefixEnd_3581906 : Nat := 4983230072969 + 3 ^ 40 * 3581906 * 2
def baseEnd_3581906 : Nat := 1839239437223568010002121

theorem tailTrace_3581906 : CollatzResearch.WordTrace tailWord_3581906 prefixEnd_3581906 1839239437223568010002121 := by
  unfold tailWord_3581906
  simp only [CollatzResearch.WordTrace]
  refine ⟨32660711140343444421683393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87095229707582518457822381 32660711140343444421683393)
  ·
    refine ⟨24495533355257583316262545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32660711140343444421683393 24495533355257583316262545)
    ·
      refine ⟨18371650016443187487196909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24495533355257583316262545 18371650016443187487196909)
      ·
        refine ⟨6889368756166195307698841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18371650016443187487196909 6889368756166195307698841)
        ·
          refine ⟨5167026567124646480774131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6889368756166195307698841 5167026567124646480774131)
          ·
            refine ⟨7750539850686969721161197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5167026567124646480774131 7750539850686969721161197)
            ·
              refine ⟨2906452444007613645435449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7750539850686969721161197 2906452444007613645435449)
              ·
                refine ⟨2179839333005710234076587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2906452444007613645435449 2179839333005710234076587)
                ·
                  refine ⟨3269758999508565351114881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2179839333005710234076587 3269758999508565351114881)
                  ·
                    refine ⟨2452319249631424013336161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3269758999508565351114881 2452319249631424013336161)
                    ·
                      refine ⟨1839239437223568010002121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2452319249631424013336161 1839239437223568010002121)
                      ·
                        rfl

theorem cell23_3581906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_3581906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581906 prefixEnd_3581906 := by exact prefixLift 3581906
  have htrace : WordTrace (prefixWord ++ tailWord_3581906) baseStart_3581906 baseEnd_3581906 := by
    simpa [prefixWord, tailWord_3581906, baseEnd_3581906] using wordTrace_append hprefix tailTrace_3581906
  have hstable : (prefixWord ++ tailWord_3581906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581906).length < 2 ^ (prefixWord ++ tailWord_3581906).sum := by decide
  have hdescent : baseEnd_3581906 < baseStart_3581906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581916 : List Nat := [2, 2, 6, 1, 1, 2, 2, 1, 2, 4]
def baseStart_3581916 : Nat := 118140960795 + 3581916 * 2 ^ 59
def prefixEnd_3581916 : Nat := 4983230072969 + 3 ^ 40 * 3581916 * 2
def baseEnd_3581916 : Nat := 613081524010037656959025

theorem tailTrace_3581916 : CollatzResearch.WordTrace tailWord_3581916 prefixEnd_3581916 613081524010037656959025 := by
  unfold tailWord_3581916
  simp only [CollatzResearch.WordTrace]
  refine ⟨65321604645668774697298801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87095472860891699596398401 65321604645668774697298801)
  ·
    refine ⟨48991203484251581022974101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65321604645668774697298801 48991203484251581022974101)
    ·
      refine ⟨2296462663324292860451911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48991203484251581022974101 2296462663324292860451911)
      ·
        refine ⟨3444693994986439290677867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2296462663324292860451911 3444693994986439290677867)
        ·
          refine ⟨5167040992479658936016801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3444693994986439290677867 5167040992479658936016801)
          ·
            refine ⟨3875280744359744202012601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5167040992479658936016801 3875280744359744202012601)
            ·
              refine ⟨2906460558269808151509451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3875280744359744202012601 2906460558269808151509451)
              ·
                refine ⟨4359690837404712227264177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2906460558269808151509451 4359690837404712227264177)
                ·
                  refine ⟨3269768128053534170448133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4359690837404712227264177 3269768128053534170448133)
                  ·
                    refine ⟨613081524010037656959025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3269768128053534170448133 613081524010037656959025)
                    ·
                      rfl

theorem cell23_3581916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_3581916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581916 prefixEnd_3581916 := by exact prefixLift 3581916
  have htrace : WordTrace (prefixWord ++ tailWord_3581916) baseStart_3581916 baseEnd_3581916 := by
    simpa [prefixWord, tailWord_3581916, baseEnd_3581916] using wordTrace_append hprefix tailTrace_3581916
  have hstable : (prefixWord ++ tailWord_3581916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581916).length < 2 ^ (prefixWord ++ tailWord_3581916).sum := by decide
  have hdescent : baseEnd_3581916 < baseStart_3581916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581928 : List Nat := [2, 1, 4, 1, 1, 1, 1, 5, 1, 4, 2]
def baseStart_3581928 : Nat := 118140960795 + 3581928 * 2 ^ 59
def prefixEnd_3581928 : Nat := 4983230072969 + 3 ^ 40 * 3581928 * 2
def baseEnd_3581928 : Nat := 1839250733797966923927019

theorem tailTrace_3581928 : CollatzResearch.WordTrace tailWord_3581928 prefixEnd_3581928 1839250733797966923927019 := by
  unfold tailWord_3581928
  simp only [CollatzResearch.WordTrace]
  refine ⟨65321823483647037722017219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87095764644862716962689625 65321823483647037722017219)
  ·
    refine ⟨97982735225470556583025829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65321823483647037722017219 97982735225470556583025829)
    ·
      refine ⟨18371762854775729359317343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97982735225470556583025829 18371762854775729359317343)
      ·
        refine ⟨27557644282163594038976015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18371762854775729359317343 27557644282163594038976015)
        ·
          refine ⟨41336466423245391058464023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27557644282163594038976015 41336466423245391058464023)
          ·
            refine ⟨62004699634868086587696035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41336466423245391058464023 62004699634868086587696035)
            ·
              refine ⟨93007049452302129881544053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62004699634868086587696035 93007049452302129881544053)
              ·
                refine ⟨8719410886153324676394755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93007049452302129881544053 8719410886153324676394755)
                ·
                  refine ⟨13079116329229987014592133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8719410886153324676394755 13079116329229987014592133)
                  ·
                    refine ⟨2452334311730622565236025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13079116329229987014592133 2452334311730622565236025)
                    ·
                      refine ⟨1839250733797966923927019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2452334311730622565236025 1839250733797966923927019)
                      ·
                        rfl

theorem cell23_3581928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_3581928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581928 prefixEnd_3581928 := by exact prefixLift 3581928
  have htrace : WordTrace (prefixWord ++ tailWord_3581928) baseStart_3581928 baseEnd_3581928 := by
    simpa [prefixWord, tailWord_3581928, baseEnd_3581928] using wordTrace_append hprefix tailTrace_3581928
  have hstable : (prefixWord ++ tailWord_3581928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581928).length < 2 ^ (prefixWord ++ tailWord_3581928).sum := by decide
  have hdescent : baseEnd_3581928 < baseStart_3581928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581978 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3]
def baseStart_3581978 : Nat := 118140960795 + 3581978 * 2 ^ 59
def prefixEnd_3581978 : Nat := 4983230072969 + 3 ^ 40 * 3581978 * 2
def baseEnd_3581978 : Nat := 1839276407830691728301789

theorem tailTrace_3581978 : CollatzResearch.WordTrace tailWord_3581978 prefixEnd_3581978 1839276407830691728301789 := by
  unfold tailWord_3581978
  simp only [CollatzResearch.WordTrace]
  refine ⟨32661367654278233495838647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87096980411408622655569725 32661367654278233495838647)
  ·
    refine ⟨48992051481417350243757971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32661367654278233495838647 48992051481417350243757971)
    ·
      refine ⟨73488077222126025365636957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48992051481417350243757971 73488077222126025365636957)
      ·
        refine ⟨27558028958297259512113859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73488077222126025365636957 27558028958297259512113859)
        ·
          refine ⟨41337043437445889268170789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27558028958297259512113859 41337043437445889268170789)
          ·
            refine ⟨7750695644521104237782023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41337043437445889268170789 7750695644521104237782023)
            ·
              refine ⟨11626043466781656356673035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7750695644521104237782023 11626043466781656356673035)
              ·
                refine ⟨17439065200172484535009553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11626043466781656356673035 17439065200172484535009553)
                ·
                  refine ⟨13079298900129363401257165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17439065200172484535009553 13079298900129363401257165)
                  ·
                    refine ⟨4904737087548511275471437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13079298900129363401257165 4904737087548511275471437)
                    ·
                      refine ⟨1839276407830691728301789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4904737087548511275471437 1839276407830691728301789)
                      ·
                        rfl

theorem cell23_3581978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_3581978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581978 prefixEnd_3581978 := by exact prefixLift 3581978
  have htrace : WordTrace (prefixWord ++ tailWord_3581978) baseStart_3581978 baseEnd_3581978 := by
    simpa [prefixWord, tailWord_3581978, baseEnd_3581978] using wordTrace_append hprefix tailTrace_3581978
  have hstable : (prefixWord ++ tailWord_3581978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581978).length < 2 ^ (prefixWord ++ tailWord_3581978).sum := by decide
  have hdescent : baseEnd_3581978 < baseStart_3581978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581998 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 1, 7]
def baseStart_3581998 : Nat := 118140960795 + 3581998 * 2 ^ 59
def prefixEnd_3581998 : Nat := 4983230072969 + 3 ^ 40 * 3581998 * 2
def baseEnd_3581998 : Nat := 613095559147927216683899

theorem tailTrace_3581998 : CollatzResearch.WordTrace tailWord_3581998 prefixEnd_3581998 613095559147927216683899 := by
  unfold tailWord_3581998
  simp only [CollatzResearch.WordTrace]
  refine ⟨16330775009630059674885331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87097466718026984932721765 16330775009630059674885331)
  ·
    refine ⟨24496162514445089512327997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16330775009630059674885331 24496162514445089512327997)
    ·
      refine ⟨9186060942916908567122999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24496162514445089512327997 9186060942916908567122999)
      ·
        refine ⟨13779091414375362850684499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9186060942916908567122999 13779091414375362850684499)
        ·
          refine ⟨20668637121563044276026749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13779091414375362850684499 20668637121563044276026749)
          ·
            refine ⟨7750738920586141603510031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20668637121563044276026749 7750738920586141603510031)
            ·
              refine ⟨11626108380879212405265047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7750738920586141603510031 11626108380879212405265047)
              ·
                refine ⟨17439162571318818607897571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11626108380879212405265047 17439162571318818607897571)
                ·
                  refine ⟨26158743856978227911846357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17439162571318818607897571 26158743856978227911846357)
                  ·
                    refine ⟨613095559147927216683899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26158743856978227911846357 613095559147927216683899)
                    ·
                      rfl

theorem cell23_3581998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_3581998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3581998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3581998 prefixEnd_3581998 := by exact prefixLift 3581998
  have htrace : WordTrace (prefixWord ++ tailWord_3581998) baseStart_3581998 baseEnd_3581998 := by
    simpa [prefixWord, tailWord_3581998, baseEnd_3581998] using wordTrace_append hprefix tailTrace_3581998
  have hstable : (prefixWord ++ tailWord_3581998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581998).length < 2 ^ (prefixWord ++ tailWord_3581998).sum := by decide
  have hdescent : baseEnd_3581998 < baseStart_3581998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582028 : List Nat := [2, 2, 1, 3, 1, 1, 3, 3, 3, 4]
def baseStart_3582028 : Nat := 118140960795 + 3582028 * 2 ^ 59
def prefixEnd_3582028 : Nat := 4983230072969 + 3 ^ 40 * 3582028 * 2
def baseEnd_3582028 : Nat := 613100693954472177558853

theorem tailTrace_3582028 : CollatzResearch.WordTrace tailWord_3582028 prefixEnd_3582028 613100693954472177558853 := by
  unfold tailWord_3582028
  simp only [CollatzResearch.WordTrace]
  refine ⟨65323647133465896261337369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87098196177954528348449825 65323647133465896261337369)
  ·
    refine ⟨48992735350099422196003027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65323647133465896261337369 48992735350099422196003027)
    ·
      refine ⟨73489103025149133294004541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48992735350099422196003027 73489103025149133294004541)
      ·
        refine ⟨27558413634430924985251703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73489103025149133294004541 27558413634430924985251703)
        ·
          refine ⟨41337620451646387477877555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27558413634430924985251703 41337620451646387477877555)
          ·
            refine ⟨62006430677469581216816333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41337620451646387477877555 62006430677469581216816333)
            ·
              refine ⟨23252411504051092956306125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62006430677469581216816333 23252411504051092956306125)
              ·
                refine ⟨8719654314019159858614797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23252411504051092956306125 8719654314019159858614797)
                ·
                  refine ⟨3269870367757184946980549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8719654314019159858614797 3269870367757184946980549)
                  ·
                    refine ⟨613100693954472177558853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3269870367757184946980549 613100693954472177558853)
                    ·
                      rfl

theorem cell23_3582028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_3582028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582028 prefixEnd_3582028 := by exact prefixLift 3582028
  have htrace : WordTrace (prefixWord ++ tailWord_3582028) baseStart_3582028 baseEnd_3582028 := by
    simpa [prefixWord, tailWord_3582028, baseEnd_3582028] using wordTrace_append hprefix tailTrace_3582028
  have hstable : (prefixWord ++ tailWord_3582028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582028).length < 2 ^ (prefixWord ++ tailWord_3582028).sum := by decide
  have hdescent : baseEnd_3582028 < baseStart_3582028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582091 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 4]
def baseStart_3582091 : Nat := 118140960795 + 3582091 * 2 ^ 59
def prefixEnd_3582091 : Nat := 4983230072969 + 3 ^ 40 * 3582091 * 2
def baseEnd_3582091 : Nat := 1839334431144649786188769

theorem tailTrace_3582091 : CollatzResearch.WordTrace tailWord_3582091 prefixEnd_3582091 1839334431144649786188769 := by
  unfold tailWord_3582091
  simp only [CollatzResearch.WordTrace]
  refine ⟨130649592065703554282218127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87099728043802369521478751 130649592065703554282218127)
  ·
    refine ⟨195974388098555331423327191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130649592065703554282218127 195974388098555331423327191)
    ·
      refine ⟨293961582147832997134990787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195974388098555331423327191 293961582147832997134990787)
      ·
        refine ⟨440942373221749495702486181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293961582147832997134990787 440942373221749495702486181)
        ·
          refine ⟨82676694979078030444216159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 440942373221749495702486181 82676694979078030444216159)
          ·
            refine ⟨124015042468617045666324239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82676694979078030444216159 124015042468617045666324239)
            ·
              refine ⟨186022563702925568499486359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124015042468617045666324239 186022563702925568499486359)
              ·
                refine ⟨279033845554388352749229539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186022563702925568499486359 279033845554388352749229539)
                ·
                  refine ⟨418550768331582529123844309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279033845554388352749229539 418550768331582529123844309)
                  ·
                    refine ⟨9809783632771465526340101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 418550768331582529123844309 9809783632771465526340101)
                    ·
                      refine ⟨1839334431144649786188769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9809783632771465526340101 1839334431144649786188769)
                      ·
                        rfl

theorem cell23_3582091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 4].length) (baseStart_3582091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582091 prefixEnd_3582091 := by exact prefixLift 3582091
  have htrace : WordTrace (prefixWord ++ tailWord_3582091) baseStart_3582091 baseEnd_3582091 := by
    simpa [prefixWord, tailWord_3582091, baseEnd_3582091] using wordTrace_append hprefix tailTrace_3582091
  have hstable : (prefixWord ++ tailWord_3582091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582091).length < 2 ^ (prefixWord ++ tailWord_3582091).sum := by decide
  have hdescent : baseEnd_3582091 < baseStart_3582091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582112 : List Nat := [2, 1, 1, 4, 2, 3, 2, 1, 2, 3, 2]
def baseStart_3582112 : Nat := 118140960795 + 3582112 * 2 ^ 59
def prefixEnd_3582112 : Nat := 4983230072969 + 3 ^ 40 * 3582112 * 2
def baseEnd_3582112 : Nat := 1839345214238394204026173

theorem tailTrace_3582112 : CollatzResearch.WordTrace tailWord_3582112 prefixEnd_3582112 1839345214238394204026173 := by
  unfold tailWord_3582112
  simp only [CollatzResearch.WordTrace]
  refine ⟨65325178999313737434366295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87100238665751649912488393 65325178999313737434366295)
  ·
    refine ⟨97987768498970606151549443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65325178999313737434366295 97987768498970606151549443)
    ·
      refine ⟨146981652748455909227324165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97987768498970606151549443 146981652748455909227324165)
      ·
        refine ⟨27559059890335482980123281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146981652748455909227324165 27559059890335482980123281)
        ·
          refine ⟨20669294917751612235092461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27559059890335482980123281 20669294917751612235092461)
          ·
            refine ⟨7750985594156854588159673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20669294917751612235092461 7750985594156854588159673)
            ·
              refine ⟨5813239195617640941119755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7750985594156854588159673 5813239195617640941119755)
              ·
                refine ⟨8719858793426461411679633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5813239195617640941119755 8719858793426461411679633)
                ·
                  refine ⟨6539894095069846058759725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8719858793426461411679633 6539894095069846058759725)
                  ·
                    refine ⟨2452460285651192272034897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6539894095069846058759725 2452460285651192272034897)
                    ·
                      refine ⟨1839345214238394204026173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2452460285651192272034897 1839345214238394204026173)
                      ·
                        rfl

theorem cell23_3582112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_3582112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582112 prefixEnd_3582112 := by exact prefixLift 3582112
  have htrace : WordTrace (prefixWord ++ tailWord_3582112) baseStart_3582112 baseEnd_3582112 := by
    simpa [prefixWord, tailWord_3582112, baseEnd_3582112] using wordTrace_append hprefix tailTrace_3582112
  have hstable : (prefixWord ++ tailWord_3582112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582112).length < 2 ^ (prefixWord ++ tailWord_3582112).sum := by decide
  have hdescent : baseEnd_3582112 < baseStart_3582112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582128 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 3]
def baseStart_3582128 : Nat := 118140960795 + 3582128 * 2 ^ 59
def prefixEnd_3582128 : Nat := 4983230072969 + 3 ^ 40 * 3582128 * 2
def baseEnd_3582128 : Nat := 1839353429928866141426099

theorem tailTrace_3582128 : CollatzResearch.WordTrace tailWord_3582128 prefixEnd_3582128 1839353429928866141426099 := by
  unfold tailWord_3582128
  simp only [CollatzResearch.WordTrace]
  refine ⟨65325470783284754800657519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87100627711046339734210025 65325470783284754800657519)
  ·
    refine ⟨97988206174927132200986279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65325470783284754800657519 97988206174927132200986279)
    ·
      refine ⟨146982309262390698301479419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97988206174927132200986279 146982309262390698301479419)
      ·
        refine ⟨220473463893586047452219129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146982309262390698301479419 220473463893586047452219129)
        ·
          refine ⟨165355097920189535589164347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220473463893586047452219129 165355097920189535589164347)
          ·
            refine ⟨248032646880284303383746521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165355097920189535589164347 248032646880284303383746521)
            ·
              refine ⟨186024485160213227537809891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248032646880284303383746521 186024485160213227537809891)
              ·
                refine ⟨279036727740319841306714837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186024485160213227537809891 279036727740319841306714837)
                ·
                  refine ⟨6539923306413746280626129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 279036727740319841306714837 6539923306413746280626129)
                  ·
                    refine ⟨4904942479810309710469597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6539923306413746280626129 4904942479810309710469597)
                    ·
                      refine ⟨1839353429928866141426099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4904942479810309710469597 1839353429928866141426099)
                      ·
                        rfl

theorem cell23_3582128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 3].length) (baseStart_3582128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582128 prefixEnd_3582128 := by exact prefixLift 3582128
  have htrace : WordTrace (prefixWord ++ tailWord_3582128) baseStart_3582128 baseEnd_3582128 := by
    simpa [prefixWord, tailWord_3582128, baseEnd_3582128] using wordTrace_append hprefix tailTrace_3582128
  have hstable : (prefixWord ++ tailWord_3582128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582128).length < 2 ^ (prefixWord ++ tailWord_3582128).sum := by decide
  have hdescent : baseEnd_3582128 < baseStart_3582128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582135 : List Nat := [1, 1, 3, 1, 4, 2, 1, 4, 2, 4]
def baseStart_3582135 : Nat := 118140960795 + 3582135 * 2 ^ 59
def prefixEnd_3582135 : Nat := 4983230072969 + 3 ^ 40 * 3582135 * 2
def baseEnd_3582135 : Nat := 613119008097815871346189

theorem tailTrace_3582135 : CollatzResearch.WordTrace tailWord_3582135 prefixEnd_3582135 613119008097815871346189 := by
  unfold tailWord_3582135
  simp only [CollatzResearch.WordTrace]
  refine ⟨130651196877544149796819859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87100797918362766531213239 130651196877544149796819859)
  ·
    refine ⟨195976795316316224695229789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130651196877544149796819859 195976795316316224695229789)
    ·
      refine ⟨73491298243618584260711171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195976795316316224695229789 73491298243618584260711171)
      ·
        refine ⟨110236947365427876391066757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73491298243618584260711171 110236947365427876391066757)
        ·
          refine ⟨20669427631017726823325017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110236947365427876391066757 20669427631017726823325017)
          ·
            refine ⟨15502070723263295117493763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20669427631017726823325017 15502070723263295117493763)
            ·
              refine ⟨23253106084894942676240645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15502070723263295117493763 23253106084894942676240645)
              ·
                refine ⟨4359957390917801751795121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23253106084894942676240645 4359957390917801751795121)
                ·
                  refine ⟨3269968043188351313846341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4359957390917801751795121 3269968043188351313846341)
                  ·
                    refine ⟨613119008097815871346189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3269968043188351313846341 613119008097815871346189)
                    ·
                      rfl

theorem cell23_3582135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_3582135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582135 prefixEnd_3582135 := by exact prefixLift 3582135
  have htrace : WordTrace (prefixWord ++ tailWord_3582135) baseStart_3582135 baseEnd_3582135 := by
    simpa [prefixWord, tailWord_3582135, baseEnd_3582135] using wordTrace_append hprefix tailTrace_3582135
  have hstable : (prefixWord ++ tailWord_3582135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582135).length < 2 ^ (prefixWord ++ tailWord_3582135).sum := by decide
  have hdescent : baseEnd_3582135 < baseStart_3582135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582175 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 4, 1, 3]
def baseStart_3582175 : Nat := 118140960795 + 3582175 * 2 ^ 59
def prefixEnd_3582175 : Nat := 4983230072969 + 3 ^ 40 * 3582175 * 2
def baseEnd_3582175 : Nat := 1839377563519627457538383

theorem tailTrace_3582175 : CollatzResearch.WordTrace tailWord_3582175 prefixEnd_3582175 1839377563519627457538383 := by
  unfold tailWord_3582175
  simp only [CollatzResearch.WordTrace]
  refine ⟨130652655797399236628275979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87101770531599491085517319 130652655797399236628275979)
  ·
    refine ⟨195978983696098854942413969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130652655797399236628275979 195978983696098854942413969)
    ·
      refine ⟨146984237772074141206810477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195978983696098854942413969 146984237772074141206810477)
      ·
        refine ⟨55119089164527802952553929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146984237772074141206810477 55119089164527802952553929)
        ·
          refine ⟨41339316873395852214415447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55119089164527802952553929 41339316873395852214415447)
          ·
            refine ⟨62008975310093778321623171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41339316873395852214415447 62008975310093778321623171)
            ·
              refine ⟨93013462965140667482434757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62008975310093778321623171 93013462965140667482434757)
              ·
                refine ⟨17440024305963875152956517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93013462965140667482434757 17440024305963875152956517)
                ·
                  refine ⟨3270004557368226591179347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17440024305963875152956517 3270004557368226591179347)
                  ·
                    refine ⟨4905006836052339886769021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3270004557368226591179347 4905006836052339886769021)
                    ·
                      refine ⟨1839377563519627457538383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4905006836052339886769021 1839377563519627457538383)
                      ·
                        rfl

theorem cell23_3582175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_3582175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582175 prefixEnd_3582175 := by exact prefixLift 3582175
  have htrace : WordTrace (prefixWord ++ tailWord_3582175) baseStart_3582175 baseEnd_3582175 := by
    simpa [prefixWord, tailWord_3582175, baseEnd_3582175] using wordTrace_append hprefix tailTrace_3582175
  have hstable : (prefixWord ++ tailWord_3582175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582175).length < 2 ^ (prefixWord ++ tailWord_3582175).sum := by decide
  have hdescent : baseEnd_3582175 < baseStart_3582175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582179 : List Nat := [1, 1, 1, 8, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3582179 : Nat := 118140960795 + 3582179 * 2 ^ 59
def prefixEnd_3582179 : Nat := 4983230072969 + 3 ^ 40 * 3582179 * 2
def baseEnd_3582179 : Nat := 1839379617442245441888365

theorem tailTrace_3582179 : CollatzResearch.WordTrace tailWord_3582179 prefixEnd_3582179 1839379617442245441888365 := by
  unfold tailWord_3582179
  simp only [CollatzResearch.WordTrace]
  refine ⟨130652801689384745311421591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87101867792923163540947727 130652801689384745311421591)
  ·
    refine ⟨195979202534077117967132387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130652801689384745311421591 195979202534077117967132387)
    ·
      refine ⟨293968803801115676950698581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195979202534077117967132387 293968803801115676950698581)
      ·
        refine ⟨3444946919544324339265999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 293968803801115676950698581 3444946919544324339265999)
        ·
          refine ⟨5167420379316486508898999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3444946919544324339265999 5167420379316486508898999)
          ·
            refine ⟨7751130568974729763348499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5167420379316486508898999 7751130568974729763348499)
            ·
              refine ⟨11626695853462094645022749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7751130568974729763348499 11626695853462094645022749)
              ·
                refine ⟨4360010945048285491883531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11626695853462094645022749 4360010945048285491883531)
                ·
                  refine ⟨6540016417572428237825297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4360010945048285491883531 6540016417572428237825297)
                  ·
                    refine ⟨4905012313179321178368973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6540016417572428237825297 4905012313179321178368973)
                    ·
                      refine ⟨1839379617442245441888365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4905012313179321178368973 1839379617442245441888365)
                      ·
                        rfl

theorem cell23_3582179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3582179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582179 prefixEnd_3582179 := by exact prefixLift 3582179
  have htrace : WordTrace (prefixWord ++ tailWord_3582179) baseStart_3582179 baseEnd_3582179 := by
    simpa [prefixWord, tailWord_3582179, baseEnd_3582179] using wordTrace_append hprefix tailTrace_3582179
  have hstable : (prefixWord ++ tailWord_3582179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582179).length < 2 ^ (prefixWord ++ tailWord_3582179).sum := by decide
  have hdescent : baseEnd_3582179 < baseStart_3582179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582208 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 2, 6]
def baseStart_3582208 : Nat := 118140960795 + 3582208 * 2 ^ 59
def prefixEnd_3582208 : Nat := 4983230072969 + 3 ^ 40 * 3582208 * 2
def baseEnd_3582208 : Nat := 613131502793741942808577

theorem tailTrace_3582208 : CollatzResearch.WordTrace tailWord_3582208 prefixEnd_3582208 613131502793741942808577 := by
  unfold tailWord_3582208
  simp only [CollatzResearch.WordTrace]
  refine ⟨65326929703139841632113639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87102572937519788842818185 65326929703139841632113639)
  ·
    refine ⟨97990394554709762448170459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65326929703139841632113639 97990394554709762448170459)
    ·
      refine ⟨146985591832064643672255689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97990394554709762448170459 146985591832064643672255689)
      ·
        refine ⟨110239193874048482754191767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146985591832064643672255689 110239193874048482754191767)
        ·
          refine ⟨165358790811072724131287651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110239193874048482754191767 165358790811072724131287651)
          ·
            refine ⟨248038186216609086196931477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165358790811072724131287651 248038186216609086196931477)
            ·
              refine ⟨11626789978903550915481163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 248038186216609086196931477 11626789978903550915481163)
              ·
                refine ⟨17440184968355326373221745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11626789978903550915481163 17440184968355326373221745)
                ·
                  refine ⟨13080138726266494779916309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17440184968355326373221745 13080138726266494779916309)
                  ·
                    refine ⟨613131502793741942808577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13080138726266494779916309 613131502793741942808577)
                    ·
                      rfl

theorem cell23_3582208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 2, 6].length) (baseStart_3582208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582208 prefixEnd_3582208 := by exact prefixLift 3582208
  have htrace : WordTrace (prefixWord ++ tailWord_3582208) baseStart_3582208 baseEnd_3582208 := by
    simpa [prefixWord, tailWord_3582208, baseEnd_3582208] using wordTrace_append hprefix tailTrace_3582208
  have hstable : (prefixWord ++ tailWord_3582208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582208).length < 2 ^ (prefixWord ++ tailWord_3582208).sum := by decide
  have hdescent : baseEnd_3582208 < baseStart_3582208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582209 : List Nat := [1, 2, 4, 1, 1, 2, 5, 1, 2, 1, 3]
def baseStart_3582209 : Nat := 118140960795 + 3582209 * 2 ^ 59
def prefixEnd_3582209 : Nat := 4983230072969 + 3 ^ 40 * 3582209 * 2
def baseEnd_3582209 : Nat := 1839395021861880324513227

theorem tailTrace_3582209 : CollatzResearch.WordTrace tailWord_3582209 prefixEnd_3582209 1839395021861880324513227 := by
  unfold tailWord_3582209
  simp only [CollatzResearch.WordTrace]
  refine ⟨130653895879276060435013681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87102597252850706956675787 130653895879276060435013681)
  ·
    refine ⟨97990421909457045326260261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130653895879276060435013681 97990421909457045326260261)
    ·
      refine ⟨18373204108023195998673799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97990421909457045326260261 18373204108023195998673799)
      ·
        refine ⟨27559806162034793998010699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18373204108023195998673799 27559806162034793998010699)
        ·
          refine ⟨41339709243052190997016049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27559806162034793998010699 41339709243052190997016049)
          ·
            refine ⟨31004781932289143247762037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41339709243052190997016049 31004781932289143247762037)
            ·
              refine ⟨2906698306152107179477691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31004781932289143247762037 2906698306152107179477691)
              ·
                refine ⟨4360047459228160769216537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2906698306152107179477691 4360047459228160769216537)
                ·
                  refine ⟨3270035594421120576912403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4360047459228160769216537 3270035594421120576912403)
                  ·
                    refine ⟨4905053391631680865368605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3270035594421120576912403 4905053391631680865368605)
                    ·
                      refine ⟨1839395021861880324513227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4905053391631680865368605 1839395021861880324513227)
                      ·
                        rfl

theorem cell23_3582209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_3582209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582209 prefixEnd_3582209 := by exact prefixLift 3582209
  have htrace : WordTrace (prefixWord ++ tailWord_3582209) baseStart_3582209 baseEnd_3582209 := by
    simpa [prefixWord, tailWord_3582209, baseEnd_3582209] using wordTrace_append hprefix tailTrace_3582209
  have hstable : (prefixWord ++ tailWord_3582209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582209).length < 2 ^ (prefixWord ++ tailWord_3582209).sum := by decide
  have hdescent : baseEnd_3582209 < baseStart_3582209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582232 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 6, 2, 2]
def baseStart_3582232 : Nat := 118140960795 + 3582232 * 2 ^ 59
def prefixEnd_3582232 : Nat := 4983230072969 + 3 ^ 40 * 3582232 * 2
def baseEnd_3582232 : Nat := 1839406831916933734525621

theorem tailTrace_3582232 : CollatzResearch.WordTrace tailWord_3582232 prefixEnd_3582232 1839406831916933734525621 := by
  unfold tailWord_3582232
  simp only [CollatzResearch.WordTrace]
  refine ⟨65327367379096367681550475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87103156505461823575400633 65327367379096367681550475)
  ·
    refine ⟨97991051068644551522325713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65327367379096367681550475 97991051068644551522325713)
    ·
      refine ⟨73493288301483413641744285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97991051068644551522325713 73493288301483413641744285)
      ·
        refine ⟨27559983113056280115654107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73493288301483413641744285 27559983113056280115654107)
        ·
          refine ⟨41339974669584420173481161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27559983113056280115654107 41339974669584420173481161)
          ·
            refine ⟨31004981002188315130110871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41339974669584420173481161 31004981002188315130110871)
            ·
              refine ⟨46507471503282472695166307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31004981002188315130110871 46507471503282472695166307)
              ·
                refine ⟨69761207254923709042749461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46507471503282472695166307 69761207254923709042749461)
                ·
                  refine ⟨3270056590074548861378881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69761207254923709042749461 3270056590074548861378881)
                  ·
                    refine ⟨2452542442555911646034161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3270056590074548861378881 2452542442555911646034161)
                    ·
                      refine ⟨1839406831916933734525621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2452542442555911646034161 1839406831916933734525621)
                      ·
                        rfl

theorem cell23_3582232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_3582232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582232 prefixEnd_3582232 := by exact prefixLift 3582232
  have htrace : WordTrace (prefixWord ++ tailWord_3582232) baseStart_3582232 baseEnd_3582232 := by
    simpa [prefixWord, tailWord_3582232, baseEnd_3582232] using wordTrace_append hprefix tailTrace_3582232
  have hstable : (prefixWord ++ tailWord_3582232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582232).length < 2 ^ (prefixWord ++ tailWord_3582232).sum := by decide
  have hdescent : baseEnd_3582232 < baseStart_3582232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582255 : List Nat := [1, 1, 2, 1, 2, 1, 4, 6, 5]
def baseStart_3582255 : Nat := 118140960795 + 3582255 * 2 ^ 59
def prefixEnd_3582255 : Nat := 4983230072969 + 3 ^ 40 * 3582255 * 2
def baseEnd_3582255 : Nat := 204379849107998571615335

theorem tailTrace_3582255 : CollatzResearch.WordTrace tailWord_3582255 prefixEnd_3582255 204379849107998571615335 := by
  unfold tailWord_3582255
  simp only [CollatzResearch.WordTrace]
  refine ⟨130655573637109410291188219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87103715758072940194125479 130655573637109410291188219)
  ·
    refine ⟨195983360455664115436782329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130655573637109410291188219 195983360455664115436782329)
    ·
      refine ⟨146987520341748086577586747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195983360455664115436782329 146987520341748086577586747)
      ·
        refine ⟨220481280512622129866380121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146987520341748086577586747 220481280512622129866380121)
        ·
          refine ⟨165360960384466597399785091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220481280512622129866380121 165360960384466597399785091)
          ·
            refine ⟨248041440576699896099677637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165360960384466597399785091 248041440576699896099677637)
            ·
              refine ⟨46507770108131230518689557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248041440576699896099677637 46507770108131230518689557)
              ·
                refine ⟨2180051723818651430563573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46507770108131230518689557 2180051723818651430563573)
                ·
                  refine ⟨204379849107998571615335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2180051723818651430563573 204379849107998571615335)
                  ·
                    rfl

theorem cell23_3582255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 5].length) (baseStart_3582255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582255 prefixEnd_3582255 := by exact prefixLift 3582255
  have htrace : WordTrace (prefixWord ++ tailWord_3582255) baseStart_3582255 baseEnd_3582255 := by
    simpa [prefixWord, tailWord_3582255, baseEnd_3582255] using wordTrace_append hprefix tailTrace_3582255
  have hstable : (prefixWord ++ tailWord_3582255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582255).length < 2 ^ (prefixWord ++ tailWord_3582255).sum := by decide
  have hdescent : baseEnd_3582255 < baseStart_3582255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582266 : List Nat := [3, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2]
def baseStart_3582266 : Nat := 118140960795 + 3582266 * 2 ^ 59
def prefixEnd_3582266 : Nat := 4983230072969 + 3 ^ 40 * 3582266 * 2
def baseEnd_3582266 : Nat := 1839424290259186601500465

theorem tailTrace_3582266 : CollatzResearch.WordTrace tailWord_3582266 prefixEnd_3582266 1839424290259186601500465 := by
  unfold tailWord_3582266
  simp only [CollatzResearch.WordTrace]
  refine ⟨32663993710017389792459663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87103983226713039446559101 32663993710017389792459663)
  ·
    refine ⟨48995990565026084688689495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32663993710017389792459663 48995990565026084688689495)
    ·
      refine ⟨73493985847539127033034243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48995990565026084688689495 73493985847539127033034243)
      ·
        refine ⟨110240978771308690549551365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73493985847539127033034243 110240978771308690549551365)
        ·
          refine ⟨20670183519620379478040881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110240978771308690549551365 20670183519620379478040881)
          ·
            refine ⟨15502637639715284608530661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20670183519620379478040881 15502637639715284608530661)
            ·
              refine ⟨2906744557446615864099499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15502637639715284608530661 2906744557446615864099499)
              ·
                refine ⟨4360116836169923796149249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2906744557446615864099499 4360116836169923796149249)
                ·
                  refine ⟨3270087627127442847111937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4360116836169923796149249 3270087627127442847111937)
                  ·
                    refine ⟨2452565720345582135333953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3270087627127442847111937 2452565720345582135333953)
                    ·
                      refine ⟨1839424290259186601500465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2452565720345582135333953 1839424290259186601500465)
                      ·
                        rfl

theorem cell23_3582266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2].length) (baseStart_3582266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582266 prefixEnd_3582266 := by exact prefixLift 3582266
  have htrace : WordTrace (prefixWord ++ tailWord_3582266) baseStart_3582266 baseEnd_3582266 := by
    simpa [prefixWord, tailWord_3582266, baseEnd_3582266] using wordTrace_append hprefix tailTrace_3582266
  have hstable : (prefixWord ++ tailWord_3582266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582266).length < 2 ^ (prefixWord ++ tailWord_3582266).sum := by decide
  have hdescent : baseEnd_3582266 < baseStart_3582266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582306 : List Nat := [3, 3, 2, 1, 1, 4, 2, 2, 5]
def baseStart_3582306 : Nat := 118140960795 + 3582306 * 2 ^ 59
def prefixEnd_3582306 : Nat := 4983230072969 + 3 ^ 40 * 3582306 * 2
def baseEnd_3582306 : Nat := 204382758831707382777809

theorem tailTrace_3582306 : CollatzResearch.WordTrace tailWord_3582306 prefixEnd_3582306 204382758831707382777809 := by
  unfold tailWord_3582306
  simp only [CollatzResearch.WordTrace]
  refine ⟨32664358439981161500323693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87104955839949764000863181 32664358439981161500323693)
  ·
    refine ⟨12249134414992935562621385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32664358439981161500323693 12249134414992935562621385)
    ·
      refine ⟨9186850811244701671966039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12249134414992935562621385 9186850811244701671966039)
      ·
        refine ⟨13780276216867052507949059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9186850811244701671966039 13780276216867052507949059)
        ·
          refine ⟨20670414325300578761923589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13780276216867052507949059 20670414325300578761923589)
          ·
            refine ⟨3875702685993858517860673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20670414325300578761923589 3875702685993858517860673)
            ·
              refine ⟨2906777014495393888395505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3875702685993858517860673 2906777014495393888395505)
              ·
                refine ⟨2180082760871545416296629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2906777014495393888395505 2180082760871545416296629)
                ·
                  refine ⟨204382758831707382777809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2180082760871545416296629 204382758831707382777809)
                  ·
                    rfl

theorem cell23_3582306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_3582306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582306 prefixEnd_3582306 := by exact prefixLift 3582306
  have htrace : WordTrace (prefixWord ++ tailWord_3582306) baseStart_3582306 baseEnd_3582306 := by
    simpa [prefixWord, tailWord_3582306, baseEnd_3582306] using wordTrace_append hprefix tailTrace_3582306
  have hstable : (prefixWord ++ tailWord_3582306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582306).length < 2 ^ (prefixWord ++ tailWord_3582306).sum := by decide
  have hdescent : baseEnd_3582306 < baseStart_3582306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582322 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 1, 6, 2]
def baseStart_3582322 : Nat := 118140960795 + 3582322 * 2 ^ 59
def prefixEnd_3582322 : Nat := 4983230072969 + 3 ^ 40 * 3582322 * 2
def baseEnd_3582322 : Nat := 1839453045175838382400207

theorem tailTrace_3582322 : CollatzResearch.WordTrace tailWord_3582322 prefixEnd_3582322 1839453045175838382400207 := by
  unfold tailWord_3582322
  simp only [CollatzResearch.WordTrace]
  refine ⟨32664504331966670183469305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87105344885244453822584813 32664504331966670183469305)
  ·
    refine ⟨24498378248975002637601979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32664504331966670183469305 24498378248975002637601979)
    ·
      refine ⟨36747567373462503956402969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24498378248975002637601979 36747567373462503956402969)
      ·
        refine ⟨27560675530096877967302227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36747567373462503956402969 27560675530096877967302227)
        ·
          refine ⟨41341013295145316950953341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27560675530096877967302227 41341013295145316950953341)
          ·
            refine ⟨15502879985679493856607503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41341013295145316950953341 15502879985679493856607503)
            ·
              refine ⟨23254319978519240784911255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15502879985679493856607503 23254319978519240784911255)
              ·
                refine ⟨34881479967778861177366883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23254319978519240784911255 34881479967778861177366883)
                ·
                  refine ⟨52322219951668291766050325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34881479967778861177366883 52322219951668291766050325)
                  ·
                    refine ⟨2452604060234451176533609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52322219951668291766050325 2452604060234451176533609)
                    ·
                      refine ⟨1839453045175838382400207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2452604060234451176533609 1839453045175838382400207)
                      ·
                        rfl

theorem cell23_3582322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_3582322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582322 prefixEnd_3582322 := by exact prefixLift 3582322
  have htrace : WordTrace (prefixWord ++ tailWord_3582322) baseStart_3582322 baseEnd_3582322 := by
    simpa [prefixWord, tailWord_3582322, baseEnd_3582322] using wordTrace_append hprefix tailTrace_3582322
  have hstable : (prefixWord ++ tailWord_3582322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582322).length < 2 ^ (prefixWord ++ tailWord_3582322).sum := by decide
  have hdescent : baseEnd_3582322 < baseStart_3582322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582339 : List Nat := [1, 1, 1, 3, 6, 2, 1, 1, 2, 1, 4]
def baseStart_3582339 : Nat := 118140960795 + 3582339 * 2 ^ 59
def prefixEnd_3582339 : Nat := 4983230072969 + 3 ^ 40 * 3582339 * 2
def baseEnd_3582339 : Nat := 1839461774346964815887629

theorem tailTrace_3582339 : CollatzResearch.WordTrace tailWord_3582339 prefixEnd_3582339 1839461774346964815887629 := by
  unfold tailWord_3582339
  simp only [CollatzResearch.WordTrace]
  refine ⟨130658637368805092637246071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87105758245870061758164047 130658637368805092637246071)
  ·
    refine ⟨195987956053207638955869107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130658637368805092637246071 195987956053207638955869107)
    ·
      refine ⟨293981934079811458433803661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195987956053207638955869107 293981934079811458433803661)
      ·
        refine ⟨110243225279929296912676373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293981934079811458433803661 110243225279929296912676373)
        ·
          refine ⟨5167651184996685792781705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 110243225279929296912676373 5167651184996685792781705)
          ·
            refine ⟨3875738388747514344586279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5167651184996685792781705 3875738388747514344586279)
            ·
              refine ⟨5813607583121271516879419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3875738388747514344586279 5813607583121271516879419)
              ·
                refine ⟨8720411374681907275319129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5813607583121271516879419 8720411374681907275319129)
                ·
                  refine ⟨6540308531011430456489347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8720411374681907275319129 6540308531011430456489347)
                  ·
                    refine ⟨9810462796517145684734021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6540308531011430456489347 9810462796517145684734021)
                    ·
                      refine ⟨1839461774346964815887629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9810462796517145684734021 1839461774346964815887629)
                      ·
                        rfl

theorem cell23_3582339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 1, 4].length) (baseStart_3582339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582339 prefixEnd_3582339 := by exact prefixLift 3582339
  have htrace : WordTrace (prefixWord ++ tailWord_3582339) baseStart_3582339 baseEnd_3582339 := by
    simpa [prefixWord, tailWord_3582339, baseEnd_3582339] using wordTrace_append hprefix tailTrace_3582339
  have hstable : (prefixWord ++ tailWord_3582339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582339).length < 2 ^ (prefixWord ++ tailWord_3582339).sum := by decide
  have hdescent : baseEnd_3582339 < baseStart_3582339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582362 : List Nat := [3, 1, 1, 4, 1, 2, 3, 2, 6]
def baseStart_3582362 : Nat := 118140960795 + 3582362 * 2 ^ 59
def prefixEnd_3582362 : Nat := 4983230072969 + 3 ^ 40 * 3582362 * 2
def baseEnd_3582362 : Nat := 204385953822446469544447

theorem tailTrace_3582362 : CollatzResearch.WordTrace tailWord_3582362 prefixEnd_3582362 204385953822446469544447 := by
  unfold tailWord_3582362
  simp only [CollatzResearch.WordTrace]
  refine ⟨32664869061930441891333335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87106317498481178376888893 32664869061930441891333335)
  ·
    refine ⟨48997303592895662837000003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32664869061930441891333335 48997303592895662837000003)
    ·
      refine ⟨73495955389343494255500005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48997303592895662837000003 73495955389343494255500005)
      ·
        refine ⟨13780491635501905172906251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73495955389343494255500005 13780491635501905172906251)
        ·
          refine ⟨20670737453252857759359377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13780491635501905172906251 20670737453252857759359377)
          ·
            refine ⟨15503053089939643319519533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20670737453252857759359377 15503053089939643319519533)
            ·
              refine ⟨5813644908727366244819825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15503053089939643319519533 5813644908727366244819825)
              ·
                refine ⟨4360233681545524683614869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5813644908727366244819825 4360233681545524683614869)
                ·
                  refine ⟨204385953822446469544447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4360233681545524683614869 204385953822446469544447)
                  ·
                    rfl

theorem cell23_3582362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 6].length) (baseStart_3582362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582362 prefixEnd_3582362 := by exact prefixLift 3582362
  have htrace : WordTrace (prefixWord ++ tailWord_3582362) baseStart_3582362 baseEnd_3582362 := by
    simpa [prefixWord, tailWord_3582362, baseEnd_3582362] using wordTrace_append hprefix tailTrace_3582362
  have hstable : (prefixWord ++ tailWord_3582362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582362).length < 2 ^ (prefixWord ++ tailWord_3582362).sum := by decide
  have hdescent : baseEnd_3582362 < baseStart_3582362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582366 : List Nat := [4, 3, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_3582366 : Nat := 118140960795 + 3582366 * 2 ^ 59
def prefixEnd_3582366 : Nat := 4983230072969 + 3 ^ 40 * 3582366 * 2
def baseEnd_3582366 : Nat := 613158546108212070083335

theorem tailTrace_3582366 : CollatzResearch.WordTrace tailWord_3582366 prefixEnd_3582366 613158546108212070083335 := by
  unfold tailWord_3582366
  simp only [CollatzResearch.WordTrace]
  refine ⟨16332452767463409531059869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87106414759804850832319301 16332452767463409531059869)
  ·
    refine ⟨6124669787798778574147451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16332452767463409531059869 6124669787798778574147451)
    ·
      refine ⟨9187004681698167861221177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6124669787798778574147451 9187004681698167861221177)
      ·
        refine ⟨6890253511273625895915883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9187004681698167861221177 6890253511273625895915883)
        ·
          refine ⟨10335380266910438843873825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6890253511273625895915883 10335380266910438843873825)
          ·
            refine ⟨7751535200182829132905369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10335380266910438843873825 7751535200182829132905369)
            ·
              refine ⟨5813651400137121849679027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7751535200182829132905369 5813651400137121849679027)
              ·
                refine ⟨8720477100205682774518541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5813651400137121849679027 8720477100205682774518541)
                ·
                  refine ⟨3270178912577131040444453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8720477100205682774518541 3270178912577131040444453)
                  ·
                    refine ⟨613158546108212070083335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3270178912577131040444453 613158546108212070083335)
                    ·
                      rfl

theorem cell23_3582366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_3582366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582366 prefixEnd_3582366 := by exact prefixLift 3582366
  have htrace : WordTrace (prefixWord ++ tailWord_3582366) baseStart_3582366 baseEnd_3582366 := by
    simpa [prefixWord, tailWord_3582366, baseEnd_3582366] using wordTrace_append hprefix tailTrace_3582366
  have hstable : (prefixWord ++ tailWord_3582366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582366).length < 2 ^ (prefixWord ++ tailWord_3582366).sum := by decide
  have hdescent : baseEnd_3582366 < baseStart_3582366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582425 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 3, 1, 6]
def baseStart_3582425 : Nat := 118140960795 + 3582425 * 2 ^ 59
def prefixEnd_3582425 : Nat := 4983230072969 + 3 ^ 40 * 3582425 * 2
def baseEnd_3582425 : Nat := 1839505933683251479412233

theorem tailTrace_3582425 : CollatzResearch.WordTrace tailWord_3582425 prefixEnd_3582425 1839505933683251479412233 := by
  unfold tailWord_3582425
  simp only [CollatzResearch.WordTrace]
  refine ⟨130661774046493529324876729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87107849364329019549917819 130661774046493529324876729)
  ·
    refine ⟨97996330534870146993657547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130661774046493529324876729 97996330534870146993657547)
    ·
      refine ⟨146994495802305220490486321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97996330534870146993657547 146994495802305220490486321)
      ·
        refine ⟨110245871851728915367864741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146994495802305220490486321 110245871851728915367864741)
        ·
          refine ⟨20671100972199171631474639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110245871851728915367864741 20671100972199171631474639)
          ·
            refine ⟨31006651458298757447211959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20671100972199171631474639 31006651458298757447211959)
            ·
              refine ⟨46509977187448136170817939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31006651458298757447211959 46509977187448136170817939)
              ·
                refine ⟨69764965781172204256226909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46509977187448136170817939 69764965781172204256226909)
                ·
                  refine ⟨26161862167939576596085091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69764965781172204256226909 26161862167939576596085091)
                  ·
                    refine ⟨39242793251909364894127637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26161862167939576596085091 39242793251909364894127637)
                    ·
                      refine ⟨1839505933683251479412233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39242793251909364894127637 1839505933683251479412233)
                      ·
                        rfl

theorem cell23_3582425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_3582425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582425 prefixEnd_3582425 := by exact prefixLift 3582425
  have htrace : WordTrace (prefixWord ++ tailWord_3582425) baseStart_3582425 baseEnd_3582425 := by
    simpa [prefixWord, tailWord_3582425, baseEnd_3582425] using wordTrace_append hprefix tailTrace_3582425
  have hstable : (prefixWord ++ tailWord_3582425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582425).length < 2 ^ (prefixWord ++ tailWord_3582425).sum := by decide
  have hdescent : baseEnd_3582425 < baseStart_3582425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582432 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 3]
def baseStart_3582432 : Nat := 118140960795 + 3582432 * 2 ^ 59
def prefixEnd_3582432 : Nat := 4983230072969 + 3 ^ 40 * 3582432 * 2
def baseEnd_3582432 : Nat := 1839509528047832952024701

theorem tailTrace_3582432 : CollatzResearch.WordTrace tailWord_3582432 prefixEnd_3582432 1839509528047832952024701 := by
  unfold tailWord_3582432
  simp only [CollatzResearch.WordTrace]
  refine ⟨65331014678734084760190775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87108019571645446346921033 65331014678734084760190775)
  ·
    refine ⟨97996522018101127140286163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65331014678734084760190775 97996522018101127140286163)
    ·
      refine ⟨146994783027151690710429245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97996522018101127140286163 146994783027151690710429245)
      ·
        refine ⟨55123043635181884016410967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146994783027151690710429245 55123043635181884016410967)
        ·
          refine ⟨82684565452772826024616451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55123043635181884016410967 82684565452772826024616451)
          ·
            refine ⟨124026848179159239036924677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82684565452772826024616451 124026848179159239036924677)
            ·
              refine ⟨23255034033592357319423377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124026848179159239036924677 23255034033592357319423377)
              ·
                refine ⟨17441275525194267989567533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23255034033592357319423377 17441275525194267989567533)
                ·
                  refine ⟨6540478321947850496087825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17441275525194267989567533 6540478321947850496087825)
                  ·
                    refine ⟨4905358741460887872065869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6540478321947850496087825 4905358741460887872065869)
                    ·
                      refine ⟨1839509528047832952024701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4905358741460887872065869 1839509528047832952024701)
                      ·
                        rfl

theorem cell23_3582432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_3582432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582432 prefixEnd_3582432 := by exact prefixLift 3582432
  have htrace : WordTrace (prefixWord ++ tailWord_3582432) baseStart_3582432 baseEnd_3582432 := by
    simpa [prefixWord, tailWord_3582432, baseEnd_3582432] using wordTrace_append hprefix tailTrace_3582432
  have hstable : (prefixWord ++ tailWord_3582432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582432).length < 2 ^ (prefixWord ++ tailWord_3582432).sum := by decide
  have hdescent : baseEnd_3582432 < baseStart_3582432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
